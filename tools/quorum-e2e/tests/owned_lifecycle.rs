//! Real Ed25519 + fsync journals for SPEC-033, with one silent validator.
use cbcl_core::{
    intend::Instance,
    quorum::*,
    role::AgentKey,
    sexpr::{Atom, SExpr},
    state::Act,
    store::ThreadId,
};
use cbcl_parser::{parse, parse_dialect};
use cbcl_quorum_e2e::{
    journal::{DurableJournal, DurableOwnerJournal},
    model::*,
};
use ed25519_dalek::{Signer, SigningKey};
use std::collections::{BTreeMap, BTreeSet};
fn sign(req: SigningRequest, key: &SigningKey) -> Vote {
    let sig = key.sign(&req.preimage()).to_bytes().to_vec();
    req.attach(sig)
}
#[test]
fn full_balance_real_signatures_durable_seal_and_restart() {
    let source = include_str!("../../../dialects/example-coin.cbcl").replace(
        "(floor 0)",
        "(floor 0) (certification quorum-budget (validators @v0 @v1 @v2 @v3))",
    );
    let d = parse_dialect(&parse(&source).unwrap()).unwrap();
    let owner = SigningKey::from_bytes(&[11; 32]);
    let keys: Vec<_> = (0..4)
        .map(|i| SigningKey::from_bytes(&[20 + i; 32]))
        .collect();
    let root = parse_act("(with-roles ((issuer @treasury) (holder @treasury @alice @bob)) (signed @treasury (hello :thread \"coin-1\" :caused-by begin)))", "@treasury").unwrap();
    let open = parse_act(&format!("(signed @treasury (lang example-coin (open (@alice @bob @treasury) :name \"Coin\" :allocations ((@treasury 1) (@alice 0) (@bob 0)) :from @treasury :thread \"coin-1\" :caused-by {})))", root.address), "@treasury").unwrap();
    let genesis = vec![sign_act(root, &owner), sign_act(open, &owner)];
    let mut public_keys: BTreeMap<_, _> = keys
        .iter()
        .enumerate()
        .map(|(i, k)| (format!("@v{i}"), k.verifying_key().to_bytes()))
        .collect();
    public_keys.insert("@treasury".into(), owner.verifying_key().to_bytes());
    let setup = Setup {
        public_keys,
        genesis: genesis.clone(),
        transactions: 1,
        delay_ms: 0,
        silent_validators: 1,
        byzantine_mode: ByzantineMode::None,
        queue_capacity: 8,
        journal_batch_size: 1,
        journal_batch_wait_ms: 0,
    };
    let mut auth = Auth::with_dialect(&setup, d.clone()).unwrap();
    let base: Vec<_> = genesis.iter().map(|s| s.act.clone()).collect();
    let inst = Instance::new(&d, ThreadId("coin-1".into()), &base).unwrap();
    let ctx = Context::from_instance(&inst, "coins", None, &auth).unwrap();
    let dir = tempfile::tempdir().unwrap();
    let mut journals: Vec<_> = (0..4)
        .map(|i| {
            DurableJournal::open(
                &dir.path().join(format!("v{i}.jsonl")),
                ctx.id(),
                &format!("@v{i}"),
            )
            .unwrap()
            .0
        })
        .collect();
    let mut replicas: Vec<_> = journals
        .iter_mut()
        .enumerate()
        .map(|(i, j)| {
            Replica::initialize(ctx.clone(), &format!("@v{i}"), Limits::default(), j).unwrap()
        })
        .collect();
    let owner_path = dir.path().join("treasury.owner.jsonl");
    let mut owner_journal = DurableOwnerJournal::open(&owner_path, ctx.id(), "@treasury").unwrap();
    let mut driver = OwnerDriver::initialize(
        &replicas[0],
        "@treasury",
        Limits::default(),
        &mut owner_journal,
    )
    .unwrap();
    let draft_message = replicas[0]
        .intend(
            &inst,
            &AgentKey("@treasury".into()),
            "pay",
            BTreeMap::from([
                (
                    "recipient".into(),
                    SExpr::Atom(Atom::Symbol("@alice".into())),
                ),
                ("amount".into(), SExpr::Atom(Atom::Num(1))),
            ]),
            "last-unit",
        )
        .unwrap();
    driver
        .enqueue(
            Act::from_message(draft_message, "@treasury").unwrap(),
            &replicas[0],
            &mut owner_journal,
        )
        .unwrap();
    assert!(matches!(
        driver.poll(&replicas[0], &mut owner_journal).unwrap(),
        OwnerAction::AuthorizeSeal { .. }
    ));
    let mut m = replicas[0]
        .draft_version(
            &BTreeSet::from([replicas[0].active_epoch("@treasury").unwrap().into()]),
            &BTreeSet::new(),
            &BTreeSet::new(),
            &BTreeSet::new(),
        )
        .unwrap();
    m.phase = VersionPhase::Owned;
    let id = m.id(ctx.id());
    let req = OwnedSealRequest {
        authorization: sign(ctx.owned_seal_request(&m, "@treasury").unwrap(), &owner),
        version: DagVersion {
            authorization: sign(ctx.version_request(&m, "@treasury").unwrap(), &owner),
            manifest: m,
        },
    };
    let votes = (0..3)
        .map(|i| {
            sign(
                replicas[i]
                    .prepare_owned_seal(req.clone(), &mut journals[i], &auth)
                    .unwrap(),
                &keys[i],
            )
        })
        .collect();
    let seal = Certificate {
        kind: VoteKind::OwnedSeal,
        payload: id.clone(),
        votes,
    };
    for i in [0, 1, 3] {
        replicas[i]
            .record_owned_proposal(req.clone(), &mut journals[i], &auth)
            .unwrap();
        replicas[i]
            .receive(seal.clone(), &mut journals[i], &auth)
            .unwrap();
        replicas[i]
            .adopt_version(&id, &mut journals[i], &auth)
            .unwrap();
    }
    let message = replicas[0]
        .intend(
            &inst,
            &AgentKey("@treasury".into()),
            "pay",
            BTreeMap::from([
                (
                    "recipient".into(),
                    SExpr::Atom(Atom::Symbol("@alice".into())),
                ),
                ("amount".into(), SExpr::Atom(Atom::Num(1))),
            ]),
            "last-unit",
        )
        .unwrap();
    let act = Act::from_message(message, "@treasury").unwrap();
    let OwnerAction::Publish(publication) = driver.poll(&replicas[0], &mut owner_journal).unwrap()
    else {
        panic!()
    };
    assert_eq!(publication.act, act);
    drop(driver);
    drop(owner_journal);
    let mut owner_journal = DurableOwnerJournal::open(&owner_path, ctx.id(), "@treasury").unwrap();
    let mut driver =
        OwnerDriver::recover(&replicas[0], "@treasury", Limits::default(), &owner_journal).unwrap();
    assert_eq!(
        published(driver.poll(&replicas[0], &mut owner_journal).unwrap()),
        act.clone()
    );
    let signed = sign_act(act, &owner);
    auth.remember(&signed);
    for journal in &mut journals {
        journal.pending_act = Some(signed.clone());
    }
    let mut receiver_auth = Auth::with_dialect(&setup, d.clone()).unwrap();
    assert!(replicas[2]
        .prepare_publication(&publication, &mut journals[2], &receiver_auth)
        .is_err());
    receiver_auth.remember(&signed); // actual envelope delivered to this recipient
    let votes = (0..3)
        .map(|i| {
            let verifier = if i == 2 { &receiver_auth } else { &auth };
            let PublicationResult::Operation(request) = replicas[i]
                .prepare_publication(&publication, &mut journals[i], verifier)
                .unwrap()
            else {
                panic!("operation expected")
            };
            sign(request, &keys[i])
        })
        .collect();
    let op = Certificate {
        kind: VoteKind::Operation,
        payload: signed.act.address.clone(),
        votes,
    };
    replicas[3]
        .register(signed.act.clone(), &mut journals[3], &auth)
        .unwrap();
    for i in 0..4 {
        replicas[i]
            .receive(op.clone(), &mut journals[i], &auth)
            .unwrap();
    }
    let votes = (0..3)
        .map(|i| {
            sign(
                replicas[i]
                    .prepare_effects(&signed.act.address, &mut journals[i], &auth)
                    .unwrap(),
                &keys[i],
            )
        })
        .collect();
    let effects = Certificate {
        kind: VoteKind::Effects,
        payload: signed.act.address.clone(),
        votes,
    };
    for i in 0..4 {
        replicas[i]
            .receive(effects.clone(), &mut journals[i], &auth)
            .unwrap();
    }
    assert_eq!(
        driver.poll(&replicas[0], &mut owner_journal).unwrap(),
        OwnerAction::Idle
    );
    drop(driver);
    drop(owner_journal);
    let expected = replicas[0].finalized_view().unwrap();
    assert_eq!(expected.rights["@treasury"], 0);
    drop(replicas);
    drop(journals);
    for i in 0..4 {
        let (journal, _) = DurableJournal::open(
            &dir.path().join(format!("v{i}.jsonl")),
            ctx.id(),
            &format!("@v{i}"),
        )
        .unwrap();
        let recovered = Replica::recover(
            ctx.clone(),
            &format!("@v{i}"),
            Limits::default(),
            &journal,
            &auth,
        )
        .unwrap();
        assert_eq!(recovered.finalized_view().unwrap(), expected);
        assert_eq!(recovered.owned_root("@treasury"), Some(id.as_str()));
    }
}

#[test]
fn durable_owner_journal_fences_forks_and_torn_suffixes() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("owner.jsonl");
    let mut j = DurableOwnerJournal::open(&path, "context", "@owner").unwrap();
    assert!(DurableOwnerJournal::open(&path, "context", "@owner").is_err());
    j.append_owner("context", "@owner", None, &OwnerEvent::Initialize)
        .unwrap();
    let expected = std::fs::read(&path).unwrap();
    assert!(j
        .append_owner("context", "@owner", Some(0), &OwnerEvent::Freeze)
        .is_err());
    assert_eq!(std::fs::read(&path).unwrap(), expected);
    drop(j);
    assert!(DurableOwnerJournal::open(&path, "wrong-context", "@owner").is_err());
    std::fs::write(&path, &expected[..expected.len() - 1]).unwrap();
    assert!(DurableOwnerJournal::open(&path, "context", "@owner").is_err());
}

fn published(action: OwnerAction) -> Act {
    match action {
        OwnerAction::Publish(publication) => publication.act,
        _ => panic!("expected durable publication"),
    }
}
