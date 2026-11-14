use cbcl_core::quorum::{Authentication, Event, Journal};
use cbcl_quorum_e2e::{
    journal::DurableJournal,
    metrics::{summarize, Outcome},
    model::*,
};
use ed25519_dalek::SigningKey;
use serde_json::Value;
use std::{collections::BTreeMap, process::Command};

#[test]
fn signatures_bind_actor_and_message() {
    let key = SigningKey::from_bytes(&[7; 32]);
    let act = parse_act(
        "(lang test (pay (@bob) :amount 1 :from @alice :thread \"t\"))",
        "@alice",
    )
    .unwrap();
    let signed = sign_act(act, &key);
    let setup = Setup {
        public_keys: BTreeMap::from([("@alice".into(), key.verifying_key().to_bytes())]),
        genesis: vec![signed.clone()],
        transactions: 1,
        delay_ms: 0,
        silent_validators: 0,
        byzantine_mode: ByzantineMode::None,
        queue_capacity: 8,
        journal_batch_size: 64,
        journal_batch_wait_ms: 1,
    };
    let auth = Auth::new(&setup).unwrap();
    assert!(auth.verify("@alice", &act_preimage(&signed.act), &signed.signature));
    let mut bad = signed.act.clone();
    bad.signer = "@bob".into();
    assert!(!auth.authenticate_act(&bad));
    let mut signature = signed.signature.clone();
    signature[0] ^= 1;
    assert!(!auth.verify("@alice", &act_preimage(&signed.act), &signature));
}

#[test]
fn durable_journal_cas_lock_and_torn_recovery() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("journal.jsonl");
    let (mut journal, _) = DurableJournal::open(&path, "ctx", "@v0").unwrap();
    assert!(DurableJournal::open(&path, "ctx", "@v0").is_err());
    journal
        .append("ctx", "@v0", None, &Event::Initialize)
        .unwrap();
    let bytes = std::fs::read(&path).unwrap();
    assert!(journal
        .append("ctx", "@v0", Some(0), &Event::Initialize)
        .is_err());
    assert_eq!(std::fs::read(&path).unwrap(), bytes);
    assert_eq!(journal.syncs, 1);
    drop(journal);
    let (journal, records) = DurableJournal::open(&path, "ctx", "@v0").unwrap();
    assert_eq!(records.len(), 1);
    assert_eq!(
        journal.load("ctx", "@v0").unwrap().unwrap(),
        vec![Event::Initialize]
    );
    drop(journal);
    std::fs::write(&path, &bytes[..bytes.len() - 1]).unwrap();
    assert!(DurableJournal::open(&path, "ctx", "@v0").is_err());
    let mut blank = bytes;
    blank.push(b'\n');
    std::fs::write(&path, blank).unwrap();
    assert!(DurableJournal::open(&path, "ctx", "@v0").is_err());
}

#[test]
fn stalls_and_overload_remain_in_metrics() {
    let row = |sequence, submitted, latency| Outcome {
        sequence,
        id: String::new(),
        status: String::new(),
        submitted_ms: submitted,
        finality_ms: latency,
        scheduler_lateness_ms: 0.,
        errors: 0,
        effects_certificate: None,
    };
    let report = summarize(
        &[
            row(0, Some(0.), Some(1000.)),
            row(1, Some(1.), None),
            row(2, None, None),
        ],
        1500,
        2.,
    );
    assert_eq!(
        report["all_submitted_latency_ms"]["p99"]["right_censored"],
        true
    );
    assert_eq!(report["finalized_latency_ms"]["p99"], 1000.);
    assert_eq!(report["fraction_within_one_second_of_submitted"], 0.5);
    assert_eq!(report["stalled"], 1);
    assert_eq!(report["client_overload"], 1);
    let empty = summarize(&[row(0, Some(0.), None)], 1000, 1.);
    assert!(empty["finalized_latency_ms"]["p50"].is_null());
}

fn run(extra: &[&str]) -> (tempfile::TempDir, Value) {
    let temp = tempfile::tempdir().unwrap();
    let out = temp.path().join("run");
    let result = Command::new(env!("CARGO_BIN_EXE_cbcl-quorum-e2e"))
        .args([
            "--allow-debug",
            "--transactions",
            "6",
            "--rate",
            "20",
            "--timeout-ms",
            "2000",
            "--out",
        ])
        .arg(&out)
        .args(extra)
        .output()
        .unwrap();
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    let report = serde_json::from_slice(&std::fs::read(out.join("report.json")).unwrap()).unwrap();
    (temp, report)
}
#[test]
fn four_process_finality_and_recovery() {
    let (temp, report) = run(&["--delay-ms", "5", "--silent-validators", "1"]);
    assert_eq!(report["metrics"]["finalized"], 6);
    assert_eq!(report["recovery_passed"], true);
    assert!(
        report["metrics"]["finalized_latency_ms"]["p50"]
            .as_f64()
            .unwrap()
            >= 20.
    );
    for observation in report["validator_observations"]
        .as_object()
        .unwrap()
        .values()
    {
        let profile = &observation["profile"];
        let sync = &profile["journal"]["journal_sync"];
        assert_eq!(
            sync["count"].as_u64().unwrap() + 1,
            observation["syncs"].as_u64().unwrap()
        );
        let service = profile["request_service"]["total_ms"].as_f64().unwrap();
        let mut components = profile["vote_signing"]["total_ms"].as_f64().unwrap();
        for group in ["journal", "authentication"] {
            for counter in profile[group].as_object().unwrap().values() {
                components += counter["total_ms"].as_f64().unwrap();
            }
        }
        assert!(components <= service + 0.01);
        if service > 0. {
            assert!(sync["total_ms"].as_f64().unwrap() > 0.);
        }
    }
    let validators = report["validators"].as_array().unwrap();
    assert_eq!(validators.len(), 4);
    let mut pids = std::collections::BTreeSet::new();
    for v in validators {
        assert_ne!(v["pid"], report["client_pid"]);
        pids.insert(v["pid"].as_u64().unwrap());
    }
    assert_eq!(pids.len(), 4);
    let setup: Setup =
        serde_json::from_slice(&std::fs::read(temp.path().join("run/public-setup.json")).unwrap())
            .unwrap();
    let auth = Auth::new(&setup).unwrap();
    let ctx = context(&setup, &auth).unwrap();
    // Even a real owner signature cannot authorize bad protocol evidence.
    let mut negative_setup = setup.clone();
    let key = SigningKey::from_bytes(&[9; 32]);
    negative_setup
        .public_keys
        .insert("@alice".into(), key.verifying_key().to_bytes());
    let mut negative_auth = Auth::new(&negative_setup).unwrap();
    let good = transaction(&negative_setup, &ctx, 0, &key).unwrap();
    negative_auth.remember(&good);
    assert!(negative_auth.authenticate_act(&good.act));
    let text = cbcl_core::intend::canonical_text(&good.act.message);
    for bad_text in [
        text.replace(
            &setup.genesis[1].act.address,
            &format!("{}00", setup.genesis[1].act.address),
        ),
        text.replace("(@alice @bob @treasury)", "(@customer)"),
    ] {
        assert_ne!(bad_text, text);
        let bad = sign_act(parse_act(&bad_text, "@alice").unwrap(), &key);
        negative_auth.remember(&bad);
        assert!(!negative_auth.authenticate_act(&bad.act));
    }
    for line in std::fs::read_to_string(temp.path().join("run/transactions.jsonl"))
        .unwrap()
        .lines()
    {
        let row: Outcome = serde_json::from_str(line).unwrap();
        let cert = row.effects_certificate.unwrap();
        verify_certificate(
            &auth,
            &ctx,
            &cert,
            cbcl_core::quorum::VoteKind::Effects,
            &row.id,
        )
        .unwrap();
        let mut bad = cert.clone();
        bad.votes[1] = bad.votes[0].clone();
        assert!(verify_certificate(&auth, &ctx, &bad, bad.kind, &row.id).is_err());
        let mut bad = cert;
        bad.votes[0].signature[0] ^= 1;
        assert!(verify_certificate(&auth, &ctx, &bad, bad.kind, &row.id).is_err());
    }
}
#[test]
fn missing_quorum_stalls_and_counts_overload() {
    let (_, report) = run(&["--silent-validators", "2", "--max-inflight", "1"]);
    assert_eq!(report["metrics"]["finalized"], 0);
    assert_eq!(report["metrics"]["stalled"], 1);
    assert_eq!(report["metrics"]["client_overload"], 5);
    assert_eq!(
        report["metrics"]["fraction_within_one_second_of_offered"],
        0.
    );
    assert_eq!(
        report["metrics"]["all_submitted_latency_ms"]["p50"]["right_censored"],
        true
    );
}

#[test]
fn active_byzantine_validator_cannot_forge_finality() {
    for mode in ["withhold", "equivocate", "invalid-flood"] {
        // This is a safety/liveness check, not a latency benchmark. In the
        // workspace suite it competes with other process-heavy tests, and the
        // invalid flood deliberately adds signature-verification work.
        let (temp, report) = run(&["--timeout-ms", "10000", "--byzantine-mode", mode]);
        assert_eq!(report["config"]["byzantine_mode"], mode);
        assert_eq!(report["metrics"]["finalized"], 6, "{mode}");
        assert_eq!(report["metrics"]["stalled"], 0, "{mode}");
        assert_eq!(report["transport_errors"], 0, "{mode}");
        assert_eq!(report["recovery_passed"], true, "{mode}");
        let observations = report["validator_observations"].as_object().unwrap();
        let fault = &observations["0"]["profile"]["byzantine"];
        assert!(fault["requests"].as_u64().unwrap() > 0);
        match mode {
            "withhold" => assert!(fault["withheld"].as_u64().unwrap() > 0),
            "equivocate" => {
                assert!(fault["conflicting_pairs"].as_u64().unwrap() > 0);
                assert!(report["verified_cancel_votes_ignored"].as_u64().unwrap() > 0);
            }
            "invalid-flood" => {
                assert!(fault["invalid_sent"].as_u64().unwrap() > 0);
                assert!(report["invalid_votes"].as_u64().unwrap() > 0);
            }
            _ => unreachable!(),
        }
        for index in ["1", "2", "3"] {
            assert_eq!(observations[index]["finalized"], 6, "{mode}");
            assert_eq!(observations[index]["value"], 999999994, "{mode}");
        }
        let setup: Setup = serde_json::from_slice(
            &std::fs::read(temp.path().join("run/public-setup.json")).unwrap(),
        )
        .unwrap();
        let auth = Auth::new(&setup).unwrap();
        let ctx = context(&setup, &auth).unwrap();
        for line in std::fs::read_to_string(temp.path().join("run/transactions.jsonl"))
            .unwrap()
            .lines()
        {
            let row: Outcome = serde_json::from_str(line).unwrap();
            let cert = row.effects_certificate.unwrap();
            verify_certificate(
                &auth,
                &ctx,
                &cert,
                cbcl_core::quorum::VoteKind::Effects,
                &row.id,
            )
            .unwrap();
            assert_eq!(cert.votes.len(), 3);
            assert!(cert.votes.iter().filter(|v| v.signer != "@v0").count() >= 2);
        }
    }
}

#[test]
fn byzantine_injection_uses_real_conflicts_and_invalid_signatures() {
    use cbcl_core::quorum::{Certificate, VoteKind};
    use cbcl_quorum_e2e::{
        faults::{Faults, INVALID_REPLIES_PER_REQUEST},
        transport::Request,
    };
    let (setup, auth, ctx, _) = fixture();
    let key = SigningKey::from_bytes(&[1; 32]);
    let request = Request::Effects {
        certificate: Certificate {
            kind: VoteKind::Operation,
            payload: "same-transaction".into(),
            votes: vec![],
        },
    };
    let mut faults = Faults::default();
    let pair = faults.respond(ByzantineMode::Equivocate, &request, ctx.id(), "@v0", &key);
    assert_eq!(pair.len(), 2);
    assert_eq!(pair[0].kind, VoteKind::Cancel);
    assert_eq!(pair[1].kind, VoteKind::Effects);
    assert_eq!(pair[0].payload, pair[1].payload);
    for vote in &pair {
        VerifiedVote::verify(&auth, &ctx, vote.clone(), vote.kind, &vote.payload).unwrap();
        // Equivocation by one committee key cannot create either quorum.
        let cert = Certificate {
            kind: vote.kind,
            payload: vote.payload.clone(),
            votes: vec![vote.clone(); 3],
        };
        assert!(verify_certificate(&auth, &ctx, &cert, vote.kind, &vote.payload).is_err());
    }
    let bad = faults.respond(ByzantineMode::InvalidFlood, &request, ctx.id(), "@v0", &key);
    assert_eq!(bad.len(), INVALID_REPLIES_PER_REQUEST);
    for vote in bad {
        assert!(VerifiedVote::verify(&auth, &ctx, vote.clone(), vote.kind, &vote.payload).is_err());
    }
    let mut faults = Faults::default();
    assert!(faults
        .respond(ByzantineMode::Withhold, &request, ctx.id(), "@v0", &key)
        .is_empty());
    assert_eq!(
        faults
            .respond(ByzantineMode::Withhold, &request, ctx.id(), "@v0", &key)
            .len(),
        1
    );
    assert!(faults
        .respond(
            ByzantineMode::Withhold,
            &Request::Stop,
            ctx.id(),
            "@v0",
            &key
        )
        .is_empty());
    assert_eq!(faults.requests, 2);
    assert_eq!(faults.withheld, 1);
    assert_eq!(setup.byzantine_mode, ByzantineMode::None);
}

#[test]
fn invalid_byzantine_cli_settings_are_rejected() {
    for args in [
        vec!["--byzantine-mode", "unknown"],
        vec!["--byzantine-mode", "withhold", "--silent-validators", "1"],
    ] {
        let result = Command::new(env!("CARGO_BIN_EXE_cbcl-quorum-e2e"))
            .arg("--allow-debug")
            .args(args)
            .output()
            .unwrap();
        assert!(!result.status.success());
        assert!(String::from_utf8_lossy(&result.stderr).contains("Byzantine"));
    }
}

fn fixture() -> (Setup, Auth, cbcl_core::quorum::Context, SigningKey) {
    let treasury = SigningKey::from_bytes(&[8; 32]);
    let alice = SigningKey::from_bytes(&[9; 32]);
    let mut public_keys = BTreeMap::from([
        ("@treasury".into(), treasury.verifying_key().to_bytes()),
        ("@alice".into(), alice.verifying_key().to_bytes()),
    ]);
    for (i, id) in VALIDATORS.iter().enumerate() {
        public_keys.insert(
            (*id).into(),
            SigningKey::from_bytes(&[i as u8 + 1; 32])
                .verifying_key()
                .to_bytes(),
        );
    }
    let root=sign_act(parse_act(&format!("(with-roles ((organizer @treasury) (seller @alice @bob)) (signed @treasury (hello :thread \"{THREAD}\" :caused-by begin)))"),"@treasury").unwrap(),&treasury);
    let open=sign_act(parse_act(&format!("(signed @treasury (lang collective-tickets (open (@alice @bob @treasury) :available 1000000000 :from @treasury :thread \"{THREAD}\" :caused-by {})))",root.act.address),"@treasury").unwrap(),&treasury);
    let setup = Setup {
        public_keys,
        genesis: vec![root, open],
        transactions: 8,
        delay_ms: 0,
        silent_validators: 0,
        byzantine_mode: ByzantineMode::None,
        queue_capacity: 32,
        journal_batch_size: 64,
        journal_batch_wait_ms: 1,
    };
    let auth = Auth::new(&setup).unwrap();
    let ctx = context(&setup, &auth).unwrap();
    (setup, auth, ctx, alice)
}
struct FailingGroup {
    journal: DurableJournal,
    fail: bool,
}
impl Journal for FailingGroup {
    fn load(&self, c: &str, v: &str) -> Result<Option<Vec<Event>>> {
        self.journal.load(c, v)
    }
    fn append(&mut self, c: &str, v: &str, n: Option<u64>, e: &Event) -> Result<()> {
        self.journal.append(c, v, n, e)
    }
}
impl cbcl_core::quorum::BatchJournal for FailingGroup {
    fn append_batch(&mut self, c: &str, v: &str, n: u64, e: &[Event]) -> Result<()> {
        if self.fail {
            return Err("injected before-write failure".into());
        }
        self.journal.append_batch(c, v, n, e)
    }
}
#[test]
fn group_rollback_failure_retry_serial_equivalence_and_recovery() {
    use cbcl_core::quorum::{BatchJournal, Replica};
    let (setup, mut auth, ctx, key) = fixture();
    let dir = tempfile::tempdir().unwrap();
    let (journal, _) =
        DurableJournal::open(&dir.path().join("group.jsonl"), ctx.id(), "@v0").unwrap();
    let mut journal = FailingGroup {
        journal,
        fail: true,
    };
    let mut replica =
        Replica::initialize(ctx.clone(), "@v0", limits(&setup), &mut journal).unwrap();
    let tx = transaction(&setup, &ctx, 0, &key).unwrap();
    auth.remember(&tx);
    journal
        .journal
        .pending_acts
        .insert(tx.act.address.clone(), tx.clone());
    let events = vec![
        Event::Candidate(tx.act.clone()),
        Event::Sign(tx.act.address.clone()),
    ];
    let sequence = replica.journal_sequence();
    // A valid prefix followed by an invalid suffix must leave no candidate/charge.
    let mut bad = events.clone();
    bad.push(Event::Effect("missing".into()));
    assert!(replica.commit_group(&bad, &mut journal, &auth).is_err());
    assert_eq!(replica.journal_sequence(), sequence);
    assert!(replica.operation_act(&tx.act.address).is_none());
    assert!(replica.commit_group(&events, &mut journal, &auth).is_err());
    assert_eq!(replica.journal_sequence(), sequence);
    assert!(replica.operation_act(&tx.act.address).is_none());
    assert_eq!(journal.journal.count(), 1);
    journal.fail = false;
    let requests = replica.commit_group(&events, &mut journal, &auth).unwrap();
    assert!(requests[0].is_none());
    assert!(requests[1].is_some());
    assert_eq!(journal.journal.count(), 3);
    assert_eq!(journal.journal.syncs, 2);
    replica.commit_group(&events, &mut journal, &auth).unwrap();
    assert_eq!(journal.journal.syncs, 2);
    let (mut serial, _) =
        DurableJournal::open(&dir.path().join("serial.jsonl"), ctx.id(), "@v0").unwrap();
    let mut other = Replica::initialize(ctx.clone(), "@v0", limits(&setup), &mut serial).unwrap();
    serial.pending_act = Some(tx.clone());
    other.register(tx.act.clone(), &mut serial, &auth).unwrap();
    other
        .prepare_operation(&tx.act.address, &mut serial, &auth)
        .unwrap();
    assert_eq!(
        journal.load(ctx.id(), "@v0").unwrap(),
        serial.load(ctx.id(), "@v0").unwrap()
    );
    let recovered = Replica::recover(ctx.clone(), "@v0", limits(&setup), &journal, &auth).unwrap();
    assert_eq!(replica.journal_sequence(), recovered.journal_sequence());
    assert_eq!(
        replica.finalized_view().unwrap(),
        recovered.finalized_view().unwrap()
    );
    // Explicit stale CAS is a no-write error.
    let bytes = std::fs::read(dir.path().join("group.jsonl")).unwrap();
    assert!(journal.append_batch(ctx.id(), "@v0", 1, &events).is_err());
    assert_eq!(
        bytes,
        std::fs::read(dir.path().join("group.jsonl")).unwrap()
    );
    // Event limit rejection rolls back a staged candidate as well.
    let (mut limited, _) =
        DurableJournal::open(&dir.path().join("limit.jsonl"), ctx.id(), "@v0").unwrap();
    let mut bounds = limits(&setup);
    bounds.events = 2;
    let mut limited_replica =
        Replica::initialize(ctx.clone(), "@v0", bounds, &mut limited).unwrap();
    assert!(limited_replica
        .commit_group(&events, &mut limited, &auth)
        .is_err());
    assert_eq!(limited_replica.journal_sequence(), 1);
    assert!(limited_replica.operation_act(&tx.act.address).is_none());
}
#[test]
fn group_unwinding_restores_staged_entries() {
    use cbcl_core::quorum::Replica;
    struct PanicAuth(Auth);
    impl Authentication for PanicAuth {
        fn verify(&self, k: &str, p: &[u8], s: &[u8]) -> bool {
            self.0.verify(k, p, s)
        }
        fn authenticate_act(&self, _: &cbcl_core::state::Act) -> bool {
            panic!("injected verifier panic")
        }
    }
    let (setup, auth, ctx, key) = fixture();
    let dir = tempfile::tempdir().unwrap();
    let (mut journal, _) =
        DurableJournal::open(&dir.path().join("panic.jsonl"), ctx.id(), "@v0").unwrap();
    let mut replica =
        Replica::initialize(ctx.clone(), "@v0", limits(&setup), &mut journal).unwrap();
    let tx = transaction(&setup, &ctx, 0, &key).unwrap();
    let mut auth = auth;
    auth.remember(&tx);
    journal.pending_act = Some(tx.clone());
    replica
        .register(tx.act.clone(), &mut journal, &auth)
        .unwrap();
    let events = [
        Event::Sign(tx.act.address.clone()),
        Event::Candidate(transaction(&setup, &ctx, 1, &key).unwrap().act),
    ];
    assert!(
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| replica.commit_group(
            &events,
            &mut journal,
            &PanicAuth(auth.clone())
        )))
        .is_err()
    );
    assert_eq!(replica.journal_sequence(), 2);
    assert_eq!(journal.count(), 2);
    let request = replica
        .prepare_operation(&tx.act.address, &mut journal, &auth)
        .unwrap();
    assert_eq!(request.attach(vec![1]).payload, tx.act.address);
    assert_eq!(journal.count(), 3);
}
#[test]
fn serial_and_grouped_process_runs_both_recover() {
    for size in ["1", "64"] {
        let (_, r) = run(&["--journal-batch-size", size]);
        assert_eq!(r["metrics"]["finalized"], 6);
        assert_eq!(r["recovery_passed"], true);
        for v in r["validator_observations"].as_object().unwrap().values() {
            if size == "1" {
                assert_eq!(v["syncs"], v["events"])
            } else {
                assert!(v["syncs"].as_u64().unwrap() < v["events"].as_u64().unwrap())
            }
        }
    }
}

#[test]
fn group_restores_existing_charge_and_certificate_effect_markers() {
    use cbcl_core::quorum::{Certificate, Replica, Vote, VoteKind};
    use ed25519_dalek::Signer;
    let (setup, mut auth, ctx, key) = fixture();
    let dir = tempfile::tempdir().unwrap();
    let (durable, _) =
        DurableJournal::open(&dir.path().join("budget.jsonl"), ctx.id(), "@v0").unwrap();
    let mut journal = FailingGroup {
        journal: durable,
        fail: false,
    };
    let mut replica =
        Replica::initialize(ctx.clone(), "@v0", limits(&setup), &mut journal).unwrap();
    let tx = |sequence, amount| {
        let base = transaction(&setup, &ctx, sequence, &key).unwrap();
        sign_act(
            parse_act(
                &cbcl_core::intend::canonical_text(&base.act.message)
                    .replace(":amount 1", &format!(":amount {amount}")),
                "@alice",
            )
            .unwrap(),
            &key,
        )
    };
    let first = tx(0, 333333333);
    let second = tx(1, 333333333);
    let excess = tx(2, 1);
    for signed in [&first, &second, &excess] {
        auth.remember(signed);
        journal
            .journal
            .pending_acts
            .insert(signed.act.address.clone(), signed.clone());
    }
    replica
        .register(first.act.clone(), &mut journal, &auth)
        .unwrap();
    replica
        .prepare_operation(&first.act.address, &mut journal, &auth)
        .unwrap();
    let events = vec![
        Event::Candidate(second.act.clone()),
        Event::Sign(second.act.address.clone()),
    ];
    let mut invalid = events.clone();
    invalid.push(Event::Effect("unknown".into()));
    let old = journal.journal.count();
    assert!(replica.commit_group(&invalid, &mut journal, &auth).is_err());
    assert_eq!(journal.journal.count(), old);
    assert!(replica.operation_act(&second.act.address).is_none());
    journal.fail = true;
    assert!(replica.commit_group(&events, &mut journal, &auth).is_err());
    assert_eq!(replica.journal_sequence(), old);
    journal.fail = false;
    replica.commit_group(&events, &mut journal, &auth).unwrap();
    // Exactly 666666666 rights have been signed. An extra unit must fail.
    replica
        .register(excess.act.clone(), &mut journal, &auth)
        .unwrap();
    assert!(replica
        .prepare_operation(&excess.act.address, &mut journal, &auth)
        .is_err());
    let certificate = |kind| {
        let votes = (0..3)
            .map(|i| {
                let mut vote = Vote {
                    context: ctx.id().into(),
                    kind,
                    payload: first.act.address.clone(),
                    signer: VALIDATORS[i].into(),
                    signature: vec![],
                };
                vote.signature = SigningKey::from_bytes(&[i as u8 + 1; 32])
                    .sign(&vote.preimage())
                    .to_bytes()
                    .to_vec();
                vote
            })
            .collect();
        Certificate {
            kind,
            payload: first.act.address.clone(),
            votes,
        }
    };
    let effects = vec![
        Event::Certificate(certificate(VoteKind::Operation)),
        Event::Effect(first.act.address.clone()),
    ];
    let mut invalid = effects.clone();
    invalid.push(Event::Sign("unknown".into()));
    let old = journal.journal.count();
    assert!(replica.commit_group(&invalid, &mut journal, &auth).is_err());
    assert_eq!(replica.journal_sequence(), old);
    assert!(replica
        .certificate(VoteKind::Operation, &first.act.address)
        .is_none());
    assert!(replica
        .prepare_effects(&first.act.address, &mut journal, &auth)
        .is_err());
    journal.fail = true;
    assert!(replica.commit_group(&effects, &mut journal, &auth).is_err());
    assert!(replica
        .certificate(VoteKind::Operation, &first.act.address)
        .is_none());
    assert!(replica
        .prepare_effects(&first.act.address, &mut journal, &auth)
        .is_err());
    journal.fail = false;
    replica.commit_group(&effects, &mut journal, &auth).unwrap();
    let old = journal.journal.count();
    replica
        .prepare_effects(&first.act.address, &mut journal, &auth)
        .unwrap();
    assert_eq!(journal.journal.count(), old);
    replica
        .commit_group(
            &[Event::Certificate(certificate(VoteKind::Effects))],
            &mut journal,
            &auth,
        )
        .unwrap();
    let recovered = Replica::recover(ctx, "@v0", limits(&setup), &journal, &auth).unwrap();
    assert_eq!(
        replica.finalized_view().unwrap(),
        recovered.finalized_view().unwrap()
    );
}

#[test]
fn group_envelope_rejection_does_not_write_a_serialized_prefix() {
    use cbcl_core::quorum::BatchJournal;
    let (setup, _auth, ctx, key) = fixture();
    let dir = tempfile::tempdir().unwrap();
    let (mut journal, _) =
        DurableJournal::open(&dir.path().join("envelope.jsonl"), ctx.id(), "@v0").unwrap();
    journal
        .append(ctx.id(), "@v0", None, &Event::Initialize)
        .unwrap();
    let before = std::fs::read(dir.path().join("envelope.jsonl")).unwrap();
    let events = [
        Event::Sign("prefix".into()),
        Event::Candidate(transaction(&setup, &ctx, 0, &key).unwrap().act),
    ];
    assert!(journal.append_batch(ctx.id(), "@v0", 1, &events).is_err());
    assert_eq!(journal.count(), 1);
    assert_eq!(journal.syncs, 1);
    assert_eq!(
        before,
        std::fs::read(dir.path().join("envelope.jsonl")).unwrap()
    );
}

#[test]
#[cfg(feature = "queue-diagnostics")]
fn queue_and_batch_diagnostics_account_for_each_protocol_phase() {
    let (_, r) = run(&["--delay-ms", "5", "--silent-validators", "1"]);
    let client = &r["client_profile"];
    for phase in ["operation", "effects"] {
        assert_eq!(
            client["response_queues"][phase]["receive_queue_ms"]["count"],
            18
        );
        assert_eq!(client["event_service_ms"][phase]["count"], 18);
    }
    assert_eq!(client["operation_round_ms"]["count"], 6);
    assert_eq!(client["effects_round_ms"]["count"], 6);
    assert!(client["timeout_collection_ms"]["count"].as_u64().unwrap() > 0);
    for v in r["validator_observations"].as_object().unwrap().values() {
        for phase in ["operation", "effects", "final"] {
            assert_eq!(
                v["profile"]["queue_phases"][phase]["receive_queue_ms"]["count"],
                6
            );
            assert_eq!(
                v["profile"]["queue_phases"][phase]["batch_hold_ms"]["count"],
                6
            );
        }
        if v["finalized"] == 6 {
            let batches = v["profile"]["batches"].as_object().unwrap();
            let sum = |key: &str| {
                batches
                    .values()
                    .map(|b| b[key].as_u64().unwrap())
                    .sum::<u64>()
            };
            assert_eq!(sum("operation_requests"), 6);
            assert_eq!(sum("effects_requests"), 6);
            assert_eq!(sum("final_requests"), 6);
            assert_eq!(sum("events") + 1, v["events"].as_u64().unwrap());
            assert_eq!(sum("syncs") + 1, v["syncs"].as_u64().unwrap());
        }
    }
}

#[test]
#[cfg(not(feature = "queue-diagnostics"))]
fn normal_build_does_not_collect_queue_diagnostic_samples() {
    let (_, r) = run(&[]);
    assert_eq!(r["client_profile"]["queue_diagnostics_enabled"], false);
    assert_eq!(r["client_profile"]["timeout_collection_ms"]["count"], 0);
    assert!(r["client_profile"]["response_queues"]
        .as_object()
        .unwrap()
        .is_empty());
    for v in r["validator_observations"].as_object().unwrap().values() {
        assert_eq!(v["profile"]["queue_diagnostics_enabled"], false);
        assert!(v["profile"]["queue_phases"].as_object().unwrap().is_empty());
        assert!(v["profile"]["batches"].as_object().unwrap().is_empty());
        assert!(v["profile"]["response_transport"]
            .as_object()
            .unwrap()
            .is_empty());
    }
}

#[test]
fn verified_vote_builder_preserves_proof_boundaries_and_avoids_duplicate_crypto() {
    use cbcl_core::quorum::{Vote, VoteKind};
    use ed25519_dalek::Signer;
    let (setup, mut auth, ctx, _key) = fixture();
    let payload = "test-payload";
    let raw: Vec<_> = VALIDATORS
        .iter()
        .enumerate()
        .take(3)
        .map(|(i, signer)| {
            let mut vote = Vote {
                context: ctx.id().into(),
                kind: VoteKind::Operation,
                payload: payload.into(),
                signer: (*signer).into(),
                signature: vec![],
            };
            vote.signature = SigningKey::from_bytes(&[i as u8 + 1; 32])
                .sign(&vote.preimage())
                .to_bytes()
                .to_vec();
            vote
        })
        .collect();
    let count = |auth: &Auth| {
        auth.costs.borrow().verify.report()["count"]
            .as_u64()
            .unwrap()
    };
    let before = count(&auth);
    let mut verified = BTreeMap::new();
    for vote in &raw {
        verified.insert(
            vote.signer.clone(),
            VerifiedVote::verify(&auth, &ctx, vote.clone(), VoteKind::Operation, payload).unwrap(),
        );
    }
    assert_eq!(count(&auth) - before, 3);
    let cert =
        certificate_from_verified(&auth, &ctx, VoteKind::Operation, payload, &verified).unwrap();
    certificate_from_verified(&auth, &ctx, VoteKind::Operation, payload, &verified).unwrap();
    assert_eq!(
        count(&auth) - before,
        3,
        "local construction must not verify signatures twice"
    );
    verify_certificate(&auth, &ctx, &cert, cert.kind, payload).unwrap();
    assert_eq!(
        count(&auth) - before,
        6,
        "external certificates still require full verification"
    );
    let mut corrupted = cert.clone();
    corrupted.votes[0].signature[0] ^= 1;
    assert!(verify_certificate(&auth, &ctx, &corrupted, cert.kind, payload).is_err());
    assert!(VerifiedVote::verify(
        &auth,
        &ctx,
        corrupted.votes[0].clone(),
        VoteKind::Operation,
        payload
    )
    .is_err());
    assert!(VerifiedVote::verify(&auth, &ctx, raw[0].clone(), VoteKind::Effects, payload).is_err());
    assert!(VerifiedVote::verify(
        &auth,
        &ctx,
        raw[0].clone(),
        VoteKind::Operation,
        "other-payload"
    )
    .is_err());
    assert!(certificate_from_verified(&auth, &ctx, VoteKind::Effects, payload, &verified).is_err());
    assert!(certificate_from_verified(
        &auth,
        &ctx,
        VoteKind::Operation,
        "other-payload",
        &verified
    )
    .is_err());
    let mut missing = BTreeMap::new();
    for vote in raw.iter().take(2) {
        missing.insert(
            vote.signer.clone(),
            VerifiedVote::verify(&auth, &ctx, vote.clone(), vote.kind, payload).unwrap(),
        );
    }
    assert!(
        certificate_from_verified(&auth, &ctx, VoteKind::Operation, payload, &missing).is_err()
    );
    let mut duplicate = BTreeMap::new();
    for label in ["@v0", "alias-a", "alias-b"] {
        duplicate.insert(
            label.into(),
            VerifiedVote::verify(&auth, &ctx, raw[0].clone(), raw[0].kind, payload).unwrap(),
        );
    }
    assert!(
        certificate_from_verified(&auth, &ctx, VoteKind::Operation, payload, &duplicate).is_err()
    );
    // A different genuine pinned instance cannot consume these tokens.
    let mut other_setup = setup.clone();
    let changed = cbcl_core::intend::canonical_text(&other_setup.genesis[1].act.message)
        .replace(":available 1000000000", ":available 999999999");
    other_setup.genesis[1] = sign_act(
        parse_act(&changed, "@treasury").unwrap(),
        &SigningKey::from_bytes(&[8; 32]),
    );
    let other_auth = Auth::new(&other_setup).unwrap();
    let other_ctx = context(&other_setup, &other_auth).unwrap();
    assert_ne!(ctx.id(), other_ctx.id());
    assert!(certificate_from_verified(
        &other_auth,
        &other_ctx,
        VoteKind::Operation,
        payload,
        &verified
    )
    .is_err());
    auth.keys.insert(
        "@v0".into(),
        SigningKey::from_bytes(&[99; 32]).verifying_key(),
    );
    assert!(
        certificate_from_verified(&auth, &ctx, VoteKind::Operation, payload, &verified).is_err()
    );
}
