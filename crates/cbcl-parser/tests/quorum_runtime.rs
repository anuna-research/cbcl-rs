//! SPEC-026 TEST-2600..2602. Deterministic test authentication, not production keys.
use cbcl_core::{
    certification::Certification,
    dialect::{Dialect, DialectRegistry},
    intend::{intend, Instance},
    quorum::*,
    role::AgentKey,
    sexpr::{Atom, SExpr},
    state::{Act, Rule},
    store::ThreadId,
};
use cbcl_parser::{parse, parse_dialect, parse_message};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
const COIN: &str = include_str!("../../../dialects/example-coin.cbcl");
#[derive(Default)]
struct Auth {
    acts: BTreeSet<(String, String)>,
}
fn signature(key: &str, bytes: &[u8]) -> Vec<u8> {
    let mut h = Sha256::new();
    h.update(key.as_bytes());
    h.update(bytes);
    h.finalize().to_vec()
}
fn sign(req: SigningRequest) -> Vote {
    let s = signature(req.signer(), &req.preimage());
    req.attach(s)
}
impl Authentication for Auth {
    fn verify(&self, key: &str, bytes: &[u8], sig: &[u8]) -> bool {
        signature(key, bytes) == sig
    }
    fn authenticate_act(&self, a: &Act) -> bool {
        self.acts.contains(&(a.address.clone(), a.signer.clone()))
    }
}
#[derive(Default)]
struct Memory {
    logs: BTreeMap<(String, String), Vec<Event>>,
    fail: bool,
}
impl Journal for Memory {
    fn load(&self, c: &str, v: &str) -> Result<Option<Vec<Event>>> {
        Ok(self.logs.get(&(c.into(), v.into())).cloned())
    }
    fn append(&mut self, c: &str, v: &str, n: Option<u64>, e: &Event) -> Result<()> {
        if self.fail {
            return Err("injected disk failure".into());
        }
        let k = (c.into(), v.into());
        if self.logs.get(&k).map(|x| x.len() as u64) != n {
            return Err("compare-and-append conflict".into());
        }
        self.logs.entry(k).or_default().push(e.clone());
        Ok(())
    }
}
fn dialect(src: &str) -> Dialect {
    let d = parse_dialect(&parse(src).unwrap()).unwrap();
    let mut r = DialectRegistry::new();
    r.install(d.clone()).unwrap();
    d
}
fn act(s: &str, key: &str) -> Act {
    Act::from_message(parse_message(&parse(s).unwrap()).unwrap(), key).unwrap()
}
fn initial(d: &Dialect, cap: bool) -> Vec<Act> {
    let root=act("(with-roles ((issuer @treasury) (holder @treasury @alice @bob)) (signed @treasury (hello :thread \"coin-1\" :caused-by begin)))","@treasury");
    let headroom = if cap {
        " :capacity ((@treasury 1000) (@alice 0) (@bob 0))"
    } else {
        ""
    };
    let open=act(&format!("(signed @treasury (lang {} (open (@alice @bob @treasury) :name \"Example Coin\" :allocations ((@treasury 1000) (@alice 0) (@bob 0)){} :from @treasury :thread \"coin-1\" :caused-by {})))",d.name,headroom,root.address),"@treasury");
    vec![root, open]
}
fn rule(d: &Dialect) -> &cbcl_core::escrow::CounterRule {
    match d.state.as_ref().unwrap().rule_of("coins").unwrap() {
        Rule::BoundedCounter(c) => c,
        _ => panic!(),
    }
}
fn fields(to: Option<&str>, amount: i64) -> BTreeMap<String, SExpr> {
    let mut f = BTreeMap::from([("amount".into(), SExpr::Atom(Atom::Num(amount)))]);
    if let Some(to) = to {
        f.insert("recipient".into(), SExpr::Atom(Atom::Symbol(to.into())));
    }
    f
}
struct Net {
    d: Dialect,
    base: Vec<Act>,
    ctx: Context,
    auth: Auth,
    j: Memory,
    rs: Vec<Replica>,
}
impl Net {
    fn new() -> Self {
        Self::source(
            COIN.replace(
                "(floor 0)",
                "(floor 0) (certification quorum-budget (validators @v0 @v1 @v2 @v3))",
            ),
            false,
        )
    }
    fn source(src: String, cap: bool) -> Self {
        let d = dialect(&src);
        let base = initial(&d, cap);
        let auth = Auth {
            acts: base
                .iter()
                .map(|a| (a.address.clone(), a.signer.clone()))
                .collect(),
        };
        let inst = Instance::new(&d, ThreadId("coin-1".into()), &base).unwrap();
        let ctx = Context::from_instance(&inst, "coins", None, &auth).unwrap();
        let mut j = Memory::default();
        let rs = (0..4)
            .map(|i| {
                Replica::initialize(ctx.clone(), &format!("@v{i}"), Limits::default(), &mut j)
                    .unwrap()
            })
            .collect();
        Self {
            d,
            base,
            ctx,
            auth,
            j,
            rs,
        }
    }
    fn make(&mut self, owner: &str, verb: &str, to: Option<&str>, amount: i64, nonce: &str) -> Act {
        let inst = Instance::new(&self.d, ThreadId("coin-1".into()), &self.base).unwrap();
        let m = self.rs[0]
            .intend(
                &inst,
                &AgentKey(owner.into()),
                verb,
                fields(to, amount),
                nonce,
            )
            .unwrap();
        let a = Act::from_message(m, owner).unwrap();
        self.auth.acts.insert((a.address.clone(), owner.into()));
        a
    }
    fn register(&mut self, a: &Act) {
        for r in &mut self.rs {
            r.register(a.clone(), &mut self.j, &self.auth).unwrap();
        }
    }
    fn operation(&mut self, a: &Act) -> Certificate {
        self.register(a);
        let votes = self
            .rs
            .iter_mut()
            .take(3)
            .map(|r| {
                sign(
                    r.prepare_operation(&a.address, &mut self.j, &self.auth)
                        .unwrap(),
                )
            })
            .collect();
        let c = Certificate {
            kind: VoteKind::Operation,
            payload: a.address.clone(),
            votes,
        };
        for r in &mut self.rs {
            r.receive(c.clone(), &mut self.j, &self.auth).unwrap();
        }
        c
    }
    fn finalize(&mut self, a: &Act) -> Certificate {
        let votes = self
            .rs
            .iter_mut()
            .take(3)
            .map(|r| {
                sign(
                    r.prepare_effects(&a.address, &mut self.j, &self.auth)
                        .unwrap(),
                )
            })
            .collect();
        let c = Certificate {
            kind: VoteKind::Effects,
            payload: a.address.clone(),
            votes,
        };
        for r in &mut self.rs {
            r.receive(c.clone(), &mut self.j, &self.auth).unwrap();
        }
        c
    }
    fn cancel(&mut self, a: &Act) -> Certificate {
        let req = sign(
            self.ctx
                .cancellation_request(&a.signer, &a.address)
                .unwrap(),
        );
        let votes = self
            .rs
            .iter_mut()
            .take(3)
            .map(|r| {
                sign(
                    r.prepare_cancel(req.clone(), &mut self.j, &self.auth)
                        .unwrap(),
                )
            })
            .collect();
        let c = Certificate {
            kind: VoteKind::Cancel,
            payload: a.address.clone(),
            votes,
        };
        for r in &mut self.rs {
            r.receive(c.clone(), &mut self.j, &self.auth).unwrap();
        }
        c
    }
    fn reports(&mut self, owner: &str) -> Vec<SealReport> {
        let epoch = self.rs[0].active_epoch(owner).unwrap().to_string();
        self.rs
            .iter_mut()
            .map(|r| {
                let (signed, req) = r.seal(&epoch, &mut self.j, &self.auth).unwrap();
                SealReport {
                    epoch: epoch.clone(),
                    signed,
                    vote: sign(req),
                }
            })
            .collect()
    }
    fn checkpoint(&mut self, owner: &str, refunds: &[String], credits: &[String]) -> Checkpoint {
        let reports = self.reports(owner);
        let epoch = self.rs[0].active_epoch(owner).unwrap().to_string();
        let m = self.rs[0]
            .draft_checkpoint(
                &epoch,
                &reports,
                &refunds.iter().cloned().collect(),
                &credits.iter().cloned().collect(),
            )
            .unwrap();
        let authorization = sign(self.ctx.checkpoint_request(&m).unwrap());
        let p = Proposal {
            manifest: m,
            reports,
            authorization,
        };
        let id = p.manifest.id(self.ctx.id());
        let votes = self
            .rs
            .iter_mut()
            .take(3)
            .map(|r| {
                r.register_proposal(p.clone(), &mut self.j, &self.auth)
                    .unwrap();
                sign(r.prepare_checkpoint(&id, &mut self.j, &self.auth).unwrap())
            })
            .collect();
        let cp = Checkpoint {
            proposal: p,
            certificate: Certificate {
                kind: VoteKind::Checkpoint,
                payload: id.clone(),
                votes,
            },
        };
        for r in &mut self.rs {
            r.receive_checkpoint(cp.clone(), &mut self.j, &self.auth)
                .unwrap();
            r.install(&id, &mut self.j, &self.auth).unwrap();
        }
        cp
    }
}
#[test]
fn defaults_and_canonical_committee() {
    let legacy = dialect(COIN);
    let explicit = dialect(&COIN.replace("(floor 0)", "(floor 0) (certification host-gate)"));
    assert_eq!(
        cbcl_core::canonical::dialect_hash(&legacy),
        cbcl_core::canonical::dialect_hash(&explicit)
    );
    let a = Net::new();
    assert_eq!(a.ctx.committee().faults, 1);
    assert_eq!(a.ctx.committee().quorum, 3);
    let b = dialect(&COIN.replace(
        "(floor 0)",
        "(floor 0) (certification quorum-budget (faults 1) (validators @v3 @v1 @v0 @v2))",
    ));
    assert_eq!(
        cbcl_core::canonical::dialect_hash(&a.d),
        cbcl_core::canonical::dialect_hash(&b)
    );
    let deferred = dialect(&COIN.replace("(floor 0)", "(floor 0) (certification quorum-budget)"));
    assert!(rule(&deferred).certification.resolve(None).is_err());
    assert_eq!(
        rule(&deferred)
            .certification
            .resolve(Some(&a.ctx.committee().validators))
            .unwrap(),
        *a.ctx.committee()
    );
    for options in [
        "(validators)",
        "(validators @a @a @b @c)",
        "(validators @a @b)",
        "(validators @a @b @c @d) (faults 0)",
        "(faults -1)",
        "(faults 1) (faults 1)",
        "(other yes)",
        "(validators \"@a\")",
    ] {
        assert!(
            parse_dialect(
                &parse(&COIN.replace(
                    "(floor 0)",
                    &format!("(floor 0) (certification quorum-budget {options})")
                ))
                .unwrap()
            )
            .is_err(),
            "{options}"
        );
    }
    assert!(Certification::QuorumBudget {
        validators: Some(vec!["@a".into(), "@a".into()]),
        faults: None
    }
    .validate()
    .is_err());
    assert!(rule(&a.d)
        .certification
        .resolve(Some(&vec!["@x".into(); 4]))
        .is_err());
}
#[test]
fn language_trace_finality_and_restart() {
    let mut n = Net::new();
    let pay = n.make("@treasury", "pay", Some("@alice"), 100, "pay-1");
    assert_eq!(n.rs[0].finalized_view().unwrap().value, 1000);
    n.operation(&pay);
    let before = n.rs[0].finalized_view().unwrap();
    assert_eq!(before.rights["@alice"], 0);
    assert!(before.pending.contains(&pay.address));
    n.finalize(&pay);
    n.checkpoint("@alice", &[], std::slice::from_ref(&pay.address));
    let pay2 = n.make("@alice", "pay", Some("@bob"), 25, "pay-2");
    n.operation(&pay2);
    n.finalize(&pay2);
    n.checkpoint("@bob", &[], std::slice::from_ref(&pay2.address));
    let burn = n.make("@bob", "burn", None, 5, "burn-1");
    n.operation(&burn);
    n.finalize(&burn);
    let mint = n.make("@treasury", "mint", None, 250, "mint-1");
    n.operation(&mint);
    n.finalize(&mint);
    let view = n.rs[0].finalized_view().unwrap();
    assert_eq!(view.value, 1245);
    assert_eq!(
        view.rights,
        BTreeMap::from([
            ("@treasury".into(), 1150),
            ("@alice".into(), 75),
            ("@bob".into(), 20)
        ])
    );
    let restored =
        Replica::recover(n.ctx.clone(), "@v0", Limits::default(), &n.j, &n.auth).unwrap();
    assert_eq!(restored.finalized_view().unwrap(), view);
    assert!(Replica::initialize(n.ctx.clone(), "@v0", Limits::default(), &mut n.j).is_err());
    let inst = Instance::new(&n.d, ThreadId("coin-1".into()), &n.base).unwrap();
    let fold = n.rs[0].fold_instance(&inst).unwrap();
    assert!(fold
        .iter()
        .find(|(f, _)| f == "coins")
        .unwrap()
        .1
        .render()
        .contains("finalized-view"));
    assert!(intend(
        &inst,
        &AgentKey("@treasury".into()),
        "mint",
        fields(None, 1)
    )
    .is_err());
    assert!(cbcl_core::escrow::observe(rule(&n.d), &n.base)
        .value()
        .render()
        .contains("fault"));
}
#[test]
fn signed_domains_distinct_members_and_no_early_effects() {
    let mut n = Net::new();
    let pay = n.make("@treasury", "pay", Some("@alice"), 10, "one");
    n.register(&pay);
    assert!(n.rs[0]
        .prepare_effects(&pay.address, &mut n.j, &n.auth)
        .is_err());
    let c = n.operation(&pay);
    for mutation in 0..7 {
        let mut bad = c.clone();
        match mutation {
            0 => bad.votes.truncate(2),
            1 => bad.votes[1] = bad.votes[0].clone(),
            2 => bad.votes[0].signature[0] ^= 1,
            3 => bad.votes[0].context.push('x'),
            4 => bad.votes[0].signer = "@outsider".into(),
            5 => bad.votes[0].kind = VoteKind::Effects,
            _ => bad.votes[0].payload = "another-operation".into(),
        };
        // Correct signatures on wrong domains/keys/payloads must still reject;
        // do not let a bad signature mask a missing semantic guard.
        if mutation >= 3 {
            bad.votes[0].signature = signature(&bad.votes[0].signer, &bad.votes[0].preimage());
        }
        let seq = n.rs[3].journal_sequence();
        assert!(n.rs[3].receive(bad, &mut n.j, &n.auth).is_err());
        assert_eq!(n.rs[3].journal_sequence(), seq);
    }
    let mut bad = pay.clone();
    bad.signer = "@alice".into();
    assert!(n.rs[0].register(bad, &mut n.j, &n.auth).is_err());
    let req = sign(n.ctx.cancellation_request("@alice", &pay.address).unwrap());
    assert!(n.rs[0].prepare_cancel(req, &mut n.j, &n.auth).is_err());
    n.rs[0]
        .prepare_effects(&pay.address, &mut n.j, &n.auth)
        .unwrap();
    let req = sign(
        n.ctx
            .cancellation_request("@treasury", &pay.address)
            .unwrap(),
    );
    assert!(n.rs[0].prepare_cancel(req, &mut n.j, &n.auth).is_err());
}
#[test]
fn cancellation_reclaims_once_and_survives_late_delivery() {
    let mut n = Net::new();
    let pay = n.make("@treasury", "pay", Some("@alice"), 600, "cancel");
    let qc = n.operation(&pay);
    assert!(n.rs[0].release(&pay.address, &mut n.j, &n.auth).is_err());
    let cancel = n.cancel(&pay);
    for r in &mut n.rs[..3] {
        r.release(&pay.address, &mut n.j, &n.auth).unwrap();
        r.release(&pay.address, &mut n.j, &n.auth).unwrap();
        assert!(r.prepare_effects(&pay.address, &mut n.j, &n.auth).is_err());
    }
    let cp = n.checkpoint("@treasury", std::slice::from_ref(&pay.address), &[]);
    assert!(cp.proposal.manifest.held.contains(&pay.address));
    assert_eq!(cp.proposal.manifest.allocation.rights, 1000);
    // Replaying old certificates/checkpoints cannot re-open the root epoch.
    let active = n.rs[0].active_epoch("@treasury").unwrap().to_string();
    n.rs[0].receive(qc, &mut n.j, &n.auth).unwrap();
    n.rs[0].receive(cancel, &mut n.j, &n.auth).unwrap();
    n.rs[0]
        .receive_checkpoint(cp.clone(), &mut n.j, &n.auth)
        .unwrap();
    assert_eq!(n.rs[0].active_epoch("@treasury").unwrap(), active);
    let restored =
        Replica::recover(n.ctx.clone(), "@v0", Limits::default(), &n.j, &n.auth).unwrap();
    assert_eq!(restored.active_epoch("@treasury").unwrap(), active);
    let next = n.make("@treasury", "pay", Some("@bob"), 600, "next");
    n.operation(&next);
    n.finalize(&next);
    assert_eq!(n.rs[0].finalized_view().unwrap().rights["@treasury"], 400);
}
#[test]
fn local_budget_triangle_and_durable_cas() {
    let mut n = Net::new();
    let a = n.make("@treasury", "pay", Some("@alice"), 400, "a");
    let b = n.make("@treasury", "pay", Some("@bob"), 400, "b");
    let c = n.make("@treasury", "burn", None, 400, "c");
    for op in [&a, &b, &c] {
        n.register(op);
    }
    n.rs[0]
        .prepare_operation(&a.address, &mut n.j, &n.auth)
        .unwrap();
    assert!(n.rs[0]
        .prepare_operation(&b.address, &mut n.j, &n.auth)
        .is_err());
    // Every honest validator fits at most one of these costs. Even one arbitrary
    // Byzantine signature cannot complete two intersecting quorums.
    n.rs[1]
        .prepare_operation(&b.address, &mut n.j, &n.auth)
        .unwrap();
    n.rs[2]
        .prepare_operation(&c.address, &mut n.j, &n.auth)
        .unwrap();
    let mut stale =
        Replica::recover(n.ctx.clone(), "@v3", Limits::default(), &n.j, &n.auth).unwrap();
    n.j.fail = true;
    let seq = n.rs[3].journal_sequence();
    assert!(n.rs[3]
        .prepare_operation(&a.address, &mut n.j, &n.auth)
        .is_err());
    assert_eq!(n.rs[3].journal_sequence(), seq);
    n.j.fail = false;
    n.rs[3]
        .prepare_operation(&a.address, &mut n.j, &n.auth)
        .unwrap();
    assert!(stale
        .prepare_operation(&b.address, &mut n.j, &n.auth)
        .is_err());
    let mut restored =
        Replica::recover(n.ctx.clone(), "@v3", Limits::default(), &n.j, &n.auth).unwrap();
    assert!(restored
        .prepare_operation(&b.address, &mut n.j, &n.auth)
        .is_err());
    assert_eq!(
        sign(
            restored
                .prepare_operation(&a.address, &mut n.j, &n.auth)
                .unwrap()
        ),
        sign(
            n.rs[3]
                .prepare_operation(&a.address, &mut n.j, &n.auth)
                .unwrap()
        )
    );
}
#[test]
fn nonce_forgery_seals_successor_choice_and_limits() {
    let mut n = Net::new();
    let a = n.make("@treasury", "pay", Some("@alice"), 10, "a");
    let retry = n.make("@treasury", "pay", Some("@alice"), 10, "a");
    let b = n.make("@treasury", "pay", Some("@alice"), 10, "b");
    assert_eq!(a.address, retry.address);
    assert_ne!(a.address, b.address);
    n.operation(&a);
    n.register(&b);
    let reports = n.reports("@treasury");
    assert!(n.rs[0]
        .prepare_operation(&b.address, &mut n.j, &n.auth)
        .is_err());
    let epoch = n.rs[0].active_epoch("@treasury").unwrap().to_string();
    let m = n.rs[0]
        .draft_checkpoint(&epoch, &reports, &BTreeSet::new(), &BTreeSet::new())
        .unwrap();
    let p = Proposal {
        authorization: sign(n.ctx.checkpoint_request(&m).unwrap()),
        manifest: m,
        reports: reports.clone(),
    };
    let id = n.rs[0]
        .register_proposal(p.clone(), &mut n.j, &n.auth)
        .unwrap();
    n.rs[0].prepare_checkpoint(&id, &mut n.j, &n.auth).unwrap();
    let mut split = p.clone();
    split.manifest.held.insert(b.address.clone());
    split.manifest.allocation.rights -= 10;
    split.authorization = sign(n.ctx.checkpoint_request(&split.manifest).unwrap());
    let other = n.rs[0].register_proposal(split, &mut n.j, &n.auth).unwrap();
    assert!(n.rs[0]
        .prepare_checkpoint(&other, &mut n.j, &n.auth)
        .is_err());
    let mut omitted = p.clone();
    omitted.manifest.held.clear();
    omitted.manifest.allocation.rights = 1000;
    omitted.authorization = sign(n.ctx.checkpoint_request(&omitted.manifest).unwrap());
    assert!(n.rs[1]
        .register_proposal(omitted, &mut n.j, &n.auth)
        .is_err());
    let mut alternate = p.clone();
    alternate.reports.reverse();
    assert_eq!(alternate.manifest.id(n.ctx.id()), id);
    n.rs[0]
        .register_proposal(alternate, &mut n.j, &n.auth)
        .unwrap();
    let inst = Instance::new(&n.d, ThreadId("coin-1".into()), &n.base).unwrap();
    for key in ["escrow-prev", "escrow-deps", "escrow-nonce"] {
        let mut f = fields(None, 1);
        f.insert(key.into(), SExpr::Atom(Atom::Str("forged".into())));
        assert!(n.rs[0]
            .intend(&inst, &AgentKey("@treasury".into()), "mint", f, "x")
            .is_err());
    }
    let mut small = Memory::default();
    let mut r = Replica::initialize(
        n.ctx.clone(),
        "@v0",
        Limits {
            operations: 1,
            ..Limits::default()
        },
        &mut small,
    )
    .unwrap();
    r.register(a, &mut small, &n.auth).unwrap();
    assert!(r.register(b, &mut small, &n.auth).is_err());
}
#[test]
fn ceiling_issuers_and_missing_epoch_evidence() {
    let src = COIN
        .replace(
            "(floor 0)",
            "(floor 0) (ceiling 2000) (certification quorum-budget (validators @v0 @v1 @v2 @v3))",
        )
        .replace(
            "(initial-rights open :allocations)",
            "(initial-rights open :allocations) (initial-headroom open :capacity)",
        )
        .replace("(to name allocations)", "(to name allocations capacity)")
        .replace(
            ":allocations allocations))",
            ":allocations allocations :capacity capacity))",
        )
        .replace(
            "(require :allocations list)",
            "(require :allocations list) (require :capacity list)",
        );
    let mut n = Net::source(src, true);
    let mint = n.make("@treasury", "mint", None, 600, "mint");
    n.operation(&mint);
    n.finalize(&mint);
    assert_eq!(
        n.rs[0].finalized_view().unwrap().headroom.unwrap()["@treasury"],
        400
    );
    let too_much = n.make("@treasury", "mint", None, 100, "more");
    n.register(&too_much);
    assert!(n.rs[0]
        .prepare_operation(&too_much.address, &mut n.j, &n.auth)
        .is_err());
    let inst = Instance::new(&n.d, ThreadId("coin-1".into()), &n.base).unwrap();
    assert!(n.rs[0]
        .intend(
            &inst,
            &AgentKey("@alice".into()),
            "mint",
            fields(None, 1),
            "forge"
        )
        .is_err());
    let pay = n.make("@treasury", "pay", Some("@alice"), 100, "pay");
    n.operation(&pay);
    n.finalize(&pay);
    let cp = n.checkpoint("@alice", &[], std::slice::from_ref(&pay.address));
    let mut j = Memory::default();
    let mut fresh = Replica::initialize(n.ctx.clone(), "@v0", Limits::default(), &mut j).unwrap();
    assert!(fresh.receive_checkpoint(cp, &mut j, &n.auth).is_err());
    assert_eq!(fresh.journal_sequence(), 1);
}

#[test]
fn late_old_effects_remain_charged_after_checkpoint() {
    let mut n = Net::new();
    let old = n.make("@treasury", "pay", Some("@alice"), 100, "old");
    n.operation(&old);
    let cp = n.checkpoint("@treasury", &[], &[]);
    assert_eq!(cp.proposal.manifest.allocation.rights, 900);
    let new = n.make("@treasury", "burn", None, 500, "new");
    n.operation(&new);
    n.finalize(&new);
    n.finalize(&old);
    let v = n.rs[0].finalized_view().unwrap();
    assert_eq!(v.rights["@treasury"], 400);
    assert_eq!(v.rights["@alice"], 100);
    assert_eq!(v.value, 500);
    assert!(n.rs[0]
        .install(&n.ctx.root_epoch("@treasury").unwrap(), &mut n.j, &n.auth)
        .is_err());
}
#[test]
fn corrupted_recovery_and_duplicate_wire_fields_reject() {
    let mut n = Net::new();
    let op = n.make("@treasury", "pay", Some("@alice"), 100, "one");
    n.operation(&op);
    let mut message = op.message.clone();
    fn simple(m: &mut cbcl_core::message::Message) -> &mut cbcl_core::message::Message {
        match m {
            cbcl_core::message::Message::Dialect { inner, .. } => simple(inner),
            cbcl_core::message::Message::Wrapped { content, .. } => simple(content),
            _ => m,
        }
    }
    if let cbcl_core::message::Message::Simple { params, .. } = simple(&mut message) {
        params.extend([
            SExpr::Atom(Atom::Keyword("amount".into())),
            SExpr::Atom(Atom::Num(1)),
        ]);
    }
    let duplicate = Act::from_message(message, "@treasury").unwrap();
    n.auth
        .acts
        .insert((duplicate.address.clone(), duplicate.signer.clone()));
    assert!(n.rs[0].register(duplicate, &mut n.j, &n.auth).is_err());
    let key = (n.ctx.id().to_string(), "@v0".to_string());
    let original = n.j.logs[&key].clone();
    n.j.logs
        .get_mut(&key)
        .unwrap()
        .push(Event::Effect("sha256-missing".into()));
    assert!(Replica::recover(n.ctx.clone(), "@v0", Limits::default(), &n.j, &n.auth).is_err());
    n.j.logs.insert(key.clone(), original);
    for event in n.j.logs.get_mut(&key).unwrap().iter_mut() {
        if let Event::Certificate(c) = event {
            c.votes[0].signature[0] ^= 1;
            break;
        }
    }
    assert!(Replica::recover(n.ctx.clone(), "@v0", Limits::default(), &n.j, &n.auth).is_err());
}
#[test]
fn persistence_roundtrip_preserves_all_decisions() {
    let mut n = Net::new();
    let op = n.make("@treasury", "pay", Some("@alice"), 100, "one");
    n.operation(&op);
    n.cancel(&op);
    n.rs[0].release(&op.address, &mut n.j, &n.auth).unwrap();
    n.checkpoint("@treasury", std::slice::from_ref(&op.address), &[]);
    for log in n.j.logs.values_mut() {
        let bytes = serde_json::to_vec(log).unwrap();
        *log = serde_json::from_slice(&bytes).unwrap();
    }
    let restored =
        Replica::recover(n.ctx.clone(), "@v0", Limits::default(), &n.j, &n.auth).unwrap();
    assert_eq!(
        restored.finalized_view().unwrap(),
        n.rs[0].finalized_view().unwrap()
    );
    assert_eq!(
        restored.active_epoch("@treasury").unwrap(),
        n.rs[0].active_epoch("@treasury").unwrap()
    );
}

#[test]
fn programmatic_and_serde_rosters_use_symbol_grammar() {
    for key in [
        "@bad:key",
        "@bad[key]",
        "@bad\\key",
        "@💰",
        "@",
        "@bad key",
        "@bad;key",
    ] {
        assert!(
            Certification::quorum_budget(Some(vec![key.into()]), None).is_err(),
            "{key}"
        );
        let raw = serde_json::json!({"QuorumBudget":{"validators":[key],"faults":null}});
        let config: Certification = serde_json::from_value(raw).unwrap();
        assert!(config.validate().is_err(), "{key}");
    }
    assert_eq!(
        Certification::quorum_budget(Some(vec!["@valid-key_1".into()]), None)
            .unwrap()
            .resolve(None)
            .unwrap()
            .quorum,
        1
    );
}

#[test]
fn json_contract_and_text_roundtrips_use_certification_options() {
    let contract = serde_json::json!({"version":3,"kind":"contract","name":"json-quorum","author":"@author",
        "roles":{"issuer":"singleton","holder":"indexed"},
        "verbs":{
            "open":{"after":["begin"],"fields":{"allocations":"list"},"from":"issuer","to":["issuer","holder"]},
            "mint":{"after":["open"],"fields":{"amount":"number"},"from":"issuer","to":["issuer","holder"]},
            "burn":{"after":["open"],"fields":{"amount":"number"},"from":"holder","to":["issuer","holder"]},
            "pay":{"after":["open"],"fields":{"recipient":"symbol","amount":"number"},"from":"holder","to":["issuer","holder"]}},
        "state":{"coins":["boundedCounter",[["floor",0],["certification","quorum-budget",["validators","@v3","@v1","@v0","@v2"]],["initial-rights","open",":allocations"],["issuers","issuer"],["increment","mint",":amount"],["decrement","burn",":amount"],["transfer","pay",":recipient",":amount"]]]}});
    let result = cbcl_parser::compile_contract_str(&contract.to_string()).unwrap();
    let result: serde_json::Value = serde_json::from_str(&result).unwrap();
    let source = result["dialect"].as_str().unwrap();
    let d = dialect(source);
    assert_eq!(rule(&d).certification.resolve(None).unwrap().quorum, 3);
    let normalized = cbcl_parser::define_text_str(source).unwrap();
    let roundtrip = dialect(&normalized);
    assert_eq!(
        cbcl_core::canonical::dialect_hash(&d),
        cbcl_core::canonical::dialect_hash(&roundtrip)
    );
    let mut injected = contract;
    injected["state"]["coins"][1][1][2][1] = serde_json::json!("@v0) (tell @evil");
    assert!(cbcl_parser::compile_contract_str(&injected.to_string()).is_err());
}
#[test]
fn bounded_inputs_reject_before_decisions() {
    let mut n = Net::new();
    let op = n.make("@treasury", "pay", Some("@alice"), 10, "bounded");
    let mut j = Memory::default();
    let mut r = Replica::initialize(
        n.ctx.clone(),
        "@v0",
        Limits {
            object_bytes: 128,
            ..Limits::default()
        },
        &mut j,
    )
    .unwrap();
    assert!(r.register(op.clone(), &mut j, &n.auth).is_err());
    assert_eq!(r.journal_sequence(), 1);
    n.operation(&op);
    let mut cert = n.rs[0]
        .certificate(VoteKind::Operation, &op.address)
        .unwrap()
        .clone();
    cert.votes[0].signature = vec![0; 8193];
    assert!(n.rs[0].receive(cert, &mut n.j, &n.auth).is_err());
    let encoded = serde_json::to_value(
        n.rs[0]
            .certificate(VoteKind::Operation, &op.address)
            .unwrap(),
    )
    .unwrap();
    let mut extra = encoded.clone();
    extra
        .as_object_mut()
        .unwrap()
        .insert("unrecognized".into(), serde_json::json!(true));
    assert!(serde_json::from_value::<Certificate>(extra).is_err());
}

#[test]
fn nested_resource_codec_rejects_unknown_fields() {
    assert!(serde_json::from_value::<Resources>(
        serde_json::json!({"rights":0,"headroom":0,"unexpected":1})
    )
    .is_err());
}
#[test]
fn malformed_context_caches_cannot_replace_genesis() {
    let n = Net::new();
    let other = dialect(COIN);
    let other_base = initial(&other, false);
    let mut inst = Instance::new(&n.d, ThreadId("coin-1".into()), &n.base).unwrap();
    inst.opener = Some(&other_base[1]);
    inst.root = None;
    inst.cast = None;
    let rebuilt = Context::from_instance(&inst, "coins", None, &n.auth).unwrap();
    assert_eq!(rebuilt.id(), n.ctx.id());
}

#[test]
fn out_of_order_certificate_delivery_can_fetch_and_retry() {
    let mut n = Net::new();
    let op = n.make("@treasury", "pay", Some("@alice"), 100, "async");
    let mut votes = Vec::new();
    for r in &mut n.rs[..3] {
        r.register(op.clone(), &mut n.j, &n.auth).unwrap();
        votes.push(sign(
            r.prepare_operation(&op.address, &mut n.j, &n.auth).unwrap(),
        ));
    }
    let operation = Certificate {
        kind: VoteKind::Operation,
        payload: op.address.clone(),
        votes,
    };
    let mut votes = Vec::new();
    for r in &mut n.rs[..3] {
        r.receive(operation.clone(), &mut n.j, &n.auth).unwrap();
        votes.push(sign(
            r.prepare_effects(&op.address, &mut n.j, &n.auth).unwrap(),
        ));
    }
    let effects = Certificate {
        kind: VoteKind::Effects,
        payload: op.address.clone(),
        votes,
    };
    let seq = n.rs[3].journal_sequence();
    assert!(n.rs[3].receive(effects.clone(), &mut n.j, &n.auth).is_err());
    assert_eq!(n.rs[3].journal_sequence(), seq);
    n.rs[3].register(op, &mut n.j, &n.auth).unwrap();
    assert!(n.rs[3].receive(effects.clone(), &mut n.j, &n.auth).is_err());
    n.rs[3].receive(operation, &mut n.j, &n.auth).unwrap();
    n.rs[3].receive(effects.clone(), &mut n.j, &n.auth).unwrap();
    let finalized = n.rs[3].finalized_view().unwrap();
    n.rs[3].receive(effects, &mut n.j, &n.auth).unwrap();
    assert_eq!(n.rs[3].finalized_view().unwrap(), finalized);
    assert_eq!(finalized.rights["@alice"], 100);
}
#[test]
fn headroom_transfers_and_burn_credits_are_independent_resources() {
    let src=COIN.replace("(floor 0)","(floor 0) (ceiling 2000) (certification quorum-budget (validators @v0 @v1 @v2 @v3))")
        .replace("(initial-rights open :allocations)","(initial-rights open :allocations) (initial-headroom open :capacity) (transfer-headroom share-space :recipient :amount)")
        .replace("(to name allocations)","(to name allocations capacity)")
        .replace(":allocations allocations))",":allocations allocations :capacity capacity))")
        .replace("(require :allocations list)","(require :allocations list) (require :capacity list)")
        .replace("  (shape open", "  (extend share-space (to recipient amount) :from holder :to (issuer holder) (tell to :recipient recipient :amount amount))\n  (shape share-space (require :recipient symbol) (require :amount number))\n  (shape open")
        .replace("(then open pay)","(then open pay) (then open share-space)");
    let mut n = Net::source(src, true);
    let space = n.make("@treasury", "share-space", Some("@alice"), 200, "space");
    n.operation(&space);
    n.finalize(&space);
    let view = n.rs[0].finalized_view().unwrap();
    assert_eq!(view.value, 1000);
    assert_eq!(view.rights["@alice"], 0);
    assert_eq!(view.headroom.unwrap()["@alice"], 200);
    n.checkpoint("@alice", &[], std::slice::from_ref(&space.address));
    let burn = n.make("@treasury", "burn", None, 200, "burn");
    n.operation(&burn);
    n.finalize(&burn);
    n.checkpoint("@treasury", &[], std::slice::from_ref(&burn.address));
    let view = n.rs[0].finalized_view().unwrap();
    assert_eq!(view.value, 800);
    assert_eq!(view.headroom.unwrap()["@treasury"], 1000);
}

#[test]
fn issuer_authority_is_checked_even_when_protocol_role_permits_mint() {
    let src = COIN
        .replace(
            "(floor 0)",
            "(floor 0) (certification quorum-budget (validators @v0 @v1 @v2 @v3))",
        )
        .replace(
            "(extend mint (to amount) :from issuer",
            "(extend mint (to amount) :from holder",
        );
    let mut n = Net::source(src, false);
    let epoch = n.ctx.root_epoch("@alice").unwrap();
    let op=act(&format!("(lang {} (mint (@alice @bob @treasury) () :amount 1 :escrow-prev {} :escrow-deps () :escrow-nonce \"mint\" :from @alice :thread \"coin-1\" :caused-by {}))",n.d.name,epoch,n.base[1].address),"@alice");
    n.auth.acts.insert((op.address.clone(), op.signer.clone()));
    let error = n.rs[0].register(op, &mut n.j, &n.auth).unwrap_err();
    assert!(error.contains("issuer authority"), "{error}");
}
