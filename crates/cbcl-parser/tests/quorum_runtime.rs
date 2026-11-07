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
    fn advance_version(
        &mut self,
        owner: &str,
        refunds: &[String],
        credits: &[String],
    ) -> DagVersion {
        let epoch = self.rs[0].active_epoch(owner).unwrap().to_string();
        let held: BTreeSet<_> = self
            .rs
            .iter()
            .flat_map(|r| r.version_snapshot(owner).unwrap().signed.into_iter())
            .collect();
        let manifest = self.rs[0]
            .draft_version(
                &[epoch].into_iter().collect(),
                &held,
                &refunds.iter().cloned().collect(),
                &credits.iter().cloned().collect(),
            )
            .unwrap();
        let authorization = sign(self.ctx.version_request(&manifest, owner).unwrap());
        let v = DagVersion {
            manifest,
            authorization,
        };
        let id = v.manifest.id(self.ctx.id());
        for r in &mut self.rs {
            r.receive_version(v.clone(), &mut self.j, &self.auth)
                .unwrap();
            r.adopt_version(&id, &mut self.j, &self.auth).unwrap();
        }
        v
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
    n.advance_version("@alice", &[], std::slice::from_ref(&pay.address));
    let pay2 = n.make("@alice", "pay", Some("@bob"), 25, "pay-2");
    n.operation(&pay2);
    n.finalize(&pay2);
    n.advance_version("@bob", &[], std::slice::from_ref(&pay2.address));
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
    let cp = n.advance_version("@treasury", std::slice::from_ref(&pay.address), &[]);
    assert!(cp.manifest.held.contains(&pay.address));
    assert_eq!(cp.manifest.allocation.rights, 1000);
    // Replaying old certificates/versions cannot re-open the root epoch.
    let active = n.rs[0].active_epoch("@treasury").unwrap().to_string();
    n.rs[0].receive(qc, &mut n.j, &n.auth).unwrap();
    n.rs[0].receive(cancel, &mut n.j, &n.auth).unwrap();
    n.rs[0]
        .receive_version(cp.clone(), &mut n.j, &n.auth)
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
fn nonce_forgery_dag_history_and_limits() {
    let mut n = Net::new();
    let a = n.make("@treasury", "pay", Some("@alice"), 10, "a");
    let retry = n.make("@treasury", "pay", Some("@alice"), 10, "a");
    let b = n.make("@treasury", "pay", Some("@alice"), 10, "b");
    assert_eq!(a.address, retry.address);
    assert_ne!(a.address, b.address);
    n.operation(&a);
    n.register(&b);
    let parents = [n.ctx.root_epoch("@treasury").unwrap()]
        .into_iter()
        .collect();
    let held = [a.address.clone()].into_iter().collect();
    let m = n.rs[0]
        .draft_version(&parents, &held, &BTreeSet::new(), &BTreeSet::new())
        .unwrap();
    let p = DagVersion {
        authorization: sign(n.ctx.version_request(&m, "@treasury").unwrap()),
        manifest: m,
    };
    let id = p.manifest.id(n.ctx.id());
    n.rs[0]
        .receive_version(p.clone(), &mut n.j, &n.auth)
        .unwrap();
    n.rs[0].adopt_version(&id, &mut n.j, &n.auth).unwrap();
    assert!(n.rs[0]
        .prepare_operation(&b.address, &mut n.j, &n.auth)
        .is_err());
    let mut omitted = p;
    omitted.manifest.held.clear();
    omitted.manifest.allocation.rights = 1000;
    omitted.authorization = sign(
        n.ctx
            .version_request(&omitted.manifest, "@treasury")
            .unwrap(),
    );
    let oid = omitted.manifest.id(n.ctx.id());
    n.rs[1].receive_version(omitted, &mut n.j, &n.auth).unwrap();
    assert!(n.rs[1].adopt_version(&oid, &mut n.j, &n.auth).is_err());
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
    let cp = n.advance_version("@alice", &[], std::slice::from_ref(&pay.address));
    let mut j = Memory::default();
    let mut fresh = Replica::initialize(n.ctx.clone(), "@v0", Limits::default(), &mut j).unwrap();
    assert!(fresh.receive_version(cp, &mut j, &n.auth).is_err());
    assert_eq!(fresh.journal_sequence(), 1);
}

#[test]
fn late_old_effects_remain_charged_after_adoption() {
    let mut n = Net::new();
    let old = n.make("@treasury", "pay", Some("@alice"), 100, "old");
    n.operation(&old);
    let cp = n.advance_version("@treasury", &[], &[]);
    assert_eq!(cp.manifest.allocation.rights, 900);
    let new = n.make("@treasury", "burn", None, 500, "new");
    n.operation(&new);
    n.finalize(&new);
    n.finalize(&old);
    let v = n.rs[0].finalized_view().unwrap();
    assert_eq!(v.rights["@treasury"], 400);
    assert_eq!(v.rights["@alice"], 100);
    assert_eq!(v.value, 500);
    assert!(n.rs[0]
        .adopt_version(&n.ctx.root_epoch("@treasury").unwrap(), &mut n.j, &n.auth)
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
    n.advance_version("@treasury", std::slice::from_ref(&op.address), &[]);
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
    n.advance_version("@alice", &[], std::slice::from_ref(&space.address));
    let burn = n.make("@treasury", "burn", None, 200, "burn");
    n.operation(&burn);
    n.finalize(&burn);
    n.advance_version("@treasury", &[], std::slice::from_ref(&burn.address));
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

const TICKETS: &str = include_str!("../../../dialects/example-collective-tickets.cbcl");
fn collective() -> Net {
    collective_source(TICKETS)
}
fn collective_source(source: &str) -> Net {
    let d = dialect(source);
    let root=act("(with-roles ((organizer @treasury) (seller @alice @bob)) (signed @treasury (hello :thread \"coin-1\" :caused-by begin)))","@treasury");
    let open=act(&format!("(signed @treasury (lang {} (open (@alice @bob @treasury) :available 100 :from @treasury :thread \"coin-1\" :caused-by {})))",d.name,root.address),"@treasury");
    let base = vec![root, open];
    let auth = Auth {
        acts: base
            .iter()
            .map(|a| (a.address.clone(), a.signer.clone()))
            .collect(),
    };
    let inst = Instance::new(&d, ThreadId("coin-1".into()), &base).unwrap();
    let ctx = Context::from_instance(&inst, "tickets", None, &auth).unwrap();
    let mut j = Memory::default();
    let rs = (0..4)
        .map(|i| {
            Replica::initialize(ctx.clone(), &format!("@v{i}"), Limits::default(), &mut j).unwrap()
        })
        .collect();
    Net {
        d,
        base,
        ctx,
        auth,
        j,
        rs,
    }
}
fn ticket(n: &mut Net, actor: &str, amount: i64, nonce: &str) -> Act {
    let inst = Instance::new(&n.d, ThreadId("coin-1".into()), &n.base).unwrap();
    let mut f = fields(None, amount);
    f.insert(
        "buyer".into(),
        SExpr::Atom(Atom::Symbol("@customer".into())),
    );
    let m = n.rs[0]
        .intend(&inst, &AgentKey(actor.into()), "sell", f, nonce)
        .unwrap();
    let a = Act::from_message(m, actor).unwrap();
    n.auth.acts.insert((a.address.clone(), actor.into()));
    a
}
#[test]
fn collective_sellers_share_one_validator_budget() {
    let mut n = collective();
    let a = ticket(&mut n, "@alice", 60, "alice");
    let b = ticket(&mut n, "@bob", 60, "bob");
    n.register(&a);
    n.register(&b);
    n.rs[0]
        .prepare_operation(&a.address, &mut n.j, &n.auth)
        .unwrap();
    assert!(n.rs[0]
        .prepare_operation(&b.address, &mut n.j, &n.auth)
        .is_err());
}
#[test]
fn collective_concurrent_sellers_finalize_one_pool() {
    let mut n = collective();
    let a = ticket(&mut n, "@alice", 3, "alice");
    let b = ticket(&mut n, "@bob", 2, "bob");
    n.operation(&a);
    n.operation(&b);
    assert_eq!(n.rs[0].finalized_view().unwrap().value, 100);
    n.finalize(&b);
    n.finalize(&a);
    let view = n.rs[0].finalized_view().unwrap();
    assert_eq!(view.value, 95);
    assert_eq!(view.rights.len(), 1);
    let rendered = view.value().render();
    assert!(rendered.contains("collective"));
    assert!(rendered.contains("unknown"));
    let restored =
        Replica::recover(n.ctx.clone(), "@v0", Limits::default(), &n.j, &n.auth).unwrap();
    assert_eq!(view, restored.finalized_view().unwrap());
}

#[test]
fn collective_cancellation_uses_original_actor_and_refunds_shared_pool() {
    let mut n = collective();
    let a = ticket(&mut n, "@alice", 60, "cancel");
    n.operation(&a);
    let wrong = sign(n.ctx.cancellation_request("@bob", &a.address).unwrap());
    assert!(n.rs[0].prepare_cancel(wrong, &mut n.j, &n.auth).is_err());
    n.cancel(&a);
    for r in &mut n.rs[..3] {
        r.release(&a.address, &mut n.j, &n.auth).unwrap();
    }
    let cp = n.advance_version("@bob", std::slice::from_ref(&a.address), &[]);
    assert_eq!(cp.manifest.allocation.rights, 100);
    assert_eq!(cp.authorization.signer, "@bob");
    assert_eq!(cp.manifest.account, COLLECTIVE_POOL);
    assert!(cp.manifest.held.contains(&a.address));
    let b = ticket(&mut n, "@bob", 60, "spend-reclaimed");
    n.operation(&b);
    n.finalize(&b);
    let view = n.rs[0].finalized_view().unwrap();
    assert_eq!(view.value, 40);
    let mut restored =
        Replica::recover(n.ctx.clone(), "@v0", Limits::default(), &n.j, &n.auth).unwrap();
    assert_eq!(restored.finalized_view().unwrap(), view);
    assert!(restored
        .prepare_effects(&a.address, &mut n.j, &n.auth)
        .is_err());
}
#[test]
fn collective_late_old_certificate_stays_charged_across_actor_adoption() {
    let mut n = collective();
    let old = ticket(&mut n, "@alice", 60, "old");
    n.operation(&old);
    let cp = n.advance_version("@bob", &[], &[]);
    assert_eq!(cp.manifest.allocation.rights, 40);
    let next = ticket(&mut n, "@bob", 20, "next");
    n.operation(&next);
    n.finalize(&next);
    n.finalize(&old);
    let view = n.rs[0].finalized_view().unwrap();
    assert_eq!(view.rights[COLLECTIVE_POOL], 20);
    assert_eq!(
        n.rs[0].active_epoch("@alice").unwrap(),
        n.rs[0].active_epoch("@bob").unwrap()
    );
    assert_eq!(
        n.ctx.root_epoch("@alice").unwrap(),
        n.ctx.root_epoch("@bob").unwrap()
    );
}
#[test]
fn collective_ceiling_issuer_and_version_authorization() {
    let mut n = collective_source(&TICKETS.replace("(floor 0)", "(floor 0) (ceiling 100)"));
    let restock = n.make("@treasury", "restock", None, 1, "too-soon");
    n.register(&restock);
    assert!(n.rs[0]
        .prepare_operation(&restock.address, &mut n.j, &n.auth)
        .is_err());
    let a = ticket(&mut n, "@alice", 30, "a");
    let b = ticket(&mut n, "@bob", 20, "b");
    n.operation(&a);
    n.operation(&b);
    n.finalize(&a);
    n.finalize(&b);
    let cp = n.advance_version("@alice", &[], &[a.address.clone(), b.address.clone()]);
    assert_eq!(
        cp.manifest.allocation,
        Resources {
            rights: 50,
            headroom: 50
        }
    );
    assert!(n
        .ctx
        .version_request(&cp.manifest, COLLECTIVE_POOL)
        .is_err());
    let restock = n.make("@treasury", "restock", None, 20, "restock");
    n.operation(&restock);
    n.finalize(&restock);
    let v = n.rs[0].finalized_view().unwrap();
    assert_eq!(v.value, 70);
    assert_eq!(v.headroom.unwrap()[COLLECTIVE_POOL], 30);
    let mut forged = cp.clone();
    forged.authorization.signer = "@outsider".into();
    forged.authorization.signature = signature(
        &forged.authorization.signer,
        &forged.authorization.preimage(),
    );
    assert!(n.rs[3].receive_version(forged, &mut n.j, &n.auth).is_err());
    // A cast member with only the opener role cannot select successors.
    let n = collective_source(&TICKETS.replace(
        "(extend restock (to amount) :from organizer",
        "(extend restock (to amount) :from seller",
    ));
    let root = n.ctx.root_epoch("@alice").unwrap();
    let m = n.rs[0]
        .draft_version(
            &[root].into_iter().collect(),
            &BTreeSet::new(),
            &BTreeSet::new(),
            &BTreeSet::new(),
        )
        .unwrap();
    assert!(n.ctx.version_request(&m, "@treasury").is_err());
    assert!(n.ctx.version_request(&m, "@alice").is_ok());
}
#[test]
fn collective_declarations_defaults_and_programmatic_validation() {
    let account = dialect(COIN);
    let explicit = dialect(&COIN.replace("(floor 0)", "(floor 0) (ownership account)"));
    assert_eq!(
        cbcl_core::canonical::dialect_hash(&account),
        cbcl_core::canonical::dialect_hash(&explicit)
    );
    let original = rule(&account);
    let mut raw = serde_json::to_value(original).unwrap();
    raw.as_object_mut().unwrap().remove("ownership");
    let decoded: cbcl_core::escrow::CounterRule = serde_json::from_value(raw).unwrap();
    assert_eq!(&decoded, original);
    let n = collective();
    let normalized = cbcl_parser::define_text_str(TICKETS).unwrap();
    assert_eq!(
        cbcl_core::canonical::dialect_hash(&n.d),
        cbcl_core::canonical::dialect_hash(&dialect(&normalized))
    );
    for bad in [
        TICKETS.replace("(ownership collective)", "(ownership unknown)"),
        TICKETS.replace(
            "(ownership collective)",
            "(ownership collective) (ownership collective)",
        ),
        TICKETS.replace(
            "(initial open :available)",
            "(initial-rights open :available)",
        ),
        TICKETS.replace(
            "(initial open :available)",
            "(initial open :available) (initial-rights open :available)",
        ),
        TICKETS.replace("(floor 0)", "(floor 0) (transfer sell :buyer :amount)"),
        TICKETS.replace("(floor 0)", "(floor 0) (initial-headroom open :space)"),
        TICKETS.replace(
            "(certification quorum-budget (validators @v0 @v1 @v2 @v3))",
            "(certification host-gate)",
        ),
        TICKETS.replace(":from seller :to", ":to"),
        COIN.replace(
            "(initial-rights open :allocations)",
            "(initial open :allocations)",
        ),
    ] {
        if let Ok(d) = parse_dialect(&parse(&bad).unwrap()) {
            assert!(!cbcl_core::r7::r7_violations(&d).is_empty(), "{bad}");
        }
    }
    let mut invalid = n.d.clone();
    if let Some(Rule::BoundedCounter(c)) = invalid
        .state
        .as_mut()
        .unwrap()
        .entries
        .iter_mut()
        .find_map(|e| match e {
            cbcl_core::state::Entry::Field { name, rule } if name == "tickets" => Some(rule),
            _ => None,
        })
    {
        c.certification = Certification::HostGate;
    }
    assert!(!cbcl_core::r7::r7_violations(&invalid).is_empty());
}
#[test]
fn collective_authoring_ignores_forged_role_caches_and_preserves_signers() {
    let mut n = collective();
    let mut inst = Instance::new(&n.d, ThreadId("coin-1".into()), &n.base).unwrap();
    inst.cast.as_mut().unwrap().indexed.insert(
        "seller".into(),
        [AgentKey("@mallory".into())].into_iter().collect(),
    );
    let mut f = fields(None, 3);
    f.insert(
        "buyer".into(),
        SExpr::Atom(Atom::Symbol("@customer".into())),
    );
    assert!(n.rs[0]
        .intend(
            &inst,
            &AgentKey("@mallory".into()),
            "sell",
            f.clone(),
            "bad"
        )
        .is_err());
    let good = n.rs[0]
        .intend(&inst, &AgentKey("@alice".into()), "sell", f, "good")
        .unwrap();
    let a = Act::from_message(good, "@alice").unwrap();
    assert_eq!(a.signer, "@alice");
    n.auth.acts.insert((a.address.clone(), a.signer.clone()));
    n.register(&a);
    assert_eq!(
        a.fields["escrow-prev"],
        SExpr::Atom(Atom::Symbol(n.ctx.root_epoch("@bob").unwrap()))
    );
    let inst = Instance::new(&n.d, ThreadId("coin-1".into()), &n.base).unwrap();
    assert!(intend(&inst, &AgentKey("@alice".into()), "sell", fields(None, 3)).is_err());
    assert!(n.rs[0]
        .fold_instance(&inst)
        .unwrap()
        .iter()
        .find(|(f, _)| f == "tickets")
        .unwrap()
        .1
        .render()
        .contains("collective"));
}

#[test]
fn collective_reserved_resource_scope_cannot_be_an_authenticated_actor() {
    let n = collective();
    let root_message = serde_json::to_string(&n.base[0].message)
        .unwrap()
        .replace("@alice", COLLECTIVE_POOL);
    let root =
        Act::from_message(serde_json::from_str(&root_message).unwrap(), "@treasury").unwrap();
    let open_message = serde_json::to_string(&n.base[1].message)
        .unwrap()
        .replace("@alice", COLLECTIVE_POOL)
        .replace(&n.base[0].address, &root.address);
    let open =
        Act::from_message(serde_json::from_str(&open_message).unwrap(), "@treasury").unwrap();
    let base = vec![root, open];
    let auth = Auth {
        acts: base
            .iter()
            .map(|a| (a.address.clone(), a.signer.clone()))
            .collect(),
    };
    let inst = Instance::new(&n.d, ThreadId("coin-1".into()), &base).unwrap();
    assert!(Context::from_instance(&inst, "tickets", None, &auth)
        .unwrap_err()
        .contains("reserved"));
}
#[test]
fn collective_json_contract_uses_shared_rule_recognizer() {
    let contract = serde_json::json!({"version":3,"kind":"contract","name":"json-tickets","author":"@author",
        "roles":{"organizer":"singleton","seller":"indexed"},
        "verbs":{
            "open":{"after":["begin"],"fields":{"available":"number"},"from":"organizer","to":["organizer","seller"]},
            "restock":{"after":["open"],"fields":{"amount":"number"},"from":"organizer","to":["organizer","seller"]},
            "sell":{"after":["open"],"fields":{"buyer":"symbol","amount":"number"},"from":"seller","to":["organizer","seller"]}},
        "state":{"tickets":["boundedCounter",[["ownership","collective"],["certification","quorum-budget"],["floor",0],["ceiling",100],["initial","open",":available"],["issuers","organizer"],["increment","restock",":amount"],["decrement","sell",":amount"]]]}});
    let compiled: serde_json::Value =
        serde_json::from_str(&cbcl_parser::compile_contract_str(&contract.to_string()).unwrap())
            .unwrap();
    let d = dialect(compiled["dialect"].as_str().unwrap());
    let Rule::BoundedCounter(c) = d.state.as_ref().unwrap().rule_of("tickets").unwrap() else {
        panic!()
    };
    assert_eq!(c.ownership, cbcl_core::escrow::Ownership::Collective);
    assert!(c.transfer.is_none());
    assert_eq!(c.ceiling, Some(100));
    let mut bad = contract;
    bad["state"]["tickets"][1]
        .as_array_mut()
        .unwrap()
        .push(serde_json::json!(["transfer", "sell", ":buyer", ":amount"]));
    assert!(cbcl_parser::compile_contract_str(&bad.to_string()).is_err());
}
#[test]
fn collective_invalid_genesis_never_creates_a_pool() {
    for (source, available, signer) in [
        (TICKETS.to_string(), -1, "@treasury"),
        (
            TICKETS.replace("(floor 0)", "(floor 0) (ceiling 99)"),
            100,
            "@treasury",
        ),
        (TICKETS.to_string(), 100, "@alice"),
    ] {
        let n = collective();
        let d = dialect(&source);
        let root = n.base[0].clone();
        let open=act(&format!("(lang {} (open (@alice @bob @treasury) :available {} :from {} :thread \"coin-1\" :caused-by {}))",d.name,available,signer,root.address),signer);
        let base = vec![root, open];
        let auth = Auth {
            acts: base
                .iter()
                .map(|a| (a.address.clone(), a.signer.clone()))
                .collect(),
        };
        let inst = Instance::new(&d, ThreadId("coin-1".into()), &base).unwrap();
        assert!(Context::from_instance(&inst, "tickets", None, &auth).is_err());
    }
}

#[test]
fn collective_received_acts_enforce_roles_and_actual_issuer() {
    for (source, actor, verb, extra, expected) in [
        (
            TICKETS.to_string(),
            "@treasury",
            "sell",
            ":buyer @customer",
            "role",
        ),
        (
            TICKETS.replace(
                "(extend restock (to amount) :from organizer",
                "(extend restock (to amount) :from seller",
            ),
            "@bob",
            "restock",
            "",
            "issuer",
        ),
    ] {
        let mut n = collective_source(&source);
        let epoch = n.ctx.root_epoch(actor).unwrap();
        let op=act(&format!("(lang {} ({} (@alice @bob @treasury) {} :amount 1 :escrow-prev {} :escrow-deps () :escrow-nonce \"received\" :from {} :thread \"coin-1\" :caused-by {}))",n.d.name,verb,extra,epoch,actor,n.base[1].address),actor);
        n.auth.acts.insert((op.address.clone(), op.signer.clone()));
        let error = n.rs[0].register(op, &mut n.j, &n.auth).unwrap_err();
        assert!(error.contains(expected), "{error}");
    }
}

#[test]
fn collective_history_and_cas_are_shared_across_actors() {
    let mut n = collective();
    let a = ticket(&mut n, "@alice", 10, "a");
    let b = ticket(&mut n, "@bob", 10, "b");
    n.register(&a);
    n.register(&b);
    let mut stale =
        Replica::recover(n.ctx.clone(), "@v0", Limits::default(), &n.j, &n.auth).unwrap();
    let sequence = n.rs[0].journal_sequence();
    n.j.fail = true;
    assert!(n.rs[0]
        .prepare_operation(&a.address, &mut n.j, &n.auth)
        .is_err());
    assert_eq!(n.rs[0].journal_sequence(), sequence);
    n.j.fail = false;
    n.rs[0]
        .prepare_operation(&a.address, &mut n.j, &n.auth)
        .unwrap();
    assert!(stale
        .prepare_operation(&b.address, &mut n.j, &n.auth)
        .is_err());
    let v = n.advance_version("@alice", &[], &[]);
    assert!(v.manifest.held.contains(&a.address));
    assert_eq!(
        n.rs[0].active_epoch("@alice").unwrap(),
        n.rs[0].active_epoch("@bob").unwrap()
    );
    let recovered =
        Replica::recover(n.ctx.clone(), "@v0", Limits::default(), &n.j, &n.auth).unwrap();
    assert_eq!(
        recovered.version_snapshot("@alice").unwrap(),
        n.rs[0].version_snapshot("@bob").unwrap()
    );
}

#[path = "quorum_runtime/multi_parent.rs"]
mod multi_parent;

#[path = "quorum_runtime/owned.rs"]
mod owned;
