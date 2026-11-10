//! SPEC-019 TEST-1960..1969: real grammar, binder and escrow observations.
use cbcl_core::intend::{intend, Instance};
use cbcl_core::role::AgentKey;
use cbcl_core::sexpr::{Atom, SExpr};
use cbcl_core::state::{fold, render_json, Act};
use cbcl_core::store::ThreadId;
use cbcl_parser::{parse, parse_dialect, parse_message};
use std::collections::BTreeMap;

const COIN: &str = include_str!("../../../dialects/example-coin.cbcl");
fn dialect() -> cbcl_core::dialect::Dialect {
    let d = parse_dialect(&parse(COIN).unwrap()).unwrap();
    let mut registry = cbcl_core::dialect::DialectRegistry::new();
    registry.install(d.clone()).unwrap();
    d
}
fn act(s: &str, signer: &str) -> Act {
    Act::from_message(parse_message(&parse(s).unwrap()).unwrap(), signer).unwrap()
}
fn initial(d: &cbcl_core::dialect::Dialect) -> Vec<Act> {
    let root = act("(with-roles ((issuer @treasury) (holder @treasury @alice @bob)) (signed @treasury (hello :thread \"coin-1\" :caused-by begin)))", "@treasury");
    let open = act(&format!("(signed @treasury (lang {} (open (@alice @bob @treasury) :name \"Example Coin\" :allocations ((@treasury 1000) (@alice 0) (@bob 0)) :from @treasury :thread \"coin-1\" :caused-by {})))",d.name,root.address),"@treasury");
    vec![root, open]
}
fn fields(xs: &[(&str, SExpr)]) -> BTreeMap<String, SExpr> {
    xs.iter().map(|(k, v)| (k.to_string(), v.clone())).collect()
}
fn num(n: i64) -> SExpr {
    SExpr::Atom(Atom::Num(n))
}
fn sym(s: &str) -> SExpr {
    SExpr::Atom(Atom::Symbol(s.to_string()))
}
fn emit(
    d: &cbcl_core::dialect::Dialect,
    acts: &mut Vec<Act>,
    signer: &str,
    verb: &str,
    xs: &[(&str, SExpr)],
) -> Result<Act, String> {
    let inst = Instance::new(d, ThreadId("coin-1".into()), acts).unwrap();
    let m = intend(&inst, &AgentKey(signer.into()), verb, fields(xs)).map_err(|e| e.to_string())?;
    let a = Act::from_message(m, signer).unwrap();
    acts.push(a.clone());
    Ok(a)
}
fn state(d: &cbcl_core::dialect::Dialect, acts: &[Act]) -> serde_json::Value {
    serde_json::from_str(&render_json(&fold(
        d.state.as_ref().unwrap(),
        d.causal_protocol.as_ref(),
        acts,
    )))
    .unwrap()
}
#[test]
fn worked_coin_trace_and_budget_refusals() {
    let d = dialect();
    let mut acts = initial(&d);
    assert_eq!(state(&d, &acts)["coins"]["value"], 1000);
    emit(
        &d,
        &mut acts,
        "@treasury",
        "pay",
        &[("recipient", sym("@alice")), ("amount", num(100))],
    )
    .unwrap();
    emit(
        &d,
        &mut acts,
        "@alice",
        "pay",
        &[("recipient", sym("@bob")), ("amount", num(25))],
    )
    .unwrap();
    emit(&d, &mut acts, "@bob", "burn", &[("amount", num(5))]).unwrap();
    emit(&d, &mut acts, "@treasury", "mint", &[("amount", num(250))]).unwrap();
    let s = state(&d, &acts);
    assert_eq!(s["coins"]["status"], "ready");
    assert_eq!(s["coins"]["value"], 1245);
    assert_eq!(
        s["coins"]["rights"],
        serde_json::json!({"@treasury":1150,"@alice":75,"@bob":20})
    );
    let before = acts.clone();
    assert!(emit(
        &d,
        &mut acts,
        "@alice",
        "pay",
        &[("recipient", sym("@bob")), ("amount", num(76))]
    )
    .is_err());
    assert!(emit(&d, &mut acts, "@alice", "mint", &[("amount", num(1))]).is_err());
    assert!(emit(&d, &mut acts, "@bob", "burn", &[("amount", num(-1))]).is_err());
    assert!(emit(&d, &mut acts, "@bob", "burn", &[("amount", num(0))]).is_err());
    assert_eq!(acts, before);
    acts.reverse();
    acts.extend(acts.clone());
    assert_eq!(state(&d, &acts), s);
}
#[test]
fn grammar_fails_closed() {
    for bad in [
        COIN.replace("(floor 0)", "(floor 0) (floor 1)"),
        COIN.replace("(floor 0)", "(ceiling 10)"),
        COIN.replace("(issuers issuer)", "(issuers missing)"),
        COIN.replace("(increment mint :amount)", "(increment burn :amount)"),
    ] {
        let parsed = parse_dialect(&parse(&bad).unwrap());
        if let Ok(d) = parsed {
            assert!(!cbcl_core::r7::r7_violations(&d).is_empty());
        }
    }
}

fn counter(d: &cbcl_core::dialect::Dialect) -> &cbcl_core::escrow::CounterRule {
    d.state
        .as_ref()
        .unwrap()
        .fields()
        .find_map(|(_, r)| {
            if let cbcl_core::state::Rule::BoundedCounter(c) = r {
                Some(c.as_ref())
            } else {
                None
            }
        })
        .unwrap()
}
fn change(a: &Act, key: &str, value: SExpr) -> Act {
    fn inner(m: &mut cbcl_core::message::Message) -> &mut cbcl_core::message::Message {
        match m {
            cbcl_core::message::Message::Wrapped { content, .. } => inner(content),
            cbcl_core::message::Message::Dialect { inner: m, .. } => inner(m),
            _ => m,
        }
    }
    let mut m = a.message.clone();
    if let cbcl_core::message::Message::Simple { params, .. } = inner(&mut m) {
        let i = params
            .iter()
            .position(|x| matches!(x,SExpr::Atom(Atom::Keyword(k)) if k==key))
            .unwrap();
        params[i + 1] = value;
    }
    Act::from_message(m, &a.signer).unwrap()
}
#[test]
fn funding_evidence_pending_replay_and_forks() {
    let d = dialect();
    let base = initial(&d);
    let mut acts = base.clone();
    let funding = emit(
        &d,
        &mut acts,
        "@treasury",
        "pay",
        &[("recipient", sym("@alice")), ("amount", num(100))],
    )
    .unwrap();
    let spend = emit(
        &d,
        &mut acts,
        "@alice",
        "pay",
        &[("recipient", sym("@bob")), ("amount", num(25))],
    )
    .unwrap();
    let mut missing = base.clone();
    missing.push(spend.clone());
    assert_eq!(state(&d, &missing)["coins"]["status"], "pending");
    assert!(state(&d, &missing)["coins"].get("rights").is_none());
    missing.push(funding.clone());
    assert_eq!(state(&d, &missing), state(&d, &acts));
    let unfunded = change(&spend, "escrow-deps", SExpr::List(vec![]));
    let mut bad = base.clone();
    bad.push(funding.clone());
    bad.push(unfunded);
    assert_eq!(state(&d, &bad)["coins"]["reason"], "insufficient rights");
    let mut other_branch = base.clone();
    let fork = emit(
        &d,
        &mut other_branch,
        "@treasury",
        "pay",
        &[("recipient", sym("@bob")), ("amount", num(101))],
    )
    .unwrap();
    acts.push(fork.clone());
    let s = state(&d, &acts);
    assert_eq!(s["coins"]["reason"], "owner fork");
    let evidence = s["coins"]["evidence"].as_array().unwrap();
    for witness in [&funding.address, &fork.address] {
        assert!(evidence.contains(&serde_json::json!(witness)));
    }
    acts.reverse();
    assert_eq!(state(&d, &acts), s);
    // Duplicate authentication with a different claimed signer cannot be hidden by fold dedup.
    let mut conflict = base;
    let mut same = funding.clone();
    same.signer = "@bob".into();
    conflict.push(funding);
    conflict.push(same);
    assert_eq!(
        state(&d, &conflict)["coins"]["reason"],
        "conflicting authenticated identity"
    );
}
#[test]
fn canonical_binding_and_reserved_fields() {
    let d = dialect();
    let mut acts = initial(&d);
    emit(
        &d,
        &mut acts,
        "@treasury",
        "pay",
        &[("recipient", sym("@alice")), ("amount", num(100))],
    )
    .unwrap();
    let mut reverse = acts.clone();
    reverse.reverse();
    let a = emit(
        &d,
        &mut acts,
        "@alice",
        "pay",
        &[("recipient", sym("@bob")), ("amount", num(1))],
    )
    .unwrap();
    let b = emit(
        &d,
        &mut reverse,
        "@alice",
        "pay",
        &[("recipient", sym("@bob")), ("amount", num(1))],
    )
    .unwrap();
    assert_eq!(a, b);
    assert!(emit(
        &d,
        &mut acts,
        "@alice",
        "burn",
        &[("amount", num(1)), ("escrow-prev", sym(&a.address))]
    )
    .is_err());
    let malformed = COIN.replace(
        "(require :amount integer)",
        "(require :amount integer) (require :escrow-deps list)",
    );
    assert!(parse_dialect(&parse(&malformed).unwrap())
        .unwrap_err()
        .contains("reserved"));
    let mut r = cbcl_core::dialect::DialectRegistry::new();
    let hidden = COIN.replace("(state", "(state (domain pay :recipient name)");
    assert!(r
        .install(parse_dialect(&parse(&hidden).unwrap()).unwrap())
        .is_err());
    let reordered = COIN.replace(
        "(floor 0)\n      (initial-rights open :allocations)",
        "(initial-rights open :allocations)\n      (floor 0)",
    );
    let reordered = parse_dialect(&parse(&reordered).unwrap()).unwrap();
    assert_eq!(
        cbcl_core::canonical::dialect_hash(&d),
        cbcl_core::canonical::dialect_hash(&reordered)
    );
    let changed = parse_dialect(&parse(&COIN.replace("(floor 0)", "(floor 1)")).unwrap()).unwrap();
    assert_ne!(
        cbcl_core::canonical::dialect_hash(&d),
        cbcl_core::canonical::dialect_hash(&changed)
    );
}
fn ceiling_dialect() -> cbcl_core::dialect::Dialect {
    let src = include_str!("../../../dialects/example-capped-coin.cbcl");
    let d = parse_dialect(&parse(src).unwrap()).unwrap();
    let mut r = cbcl_core::dialect::DialectRegistry::new();
    r.install(d.clone()).unwrap();
    d
}
fn ceiling_initial(d: &cbcl_core::dialect::Dialect) -> Vec<Act> {
    let root=act("(with-roles ((issuer @treasury @alice) (holder @treasury @alice @bob)) (signed @treasury (hello :thread \"coin-1\" :caused-by begin)))","@treasury");
    let open=act(&format!("(signed @treasury (lang {} (open (@alice @bob @treasury) :name \"Capped\" :allocations ((@treasury 2) (@alice 2) (@bob 0)) :space ((@treasury 3) (@alice 3) (@bob 0)) :from @treasury :thread \"coin-1\" :caused-by {})))",d.name,root.address),"@treasury");
    vec![root, open]
}
#[test]
fn optional_ceiling_concurrent_increments_and_headroom_transfer() {
    let d = ceiling_dialect();
    let base = ceiling_initial(&d);
    let mut left = base.clone();
    let mut right = base.clone();
    let a = emit(&d, &mut left, "@treasury", "mint", &[("amount", num(3))]).unwrap();
    let b = emit(&d, &mut right, "@alice", "mint", &[("amount", num(3))]).unwrap();
    let mut merged = base.clone();
    merged.extend([a, b]);
    assert_eq!(state(&d, &merged)["coins"]["value"], 10);
    assert!(emit(&d, &mut merged, "@treasury", "mint", &[("amount", num(1))]).is_err());
    emit(&d, &mut merged, "@alice", "burn", &[("amount", num(2))]).unwrap();
    assert_eq!(state(&d, &merged)["coins"]["headroom"]["@alice"], 2);
    emit(
        &d,
        &mut merged,
        "@alice",
        "share-space",
        &[("recipient", sym("@treasury")), ("amount", num(2))],
    )
    .unwrap();
    emit(&d, &mut merged, "@treasury", "mint", &[("amount", num(2))]).unwrap();
    assert_eq!(state(&d, &merged)["coins"]["value"], 10);
    let before = merged.clone();
    assert!(emit(
        &d,
        &mut merged,
        "@alice",
        "share-space",
        &[("recipient", sym("@treasury")), ("amount", num(1))]
    )
    .is_err());
    assert_eq!(before, merged);
    let bad = change(
        &base[1],
        "space",
        SExpr::List(vec![
            SExpr::List(vec![sym("@treasury"), num(7)]),
            SExpr::List(vec![sym("@alice"), num(3)]),
            SExpr::List(vec![sym("@bob"), num(0)]),
        ]),
    );
    assert_eq!(
        state(&d, &[base[0].clone(), bad])["coins"]["status"],
        "fault"
    );
}
#[test]
fn shared_export_keeps_protocol_and_resource_verdicts_separate() {
    use cbcl_core::serializer::serialize;
    let d = dialect();
    let mut history = initial(&d);
    let good = emit(
        &d,
        &mut history,
        "@treasury",
        "pay",
        &[("recipient", sym("@alice")), ("amount", num(1))],
    )
    .unwrap();
    let candidate = change(&good, "amount", num(1001));
    history.pop();
    let entries = history
        .iter()
        .map(|a| format!("({} {})", a.signer, serialize(&SExpr::from(&a.message))))
        .collect::<Vec<_>>()
        .join(" ");
    let candidate_text = format!(
        "({} (signed {} {}))",
        candidate.signer,
        candidate.signer,
        serialize(&SExpr::from(&candidate.message))
    );
    let frame = format!("(resource-check {COIN} \"coin-1\" (acts {entries}) {candidate_text})");
    let result = cbcl_parser::state_exports::resource_check_str(&frame).unwrap();
    assert_eq!(
        serde_json::from_str::<serde_json::Value>(&result).unwrap()["status"],
        "rejected"
    );
    let protocol =
        cbcl_parser::state_exports::admit_str(&frame.replacen("resource-check", "admit", 1))
            .unwrap();
    assert_eq!(
        serde_json::from_str::<serde_json::Value>(&protocol).unwrap()["verdict"],
        "accepted"
    );
    assert!(matches!(
        cbcl_core::escrow::observe(counter(&d), &history),
        cbcl_core::escrow::Outcome::Ready(_)
    ));
}

proptest::proptest! {
    // Independent arithmetic oracle; failed intents must not mutate history.
    #[test]
    fn dual_budget_matches_independent_machine(ops in proptest::collection::vec((0usize..3,0usize..3,0u8..4,1i64..8),0..35)) {
        let d=ceiling_dialect();let mut acts=ceiling_initial(&d);
        let accounts=["@treasury","@alice","@bob"];
        let mut rights=[2i64,2,0];let mut headroom=[3i64,3,0];
        for (owner,to,kind,n) in ops {
            let (verb,allowed)=match kind {
                0=>("pay",owner!=to&&rights[owner]>=n),
                1=>("burn",rights[owner]>=n),
                2=>("mint",owner<2&&headroom[owner]>=n),
                _=>("share-space",owner!=to&&headroom[owner]>=n),
            };
            let mut fields=vec![("amount",num(n))];if kind==0||kind==3{fields.push(("recipient",sym(accounts[to])));}
            let before=acts.len();let result=emit(&d,&mut acts,accounts[owner],verb,&fields);
            proptest::prop_assert_eq!(result.is_ok(),allowed);
            if allowed { match kind {0=>{rights[owner]-=n;rights[to]+=n;},1=>{rights[owner]-=n;headroom[owner]+=n;},2=>{headroom[owner]-=n;rights[owner]+=n;},_=>{headroom[owner]-=n;headroom[to]+=n;}} }
            else {proptest::prop_assert_eq!(acts.len(),before);}
            let s=state(&d,&acts);
            proptest::prop_assert_eq!(&s["coins"]["status"],"ready");
            for i in 0..3 {proptest::prop_assert_eq!(s["coins"]["rights"][accounts[i]].as_i64(),Some(rights[i]));proptest::prop_assert_eq!(s["coins"]["headroom"][accounts[i]].as_i64(),Some(headroom[i]));}
            let total:i64=rights.iter().sum();proptest::prop_assert!((0..=10).contains(&total));proptest::prop_assert_eq!(total+headroom.iter().sum::<i64>(),10);
        }
    }
}

/// Real file-backed test adapter. The production host supplies its own gate;
/// this exercises full-candidate persistence, exclusive issuance and recovery.
struct FileGate {
    dir: std::path::PathBuf,
}
impl cbcl_core::escrow::IssuanceGate for FileGate {
    fn compare_and_append(
        &mut self,
        lane: &cbcl_core::escrow::IssuanceLane,
        expected: &str,
        candidate: &Act,
    ) -> Result<(), String> {
        use std::io::Write;
        let lock = self.dir.join("lock");
        let _exclusive = std::fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&lock)
            .map_err(|e| e.to_string())?;
        struct Unlock(std::path::PathBuf);
        impl Drop for Unlock {
            fn drop(&mut self) {
                let _ = std::fs::remove_file(&self.0);
            }
        }
        let _unlock = Unlock(lock);
        let path = self.dir.join("record");
        let previous = std::fs::read_to_string(&path)
            .ok()
            .map(|s| serde_json::from_str::<serde_json::Value>(&s).unwrap());
        let namespace = format!("{:?}", lane);
        if let Some(p) = &previous {
            if p["lane"] != namespace || p["address"] != expected {
                return Err("stale tip or wrong lane".into());
            }
        } else if expected != lane.opener {
            return Err("uninitialized lane cannot skip owner history".into());
        }
        let text = cbcl_core::serializer::serialize(&SExpr::from(&candidate.message));
        let record =
            serde_json::json!({"lane":namespace,"address":candidate.address,"canonical":text});
        let temp = self.dir.join("next");
        let mut f = std::fs::File::create(&temp).map_err(|e| e.to_string())?;
        f.write_all(record.to_string().as_bytes())
            .map_err(|e| e.to_string())?;
        f.sync_all().map_err(|e| e.to_string())?;
        std::fs::rename(temp, path).map_err(|e| e.to_string())?;
        std::fs::File::open(&self.dir)
            .and_then(|f| f.sync_all())
            .map_err(|e| e.to_string())?;
        Ok(())
    }
}
#[test]
fn durable_issuance_race_and_recovery() {
    use std::sync::{Arc, Barrier};
    let d = dialect();
    let acts = initial(&d);
    let unique = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let dir = std::env::temp_dir().join(format!("cbcl-escrow-{}-{unique}", std::process::id()));
    std::fs::create_dir(&dir).unwrap();
    let barrier = Arc::new(Barrier::new(2));
    let mut threads = Vec::new();
    for amount in [500, 600] {
        let d = d.clone();
        let acts = acts.clone();
        let dir = dir.clone();
        let barrier = barrier.clone();
        threads.push(std::thread::spawn(move || {
            let inst = Instance::new(&d, ThreadId("coin-1".into()), &acts).unwrap();
            barrier.wait();
            cbcl_core::escrow::issue(
                &inst,
                &AgentKey("@treasury".into()),
                "pay",
                fields(&[("recipient", sym("@alice")), ("amount", num(amount))]),
                &mut FileGate { dir },
            )
        }));
    }
    let outcomes = threads
        .into_iter()
        .map(|t| t.join().unwrap())
        .collect::<Vec<_>>();
    assert_eq!(outcomes.iter().filter(|r| r.is_ok()).count(), 1);
    let record: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(dir.join("record")).unwrap()).unwrap();
    let recovered = act(record["canonical"].as_str().unwrap(), "@treasury");
    assert_eq!(record["address"], recovered.address);
    let mut recovered_history = acts.clone();
    recovered_history.push(recovered.clone());
    let inst = Instance::new(&d, ThreadId("coin-1".into()), &recovered_history).unwrap();
    let next = cbcl_core::escrow::issue(
        &inst,
        &AgentKey("@treasury".into()),
        "burn",
        fields(&[("amount", num(1))]),
        &mut FileGate { dir: dir.clone() },
    )
    .unwrap();
    let next = Act::from_message(next, "@treasury").unwrap();
    assert_eq!(next.fields["escrow-prev"], sym(&recovered.address));
    // Publication retries after recovery use the same persisted identity.
    let mut sink = std::collections::BTreeSet::new();
    assert!(sink.insert(recovered.address.clone()));
    assert!(!sink.insert(recovered.address));
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn pinned_context_and_conflicting_root_casts() {
    let d = dialect();
    let history = initial(&d);
    let wrong = cbcl_core::escrow::fold_instance(&d, "another-thread", &history);
    let s: serde_json::Value = serde_json::from_str(&render_json(&wrong)).unwrap();
    assert_eq!(s["coins"]["status"], "fault");
    let mut foreign = d.clone();
    foreign.name = "foreign-coin".into();
    let s: serde_json::Value = serde_json::from_str(&render_json(
        &cbcl_core::escrow::fold_instance(&foreign, "coin-1", &history),
    ))
    .unwrap();
    assert_eq!(s["coins"]["status"], "fault");
    let other_root=act("(with-roles ((issuer @alice) (holder @treasury @alice @bob)) (signed @treasury (hello :thread \"coin-1\" :caused-by begin)))","@treasury");
    // SPEC-038 ADR-3807: distinct sealed casts no longer alias. Preserve
    // the separate same-address authenticated-signer conflict regression.
    assert_ne!(other_root.address, history[0].address);
    let mut conflicting_identity = history[0].clone();
    conflicting_identity.signer = "@alice".into();
    let mut conflict = history.clone();
    conflict.push(conflicting_identity);
    let s = state(&d, &conflict);
    assert_eq!(s["coins"]["reason"], "conflicting authenticated identity");
    conflict.reverse();
    assert_eq!(s, state(&d, &conflict));
    let mut foreign_acts = initial(&foreign);
    let candidate = emit(
        &foreign,
        &mut foreign_acts,
        "@treasury",
        "mint",
        &[("amount", num(1))],
    )
    .unwrap();
    foreign_acts.pop();
    let text = foreign_acts
        .iter()
        .map(|a| {
            format!(
                "({} {})",
                a.signer,
                cbcl_core::serializer::serialize(&SExpr::from(&a.message))
            )
        })
        .collect::<Vec<_>>()
        .join(" ");
    let frame = format!(
        "(resource-check {COIN} \"coin-1\" (acts {text}) ({} {}))",
        candidate.signer,
        cbcl_core::serializer::serialize(&SExpr::from(&candidate.message))
    );
    let outcome: serde_json::Value =
        serde_json::from_str(&cbcl_parser::state_exports::resource_check_str(&frame).unwrap())
            .unwrap();
    assert_eq!(outcome["status"], "fault");
}

#[test]
fn json_authoring_uses_the_same_counter_recognizer() {
    let contract = serde_json::json!({"version":3,"kind":"contract","name":"json-coin","author":"@author",
        "roles":{"issuer":"singleton","holder":"indexed"},
        "verbs":{
            "open":{"after":["begin"],"fields":{"allocations":"list"},"from":"issuer","to":["issuer","holder"]},
            "mint":{"after":["open"],"fields":{"amount":"integer"},"from":"issuer","to":["issuer","holder"]},
            "burn":{"after":["open"],"fields":{"amount":"integer"},"from":"holder","to":["issuer","holder"]},
            "pay":{"after":["open"],"fields":{"recipient":"symbol","amount":"integer"},"from":"holder","to":["issuer","holder"]}},
        "state":{"coins":["boundedCounter",[["floor",0],["initial-rights","open",":allocations"],["issuers","issuer"],["increment","mint",":amount"],["decrement","burn",":amount"],["transfer","pay",":recipient",":amount"]]]}});
    let result = cbcl_parser::compile_contract_str(&contract.to_string()).unwrap();
    let result: serde_json::Value = serde_json::from_str(&result).unwrap();
    assert!(result["dialect"]
        .as_str()
        .unwrap()
        .contains("bounded-counter"));
    let d = parse_dialect(&parse(result["dialect"].as_str().unwrap()).unwrap()).unwrap();
    assert_eq!(counter(&d).floor, 0);
    let mut bad = contract;
    bad["state"]["coins"][1][0][0] = serde_json::json!("floor) (tell @evil");
    assert!(cbcl_parser::compile_contract_str(&bad.to_string()).is_err());
}

/// Explicit corpus-authoring tool. Expectations for balances are independent
/// arithmetic constants; message hashes/canonical source come from the binder.
#[test]
#[ignore = "authors the checked-in conformance vector; run explicitly"]
fn author_coin_corpus() {
    use cbcl_core::serializer::serialize;
    let d = dialect();
    let mut acts = initial(&d);
    emit(
        &d,
        &mut acts,
        "@treasury",
        "pay",
        &[("recipient", sym("@alice")), ("amount", num(100))],
    )
    .unwrap();
    emit(
        &d,
        &mut acts,
        "@alice",
        "pay",
        &[("recipient", sym("@bob")), ("amount", num(25))],
    )
    .unwrap();
    emit(&d, &mut acts, "@bob", "burn", &[("amount", num(5))]).unwrap();
    emit(&d, &mut acts, "@treasury", "mint", &[("amount", num(250))]).unwrap();
    let canonical = |a: &Act| {
        let text = serialize(&SExpr::from(&a.message));
        if text.starts_with("(with-roles") || text.starts_with("(signed") {
            text
        } else {
            format!("(signed {} {text})", a.signer)
        }
    };
    let messages = acts
        .iter()
        .map(|a| serde_json::json!({"signer":a.signer,"canonical":canonical(a)}))
        .collect::<Vec<_>>();
    let verdicts = acts
        .iter()
        .map(|a| (a.address.clone(), serde_json::json!("accepted")))
        .collect::<serde_json::Map<_, _>>();
    let vector = serde_json::json!({"id":"bounded-coin","version":"2.0.0","thread":"coin-1","contract":COIN,"covers":["bounded-counter","transfer","mint","burn","resource-evidence"],"messages":messages,"expect":{"addresses":acts.iter().map(|a|&a.address).collect::<Vec<_>>(),"verdicts":verdicts,"state":{"name":"Example Coin","coins":{"status":"ready","value":1245,"rights":{"@treasury":1150,"@alice":75,"@bob":20}}},"intents":[]}});
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../test-vectors/state/bounded-coin.json"
    );
    std::fs::write(path, serde_json::to_string_pretty(&vector).unwrap() + "\n").unwrap();
    let accepted = acts[..acts.len() - 1]
        .iter()
        .map(|a| format!("({} {})", a.signer, canonical(a)))
        .collect::<Vec<_>>()
        .join(" ");
    let last = acts.last().unwrap();
    let frame = format!(
        "(resource-check {COIN} \"coin-1\" (acts {accepted}) ({} {}))",
        last.signer,
        canonical(last)
    );
    std::fs::write(
        concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../test-vectors/state/resource-check.sexp"
        ),
        frame + "\n",
    )
    .unwrap();
    let capped = include_str!("../../../dialects/example-capped-coin.cbcl");
    let d = ceiling_dialect();
    let mut left = ceiling_initial(&d);
    let mut right = left.clone();
    emit(&d, &mut left, "@treasury", "mint", &[("amount", num(3))]).unwrap();
    let b = emit(&d, &mut right, "@alice", "mint", &[("amount", num(3))]).unwrap();
    left.push(b);
    let messages = left
        .iter()
        .map(|a| serde_json::json!({"signer":a.signer,"canonical":canonical(a)}))
        .collect::<Vec<_>>();
    let verdicts = left
        .iter()
        .map(|a| (a.address.clone(), serde_json::json!("accepted")))
        .collect::<serde_json::Map<_, _>>();
    let vector = serde_json::json!({"id":"bounded-ceiling","version":"2.0.0","thread":"coin-1","contract":capped,"covers":["bounded-counter","ceiling","concurrent-mint","headroom"],"messages":messages,"expect":{"addresses":left.iter().map(|a|&a.address).collect::<Vec<_>>(),"verdicts":verdicts,"state":{"name":"Capped","coins":{"status":"ready","value":10,"rights":{"@treasury":5,"@alice":5,"@bob":0},"headroom":{"@treasury":0,"@alice":0,"@bob":0}}},"intents":[]}});
    std::fs::write(
        concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../test-vectors/state/bounded-ceiling.json"
        ),
        serde_json::to_string_pretty(&vector).unwrap() + "\n",
    )
    .unwrap();
    let accepted = left[..left.len() - 1]
        .iter()
        .map(|a| format!("({} {})", a.signer, canonical(a)))
        .collect::<Vec<_>>()
        .join(" ");
    let last = left.last().unwrap();
    let frame = format!(
        "(resource-check {capped} \"coin-1\" (acts {accepted}) ({} {}))",
        last.signer,
        canonical(last)
    );
    std::fs::write(
        concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../test-vectors/state/resource-check-capped.sexp"
        ),
        frame + "\n",
    )
    .unwrap();
}

#[test]
fn fixed_supply_can_disable_all_issuance() {
    let src = COIN.replace("(issuers issuer)", "(issuers ())");
    let d = parse_dialect(&parse(&src).unwrap()).unwrap();
    let mut r = cbcl_core::dialect::DialectRegistry::new();
    r.install(d.clone()).unwrap();
    let mut history = initial(&d);
    assert_eq!(state(&d, &history)["coins"]["status"], "ready");
    assert!(emit(&d, &mut history, "@treasury", "mint", &[("amount", num(1))]).is_err());
    emit(
        &d,
        &mut history,
        "@treasury",
        "pay",
        &[("recipient", sym("@alice")), ("amount", num(10))],
    )
    .unwrap();
    assert_eq!(state(&d, &history)["coins"]["value"], 1000);
}
#[test]
fn headroom_must_be_in_the_increment_causal_past() {
    let d = ceiling_dialect();
    let mut history = ceiling_initial(&d);
    emit(
        &d,
        &mut history,
        "@treasury",
        "share-space",
        &[("recipient", sym("@alice")), ("amount", num(1))],
    )
    .unwrap();
    let funded = emit(&d, &mut history, "@alice", "mint", &[("amount", num(4))]).unwrap();
    history.pop();
    let unfunded = change(&funded, "escrow-deps", SExpr::List(vec![]));
    history.push(unfunded);
    assert_eq!(
        state(&d, &history)["coins"]["reason"],
        "insufficient headroom"
    );
}

#[test]
fn resource_fault_evidence_keeps_prior_witnesses_when_another_fork_arrives() {
    let d = dialect();
    let base = initial(&d);
    let mut siblings = Vec::new();
    for amount in [10, 11, 12] {
        let mut branch = base.clone();
        siblings.push(
            emit(
                &d,
                &mut branch,
                "@treasury",
                "pay",
                &[("recipient", sym("@alice")), ("amount", num(amount))],
            )
            .unwrap(),
        );
    }
    siblings.sort_by(|a, b| a.address.cmp(&b.address));
    let mut history = base;
    history.extend([siblings[1].clone(), siblings[2].clone()]);
    let before = state(&d, &history);
    assert_eq!(before["coins"]["status"], "fault");
    history.push(siblings[0].clone());
    let after = state(&d, &history);
    for address in before["coins"]["evidence"].as_array().unwrap() {
        assert!(
            after["coins"]["evidence"]
                .as_array()
                .unwrap()
                .contains(address),
            "lost {address}: {before} -> {after}"
        );
    }
}

#[test]
fn missing_dependency_cannot_hide_an_independent_resource_fault() {
    // SPEC-038 REQ-3806: independent missing evidence cannot retract a fault.
    let d = dialect();
    let mut history = initial(&d);
    let opener = history[1].address.clone();
    let burn = |signer: &str, dependencies: &str| {
        act(&format!(
        "(signed {signer} (lang {} (burn (@alice @bob @treasury) :amount 1 :from {signer} :thread \"coin-1\" :caused-by {opener} :escrow-prev {opener} :escrow-deps ({dependencies}))))", d.name), signer)
    };
    let first = burn("@alice", "");
    let verdict =
        cbcl_parser::state_exports::admit(&d, &ThreadId("coin-1".into()), &history, &first);
    assert!(
        matches!(verdict, cbcl_parser::state_exports::Admission::Accepted),
        "{verdict:?}"
    );
    history.push(first);
    let before = state(&d, &history);
    assert_eq!(before["coins"]["reason"], "insufficient rights");
    let later = burn("@bob", &format!("sha256-{}", "f".repeat(64)));
    assert!(matches!(
        cbcl_parser::state_exports::admit(&d, &ThreadId("coin-1".into()), &history, &later),
        cbcl_parser::state_exports::Admission::Accepted
    ));
    history.push(later);
    let after = state(&d, &history);
    assert_eq!(after["coins"]["status"], "fault", "{before} -> {after}");
    for address in before["coins"]["evidence"].as_array().unwrap() {
        assert!(after["coins"]["evidence"]
            .as_array()
            .unwrap()
            .contains(address));
    }
}

// SPEC-038 REQ-3806: all public resource observation paths retain the same
// evidence. Profiles delegated to certificate runtimes keep constant faults.
#[test]
fn unsupported_resource_profiles_keep_projection_fault_evidence() {
    use cbcl_core::certification::Certification;
    use cbcl_core::escrow::{self, Outcome, Ownership};
    let d = dialect();
    let history = initial(&d);
    for collective in [true, false] {
        let mut rule = counter(&d).clone();
        if collective {
            rule.ownership = Ownership::Collective;
        } else {
            rule.certification = Certification::QuorumBudget {
                validators: None,
                faults: None,
            };
        }
        let facts = history
            .iter()
            .filter_map(|act| {
                escrow::project_resource_fact(&rule, act)
                    .unwrap()
                    .map(|fact| (fact.address.clone(), fact))
            })
            .collect();
        let present = |id: &str| history.iter().any(|act| act.address == id);
        match (
            escrow::observe(&rule, &history),
            escrow::observe_facts(&rule, &facts, present),
        ) {
            (Outcome::Fault { evidence: a, .. }, Outcome::Fault { evidence: b, .. }) => {
                assert!(b.is_empty());
                assert_eq!(a, b);
            }
            other => panic!("expected equivalent faults, got {other:?}"),
        }
    }
}
