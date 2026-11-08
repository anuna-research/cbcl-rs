//! Single-decrement resource verifier profile; no native admission claim.
use super::*;

fn native(dialect: &cbcl_core::dialect::Dialect, case: &Value) -> Value {
    let root = Act::from_message(parse_message(&parse("(with-roles ((issuer @treasury) (holder @treasury @alice @bob)) (signed @treasury (hello :thread \"coin-1\" :caused-by begin)))").unwrap()).unwrap(),"@treasury").unwrap();
    let opener = Act::from_message(parse_message(&parse(&format!("(signed @treasury (lang example-coin (open (@alice @bob @treasury) :name \"Example Coin\" :allocations ((@treasury 1000) (@alice 0) (@bob 0)) :from @treasury :thread \"coin-1\" :caused-by {})))",root.address)).unwrap()).unwrap(),"@treasury").unwrap();
    let owner = case["owner"].as_str().unwrap();
    let amount = case["amount"].as_i64().unwrap();
    let operation = Act::from_message(parse_message(&parse(&format!("(signed {owner} (lang example-coin (burn (@alice @bob @treasury) :amount {amount} :from {owner} :thread \"coin-1\" :caused-by {} :escrow-prev {} :escrow-deps ())))",opener.address,opener.address)).unwrap()).unwrap(),owner).unwrap();
    let mut acts = vec![operation];
    if case["root"].as_bool().unwrap() { acts.push(root); }
    if case["opener"].as_bool().unwrap() { acts.push(opener); }
    let state = |acts: &[Act]| {
        let state: Value = serde_json::from_str(&render_json(&fold(dialect.state.as_ref().unwrap(),dialect.causal_protocol.as_ref(),acts))).unwrap();
        let coins = &state["coins"];
        if coins["status"] == "ready" {
            json!({"status":"ready","value":coins["value"],"rights":coins["rights"]})
        } else { json!({"status":coins["status"]}) }
    };
    let observed = state(&acts);
    acts.reverse();
    acts.extend(acts.clone());
    assert_eq!(state(&acts),observed,"resource reorder/duplicate case={case}");
    observed
}

#[test]
#[ignore = "requires lake build cbcl-state-oracle; explicitly run in Lean CI"]
fn decrement_verifier_matches_lean() {
    let dialect = cbcl_parser::parse_dialect(&parse(include_str!("../../../../dialects/example-coin.cbcl")).unwrap()).unwrap();
    let mut registry = cbcl_core::dialect::DialectRegistry::new();
    registry.install(dialect.clone()).unwrap();
    let oracle = RefCell::new(Oracle::start());
    for owner in ["@treasury","@alice","@bob","@outsider"] {
        for amount in [i64::MIN,-1,0,1,999,1000,1001,i64::MAX] {
            for (root,opener) in [(false,false),(false,true),(true,false),(true,true)] {
                let case = json!({"profile":"resource-decrement","owner":owner,"amount":amount,"root":root,"opener":opener});
                assert_eq!(native(&dialect,&case),oracle.borrow_mut().request(&case),"resource case={case}");
            }
        }
    }
    for (key,invalid) in [("amount",json!("1")),("owner",json!("@unknown")),
        ("root",json!(1)),("opener",Value::Null)] {
        let mut case = json!({"profile":"resource-decrement","owner":"@treasury","amount":1,"root":true,"opener":true});
        case[key] = invalid;
        assert!(oracle.borrow_mut().response(&case).get("error").is_some(),"invalid resource transport={case}");
    }
    let mut config = proptest::test_runner::Config::default();
    if std::env::var_os("PROPTEST_CASES").is_none() { config.cases = 512; }
    let mut runner = proptest::test_runner::TestRunner::new(config);
    runner.run(&(0usize..4,prop_oneof![any::<i64>(),-2i64..1003],any::<bool>(),any::<bool>()), |(owner,amount,root,opener)| {
        let owner = ["@treasury","@alice","@bob","@outsider"][owner];
        let case = json!({"profile":"resource-decrement","owner":owner,"amount":amount,"root":root,"opener":opener});
        prop_assert_eq!(native(&dialect,&case),oracle.borrow_mut().request(&case),"resource case={}",case);
        Ok(())
    }).unwrap();
}
