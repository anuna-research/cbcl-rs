//! Resource decrement/funding/fork profiles; no native admission claim.
use super::*;

fn initial() -> (Act,Act) {
    let root = Act::from_message(parse_message(&parse("(with-roles ((issuer @treasury) (holder @treasury @alice @bob)) (signed @treasury (hello :thread \"coin-1\" :caused-by begin)))").unwrap()).unwrap(),"@treasury").unwrap();
    let opener = Act::from_message(parse_message(&parse(&format!("(signed @treasury (lang example-coin (open (@alice @bob @treasury) :name \"Example Coin\" :allocations ((@treasury 1000) (@alice 0) (@bob 0)) :from @treasury :thread \"coin-1\" :caused-by {})))",root.address)).unwrap()).unwrap(),"@treasury").unwrap();
    (root,opener)
}

fn observed(dialect: &cbcl_core::dialect::Dialect, acts: &[Act], ids: &BTreeMap<String,u64>) -> Value {
    let state: Value = serde_json::from_str(&render_json(&fold(dialect.state.as_ref().unwrap(),dialect.causal_protocol.as_ref(),acts))).unwrap();
    let coins = &state["coins"];
    if coins["status"] == "ready" {
        json!({"status":"ready","value":coins["value"],"rights":coins["rights"]})
    } else if coins["status"] == "fault" {
        let mut evidence = coins["evidence"].as_array().unwrap().iter().map(|name| {
            let name = name.as_str().unwrap();
            assert!(acts.iter().any(|act| act.address == name),"resource evidence names an absent act");
            ids[name]
        }).collect::<Vec<_>>();
        evidence.sort(); // Normalize the fixed hash/ordinal representation only.
        assert!(evidence.windows(2).all(|pair| pair[0] != pair[1]),"duplicate native resource witness");
        json!({"status":"fault","evidence":evidence})
    } else { json!({"status":coins["status"]}) }
}

fn native(dialect: &cbcl_core::dialect::Dialect, case: &Value) -> Value {
    let (root,opener) = initial();
    let owner = case["owner"].as_str().unwrap();
    let amount = case["amount"].as_i64().unwrap();
    let operation = Act::from_message(parse_message(&parse(&format!("(signed {owner} (lang example-coin (burn (@alice @bob @treasury) :amount {amount} :from {owner} :thread \"coin-1\" :caused-by {} :escrow-prev {} :escrow-deps ())))",opener.address,opener.address)).unwrap()).unwrap(),owner).unwrap();
    let ids = BTreeMap::from([(root.address.clone(),1),(opener.address.clone(),2),(operation.address.clone(),3)]);
    assert_eq!(ids.len(),3,"fixture address projection must be injective");
    let mut acts = vec![operation];
    if case["root"].as_bool().unwrap() { acts.push(root); }
    if case["opener"].as_bool().unwrap() { acts.push(opener); }
    let result = observed(dialect,&acts,&ids);
    acts.reverse();
    acts.extend(acts.clone());
    assert_eq!(observed(dialect,&acts,&ids),result,"resource reorder/duplicate case={case}");
    result
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

fn native_graph(dialect: &cbcl_core::dialect::Dialect, case: &Value) -> Value {
    let (root,opener) = initial();
    let funding = case["funding"].as_i64().unwrap();
    let spend = case["spend"].as_i64().unwrap();
    let payment = Act::from_message(parse_message(&parse(&format!("(signed @treasury (lang example-coin (pay (@alice @bob @treasury) :recipient @alice :amount {funding} :from @treasury :thread \"coin-1\" :caused-by {} :escrow-prev {} :escrow-deps ())))",opener.address,opener.address)).unwrap()).unwrap(),"@treasury").unwrap();
    let dependency = case["dependency"].as_bool().unwrap();
    let deps = if dependency { payment.address.clone() } else { String::new() };
    let causes = if dependency { format!("({} {})",opener.address,payment.address) } else { opener.address.clone() };
    let spent = Act::from_message(parse_message(&parse(&format!("(signed @alice (lang example-coin (burn (@alice @bob @treasury) :amount {spend} :from @alice :thread \"coin-1\" :caused-by {causes} :escrow-prev {} :escrow-deps ({deps}))))",opener.address)).unwrap()).unwrap(),"@alice").unwrap();
    let competing = Act::from_message(parse_message(&parse(&format!("(signed @alice (lang example-coin (burn (@alice @bob @treasury) :amount 1 :from @alice :thread \"coin-1\" :caused-by {causes} :escrow-prev {} :escrow-deps ({deps}) :escrow-nonce \"fork\")))",opener.address)).unwrap()).unwrap(),"@alice").unwrap();
    let ids = BTreeMap::from([(root.address.clone(),1),(opener.address.clone(),2),(spent.address.clone(),3),(payment.address.clone(),4),(competing.address.clone(),5)]);
    assert_eq!(ids.len(),5,"fixture address projection must be injective");
    let mut acts = vec![root,opener,spent];
    if case["included"].as_bool().unwrap() { acts.push(payment); }
    if case["fork"].as_bool().unwrap() { acts.push(competing); }
    let result = observed(dialect,&acts,&ids);
    acts.reverse(); acts.extend(acts.clone());
    assert_eq!(observed(dialect,&acts,&ids),result,"resource graph reorder/duplicate case={case}");
    result
}

#[test]
#[ignore = "requires lake build cbcl-state-oracle; explicitly run in Lean CI"]
fn funding_graph_matches_lean() {
    let dialect = cbcl_parser::parse_dialect(&parse(include_str!("../../../../dialects/example-coin.cbcl")).unwrap()).unwrap();
    let mut registry = cbcl_core::dialect::DialectRegistry::new();
    registry.install(dialect.clone()).unwrap();
    let oracle = RefCell::new(Oracle::start());
    for (funding,spend) in [(5,1),(5,5),(5,6),(1000,1000),(1001,1),(0,1),(5,0),(-1,1),(5,-1),(i64::MAX,1),(1,i64::MAX)] {
        for included in [false,true] { for dependency in [false,true] { for fork in [false,true] {
            let case = json!({"profile":"resource-graph","funding":funding,"spend":spend,"included":included,"dependency":dependency,"fork":fork});
            assert_eq!(native_graph(&dialect,&case),oracle.borrow_mut().request(&case),"resource graph={case}");
        } } }
    }
    let mut config = proptest::test_runner::Config::default();
    if std::env::var_os("PROPTEST_CASES").is_none() { config.cases = 512; }
    let mut runner = proptest::test_runner::TestRunner::new(config);
    let amount = prop_oneof![any::<i64>(),-2i64..1003];
    runner.run(&(amount.clone(),amount,any::<bool>(),any::<bool>(),any::<bool>()), |(funding,spend,included,dependency,fork)| {
        let case = json!({"profile":"resource-graph","funding":funding,"spend":spend,"included":included,"dependency":dependency,"fork":fork});
        prop_assert_eq!(native_graph(&dialect,&case),oracle.borrow_mut().request(&case),"resource graph={}",case);
        Ok(())
    }).unwrap();
}
