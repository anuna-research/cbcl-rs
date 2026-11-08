//! Resource decrement/funding/fork profiles; no native admission claim.
use super::*;

fn initial() -> (Act,Act) {
    let root = Act::from_message(parse_message(&parse("(with-roles ((issuer @treasury) (holder @treasury @alice @bob)) (signed @treasury (hello :thread \"coin-1\" :caused-by begin)))").unwrap()).unwrap(),"@treasury").unwrap();
    let opener = Act::from_message(parse_message(&parse(&format!("(signed @treasury (lang example-coin (open (@alice @bob @treasury) :name \"Example Coin\" :allocations ((@treasury 1000) (@alice 0) (@bob 0)) :from @treasury :thread \"coin-1\" :caused-by {})))",root.address)).unwrap()).unwrap(),"@treasury").unwrap();
    (root,opener)
}

fn observed(dialect: &cbcl_core::dialect::Dialect, acts: &[Act], ids: &BTreeMap<String,u64>) -> Value {
    let folded = fold(dialect.state.as_ref().unwrap(),dialect.causal_protocol.as_ref(),acts);
    let state: Value = serde_json::from_str(&render_json(&folded)).unwrap();
    let coins = &state["coins"];
    if coins.get("frozen").is_some() {
        let bytes = folded.iter().find(|(name,_)| name == "coins").unwrap().1.render();
        json!({"status":"frozen","rendered":bytes})
    } else if coins["status"] == "ready" {
        json!({"status":"ready","value":coins["value"],"rights":coins["rights"]})
    } else if coins["status"] == "fault" {
        let mut evidence = coins["evidence"].as_array().unwrap().iter().map(|name| {
            let name = name.as_str().unwrap();
            assert!(acts.iter().any(|act| act.address == name),"resource evidence names an absent act");
            ids[name]
        }).collect::<Vec<_>>();
        evidence.sort(); // Normalize the fixed hash/ordinal representation only.
        assert!(evidence.windows(2).all(|pair| pair[0] != pair[1]),"duplicate native resource witness");
        let cbcl_core::state::Value::Map(fields) = &folded.iter().find(|(name,_)| name == "coins").unwrap().1 else { panic!("fault must be a map") };
        let witness_bytes = fields.iter().find(|(key,_)| matches!(key,cbcl_core::state::Value::Str(name) if name == "evidence")).unwrap().1.render();
        json!({"status":"fault","evidence":evidence,"witness_bytes":witness_bytes})
    } else { json!({"status":coins["status"]}) }
}

fn native(dialect: &cbcl_core::dialect::Dialect, case: &mut Value) -> Value {
    let (root,opener) = initial();
    let owner = case["owner"].as_str().unwrap();
    let amount = case["amount"].as_i64().unwrap();
    let operation = Act::from_message(parse_message(&parse(&format!("(signed {owner} (lang example-coin (burn (@alice @bob @treasury) :amount {amount} :from {owner} :thread \"coin-1\" :caused-by {} :escrow-prev {} :escrow-deps ())))",opener.address,opener.address)).unwrap()).unwrap(),owner).unwrap();
    let ids = BTreeMap::from([(root.address.clone(),1),(opener.address.clone(),2),(operation.address.clone(),3)]);
    assert_eq!(ids.len(),3,"fixture address projection must be injective");
    let mut acts = vec![operation];
    if case["root"].as_bool().unwrap() { acts.push(root); }
    if case["opener"].as_bool().unwrap() { acts.push(opener); }
    case["addresses"] = json!(acts.iter().map(|act| json!([ids[&act.address],act.address])).collect::<Vec<_>>());
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
                let mut case = json!({"profile":"resource-decrement","owner":owner,"amount":amount,"root":root,"opener":opener});
                assert_eq!(native(&dialect,&mut case),oracle.borrow_mut().request(&case),"resource case={case}");
            }
        }
    }
    for (key,invalid) in [("amount",json!("1")),("owner",json!("@unknown")),
        ("root",json!(1)),("opener",Value::Null)] {
        let mut case = json!({"profile":"resource-decrement","owner":"@treasury","amount":1,"root":true,"opener":true});
        case[key] = invalid;
        assert!(oracle.borrow_mut().response(&case).get("error").is_some(),"invalid resource transport={case}");
    }
    let mut dictionary_case = json!({"profile":"resource-decrement","owner":"@treasury","amount":0,"root":true,"opener":true});
    let dictionary_expected = native(&dialect,&mut dictionary_case);
    let original = dictionary_case["addresses"].as_array().unwrap().clone();
    let mut reversed = original.clone(); reversed.reverse();
    dictionary_case["addresses"] = json!(reversed);
    assert_eq!(oracle.borrow_mut().request(&dictionary_case),dictionary_expected,"dictionary row order is not identity order");
    for malformed in [json!([]),json!([original[0],original[0],original[2]]),
        json!([[1,"same"],[2,"same"],[3,"other"]]),json!([[1,"a"],[2,"b"],[99,"c"]]),
        json!([[1,"a"],[2,"b"],[3,"c"],[4,"d"]]),json!([["1","a"],[2,"b"],[3,"c"]])] {
        dictionary_case["addresses"] = malformed;
        assert!(oracle.borrow_mut().response(&dictionary_case).get("error").is_some(),"invalid resource address dictionary={dictionary_case}");
    }
    let mut config = proptest::test_runner::Config::default();
    if std::env::var_os("PROPTEST_CASES").is_none() { config.cases = 512; }
    let mut runner = proptest::test_runner::TestRunner::new(config);
    runner.run(&(0usize..4,prop_oneof![any::<i64>(),-2i64..1003],any::<bool>(),any::<bool>()), |(owner,amount,root,opener)| {
        let owner = ["@treasury","@alice","@bob","@outsider"][owner];
        let mut case = json!({"profile":"resource-decrement","owner":owner,"amount":amount,"root":root,"opener":opener});
        prop_assert_eq!(native(&dialect,&mut case),oracle.borrow_mut().request(&case),"resource case={}",case);
        Ok(())
    }).unwrap();
}

fn native_graph(dialect: &cbcl_core::dialect::Dialect, case: &mut Value) -> Value {
    let (root,opener) = initial();
    let funding = case["funding"].as_i64().unwrap();
    let context = case.get("context").map(|value| value.as_bool().unwrap()).unwrap_or(false);
    let cited_context = case.get("cited_context").map(|value| value.as_bool().unwrap()).unwrap_or(false);
    let note = Act::from_message(parse_message(&parse(&format!("(signed @treasury (tell :content \"context\" :thread \"coin-1\" :caused-by {}))",opener.address)).unwrap()).unwrap(),"@treasury").unwrap();
    let payment_causes = if cited_context { format!("({} {})",opener.address,note.address) } else { opener.address.clone() };
    let spend = case["spend"].as_i64().unwrap();
    let payment = Act::from_message(parse_message(&parse(&format!("(signed @treasury (lang example-coin (pay (@alice @bob @treasury) :recipient @alice :amount {funding} :from @treasury :thread \"coin-1\" :caused-by {payment_causes} :escrow-prev {} :escrow-deps ())))",opener.address)).unwrap()).unwrap(),"@treasury").unwrap();
    let dependency = case["dependency"].as_bool().unwrap();
    let deps = if dependency { payment.address.clone() } else { String::new() };
    let causes = if dependency { format!("({} {})",opener.address,payment.address) } else { opener.address.clone() };
    let spent = Act::from_message(parse_message(&parse(&format!("(signed @alice (lang example-coin (burn (@alice @bob @treasury) :amount {spend} :from @alice :thread \"coin-1\" :caused-by {causes} :escrow-prev {} :escrow-deps ({deps}))))",opener.address)).unwrap()).unwrap(),"@alice").unwrap();
    let competing = Act::from_message(parse_message(&parse(&format!("(signed @alice (lang example-coin (burn (@alice @bob @treasury) :amount 1 :from @alice :thread \"coin-1\" :caused-by {causes} :escrow-prev {} :escrow-deps ({deps}) :escrow-nonce \"fork\")))",opener.address)).unwrap()).unwrap(),"@alice").unwrap();
    let ids = BTreeMap::from([(root.address.clone(),1),(opener.address.clone(),2),(spent.address.clone(),3),(payment.address.clone(),4),(competing.address.clone(),5),(note.address.clone(),6)]);
    assert_eq!(ids.len(),6,"fixture address projection must be injective");
    let mut acts = vec![root,opener,spent];
    if case["included"].as_bool().unwrap() { acts.push(payment); }
    if case["fork"].as_bool().unwrap() { acts.push(competing); }
    if context { acts.push(note); }
    case["addresses"] = json!(acts.iter().map(|act| json!([ids[&act.address],act.address])).collect::<Vec<_>>());
    let result = observed(dialect,&acts,&ids);
    acts.reverse(); acts.extend(acts.clone());
    assert_eq!(observed(dialect,&acts,&ids),result,"resource graph reorder/duplicate case={case}");
    result
}

fn compare_graph_growth(oracle: &RefCell<Oracle>, dialect: &cbcl_core::dialect::Dialect, case: &mut Value) {
    let earlier = native_graph(dialect,case);
    assert_eq!(earlier,oracle.borrow_mut().request(case),"resource graph={case}");
    let mut grown = case.clone();
    grown["included"] = json!(true);
    grown["fork"] = json!(true);
    let later = native_graph(dialect,&mut grown);
    for earlier_source in case["addresses"].as_array().unwrap() {
        assert!(grown["addresses"].as_array().unwrap().contains(earlier_source),"growth changed an earlier source identity; before={case}; after={grown}");
    }
    assert_eq!(later,oracle.borrow_mut().request(&grown),"grown resource graph={grown}");
    if earlier["status"] == "fault" {
        assert_eq!(later["status"],"fault","resource fault disappeared; before={case}; after={grown}");
        for witness in earlier["evidence"].as_array().unwrap() {
            assert!(later["evidence"].as_array().unwrap().contains(witness),
                "resource fault witness disappeared; witness={witness}; before={case}; after={grown}");
        }
    }
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
            let mut case = json!({"profile":"resource-graph","funding":funding,"spend":spend,"included":included,"dependency":dependency,"fork":fork});
            compare_graph_growth(&oracle,&dialect,&mut case);
        } } }
    }
    let mut config = proptest::test_runner::Config::default();
    if std::env::var_os("PROPTEST_CASES").is_none() { config.cases = 512; }
    let mut runner = proptest::test_runner::TestRunner::new(config);
    let amount = prop_oneof![any::<i64>(),-2i64..1003];
    runner.run(&(amount.clone(),amount,any::<bool>(),any::<bool>(),any::<bool>()), |(funding,spend,included,dependency,fork)| {
        let mut case = json!({"profile":"resource-graph","funding":funding,"spend":spend,"included":included,"dependency":dependency,"fork":fork});
        compare_graph_growth(&oracle,&dialect,&mut case);
        Ok(())
    }).unwrap();
}

#[test]
#[ignore = "requires lake build cbcl-state-oracle; explicitly run in Lean CI"]
fn cited_context_evidence_matches_lean() {
    let dialect = cbcl_parser::parse_dialect(&parse(include_str!("../../../../dialects/example-coin.cbcl")).unwrap()).unwrap();
    let mut registry = cbcl_core::dialect::DialectRegistry::new();
    registry.install(dialect.clone()).unwrap();
    let oracle = RefCell::new(Oracle::start());
    for context in [false,true] { for cited_context in [false,true] {
        let mut case = json!({"profile":"resource-graph","funding":5,"spend":6,"included":true,"dependency":true,"fork":false,"context":context,"cited_context":cited_context});
        let observed = native_graph(&dialect,&mut case);
        assert_eq!(observed,oracle.borrow_mut().request(&case),"resource cited context={case}");
        assert_eq!(observed["status"],"fault");
        assert_eq!(observed["evidence"].as_array().unwrap().contains(&json!(6)),context && cited_context,
            "only accepted cited context belongs in the witness; case={case}");
        compare_graph_growth(&oracle,&dialect,&mut case);
    } }
    for key in ["context","cited_context"] {
        let mut case = json!({"profile":"resource-graph","funding":5,"spend":6,"included":true,"dependency":true,"fork":false});
        let _ = native_graph(&dialect,&mut case);
        case[key] = json!("true");
        assert!(oracle.borrow_mut().response(&case).get("error").is_some());
    }
    let mut config = proptest::test_runner::Config::default();
    if std::env::var_os("PROPTEST_CASES").is_none() { config.cases = 512; }
    let mut runner = proptest::test_runner::TestRunner::new(config);
    runner.run(&(-2i64..1003,-2i64..1003,any::<bool>(),any::<bool>(),any::<bool>(),any::<bool>(),any::<bool>()),
        |(funding,spend,included,dependency,fork,context,cited_context)| {
        let mut case = json!({"profile":"resource-graph","funding":funding,"spend":spend,"included":included,"dependency":dependency,"fork":fork,"context":context,"cited_context":cited_context});
        compare_graph_growth(&oracle,&dialect,&mut case);
        Ok(())
    }).unwrap();
}

#[test]
#[ignore = "requires lake build cbcl-state-oracle; explicitly run in Lean CI"]
fn resource_freeze_matches_lean() {
    use cbcl_core::state::{Entry, FreezePolicy};
    let oracle = RefCell::new(Oracle::start());
    for fault_policy in [false,true] {
        let mut dialect = cbcl_parser::parse_dialect(&parse(include_str!("../../../../dialects/example-coin.cbcl")).unwrap()).unwrap();
        dialect.state.as_mut().unwrap().entries.push(Entry::Freeze {
            field:"coins".into(),verb:"pay".into(),
            policy:if fault_policy { FreezePolicy::Fault } else { FreezePolicy::Supersede },
        });
        let mut registry = cbcl_core::dialect::DialectRegistry::new();
        registry.install(dialect.clone()).unwrap();
        for (funding,spend,included,dependency,fork) in [
            (5,1,true,true,false),(5,5,true,true,false),(5,6,true,true,false),
            (5,1,true,false,false),(5,1,false,true,false),(5,1,true,true,true),
            (0,1,true,true,false),(1001,1,true,true,false),
        ] {
            let mut case = json!({"profile":"resource-freeze","funding":funding,"spend":spend,"included":included,"dependency":dependency,"fork":fork,"fault_policy":fault_policy});
            let observed = native_graph(&dialect,&mut case);
            assert_eq!(observed,oracle.borrow_mut().request(&case),"resource freeze={case}");
            if funding == 5 && spend == 1 && included && dependency && !fork {
                if fault_policy {
                    assert_eq!(observed["status"],"fault");
                    assert_eq!(observed["evidence"],json!([3,4]));
                } else {
                    assert_eq!(observed["status"],"frozen");
                    let wrapper: Value = serde_json::from_str(observed["rendered"].as_str().unwrap()).unwrap();
                    assert_eq!(wrapper["value"]["value"],1000);
                    assert_eq!(wrapper["value"]["rights"]["@alice"],5);
                    assert_eq!(wrapper["superseded"].as_array().unwrap().len(),1);
                }
            }
            if funding == 5 && spend == 6 { assert_eq!(observed["status"],"fault"); }
            compare_graph_growth(&oracle,&dialect,&mut case);
        }
        for invalid in [json!("true"),Value::Null,json!(1)] {
            let mut case = json!({"profile":"resource-freeze","funding":5,"spend":1,"included":true,"dependency":true,"fork":false,"fault_policy":fault_policy});
            let _ = native_graph(&dialect,&mut case);
            case["fault_policy"] = invalid;
            assert!(oracle.borrow_mut().response(&case).get("error").is_some(),"invalid freeze policy transport={case}");
        }
        let mut config = proptest::test_runner::Config::default();
        if std::env::var_os("PROPTEST_CASES").is_none() { config.cases = 512; }
        let mut runner = proptest::test_runner::TestRunner::new(config);
        runner.run(&(-2i64..1003,-2i64..1003,any::<bool>(),any::<bool>(),any::<bool>(),any::<bool>(),any::<bool>()),
            |(funding,spend,included,dependency,fork,context,cited_context)| {
            let mut case = json!({"profile":"resource-freeze","funding":funding,"spend":spend,"included":included,"dependency":dependency,"fork":fork,"context":context,"cited_context":cited_context,"fault_policy":fault_policy});
            compare_graph_growth(&oracle,&dialect,&mut case);
            Ok(())
        }).unwrap();
    }
}
