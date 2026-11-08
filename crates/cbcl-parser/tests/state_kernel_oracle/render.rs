//! Exact UTF-8 serialization comparison, preserving stored container/clause order.
use super::*;
use cbcl_core::state::Value as Native;

fn value(tag: &Value) -> Native {
    match tag[0].as_str().unwrap() {
        "absent" => Native::Absent,
        "str" => Native::Str(tag[1].as_str().unwrap().into()),
        "int" => Native::Int(tag[1].as_str().unwrap().parse().unwrap()),
        "bool" => Native::Bool(tag[1].as_bool().unwrap()),
        "list" => Native::List(tag[1].as_array().unwrap().iter().map(value).collect()),
        "set" => Native::Set(tag[1].as_array().unwrap().iter().map(value).collect()),
        "map" => Native::Map(tag[1].as_array().unwrap().iter().map(|row| (value(&row[0]),value(&row[1]))).collect()),
        "event" => Native::Pair { by: tag[1].as_str().unwrap().into(), value: Box::new(value(&tag[2])) },
        _ => panic!("invalid test value"),
    }
}
fn native(case: &Value) -> Value {
    let fields = case["state"].as_array().unwrap().iter()
        .map(|row| (row[0].as_str().unwrap().to_owned(),value(&row[1]))).collect::<Vec<_>>();
    json!({"rendered":value(&case["value"]).render(),"state":render_json(&fields)})
}
fn text() -> BoxedStrategy<String> {
    prop_oneof![
        prop::collection::vec(any::<char>(),0..24).prop_map(|chars| chars.into_iter().collect()),
        prop::collection::vec(0u8..32,0..24).prop_map(|chars| chars.into_iter().map(char::from).collect()),
        Just("quote\"slash\\\n\r\t\u{8}\u{c}".to_owned()),
    ].boxed()
}
fn tree() -> BoxedStrategy<Value> {
    let leaf = prop_oneof![
        Just(json!(["absent"])), text().prop_map(|s| json!(["str",s])),
        any::<i128>().prop_map(|n| json!(["int",n.to_string()])),
        any::<bool>().prop_map(|b| json!(["bool",b])),
    ];
    leaf.prop_recursive(4,96,8,|inner| prop_oneof![
        prop::collection::vec(inner.clone(),0..6).prop_map(|values| json!(["list",values])),
        prop::collection::vec(inner.clone(),0..6).prop_map(|values| json!(["set",values])),
        prop::collection::vec((inner.clone(),inner.clone()),0..6).prop_map(|rows| json!(["map",rows])),
        (text(),inner).prop_map(|(by,value)| json!(["event",by,value])),
    ]).boxed()
}
#[test]
#[ignore = "requires lake build cbcl-state-oracle; explicitly run in Lean CI"]
fn native_json_bytes_match_lean() {
    let oracle = RefCell::new(Oracle::start());
    let controls = (0u8..32).map(char::from).collect::<String>();
    for value in [
        json!(["absent"]), json!(["str",controls]), json!(["str","é𝄞🌍é"]),
        json!(["int",i128::MIN.to_string()]),json!(["int",i128::MAX.to_string()]),
        json!(["set",[["int","2"],["int","1"],["int","1"]]]),
        json!(["map",[[["int","2"],["str","x"]],[["str","quoted\"key"],["absent"]]]]),
        json!(["event","@a",["list",[["int","2"],["bool",true]]]]),
        json!(["map",[[["list",[["str","key"]]],["map",[]]]]]),
    ] {
        let case = json!({"profile":"state-render","value":value,"state":[["z",value],["a",["bool",true]]]});
        assert_eq!(native(&case),oracle.borrow_mut().request(&case),"render case={case}");
    }
    for invalid in [json!(["int","170141183460469231731687303715884105728"]),
        json!(["int","-170141183460469231731687303715884105729"]),json!(["int","01"]),
        json!(["int","-0"]),json!(["unknown"]),json!(["bool",true,"extra"])] {
        let case = json!({"profile":"state-render","value":invalid,"state":[]});
        assert!(oracle.borrow_mut().response(&case).get("error").is_some(),"invalid renderer transport={case}");
    }
    let mut deep = json!(["absent"]);
    for _ in 0..33 { deep = json!(["list",[deep]]); }
    assert!(oracle.borrow_mut().response(&json!({"profile":"state-render","value":deep,"state":[]})).get("error").is_some());
    let mut config = proptest::test_runner::Config::default();
    if std::env::var_os("PROPTEST_CASES").is_none() { config.cases = 512; }
    config.failure_persistence = Some(Box::new(proptest::test_runner::FileFailurePersistence::Direct(
        concat!(env!("CARGO_MANIFEST_DIR"),"/tests/state_json_render.proptest-regressions"))));
    let mut runner = proptest::test_runner::TestRunner::new(config);
    runner.run(&(tree(),prop::collection::vec((text(),tree()),0..6)), |(value,fields)| {
        let case = json!({"profile":"state-render","value":value,"state":fields});
        let actual = native(&case);
        prop_assert_eq!(&actual,&oracle.borrow_mut().request(&case),"render case={}",case);
        prop_assert!(serde_json::from_str::<Value>(actual["rendered"].as_str().unwrap()).is_ok());
        prop_assert!(serde_json::from_str::<Value>(actual["state"].as_str().unwrap()).is_ok());
        Ok(())
    }).unwrap();
}

// Address aliases deliberately exercise arbitrary UTF-8 ordering below admission;
// this profile makes no claim about content-hash identity or root-cast binding.
fn native_fault(case: &Value) -> Value {
    let result = std::panic::catch_unwind(|| native_fault_unchecked(case));
    assert!(result.is_ok(), "native fault fold panicked; case={case}");
    result.unwrap()
}
fn native_fault_unchecked(case: &Value) -> Value {
    use cbcl_core::state::{Entry, FreezePolicy, Rule, StateClause};
    let clause = StateClause { entries: vec![
        Entry::Field { name: "observed".into(), rule: Rule::Count { verb: "tick".into() } },
        Entry::Freeze { field: "observed".into(), verb: "close".into(), policy: FreezePolicy::Fault },
    ] };
    let mut acts = Vec::new();
    for (key,verb) in [("freezers","close"),("writers","tick")] {
        for address in case[key].as_array().unwrap() {
            let mut act = make_act(&format!("(lang fault-demo ({verb}))"));
            act.address = address.as_str().unwrap().into();
            acts.push(act);
        }
    }
    json!({"rendered":fold(&clause,None,&acts)[0].1.render()})
}

#[test]
#[ignore = "requires lake build cbcl-state-oracle; explicitly run in Lean CI"]
fn fault_evidence_bytes_match_lean() {
    let oracle = RefCell::new(Oracle::start());
    for (freezers,writers) in [
        (vec!["z","a"],vec!["m"]), (vec!["\0",""],vec!["w"]),
        (vec!["a\0","a","aa"],vec!["b"]), (vec!["[","\""],vec!["β","\n"]),
        (vec!["😀","é","a","a"],vec!["β","β"]),
    ] {
        let case = json!({"profile":"fault-evidence","freezers":freezers,"writers":writers});
        assert_eq!(native_fault(&case),oracle.borrow_mut().request(&case),"fault case={case}");
    }
    for case in [json!({"freezers":[],"writers":[]}),json!({"freezers":["a","a"],"writers":[]}),
        json!({"freezers":["a","b"],"writers":["a"]})] {
        let mut case = case;
        case["profile"] = json!("fault-evidence");
        assert!(oracle.borrow_mut().response(&case).get("error").is_some());
    }
    let mut config = proptest::test_runner::Config::default();
    if std::env::var_os("PROPTEST_CASES").is_none() { config.cases = 512; }
    config.failure_persistence = Some(Box::new(proptest::test_runner::FileFailurePersistence::Direct(
        concat!(env!("CARGO_MANIFEST_DIR"),"/tests/state_fault_evidence.proptest-regressions"))));
    let mut runner = proptest::test_runner::TestRunner::new(config);
    runner.run(&(prop::collection::vec(text(),0..12),prop::collection::vec(text(),0..12)), |(fs,ws)| {
        let mut freezers = vec!["f:0".to_owned(),"f:1".to_owned()];
        freezers.extend(fs.into_iter().map(|s|format!("f:{s}")));
        let mut writers = vec!["w:0".to_owned()];
        writers.extend(ws.into_iter().map(|s|format!("w:{s}")));
        let case = json!({"profile":"fault-evidence","freezers":freezers,"writers":writers});
        let expected = oracle.borrow_mut().request(&case);
        prop_assert_eq!(native_fault(&case),expected.clone(),"fault case={}",case);
        freezers.reverse(); writers.reverse();
        freezers.extend(freezers.clone()); writers.extend(writers.clone());
        let repeated = json!({"profile":"fault-evidence","freezers":freezers,"writers":writers});
        prop_assert_eq!(native_fault(&repeated),expected.clone());
        prop_assert_eq!(oracle.borrow_mut().request(&repeated),expected);
        Ok(())
    }).unwrap();
}

fn native_frozen(case: &Value) -> Value {
    use cbcl_core::state::{Entry, FreezePolicy, Rule, StateClause};
    let clause = StateClause { entries: vec![
        Entry::Field { name: "observed".into(), rule: Rule::Count { verb: "tick".into() } },
        Entry::Freeze { field: "observed".into(), verb: "close".into(), policy: FreezePolicy::Supersede },
    ] };
    let mut acts = Vec::new();
    for group in ["before","after"] {
        for name in case[group].as_array().unwrap() {
            let mut act = make_act("(lang frozen-demo (tick))");
            act.address = name.as_str().unwrap().into();
            if group == "after" && case["descendants"].as_bool().unwrap() {
                act.predecessors = vec![case["freezer"].as_str().unwrap().into()];
            }
            acts.push(act);
        }
    }
    let mut root = make_act("(lang frozen-demo (close))");
    root.address = case["freezer"].as_str().unwrap().into();
    root.predecessors = case["before"].as_array().unwrap().iter()
        .map(|name| name.as_str().unwrap().to_owned()).collect();
    root.predecessors.sort();
    root.predecessors.dedup();
    acts.push(root);
    json!({"rendered":fold(&clause,None,&acts)[0].1.render()})
}

#[test]
#[ignore = "requires lake build cbcl-state-oracle; explicitly run in Lean CI"]
fn frozen_wrapper_bytes_match_lean() {
    let oracle = RefCell::new(Oracle::start());
    for (freezer,before,after) in [
        ("root",vec![],vec![]), ("",vec!["z"],vec!["a","a\0","aa"]),
        ("β",vec!["😀","é"],vec!["[","\"","\0"]),
        ("z",vec!["a","a"],vec!["m","b","m"]),
    ] {
        for descendants in [false,true] {
            let case = json!({"profile":"frozen-wrapper","descendants":descendants,"freezer":freezer,"before":before,"after":after});
            assert_eq!(native_frozen(&case),oracle.borrow_mut().request(&case),"frozen case={case}");
        }
    }
    for case in [json!({"freezer":"r","before":["r"],"after":[]}),
        json!({"freezer":"r","before":[],"after":["r"]}),
        json!({"freezer":"r","before":["a"],"after":["a"]})] {
        let mut case = case;
        case["profile"] = json!("frozen-wrapper");
        case["descendants"] = json!(false);
        assert!(oracle.borrow_mut().response(&case).get("error").is_some());
    }
    for invalid in [json!("true"),json!(0),Value::Null] {
        let case = json!({"profile":"frozen-wrapper","descendants":invalid,"freezer":"r","before":[],"after":[]});
        assert!(oracle.borrow_mut().response(&case).get("error").is_some());
    }
    let mut config = proptest::test_runner::Config::default();
    if std::env::var_os("PROPTEST_CASES").is_none() { config.cases = 512; }
    let mut runner = proptest::test_runner::TestRunner::new(config);
    runner.run(&(text(),prop::collection::vec(text(),0..12),prop::collection::vec(text(),0..12),any::<bool>()), |(root,bs,as_,descendants)| {
        let freezer = format!("root:{root}");
        let mut before = bs.into_iter().map(|name|format!("before:{name}")).collect::<Vec<_>>();
        let mut after = as_.into_iter().map(|name|format!("after:{name}")).collect::<Vec<_>>();
        let case = json!({"profile":"frozen-wrapper","descendants":descendants,"freezer":freezer,"before":before,"after":after});
        let expected = oracle.borrow_mut().request(&case);
        prop_assert_eq!(native_frozen(&case),expected.clone(),"frozen case={}",case);
        before.reverse(); after.reverse();
        before.extend(before.clone()); after.extend(after.clone());
        let repeated = json!({"profile":"frozen-wrapper","descendants":descendants,"freezer":freezer,"before":before,"after":after});
        prop_assert_eq!(native_frozen(&repeated),expected.clone());
        prop_assert_eq!(oracle.borrow_mut().request(&repeated),expected);
        Ok(())
    }).unwrap();
}
