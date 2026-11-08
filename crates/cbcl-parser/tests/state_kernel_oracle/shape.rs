//! TEST-3809: compare the Lean shape projection with native ShapeConstraint::check.
use super::*;
use cbcl_core::sexpr::{Atom, SExpr};
use cbcl_core::shape::{ShapeConstraint, ShapeRule, TypeConstraint};

fn tree(value: &Value) -> SExpr {
    match value[0].as_str().unwrap() {
        "num" => SExpr::Atom(Atom::Num(value[1].as_i64().unwrap())),
        "str" => SExpr::Atom(Atom::Str(value[1].as_str().unwrap().into())),
        "symbol" => SExpr::Atom(Atom::Symbol(value[1].as_str().unwrap().into())),
        "keyword" => SExpr::Atom(Atom::Keyword(value[1].as_str().unwrap().into())),
        "bool" => SExpr::Atom(Atom::Bool(value[1].as_bool().unwrap())),
        "list" => SExpr::List(value[1].as_array().unwrap().iter().map(tree).collect()),
        _ => panic!("invalid test tree"),
    }
}
fn native(case: &Value) -> Value {
    let message = tree(&case["message"]);
    let checked = case["shapes"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|shape| shape["verb"] == case["verb"])
        .all(|shape| {
            let keyword = shape["field"].as_str().unwrap().to_owned();
            let type_constraint = shape["nonnegative"]
                .as_bool()
                .unwrap()
                .then_some(TypeConstraint::Nonnegative);
            let rule = if shape["required"].as_bool().unwrap() {
                ShapeRule::Require {
                    keyword,
                    type_constraint,
                    children: vec![],
                }
            } else {
                ShapeRule::Optional {
                    keyword,
                    type_constraint,
                    default: None,
                    children: vec![],
                }
            };
            ShapeConstraint {
                performative: shape["verb"].as_str().unwrap().into(),
                rules: vec![rule],
            }
            .check(&message)
            .is_ok()
        });
    json!({"checked":checked})
}
fn atom() -> BoxedStrategy<Value> {
    prop_oneof![
        (-100i64..100).prop_map(|n| json!(["num", n])),
        any::<bool>().prop_map(|b| json!(["bool", b])),
        Just(json!(["str", "5"])),
        Just(json!(["symbol", "5"])),
        Just(json!(["keyword", "amount"])),
        Just(json!(["keyword", "other"])),
        Just(json!(["list", [["keyword", "amount"], ["num", 99]]])),
    ]
    .boxed()
}
#[test]
#[ignore = "requires lake build cbcl-state-oracle; explicitly run in Lean CI"]
fn mandatory_nonnegative_shapes_match_lean() {
    let oracle = RefCell::new(Oracle::start());
    let shapes = json!([
        {"verb":"mint","field":"amount","required":true,"nonnegative":true},
        {"verb":"other","field":"other","required":true,"nonnegative":true}
    ]);
    for message in [
        json!(["list", []]),
        json!(["list", [["keyword", "amount"]]]),
        json!([
            "list",
            [
                ["keyword", "amount"],
                ["num", -1],
                ["keyword", "amount"],
                ["num", 5]
            ]
        ]),
        json!([
            "list",
            [
                ["keyword", "amount"],
                ["num", 0],
                ["keyword", "amount"],
                ["num", -1]
            ]
        ]),
        json!(["list", [["keyword", "amount"], ["str", "5"]]]),
        json!(["list", [["keyword", "amount"], ["symbol", "5"]]]),
        json!(["list", [["keyword", "amount"], ["list", [["num", 5]]]]]),
    ] {
        let case =
            json!({"profile":"nonnegative-shape","verb":"mint","shapes":shapes,"message":message});
        assert_eq!(native(&case), oracle.borrow_mut().request(&case), "{case}");
    }
    for message in [
        json!(["num", 5, "extra"]),
        json!(["unknown", 5]),
        json!(["bool", "true"]),
    ] {
        let case =
            json!({"profile":"nonnegative-shape","verb":"mint","shapes":shapes,"message":message});
        assert!(oracle.borrow_mut().response(&case)["error"].is_string());
    }
    let mut too_deep = json!(["num", 0]);
    for _ in 0..33 {
        too_deep = json!(["list", [too_deep]]);
    }
    let case =
        json!({"profile":"nonnegative-shape","verb":"mint","shapes":shapes,"message":too_deep});
    assert!(oracle.borrow_mut().response(&case)["error"]
        .as_str()
        .unwrap()
        .contains("depth 32"));
    let mut config = proptest::test_runner::Config::default();
    if std::env::var_os("PROPTEST_CASES").is_none() {
        config.cases = 512;
    }
    let mut runner = proptest::test_runner::TestRunner::new(config);
    runner.run(&(prop::collection::vec(atom(),0..16),any::<bool>(),any::<bool>(),any::<bool>()), |(items,required,numeric,other)| {
        let shapes = json!([
            {"verb":"mint","field":"amount","required":required,"nonnegative":numeric},
            {"verb":"mint","field":"other","required":other,"nonnegative":true},
            {"verb":"else","field":"amount","required":true,"nonnegative":true}
        ]);
        let case = json!({"profile":"nonnegative-shape","verb":"mint","shapes":shapes,"message":["list",items]});
        prop_assert_eq!(native(&case),oracle.borrow_mut().request(&case),"case={}",case);
        Ok(())
    }).unwrap();
}
