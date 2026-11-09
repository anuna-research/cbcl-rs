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

// State-shape receipt plus native field extraction, deliberately distinct from
// the first-keyword ShapeConstraint projection campaign above.
fn native_keywords(case: &Value) -> Value {
    let source = "(define keyword-demo (cbcl) @a (extend open (to) (tell to)) \
        (extend mint (to amount) (tell to :amount amount)) \
        (shape mint (require :amount nonnegative) (optional :other)) \
        (protocol (then begin open) (then open mint)) (state (credits (events mint :amount))))";
    let registry = state_exports::parse_and_install_dialect(&parse(source).unwrap()).unwrap();
    let dialect = registry.iter().last().unwrap();
    let SExpr::List(params) = tree(&case["params"]) else { panic!("params must be a list"); };
    let wire = format!("(lang keyword-demo (mint () {}))", params.iter().map(ToString::to_string).collect::<Vec<_>>().join(" "));
    let raw = parse(&wire).unwrap();
    let Ok(message) = parse_message(&raw) else { return json!({"accepted":false}); };
    if cbcl_core::r7::verify_state_shape(dialect, &message).is_err() { return json!({"accepted":false}); }
    let act = Act::from_message(message, "@a").unwrap();
    if dialect.shapes.iter().any(|shape| shape.performative == "mint" && shape.check(&SExpr::from(act.simple())).is_err()) {
        return json!({"accepted":false});
    }
    let amount = match act.fields.get("amount") { Some(SExpr::Atom(Atom::Num(n))) => *n, _ => 0 };
    json!({"accepted":true,"amount":amount})
}

#[test]
#[ignore = "requires lake build cbcl-state-oracle; explicitly run in Lean CI"]
fn keyword_extraction_matches_lean() {
    let oracle = RefCell::new(Oracle::start());
    for params in [
        json!(["list", [["keyword","amount"],["num",5]]]),
        json!(["list", [["keyword","amount"],["num",10],["keyword","amount"],["num",-1]]]),
        json!(["list", [["keyword","amount"],["num",1],["keyword","amount"],["num",1]]]),
        json!(["list", [["keyword","thread"],["str","a"],["keyword","amount"],["num",5],["keyword","thread"],["str","b"]]]),
        json!(["list", [["keyword","other"],["keyword","amount"],["keyword","amount"],["num",5]]]),
        json!(["list", [["num",5],["keyword","amount"],["num",5]]]),
        json!(["list", [["keyword","amount"]]]),
        json!(["list", [["keyword","amount"],["num",1000000000001i64]]]),
    ] {
        let case = json!({"profile":"keyword-extraction","params":params});
        assert_eq!(native_keywords(&case), oracle.borrow_mut().request(&case), "keyword case={case}");
    }
    let value = prop_oneof![(-20i64..20).prop_map(|n| json!(["num",n])),
        any::<bool>().prop_map(|b| json!(["bool",b])), Just(json!(["str","5"])),
        Just(json!(["symbol","word"])), Just(json!(["keyword","amount"])),
        Just(json!(["list",[["num",5]]]))];
    let row = prop_oneof![(prop_oneof![Just("amount"),Just("other")], value)
        .prop_map(|(key,value)| vec![json!(["keyword",key]),value]),
        prop_oneof![Just("a"),Just("b")].prop_map(|thread| vec![json!(["keyword","thread"]),json!(["str",thread])])];
    let mut config = proptest::test_runner::Config::default();
    if std::env::var_os("PROPTEST_CASES").is_none() { config.cases = 512; }
    let mut runner = proptest::test_runner::TestRunner::new(config);
    runner.run(&prop::collection::vec(row, 0..9), |rows| {
        let params = rows.into_iter().flatten().collect::<Vec<_>>();
        let case = json!({"profile":"keyword-extraction","params":["list",params]});
        prop_assert_eq!(native_keywords(&case), oracle.borrow_mut().request(&case), "keyword case={}",case);
        Ok(())
    }).unwrap();
}
