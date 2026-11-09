//! TEST-3815: authored nested conditions against independently executed Lean finite sources.
use super::*;
use cbcl_core::sexpr::{Atom, SExpr};

fn element(value: &Value) -> String {
    if let Some(count) = value.get("count") {
        return format!("(count {count})");
    }
    if let Some(member) = value.get("member") {
        return format!("(member {})", wire(member));
    }
    wire(value)
}
fn expression(node: &Value) -> String {
    let parts = node.as_array().unwrap();
    if parts[0] == "read" {
        format!(
            "(read {} {})",
            parts[1].as_str().unwrap(),
            element(&parts[2])
        )
    } else {
        format!(
            "(and {})",
            parts[1..]
                .iter()
                .map(expression)
                .collect::<Vec<_>>()
                .join(" ")
        )
    }
}
fn native_condition(case: &Value) -> Value {
    let mut source = case.clone();
    source["queries"] = Value::Null;
    // Include permitted close/seal verbs even when neither source freezes.
    source["freeze"] = json!(true);
    let text = dialect(&source)
        .replace(
            "(shape mark",
            "(extend seal (to) :from owner :to owner (tell to)) (shape mark",
        )
        .replace("(repeat 16 mark close)", "(repeat 16 mark close seal)");
    let SExpr::List(mut definition) = parse(&text).unwrap() else {
        unreachable!()
    };
    let state = definition
        .iter_mut()
        .find_map(|entry| match entry {
            SExpr::List(parts) if parts.first().is_some_and(|p| p.is_symbol("state")) => {
                Some(parts)
            }
            _ => None,
        })
        .unwrap();
    state.retain(|entry| !matches!(entry, SExpr::List(parts) if parts.first().is_some_and(|p| p.is_symbol("freeze"))));
    let mut second = state.iter().find(|entry| matches!(entry, SExpr::List(parts) if parts.first().is_some_and(|p| p.is_symbol("value")))).unwrap().clone();
    if let SExpr::List(parts) = &mut second {
        parts[0] = SExpr::Atom(Atom::Symbol("second".into()));
    }
    state.push(second);
    for field in [
        "(votes (count mark))",
        "(seen (exists mark))",
        "(members (set-union mark :phase))",
    ] {
        state.push(parse(field).unwrap());
    }
    state.push(
        parse(&format!(
            "(threshold ready {})",
            expression(&case["condition"])
        ))
        .unwrap(),
    );
    for (field, verb, policy) in [
        ("value", "close", &case["freeze"]),
        ("second", "seal", &case["second-freeze"]),
    ] {
        if let Some(fault) = policy.as_bool() {
            state.push(
                parse(&format!(
                    "(freeze {field} {verb} {})",
                    if fault { "fault" } else { "supersede" }
                ))
                .unwrap(),
            );
        }
    }
    let Ok(registry) = state_exports::parse_and_install_dialect(&SExpr::List(definition)) else {
        return json!({"installed":false});
    };
    let d = registry.iter().last().unwrap();
    let (ids, acts) = graph_acts(case);
    let result: Value = serde_json::from_str(&render_json(&fold(
        d.state.as_ref().unwrap(),
        d.causal_protocol.as_ref(),
        &acts,
    )))
    .unwrap();
    let condition = if result["ready"]["status"] == "fault" {
        normalize_fault(&result["ready"], &ids)
    } else {
        result["ready"].clone()
    };
    let schema: Value = serde_json::from_str(&cbcl_core::state::render_schema(
        &cbcl_core::state::state_schema(d.state.as_ref().unwrap(), &d.shapes),
    ))
    .unwrap();
    json!({"installed":true,"condition":condition,"schema":schema["ready"]})
}
fn request(case: &Case, condition: Value, first: Value, second: Value, acts: Value) -> Value {
    let mut result = case.request();
    result["profile"] = json!("authored-condition");
    result["condition"] = condition;
    result["freeze"] = first;
    result["second-freeze"] = second;
    result["acts"] = acts;
    result
}
fn condition_strategy() -> impl Strategy<Value = Value> {
    prop_oneof![
        (
            prop_oneof![Just("value"), Just("second"), Just("missing")],
            0usize..4
        )
            .prop_map(|(field, q)| json!(["read", field, format!("e{q}")])),
        Just(json!(["read", "value", true])),
        (0u64..8).prop_map(|n| json!(["read","votes",{"count":n}])),
        Just(json!(["read", "seen", true])),
        (0u8..3).prop_map(|n| json!(["read","members",{"member":format!("p{n}")}])),
    ]
    .prop_recursive(3, 20, 4, |inner| {
        proptest::collection::vec(inner, 0..5).prop_map(|children| {
            let mut node = vec![json!("and")];
            node.extend(children);
            json!(node)
        })
    })
}
#[test]
#[ignore = "requires the live Lean oracle executable"]
fn authored_conditions_match_live_lean_oracle() {
    let oracle = RefCell::new(Oracle::start());
    let mut base = directed_cases()[0].clone();
    base.n = 4;
    base.fan = true;
    base.mutation = None;
    base.table_edit = 0;
    base.projection = 0;
    base.rows = vec![(0, 0, 1), (0, 1, 2)];
    let history = json!([
        [0, "open", [], []],
        [
            1,
            "mark",
            [0],
            [["phase", "p0"], ["amount", 1], ["flag", true]]
        ],
        [2, "close", [1], []],
        [
            3,
            "mark",
            [0],
            [["phase", "p1"], ["amount", 1], ["flag", true]]
        ],
        [4, "seal", [3], []]
    ]);
    let conditions = [
        json!(["and",["read","votes",{"count":2}],["read","seen",true],["read","members",{"member":"p0"}],["read","value","e1"]]),
        json!(["read", "value", "e1"]),
        json!(["and", ["read", "value", "e1"], ["read", "second", "e2"]]),
        json!([
            "and",
            ["read", "value", "e0"],
            ["and", ["read", "second", "e1"], ["read", "value", "e2"]]
        ]),
        json!(["and", ["read", "value", "e1"]]),
        json!(["read", "missing", "e1"]),
        json!(["read", "value", true]),
    ];
    for condition in conditions {
        for first in [Value::Null, json!(true), json!(false)] {
            for second in [Value::Null, json!(true), json!(false)] {
                let case = request(
                    &base,
                    condition.clone(),
                    first.clone(),
                    second,
                    history.clone(),
                );
                assert_eq!(
                    native_condition(&case),
                    oracle.borrow_mut().request(&case),
                    "request={}",
                    case
                );
            }
        }
    }
    let success = json!(["and",["read","votes",{"count":1}],["read","seen",true],["read","members",{"member":"p0"}],["read","value","e1"]]);
    let successful_history = json!([
        [0, "open", [], []],
        [
            1,
            "mark",
            [0],
            [["phase", "p0"], ["amount", 1], ["flag", true]]
        ]
    ]);
    let success_case = request(
        &base,
        success,
        Value::Null,
        Value::Null,
        successful_history.clone(),
    );
    let expected = oracle.borrow_mut().request(&success_case);
    assert_eq!(
        expected["condition"],
        json!({"status":"reached","element":true})
    );
    assert_eq!(native_condition(&success_case), expected);
    let mut pending = success_case.clone();
    pending["acts"] = json!([[0, "open", [], []]]);
    let expected = oracle.borrow_mut().request(&pending);
    assert_eq!(expected["condition"], json!({"status":"pending"}));
    assert_eq!(native_condition(&pending), expected);
    // The valid table has four elements, so max-list=4 admits the table while
    // distinguishing a three-node condition from a five-node condition.
    for (condition, installed) in [
        (
            json!(["and", ["read", "value", "e1"], ["read", "seen", true]]),
            true,
        ),
        (
            json!([
                "and",
                ["read", "value", "e1"],
                ["read", "seen", true],
                ["read", "seen", true],
                ["read", "seen", true]
            ]),
            false,
        ),
    ] {
        let mut bounded = request(
            &base,
            condition,
            Value::Null,
            Value::Null,
            successful_history.clone(),
        );
        bounded["max-list"] = json!(4);
        let expected = oracle.borrow_mut().request(&bounded);
        assert_eq!(expected["installed"], installed);
        assert_eq!(
            native_condition(&bounded),
            expected,
            "bounded request={bounded}"
        );
    }
    let mut config = proptest::test_runner::Config::default();
    if std::env::var_os("PROPTEST_CASES").is_none() {
        config.cases = 512;
    }
    let mut runner = proptest::test_runner::TestRunner::new(config);
    runner
        .run(
            &(
                cases(),
                condition_strategy(),
                prop::option::of(any::<bool>()),
                prop::option::of(any::<bool>()),
                any::<bool>(),
            ),
            |(finite, condition, first, second, reverse)| {
                let mut acts = vec![json!([0, "open", [], []])];
                for (i, (phase, amount, flag)) in finite.history.iter().enumerate() {
                    acts.push(json!([
                        i + 1,
                        "mark",
                        [0],
                        [
                            ["phase", format!("p{}", phase % 3)],
                            ["amount", amount],
                            ["flag", flag]
                        ]
                    ]));
                }
                let last = acts.len();
                acts.push(json!([last, "close", [0], []]));
                acts.push(json!([last + 1, "seal", [last], []]));
                if reverse {
                    acts.reverse();
                }
                let case = request(&finite, condition, json!(first), json!(second), json!(acts));
                let expected = oracle.borrow_mut().request(&case);
                prop_assert_eq!(
                    native_condition(&case),
                    expected.clone(),
                    "request={}",
                    case
                );
                let mut duplicate = case.clone();
                let extra = duplicate["acts"].as_array().unwrap().clone();
                duplicate["acts"].as_array_mut().unwrap().extend(extra);
                prop_assert_eq!(
                    native_condition(&duplicate),
                    expected.clone(),
                    "duplicate request={}",
                    duplicate
                );
                prop_assert_eq!(
                    oracle.borrow_mut().request(&duplicate),
                    expected,
                    "duplicate request={}",
                    duplicate
                );
                Ok(())
            },
        )
        .unwrap();
}
