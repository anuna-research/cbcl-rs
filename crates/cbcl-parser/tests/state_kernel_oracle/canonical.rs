//! SPEC-042 TEST-4206/4207: actual Rust functions versus executable proved model.
//! No parser, receipt or Rust-supplied sorted order stands in for the function.
use super::*;
use cbcl_core::{
    canonical::{atom_to_octets, canonical_params, canonicalise_dialect},
    dialect::base_dialect,
    numeric::Float,
    sexpr::{Atom, SExpr},
    shape::{ShapeConstraint, ShapeRule, TypeConstraint},
};

fn token(value: &SExpr) -> Value {
    match value {
        SExpr::Atom(Atom::Keyword(k)) => json!(["keyword", k]),
        SExpr::Atom(atom) => json!(["atom", String::from_utf8(atom_to_octets(atom)).unwrap()]),
        SExpr::List(xs) => json!(["list", xs.iter().map(token).collect::<Vec<_>>()]),
    }
}

fn check_params(oracle: &mut Oracle, params: &[SExpr]) {
    let case = json!({"profile":"canonicalisation","operation":"params",
        "params":params.iter().map(token).collect::<Vec<_>>()});
    let out = canonical_params(params);
    assert_eq!(out.len(), params.len());
    assert_eq!(canonical_params(&out), out, "Rust fixed point: {params:?}");
    assert_eq!(
        oracle.request(&case),
        json!({"params":out.iter().map(token).collect::<Vec<_>>()}),
        "{case}"
    );
}

fn key() -> BoxedStrategy<String> {
    prop_oneof![
        Just(String::new()),
        Just("a".into()),
        Just("aa".into()),
        Just("a\0".into()),
        Just("a\n".into()),
        Just("é".into()),
        Just("β".into()),
        Just("😀".into()),
        "[a-z]{1,8}",
        prop::collection::vec(any::<char>(), 0..8).prop_map(|chars| chars.into_iter().collect()),
    ]
    .boxed()
}

fn value() -> BoxedStrategy<SExpr> {
    let leaf = prop_oneof![
        any::<i64>().prop_map(|n| SExpr::Atom(Atom::Num(n))),
        any::<bool>().prop_map(|b| SExpr::Atom(Atom::Bool(b))),
        key().prop_map(|s| SExpr::Atom(Atom::Str(s))),
        key().prop_map(|s| SExpr::Atom(Atom::Symbol(s))),
        key().prop_map(|s| SExpr::Atom(Atom::Keyword(s))),
        (-1000i32..1000)
            .prop_map(|n| SExpr::Atom(Atom::Float(Float::new(n as f64 / 8.0).unwrap()))),
        (-1000i32..1000)
            .prop_map(|n| SExpr::Atom(Atom::Decimal(format!("{n}.25").parse().unwrap()))),
    ];
    leaf.prop_recursive(3, 48, 5, |inner| {
        prop::collection::vec(inner, 0..5).prop_map(SExpr::List)
    })
    .boxed()
}

fn runner() -> proptest::test_runner::TestRunner {
    let mut config = proptest::test_runner::Config::default();
    if std::env::var_os("PROPTEST_CASES").is_none() {
        config.cases = 512;
    }
    proptest::test_runner::TestRunner::new(config)
}

#[test]
#[ignore = "requires live proved canonicalisation oracle; mandatory in Lean CI"]
fn parameter_function_matches_formal_model() {
    let oracle = RefCell::new(Oracle::start());
    // Enumerate every permutation and positional layout of three unique pairs.
    let permutations = [
        [0, 1, 2],
        [0, 2, 1],
        [1, 0, 2],
        [1, 2, 0],
        [2, 0, 1],
        [2, 1, 0],
    ];
    let keys = ["a", "aa", "é"];
    for slots in 0..16 {
        let mut fixed = None;
        for order in permutations {
            let mut params = Vec::new();
            for i in 0..4 {
                if slots & (1 << i) != 0 {
                    params.push(SExpr::List(vec![SExpr::Atom(Atom::Str(format!(
                        "pos-{i}"
                    )))]));
                }
                if i < 3 {
                    let k = order[i];
                    params.push(SExpr::Atom(Atom::Keyword(keys[k].into())));
                    // A keyword-looking value must stay attached to its key.
                    params.push(SExpr::Atom(Atom::Keyword(format!("value-{k}"))));
                }
            }
            check_params(&mut oracle.borrow_mut(), &params);
            let normal = canonical_params(&params);
            if let Some(expected) = &fixed {
                assert_eq!(&normal, expected);
            } else {
                fixed = Some(normal);
            }
        }
    }
    let rows = prop::collection::vec((any::<bool>(), key(), value()), 0..24);
    runner()
        .run(&rows, |rows| {
            let params = rows
                .into_iter()
                .flat_map(|(field, key, value)| {
                    if field {
                        vec![SExpr::Atom(Atom::Keyword(key)), value]
                    } else {
                        vec![value]
                    }
                })
                .collect::<Vec<_>>();
            check_params(&mut oracle.borrow_mut(), &params);
            Ok(())
        })
        .unwrap();
}

fn atom_expr(value: Atom) -> Value {
    json!(["atom", String::from_utf8(atom_to_octets(&value)).unwrap()])
}
fn expr(value: &SExpr) -> Value {
    match value {
        SExpr::Atom(atom) => atom_expr(atom.clone()),
        SExpr::List(xs) => json!(["list", xs.iter().map(expr).collect::<Vec<_>>()]),
    }
}
fn symbol(s: &str) -> Value {
    atom_expr(Atom::Symbol(s.into()))
}
fn type_expr(ty: &Option<TypeConstraint>) -> Value {
    let mut xs = vec![symbol("type")];
    if let Some(ty) = ty {
        xs.push(expr(&ty.source()));
    }
    json!(["list", xs])
}
fn rule(rule: &ShapeRule) -> Value {
    match rule {
        ShapeRule::Require {
            keyword,
            type_constraint,
            children,
        } => json!({
            "kind":"require","name":keyword,
            "prefix":[symbol("require"),atom_expr(Atom::Str(keyword.clone())),type_expr(type_constraint)],
            "children":children.iter().map(self::rule).collect::<Vec<_>>() }),
        ShapeRule::Optional {
            keyword,
            type_constraint,
            default,
            children,
        } => {
            let mut xs = vec![symbol("default")];
            if let Some(default) = default {
                xs.push(expr(default));
            }
            json!({"kind":"optional","name":keyword,
                "prefix":[symbol("optional"),atom_expr(Atom::Str(keyword.clone())),type_expr(type_constraint),json!(["list",xs])],
                "children":children.iter().map(self::rule).collect::<Vec<_>>() })
        }
        ShapeRule::MaxDepth(n) => json!({"kind":"max-depth","name":"",
            "prefix":[symbol("max-depth"),atom_expr(Atom::Num(*n as i64))],"children":[]}),
    }
}
fn shapes_tree(shapes: &[ShapeConstraint]) -> Value {
    json!({"kind":"root","name":"","prefix":[],"children":shapes.iter().map(|s| json!({
        "kind":"shape","name":s.performative,
        "prefix":[symbol("shape"),atom_expr(Atom::Str(s.performative.clone()))],
        "children":s.rules.iter().map(rule).collect::<Vec<_>>() })).collect::<Vec<_>>()})
}
fn check_shapes(oracle: &mut Oracle, shapes: Vec<ShapeConstraint>) {
    let case =
        json!({"profile":"canonicalisation","operation":"shapes","tree":shapes_tree(&shapes)});
    let mut d = base_dialect();
    d.shapes = shapes;
    canonicalise_dialect(&mut d);
    let expected = shapes_tree(&d.shapes);
    let once = d.clone();
    canonicalise_dialect(&mut d);
    assert_eq!(d, once, "Rust recursive shape fixed point");
    assert_eq!(oracle.request(&case), json!({"tree":expected}), "{case}");
}
fn rules() -> BoxedStrategy<ShapeRule> {
    let ty = prop_oneof![
        Just(None),
        Just(Some(TypeConstraint::Integer)),
        Just(Some(TypeConstraint::String)),
        Just(Some(TypeConstraint::Decimal)),
        Just(Some(TypeConstraint::Float)),
        Just(Some(TypeConstraint::List)),
        Just(Some(TypeConstraint::Contract(
            cbcl_core::contracts::Contract::unresolved(
                cbcl_parser::parse("(integer (between 0 10))").unwrap()
            )
        )))
    ];
    let leaf = prop_oneof![
        (key(), ty.clone()).prop_map(|(keyword, type_constraint)| ShapeRule::Require {
            keyword,
            type_constraint,
            children: vec![]
        }),
        (key(), ty, prop::option::of(value())).prop_map(|(keyword, type_constraint, default)| {
            ShapeRule::Optional {
                keyword,
                type_constraint,
                default,
                children: vec![],
            }
        }),
        (1u32..65).prop_map(ShapeRule::MaxDepth),
    ];
    leaf.prop_recursive(3, 48, 5, |inner| {
        (any::<bool>(), key(), prop::collection::vec(inner, 0..5)).prop_map(
            |(required, keyword, children)| {
                if required {
                    ShapeRule::Require {
                        keyword,
                        type_constraint: Some(TypeConstraint::List),
                        children,
                    }
                } else {
                    ShapeRule::Optional {
                        keyword,
                        type_constraint: Some(TypeConstraint::List),
                        default: None,
                        children,
                    }
                }
            },
        )
    })
    .boxed()
}

#[test]
#[ignore = "requires live proved canonicalisation oracle; mandatory in Lean CI"]
fn dialect_function_matches_formal_model() {
    let oracle = RefCell::new(Oracle::start());
    let required = |ty| ShapeRule::Require {
        keyword: "same".into(),
        type_constraint: Some(ty),
        children: vec![],
    };
    let optional = |default, children| ShapeRule::Optional {
        keyword: "same".into(),
        type_constraint: Some(TypeConstraint::List),
        default,
        children,
    };
    let deep = |n| {
        let mut value = SExpr::Atom(Atom::Num(n));
        for _ in 0..30 {
            value = SExpr::List(vec![value]);
        }
        value
    };
    let tie_cases = vec![
        vec![required(TypeConstraint::Integer), optional(None, vec![])],
        vec![
            required(TypeConstraint::String),
            required(TypeConstraint::Integer),
        ],
        vec![
            optional(Some(SExpr::Atom(Atom::Str("β".into()))), vec![]),
            optional(Some(SExpr::Atom(Atom::Str("é".into()))), vec![]),
        ],
        vec![ShapeRule::MaxDepth(10), ShapeRule::MaxDepth(2)],
        vec![
            optional(None, vec![required(TypeConstraint::String)]),
            optional(None, vec![required(TypeConstraint::Integer)]),
        ],
        vec![
            optional(Some(deep(1)), vec![]),
            optional(Some(deep(0)), vec![]),
        ],
    ];
    for reversed in [false, true] {
        let mut distinct_shapes = vec![
            ShapeConstraint {
                performative: "same".into(),
                rules: vec![required(TypeConstraint::String)],
            },
            ShapeConstraint {
                performative: "same".into(),
                rules: vec![required(TypeConstraint::Integer)],
            },
            ShapeConstraint {
                performative: "a".into(),
                rules: vec![],
            },
        ];
        if reversed {
            distinct_shapes.reverse();
        }
        check_shapes(&mut oracle.borrow_mut(), distinct_shapes);
    }
    for rules in tie_cases {
        for reversed in [false, true] {
            let mut rules = rules.clone();
            if reversed {
                rules.reverse();
            }
            check_shapes(
                &mut oracle.borrow_mut(),
                vec![
                    ShapeConstraint {
                        performative: "same".into(),
                        rules: rules.clone(),
                    },
                    ShapeConstraint {
                        performative: "same".into(),
                        rules: rules.into_iter().rev().collect(),
                    },
                ],
            );
        }
    }
    check_shapes(
        &mut oracle.borrow_mut(),
        vec![ShapeConstraint {
            performative: "nested-optional".into(),
            rules: vec![optional(
                None,
                vec![
                    ShapeRule::Require {
                        keyword: "z".into(),
                        type_constraint: None,
                        children: vec![],
                    },
                    ShapeRule::Require {
                        keyword: "a".into(),
                        type_constraint: None,
                        children: vec![],
                    },
                ],
            )],
        }],
    );
    let strategy = prop::collection::vec((key(), prop::collection::vec(rules(), 0..6)), 0..7);
    runner()
        .run(&strategy, |shapes| {
            let shapes = shapes
                .into_iter()
                .map(|(performative, rules)| ShapeConstraint {
                    performative,
                    rules,
                })
                .collect();
            check_shapes(&mut oracle.borrow_mut(), shapes);
            Ok(())
        })
        .unwrap();
}

#[test]
#[ignore = "requires live proved canonicalisation oracle; mandatory in Lean CI"]
fn shape_transport_rejects_malformed_or_overdeep_keys() {
    let mut oracle = Oracle::start();
    let tree = |metadata| json!({"kind":"root","name":"","prefix":[metadata],"children":[]});
    for metadata in [
        json!(["unknown", "bad"]),
        json!(["atom", 3]),
        json!(["list", false]),
    ] {
        let case = json!({"profile":"canonicalisation","operation":"shapes","tree":tree(metadata)});
        assert!(oracle.response(&case)["error"].is_string());
    }
    let mut metadata = json!(["atom", "N1"]);
    for _ in 0..32 {
        metadata = json!(["list", [metadata]]);
    }
    let case = json!({"profile":"canonicalisation","operation":"shapes","tree":tree(metadata)});
    assert!(oracle.response(&case)["error"]
        .as_str()
        .unwrap()
        .contains("depth"));
    let mut too_deep = json!({"kind":"root","name":"","prefix":[],"children":[]});
    for _ in 0..16 {
        too_deep = json!({"kind":"root","name":"","prefix":[],"children":[too_deep]});
    }
    let case = json!({"profile":"canonicalisation","operation":"shapes","tree":too_deep});
    assert!(oracle.response(&case)["error"]
        .as_str()
        .unwrap()
        .contains("depth"));
}
