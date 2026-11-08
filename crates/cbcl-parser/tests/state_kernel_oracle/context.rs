//! TEST-3809: live context refinement, including complete fault witness membership.
use super::*;

fn paths() -> Vec<Vec<&'static str>> {
    vec![
        vec![],
        vec!["dialect"],
        vec!["dialect", "name"],
        vec!["dialect", "address"],
        vec!["dialect", "body-address"],
        vec!["dialect", "author"],
        vec!["dialect", "roles"],
        vec!["dialect", "roles", "chair"],
        vec!["dialect", "roles", "reviewer"],
        vec!["dialect", "bounds"],
        vec!["dialect", "bounds", "max-fields"],
        vec!["dialect", "bounds", "max-list"],
        vec!["dialect", "bounds", "max-number"],
        vec!["dialect", "bounds", "max-string"],
        vec!["thread"],
        vec!["thread", "id"],
        vec!["thread", "root"],
        vec!["thread", "initiator"],
        vec!["thread", "opener"],
        vec!["thread", "roles"],
        vec!["thread", "roles", "chair"],
        vec!["thread", "roles", "reviewer"],
        vec!["observation"],
        vec!["observation", "accepted-count"],
        vec!["observation", "frontier"],
        vec!["thread", "roles", "unknown"],
        vec!["dialect", "bounds", "unknown"],
        vec!["observation", "local-clock"],
        vec!["thread", "id", "extra"],
    ]
}
fn fact(id: u64, verb: &str, parents: Vec<u64>, cast: Value, pin: Value, thread: Value) -> Value {
    json!({"id":id,"verb":verb,"signer":"@a","parents":parents,"cast":cast,"pin":pin,"thread":thread})
}
fn good_cast() -> Value {
    json!([["chair", ["@chair"]], ["reviewer", ["@a", "@b"]]])
}
fn request(facts: Vec<Value>, path: &[&str], query: Value) -> Value {
    json!({"profile":"context","name":"oracle-context","path":path,"query":query,"facts":facts})
}

fn native_context(case: &Value) -> Value {
    let name = case["name"].as_str().unwrap();
    let path = case["path"]
        .as_array()
        .unwrap()
        .iter()
        .map(|s| s.as_str().unwrap())
        .collect::<Vec<_>>()
        .join(" ");
    let threshold = case["query"]
        .as_str()
        .map(|q| format!("(threshold eligible result (member {q:?}))"))
        .unwrap_or_default();
    let text = format!(
        r#"(define {name} (cbcl) @a
        (:roles (chair (* reviewer))) (:causal-locality derive)
        (extend open (to) :from chair :to reviewer (tell to))
        (extend approve (to) :from reviewer :to chair (tell to))
        (extend close (to) :from chair :to reviewer (tell to))
        (protocol (then begin open) (then open (repeat 8 approve close)))
        (state (result (context {path})) {threshold}))"#
    );
    let tree = parse(&text).unwrap();
    let Ok(registry) = state_exports::parse_and_install_dialect(&tree) else {
        return json!({"installed":false});
    };
    let dialect = registry.iter().last().unwrap();
    let hash = cbcl_core::canonical::dialect_hash(dialect);
    let body = cbcl_core::canonical::dialect_name(dialect);
    let rows = case["facts"].as_array().unwrap();
    let mut pending = rows.clone();
    let mut built: BTreeMap<u64, Act> = BTreeMap::new();
    while !pending.is_empty() {
        let ready = pending
            .iter()
            .position(|fact| {
                fact["parents"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .all(|parent| built.contains_key(&parent.as_u64().unwrap()))
            })
            .expect("context oracle test history must be closed and acyclic");
        let f = pending.remove(ready);
        let id = f["id"].as_u64().unwrap();
        if built.contains_key(&id) {
            continue;
        }
        let parents = f["parents"]
            .as_array()
            .unwrap()
            .iter()
            .map(|p| built[&p.as_u64().unwrap()].address.clone())
            .collect::<Vec<_>>();
        let cause = match parents.as_slice() {
            [] => "begin".to_owned(),
            [one] => one.clone(),
            _ => format!("({})", parents.join(" ")),
        };
        let thread = f["thread"]
            .as_str()
            .map(|t| format!(":thread {t:?}"))
            .unwrap_or_default();
        let verb = f["verb"].as_str().unwrap();
        let signer = f["signer"].as_str().unwrap();
        let message = if verb == "hello" {
            format!("(hello :nonce {id} {thread} :caused-by {cause})")
        } else {
            format!("(lang {name} ({verb} @all :nonce {id} {thread} :from {signer} :caused-by {cause}))")
        };
        let signed = format!("(signed {signer} {message})");
        let cast = match &f["cast"] {
            Value::Null => None,
            Value::String(_) => Some("#t".to_owned()),
            Value::Array(bindings) => Some(format!(
                "({})",
                bindings
                    .iter()
                    .map(|b| format!(
                        "({} {})",
                        b[0].as_str().unwrap(),
                        b[1].as_array()
                            .unwrap()
                            .iter()
                            .map(|a| a.as_str().unwrap())
                            .collect::<Vec<_>>()
                            .join(" ")
                    ))
                    .collect::<Vec<_>>()
                    .join(" ")
            )),
            _ => unreachable!(),
        };
        let pin = match f["pin"].as_str() {
            Some("correct") => format!(":dialect {hash}"),
            Some("wrong") => format!(":dialect sha256:{}", "0".repeat(64)),
            Some("malformed") => ":dialect #t".to_owned(),
            _ => String::new(),
        };
        let wire = cast
            .map(|c| format!("(with-roles {c} {pin} {signed})"))
            .unwrap_or(signed);
        // BUG-006: use the typed message boundary because the strict wire lexer
        // splits sha256 pins. Hashing, signature verification and admission are
        // outside this oracle profile; casts and projections use native code.
        let expr: cbcl_core::sexpr::SExpr = wire.parse().unwrap();
        let message = cbcl_core::message::Message::try_from(&expr).unwrap();
        built.insert(id, Act::from_message(message, signer).unwrap());
    }
    let ids: BTreeMap<_, _> = built
        .iter()
        .map(|(id, a)| (a.address.clone(), *id))
        .collect();
    let acts = rows
        .iter()
        .map(|f| built[&f["id"].as_u64().unwrap()].clone())
        .collect::<Vec<_>>();
    let state: Value = serde_json::from_str(&render_json(&fold(
        dialect.state.as_ref().unwrap(),
        dialect.causal_protocol.as_ref(),
        &acts,
    )))
    .unwrap();
    fn normalize(v: &Value, ids: &BTreeMap<String, u64>, hash: &str, body: &str) -> Value {
        if v["status"] == "fault" {
            return normalize_fault(v, ids);
        }
        match v {
            Value::String(s) if s == hash => json!("dialect"),
            Value::String(s) if s == body => json!("body"),
            Value::String(s) if ids.contains_key(s) => json!(format!("act:{}", ids[s])),
            Value::Array(values) => {
                let mut values = values
                    .iter()
                    .map(|v| normalize(v, ids, hash, body))
                    .collect::<Vec<_>>();
                values.sort_by_key(Value::to_string);
                json!(values)
            }
            Value::Object(fields) => fields
                .iter()
                .map(|(key, v)| (key.clone(), normalize(v, ids, hash, body)))
                .collect(),
            _ => v.clone(),
        }
    }
    let schema: Value = serde_json::from_str(&cbcl_core::state::render_schema(
        &cbcl_core::state::state_schema(dialect.state.as_ref().unwrap(), &dialect.shapes),
    ))
    .unwrap();
    json!({"installed":true,"value":normalize(&state["result"],&ids,&hash,&body),
        "threshold":normalize(&state["eligible"],&ids,&hash,&body),"schema":schema["result"]["observation"]})
}

fn compare(oracle: &mut Oracle, case: &Value) {
    let expected = oracle.request(case);
    let actual = native_context(case);
    assert_eq!(actual, expected, "context case={case}");
}

#[test]
#[ignore = "requires lake build cbcl-state-oracle"]
fn context_kernel_matches_live_lean_oracle() {
    let mut oracle = Oracle::start();
    let root = fact(0, "hello", vec![], good_cast(), Value::Null, json!("t"));
    let mut conflicting = root.clone();
    conflicting["signer"] = json!("@other");
    for malformed in [
        request(vec![root.clone(), conflicting], &["thread"], Value::Null),
        request(
            vec![fact(
                1,
                "open",
                vec![0],
                Value::Null,
                Value::Null,
                json!("t"),
            )],
            &["thread"],
            Value::Null,
        ),
        request(
            vec![fact(
                0,
                "hello",
                vec![0],
                good_cast(),
                Value::Null,
                json!("t"),
            )],
            &["thread"],
            Value::Null,
        ),
    ] {
        assert!(
            oracle.response(&malformed).get("error").is_some(),
            "context boundary accepted {malformed}"
        );
    }
    let open = fact(1, "open", vec![0], Value::Null, Value::Null, json!("t"));
    let child = fact(2, "approve", vec![1], Value::Null, Value::Null, json!("t"));
    for path in paths() {
        for facts in [
            vec![],
            vec![root.clone()],
            vec![root.clone(), open.clone(), child.clone()],
        ] {
            let mut case = request(facts, &path, Value::Null);
            for delivery in 0..3 {
                if delivery == 1 {
                    case["facts"].as_array_mut().unwrap().reverse();
                }
                if delivery == 2 {
                    let extra = case["facts"].as_array().unwrap().clone();
                    case["facts"].as_array_mut().unwrap().extend(extra);
                }
                compare(&mut oracle, &case);
            }
        }
    }
    let casts = vec![
        Value::Null,
        json!("malformed"),
        json!([]),
        json!([["chair", ["@a"]]]),
        json!([["chair", ["@a", "@b"]], ["reviewer", ["@a"]]]),
        json!([["chair", ["@a"]], ["reviewer", []]]),
        json!([["chair", ["@a"]], ["reviewer", ["@a", "@a"]]]),
        json!([["chair", ["@a"]], ["reviewer", ["@a"]], ["chair", ["@a"]]]),
        json!([["chair", ["@a"]], ["reviewer", ["@a"]], ["unknown", ["@a"]]]),
        good_cast(),
    ];
    let mut histories = Vec::new();
    for cast in casts.iter() {
        histories.push(vec![
            fact(0, "hello", vec![], Value::Null, Value::Null, json!("t")),
            fact(1, "open", vec![0], Value::Null, Value::Null, json!("t")),
            fact(2, "open", vec![0], Value::Null, Value::Null, json!("t")),
            fact(
                3,
                "approve",
                vec![1, 2],
                Value::Null,
                Value::Null,
                json!("t"),
            ),
        ]);
        histories.push(vec![
            fact(0, "hello", vec![], cast.clone(), Value::Null, json!("t")),
            open.clone(),
        ]);
    }
    for pin in ["correct", "wrong", "malformed"] {
        histories.push(vec![
            fact(0, "hello", vec![], good_cast(), json!(pin), json!("t")),
            open.clone(),
        ]);
    }
    histories.extend([
        vec![
            root.clone(),
            fact(1, "hello", vec![], good_cast(), Value::Null, json!("t")),
        ],
        vec![
            root.clone(),
            open.clone(),
            fact(2, "open", vec![0], Value::Null, Value::Null, json!("t")),
        ],
        vec![
            root.clone(),
            fact(1, "open", vec![0], Value::Null, Value::Null, json!("other")),
        ],
        vec![
            fact(0, "hello", vec![], good_cast(), Value::Null, Value::Null),
            open.clone(),
        ],
    ]);
    histories.push(vec![
        fact(0, "hello", vec![], Value::Null, Value::Null, json!("t")),
        fact(1, "hello", vec![], good_cast(), Value::Null, json!("t")),
        fact(2, "open", vec![0], Value::Null, Value::Null, json!("other")),
        fact(3, "open", vec![1], Value::Null, Value::Null, json!("t")),
        fact(
            4,
            "approve",
            vec![2, 3],
            Value::Null,
            Value::Null,
            json!("t"),
        ),
    ]);
    for facts in histories {
        for path in paths() {
            compare(&mut oracle, &request(facts.clone(), &path, Value::Null));
        }
        for query in ["@a", "@outside"] {
            compare(
                &mut oracle,
                &request(
                    facts.clone(),
                    &["thread", "roles", "reviewer"],
                    json!(query),
                ),
            );
        }
    }
    let oracle = RefCell::new(oracle);
    let strategy = (
        0usize..paths().len(),
        0usize..casts.len() + 4,
        0u8..4,
        prop::collection::vec((0u8..4, any::<u8>(), any::<u8>(), 0u8..5), 0..9),
        any::<bool>(),
        any::<bool>(),
        0u8..4,
        prop::collection::vec(0usize..4, 0..7),
    );
    let mut config = proptest::test_runner::Config::default();
    if std::env::var_os("PROPTEST_CASES").is_none() {
        config.cases = 512;
    }
    config.failure_persistence = Some(Box::new(
        proptest::test_runner::FileFailurePersistence::Direct(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/state_context_oracle.proptest-regressions"
        )),
    ));
    let mut runner = proptest::test_runner::TestRunner::new(config);
    runner
        .run(
            &strategy,
            |(path, cast, pin, nodes, root_present, alias, query, roster)| {
                let generated_cast = json!([
                    ["chair", ["@chair"]],
                    [
                        "reviewer",
                        roster
                            .iter()
                            .map(|i| ["@a", "@b", "@c", "@d"][*i])
                            .collect::<Vec<_>>()
                    ]
                ]);
                let cast = casts.get(cast).cloned().unwrap_or(generated_cast);
                let pin = [
                    Value::Null,
                    json!("correct"),
                    json!("wrong"),
                    json!("malformed"),
                ][pin as usize]
                    .clone();
                let mut facts = if root_present {
                    vec![fact(0, "hello", vec![], cast, pin, json!("t"))]
                } else {
                    vec![]
                };
                for (verb, a, b, thread) in nodes {
                    let id = facts.len() as u64;
                    let parents = if id == 0 || verb == 3 {
                        vec![]
                    } else {
                        let mut ps = vec![u64::from(a) % id, u64::from(b) % id];
                        ps.sort();
                        ps.dedup();
                        ps
                    };
                    facts.push(fact(
                        id,
                        ["open", "approve", "close", "hello"][verb as usize],
                        parents,
                        if verb == 3 { good_cast() } else { Value::Null },
                        Value::Null,
                        match thread {
                            0 => Value::Null,
                            1 => json!("other"),
                            _ => json!("t"),
                        },
                    ));
                }
                let mut case = request(
                    facts,
                    &paths()[path],
                    match query {
                        0 => json!("@a"),
                        1 => json!("@outside"),
                        _ => Value::Null,
                    },
                );
                if alias {
                    case["name"] = json!("context-alias");
                    for f in case["facts"].as_array_mut().unwrap() {
                        f["signer"] = if f["id"] == 0 {
                            json!("@chair")
                        } else {
                            json!("@b")
                        };
                    }
                }
                // Separate semantic identities from causal construction order.
                let size = case["facts"].as_array().unwrap().len() as u64;
                let label = |id: u64| 101 + (size - id) * 13;
                for fact in case["facts"].as_array_mut().unwrap() {
                    let id = fact["id"].as_u64().unwrap();
                    let parents = fact["parents"]
                        .as_array()
                        .unwrap()
                        .iter()
                        .map(|parent| label(parent.as_u64().unwrap()))
                        .collect::<Vec<_>>();
                    fact["id"] = json!(label(id));
                    fact["parents"] = json!(parents);
                }
                for delivery in 0..3 {
                    if delivery == 1 {
                        case["facts"].as_array_mut().unwrap().reverse();
                    }
                    if delivery == 2 {
                        let extra = case["facts"].as_array().unwrap().clone();
                        case["facts"].as_array_mut().unwrap().extend(extra);
                    }
                    let expected = oracle.borrow_mut().request(&case);
                    let actual = native_context(&case);
                    prop_assert_eq!(actual, expected, "context case={}", case);
                }
                Ok(())
            },
        )
        .unwrap();
}
