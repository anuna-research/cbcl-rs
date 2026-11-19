//! Bounded typed observe_facts graphs; aliases do not claim signed admission.
use super::*;
use cbcl_core::{
    escrow,
    sexpr::{Atom, SExpr},
    state::Rule,
};
use std::collections::BTreeSet;

fn address(id: u64) -> String {
    format!("f1220{id:064}")
}
fn owner(index: &Value) -> String {
    ["@treasury", "@alice", "@bob", "@outsider"][index.as_u64().unwrap() as usize].into()
}
fn symbol(value: String) -> SExpr {
    SExpr::Atom(Atom::Symbol(value))
}

fn native(rule: &escrow::CounterRule, case: &Value) -> Value {
    let bounded = case
        .get("bounded")
        .map(|value| value.as_bool().unwrap())
        .unwrap_or(false);
    let mut configured = rule.clone();
    if bounded {
        configured.ceiling = Some(2000);
        configured.headroom_key = Some("space".into());
        configured.transfer_headroom = Some(("space".into(), "recipient".into(), "amount".into()));
    }
    let rule = &configured;
    let (root, opener) = resource::initial();
    let mut root = escrow::project_resource_fact(rule, &root).unwrap().unwrap();
    let mut opener = escrow::project_resource_fact(rule, &opener)
        .unwrap()
        .unwrap();
    root.address = address(1);
    opener.address = address(2);
    opener.predecessors = vec![address(1)];
    if bounded {
        opener.fields.insert(
            "space".into(),
            SExpr::List(
                [("@treasury", 1000), ("@alice", 0), ("@bob", 0)]
                    .into_iter()
                    .map(|(owner, amount)| {
                        SExpr::List(vec![symbol(owner.into()), SExpr::Atom(Atom::Num(amount))])
                    })
                    .collect(),
            ),
        );
    }
    let mut accepted = BTreeMap::<String, u64>::new();
    let mut facts = BTreeMap::<String, escrow::ResourceFact>::new();
    if case["root"].as_bool().unwrap() {
        accepted.insert(root.address.clone(), 1);
        facts.insert(root.address.clone(), root);
    }
    if case["opener"].as_bool().unwrap() {
        accepted.insert(opener.address.clone(), 2);
        facts.insert(opener.address.clone(), opener);
    }
    let mut rows = case["nodes"]
        .as_array()
        .unwrap()
        .iter()
        .enumerate()
        .collect::<Vec<_>>();
    if case["reverse"].as_bool().unwrap() {
        rows.reverse();
    }
    for (index, row) in rows {
        let id = index as u64 + 3;
        accepted.insert(address(id), id);
        if !rule.verbs().contains(&row["kind"].as_str().unwrap()) {
            continue;
        }
        let mut fields = BTreeMap::from([
            (
                "amount".into(),
                SExpr::Atom(Atom::Num(row["amount"].as_i64().unwrap())),
            ),
            (
                escrow::DEPS.into(),
                SExpr::List(
                    row["deps"]
                        .as_array()
                        .unwrap()
                        .iter()
                        .map(|id| symbol(address(id.as_u64().unwrap())))
                        .collect(),
                ),
            ),
        ]);
        if let Some(previous) = row["prev"].as_u64() {
            fields.insert(escrow::PREV.into(), symbol(address(previous)));
        }
        if row["kind"] == "pay" || row["kind"] == "space" {
            fields.insert("recipient".into(), symbol(owner(&row["recipient"])));
        }
        let signer = owner(&row["owner"]);
        let fact = escrow::ResourceFact {
            address: address(id),
            verb: row["kind"].as_str().unwrap().into(),
            signer: signer.clone(),
            predecessors: row["causes"]
                .as_array()
                .unwrap()
                .iter()
                .map(|id| address(id.as_u64().unwrap()))
                .collect(),
            fields,
            language: Some("example-coin".into()),
            thread: Some("coin-1".into()),
            from: Some(symbol(signer)),
            bindings: None,
            identity: [id as u8; 32],
        };
        facts.insert(fact.address.clone(), fact);
    }
    let value = escrow::observe_facts(rule, &facts, |id| accepted.contains_key(id)).value();
    let parsed: Value = serde_json::from_str(&value.render()).unwrap();
    if parsed["status"] == "ready" {
        let mut observed = json!({"status":"ready","value":parsed["value"],"rights":parsed["rights"],"ready_bytes":value.render()});
        if let Some(headroom) = parsed.get("headroom") {
            observed["headroom"] = headroom.clone();
        }
        observed
    } else if parsed["status"] == "fault" {
        let names = parsed["evidence"].as_array().unwrap();
        let mut evidence = names
            .iter()
            .map(|name| accepted[name.as_str().unwrap()])
            .collect::<Vec<_>>();
        assert_eq!(
            evidence.len(),
            evidence.iter().collect::<BTreeSet<_>>().len(),
            "duplicate typed native witness"
        );
        evidence.sort();
        let cbcl_core::state::Value::Map(fields) = value else {
            panic!("fault must be a map")
        };
        let bytes = fields
            .iter()
            .find(|(key, _)| matches!(key,cbcl_core::state::Value::Str(name) if name=="evidence"))
            .unwrap()
            .1
            .render();
        json!({"status":"fault","evidence":evidence,"witness_bytes":bytes})
    } else {
        json!({"status":"pending"})
    }
}

fn row(
    kind: &str,
    owner: u64,
    amount: i64,
    prev: Option<u64>,
    deps: Vec<u64>,
    recipient: u64,
) -> Value {
    json!({"kind":kind,"owner":owner,"amount":amount,"prev":prev,"deps":deps,"causes":[2],"recipient":recipient})
}

fn compare(rule: &escrow::CounterRule, oracle: &RefCell<Oracle>, case: &Value) {
    let earlier = native(rule, case);
    assert_eq!(
        earlier,
        oracle.borrow_mut().request(case),
        "typed resource graph={case}"
    );
    let mut grown = case.clone();
    grown["nodes"]
        .as_array_mut()
        .unwrap()
        .push(row("tell", 0, 0, None, vec![], 0));
    grown["reverse"] = json!(!case["reverse"].as_bool().unwrap());
    let later = native(rule, &grown);
    assert_eq!(
        later,
        oracle.borrow_mut().request(&grown),
        "grown typed resource graph={grown}"
    );
    if earlier["status"] == "fault" {
        assert_eq!(later["status"], "fault", "typed resource fault disappeared");
        for witness in earlier["evidence"].as_array().unwrap() {
            assert!(
                later["evidence"].as_array().unwrap().contains(witness),
                "typed resource witness disappeared"
            );
        }
    }
}

#[test]
#[ignore = "requires lake build cbcl-state-oracle; explicitly run in Lean CI"]
fn arbitrary_resource_graphs_match_lean() {
    let dialect = cbcl_parser::parse_dialect(
        &parse(include_str!("../../../../dialects/example-coin.cbcl")).unwrap(),
    )
    .unwrap();
    let mut registry = cbcl_core::dialect::DialectRegistry::new();
    registry.install(dialect.clone()).unwrap();
    let Rule::BoundedCounter(rule) = dialect.state.as_ref().unwrap().rule_of("coins").unwrap()
    else {
        panic!("resource fixture")
    };
    let oracle = RefCell::new(Oracle::start());
    for nodes in [
        vec![],
        vec![row("burn", 0, 1, Some(2), vec![], 0)],
        vec![
            row("pay", 0, 5, Some(2), vec![], 1),
            row("burn", 1, 5, Some(2), vec![3], 0),
        ],
        vec![
            row("mint", 0, 1, Some(4), vec![], 0),
            row("mint", 0, 1, Some(3), vec![], 0),
        ],
        vec![
            row("burn", 0, 1, Some(2), vec![], 0),
            row("burn", 0, 2, Some(2), vec![], 0),
        ],
        vec![row("burn", 1, 1, Some(2), vec![4, 4], 0)],
        vec![
            row("pay", 0, 5, Some(2), vec![], 1),
            row("burn", 1, 5, Some(3), vec![], 0),
        ],
        vec![
            row("burn", 1, 1, Some(2), vec![], 0),
            row("mint", 0, 1, Some(32), vec![], 0),
        ],
        vec![
            row("mint", 0, 1, Some(4), vec![], 0),
            row("mint", 0, 1, Some(3), vec![], 0),
            row("burn", 1, 1, Some(32), vec![], 0),
        ],
    ] {
        for root in [false, true] {
            for opener in [false, true] {
                compare(
                    rule,
                    &oracle,
                    &json!({"profile":"resource-facts","root":root,"opener":opener,"reverse":false,"nodes":nodes}),
                );
            }
        }
    }
    let capped_cases = [
        vec![row("mint", 0, 1000, Some(2), vec![], 0)],
        vec![row("mint", 0, 1001, Some(2), vec![], 0)],
        vec![
            row("burn", 0, 1000, Some(2), vec![], 0),
            row("mint", 0, 2000, Some(3), vec![], 0),
        ],
        vec![
            row("space", 0, 800, Some(2), vec![], 1),
            row("space", 1, 800, Some(2), vec![3], 0),
            row("mint", 0, 1000, Some(3), vec![4], 0),
        ],
        vec![
            row("space", 0, 800, Some(2), vec![], 1),
            row("space", 1, 800, Some(2), vec![3], 0),
            row("mint", 0, 1000, Some(3), vec![], 0),
        ],
        vec![
            row("pay", 0, 5, Some(2), vec![], 1),
            row("burn", 1, 5, Some(2), vec![3], 0),
            row("space", 1, 5, Some(4), vec![], 0),
            row("mint", 0, 1005, Some(3), vec![5], 0),
        ],
        vec![
            row("pay", 0, 5, Some(2), vec![], 1),
            row("burn", 1, 5, Some(2), vec![3], 0),
            row("space", 1, 5, Some(4), vec![], 0),
            row("mint", 0, 1005, Some(3), vec![], 0),
        ],
    ];
    for (index, nodes) in capped_cases.into_iter().enumerate() {
        let case = json!({"profile":"resource-facts","root":true,"opener":true,"reverse":false,"bounded":true,"nodes":nodes});
        let observed = native(rule, &case);
        assert_eq!(
            observed["status"],
            if [1, 4, 6].contains(&index) {
                "fault"
            } else {
                "ready"
            },
            "headroom case={case}"
        );
        if observed["status"] == "ready" {
            assert!(observed.get("headroom").is_some());
        }
        compare(rule, &oracle, &case);
    }
    let big_nodes = (0..8)
        .map(|index| row("mint", 0, i64::MAX, Some(index + 2), vec![], 0))
        .collect::<Vec<_>>();
    let big = json!({"profile":"resource-facts","root":true,"opener":true,"reverse":false,"nodes":big_nodes});
    assert!(native(rule, &big)["ready_bytes"]
        .as_str()
        .unwrap()
        .contains(&(1000i128 + 8 * i128::from(i64::MAX)).to_string()));
    compare(rule, &oracle, &big);
    let valid = json!({"profile":"resource-facts","root":true,"opener":true,"reverse":false,"nodes":[row("burn",0,1,Some(2),vec![],0)]});
    for (key, invalid) in [
        ("root", json!("true")),
        ("expected", json!("ready")),
        ("nodes", json!(vec![row("tell", 0, 0, None, vec![], 0); 17])),
        ("bounded", json!("true")),
    ] {
        let mut case = valid.clone();
        case[key] = invalid;
        assert!(
            oracle.borrow_mut().response(&case).get("error").is_some(),
            "invalid typed resource input={case}"
        );
    }
    for (key, invalid) in [
        ("kind", json!("open")),
        ("owner", json!(4)),
        ("recipient", json!(4)),
        ("amount", json!(9223372036854775808u64)),
        ("prev", json!(-1)),
        ("deps", json!(vec![2; 17])),
        ("causes", json!([33])),
        ("expected", json!("fault")),
    ] {
        let mut case = valid.clone();
        case["nodes"][0][key] = invalid;
        assert!(
            oracle.borrow_mut().response(&case).get("error").is_some(),
            "invalid typed resource row={case}"
        );
    }
    let boundary = json!({"profile":"resource-facts","root":true,"opener":true,"reverse":true,"nodes":vec![row("tell",0,0,None,vec![],0);16]});
    assert_eq!(
        native(rule, &boundary),
        oracle.borrow_mut().request(&boundary)
    );
    let node = (0usize..5,0u64..4,prop_oneof![any::<i64>(),-2i64..1003],prop::option::of(0u64..13),
        prop::collection::vec(0u64..13,0..5),prop::collection::vec(0u64..13,0..5),0u64..4)
        .prop_map(|(kind,owner,amount,prev,deps,causes,recipient)| json!({"kind":(["mint","burn","pay","tell","space"][kind]),"owner":owner,"amount":amount,"prev":prev,"deps":deps,"causes":causes,"recipient":recipient}));
    let mut config = proptest::test_runner::Config::default();
    if std::env::var_os("PROPTEST_CASES").is_none() {
        config.cases = 512;
    }
    let mut runner = proptest::test_runner::TestRunner::new(config);
    let arbitrary = (
        prop::collection::vec(node, 0..9),
        any::<bool>(),
        any::<bool>(),
    );
    let structured = prop::collection::vec((0usize..3, 0usize..4, 1i64..101, 0u64..3), 0..9)
        .prop_map(|seeds| {
            let mut tips = [2u64; 3];
            let mut nodes = Vec::new();
            for (index, (owner, kind, amount, recipient)) in seeds.into_iter().enumerate() {
                let previous = tips[owner];
                let deps = tips
                    .iter()
                    .copied()
                    .filter(|id| *id != 2 && *id != previous)
                    .collect::<BTreeSet<_>>()
                    .into_iter()
                    .collect::<Vec<_>>();
                let mut node = row(
                    if kind == 0 && owner == 0 {
                        "mint"
                    } else if kind == 2 {
                        "pay"
                    } else if kind == 3 {
                        "space"
                    } else {
                        "burn"
                    },
                    owner as u64,
                    amount,
                    Some(previous),
                    deps.clone(),
                    recipient,
                );
                node["causes"] = json!(std::iter::once(previous).chain(deps).collect::<Vec<_>>());
                nodes.push(node);
                tips[owner] = index as u64 + 3;
            }
            (nodes, true, true)
        });
    runner.run(&(prop_oneof![arbitrary,structured],any::<bool>(),any::<bool>()),|((nodes,root,opener),reverse,bounded)|{
        compare(rule,&oracle,&json!({"profile":"resource-facts","nodes":nodes,"root":root,"opener":opener,"reverse":reverse,"bounded":bounded}));
        Ok(())
    }).unwrap();
}
