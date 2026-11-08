//! SPEC-038: randomized live Rust/Lean differential checks, not a Rust/Rust mirror.
//! Run `lake build cbcl-state-oracle` in lean-cbcl, then this ignored test.
use cbcl_core::state::{fold, render_json, Act};
use cbcl_parser::{parse, parse_message, state_exports};
use proptest::prelude::*;
use serde_json::{json, Value};
use std::cell::{Cell, RefCell};
use std::collections::BTreeMap;
use std::io::{BufRead, BufReader, Write};
use std::process::{Child, ChildStdin, Command, Stdio};

struct Oracle {
    child: Child,
    input: ChildStdin,
    output: std::sync::mpsc::Receiver<Result<String, String>>,
    worker: Option<std::thread::JoinHandle<()>>,
}
impl Oracle {
    fn start() -> Self {
        let executable = std::env::var_os("CBCL_STATE_ORACLE")
            .map(std::path::PathBuf::from)
            .unwrap_or_else(|| {
                std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                    .join("../../lean-cbcl/.lake/build/bin/cbcl-state-oracle")
            });
        let mut child = Command::new(&executable)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::inherit())
            .spawn()
            .unwrap_or_else(|e| panic!("build Lean oracle first: {}: {e}", executable.display()));
        let stdout = child.stdout.take().unwrap();
        let (send, receive) = std::sync::mpsc::channel();
        let worker = std::thread::spawn(move || {
            let mut output = BufReader::new(stdout);
            loop {
                let mut line = String::new();
                match output.read_line(&mut line) {
                    Ok(0) => break,
                    Ok(_) => {
                        if send.send(Ok(line)).is_err() {
                            break;
                        }
                    }
                    Err(error) => {
                        let _ = send.send(Err(error.to_string()));
                        break;
                    }
                }
            }
        });
        Self {
            input: child.stdin.take().unwrap(),
            output: receive,
            worker: Some(worker),
            child,
        }
    }

    fn response(&mut self, case: &Value) -> Value {
        writeln!(self.input, "{case}").unwrap();
        self.input.flush().unwrap();
        let line = self
            .output
            .recv_timeout(std::time::Duration::from_secs(10))
            .expect("Lean oracle exited or failed to respond within 10 seconds")
            .expect("Lean oracle stdout error");
        let reply: Value = serde_json::from_str(&line).expect("Lean JSON response");
        reply
    }
    fn request(&mut self, case: &Value) -> Value {
        let reply = self.response(case);
        assert!(
            reply.get("error").is_none(),
            "oracle input error: {reply}; input={case}"
        );
        reply
    }
}
impl Drop for Oracle {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
        if let Some(worker) = self.worker.take() {
            let _ = worker.join();
        }
    }
}

#[derive(Clone, Debug)]
struct Case {
    n: usize,
    fan: bool,
    mutation: Option<(usize, usize, usize)>,
    table_edit: u8,
    projection: u8,
    stable: bool,
    values: Vec<i8>,
    rows: Vec<(u8, i8, u8)>,
    queries: Option<Vec<(u8, i8)>>,
    history: Vec<(u8, i8, bool)>,
}
fn cases() -> impl Strategy<Value = Case> {
    (2usize..8).prop_flat_map(|n| (
        Just(n), any::<bool>(), prop_oneof![4 => Just(None), 1 => (0usize..n, 0usize..n, 0usize..n).prop_map(Some)],
        prop_oneof![4 => Just(0u8), 1 => 1u8..4],
        0u8..5, any::<bool>(), proptest::collection::vec(-4i8..8, n),
        proptest::collection::vec((0u8..3, -3i8..4, 0u8..8), 1..9),
        prop_oneof![2 => Just(None), 3 => proptest::collection::vec((0u8..4, -4i8..8), 0..4).prop_map(Some)],
        proptest::collection::vec((0u8..6, -3i8..4, any::<bool>()), 0..18),
    )).prop_map(|(n, fan, mutation, table_edit, projection, stable, values, rows, queries, history)|
        Case { n, fan, mutation, table_edit, projection, stable, values, rows, queries, history })
}
fn literal(key: u8, value: i8) -> Value {
    match key {
        0 => json!(format!("p{}", value.rem_euclid(3))),
        1 => json!(value),
        _ => json!(value.rem_euclid(2) == 1),
    }
}
fn key(k: u8) -> &'static str {
    ["phase", "amount", "flag"][usize::from(k)]
}
fn wire(value: &Value) -> String {
    match value {
        Value::Bool(true) => "#t".into(),
        Value::Bool(false) => "#f".into(),
        Value::Array(parts) if parts.len() == 2 && parts[0] == "symbol" => {
            let token = parts[1].as_str().unwrap();
            assert!(
                matches!(parse(token), Ok(cbcl_core::sexpr::SExpr::Atom(cbcl_core::sexpr::Atom::Symbol(ref name))) if name == token)
            );
            token.to_owned()
        }
        _ => value.to_string(),
    }
}

impl Case {
    fn request(&self) -> Value {
        let names: Vec<_> = (0..self.n).map(|i| format!("e{i}")).collect();
        let mut joins = Vec::new();
        for a in 0..self.n {
            for b in 0..self.n {
                let mut result = if self.fan && a != b && a != 0 && b != 0 {
                    self.n - 1
                } else {
                    a.max(b)
                };
                if let Some((x, y, z)) = self.mutation {
                    if (a, b) == (x, y) {
                        result = z;
                    }
                }
                joins.push(json!([names[a], names[b], names[result]]));
            }
        }
        match self.table_edit {
            1 => {
                joins.pop();
            }
            2 => joins.push(joins[0].clone()),
            3 => joins[0][2] = json!("unknown"),
            _ => {}
        }
        let projection = match self.projection {
            0 => Value::Null,
            kind => {
                let mut values = self.values.clone();
                if kind == 1 {
                    values.sort();
                }
                json!({"stable":self.stable, "rows": (0..self.n).map(|i| json!([names[i],
                    match kind { 1 | 2 => json!(values[i]), 3 => json!(i >= self.n / 2), _ => if i % 2 == 0 { json!(values[i]) } else { json!(true) } }
                ])).collect::<Vec<_>>()})
            }
        };
        let queries = self.queries.as_ref().map(|queries| {
            queries
                .iter()
                .map(|(kind, value)| match kind {
                    0 => json!(names[value.rem_euclid(self.n as i8) as usize]),
                    1 => json!(value),
                    2 => json!(true),
                    _ => json!(false),
                })
                .collect::<Vec<_>>()
        });
        json!({"table":{"elements":names, "bottom":"e0", "top":format!("e{}", self.n - 1), "rows":joins},
            "projection":projection,
            "contributions":self.rows.iter().map(|(k,v,e)| json!([key(*k), literal(*k,*v), format!("e{}", usize::from(*e) % self.n)])).collect::<Vec<_>>(),
            "queries":queries,
            "acts": self.history.iter().enumerate().map(|(i,(p,n,b))| json!([i, [["phase",if *p < 3 {json!(format!("p{p}"))} else {json!(["symbol",format!("p{}",p-3)])}],["amount",n],["flag",b]]])).collect::<Vec<_>>()})
    }
}
fn dialect(case: &Value) -> String {
    let table = &case["table"];
    let names = table["elements"]
        .as_array()
        .unwrap()
        .iter()
        .map(|v| v.as_str().unwrap())
        .collect::<Vec<_>>()
        .join(" ");
    let joins = table["rows"]
        .as_array()
        .unwrap()
        .iter()
        .map(|v| {
            format!(
                "({} {} {})",
                v[0].as_str().unwrap(),
                v[1].as_str().unwrap(),
                v[2].as_str().unwrap()
            )
        })
        .collect::<Vec<_>>()
        .join(" ");
    let rows = case["contributions"]
        .as_array()
        .unwrap()
        .iter()
        .map(|v| {
            format!(
                "(:{} {} {})",
                v[0].as_str().unwrap(),
                wire(&v[1]),
                v[2].as_str().unwrap()
            )
        })
        .collect::<Vec<_>>()
        .join(" ");
    let projection = if case["projection"].is_null() {
        String::new()
    } else {
        let p = &case["projection"];
        format!(
            "(project {} ({}))",
            if p["stable"] == true { "stable" } else { "" },
            p["rows"]
                .as_array()
                .unwrap()
                .iter()
                .map(|v| format!("({} {})", v[0].as_str().unwrap(), wire(&v[1])))
                .collect::<Vec<_>>()
                .join(" ")
        )
    };
    let threshold = case["queries"]
        .as_array()
        .map(|qs| {
            format!(
                "(threshold ready value {})",
                qs.iter().map(wire).collect::<Vec<_>>().join(" ")
            )
        })
        .unwrap_or_default();
    let has_freeze = case["freeze"].is_boolean();
    let freeze = if has_freeze {
        format!(
            "(freeze value close {})",
            if case["freeze"] == true {
                "fault"
            } else {
                "supersede"
            }
        )
    } else {
        String::new()
    };
    let source = format!("(define oracle-demo (cbcl) @a (extend open (to) (tell to)) (extend mark (to phase amount flag) (tell to :phase phase :amount amount :flag flag)) (shape mark (require :phase string) (require :amount number) (require :flag bool)) (protocol (then begin open) (then open mark)) (state (lattice rank (elements {names}) (bottom e0) (top {}) (join {joins})) (value (lift mark (into rank) (contribute {rows}) {projection})) {threshold} {freeze}))",table["top"].as_str().unwrap());
    let source = if let Some(limit) = case.get("max-list").and_then(Value::as_u64) {
        source.replace("(state", &format!("(:state-bounds (max-list {limit})) (state"))
    } else { source };
    if has_freeze {
        source
            .replace("@a (extend open", "@a (:roles (owner)) (extend open")
            .replace(
                "(extend open (to)",
                "(extend open (to) :from owner :to owner",
            )
            .replace(
                "(extend mark (to phase amount flag)",
                "(extend mark (to phase amount flag) :from owner :to owner",
            )
            .replace(
                "(shape mark",
                "(extend close (to) :from owner :to owner (tell to)) (shape mark",
            )
            .replace("(then open mark)", "(then open (repeat 16 mark close))")
    } else {
        source
    }
}
fn make_act(text: &str) -> Act {
    Act::from_message(parse_message(&parse(text).unwrap()).unwrap(), "@a").unwrap()
}
fn normalize_fault(value: &Value, ids: &BTreeMap<String, u64>) -> Value {
    let mut evidence: Vec<_> = value["evidence"]
        .as_array()
        .unwrap()
        .iter()
        .map(|address| ids[address.as_str().unwrap()])
        .collect();
    evidence.sort();
    evidence.dedup();
    json!({"status":"fault", "evidence":evidence})
}
fn graph_acts(case: &Value) -> (BTreeMap<String, u64>, Vec<Act>) {
    let rows = case["acts"].as_array().unwrap();
    let mut pending = rows.clone();
    let mut built: BTreeMap<u64, Act> = BTreeMap::new();
    while !pending.is_empty() {
        let ready = pending
            .iter()
            .position(|row| {
                row[2]
                    .as_array()
                    .unwrap()
                    .iter()
                    .all(|parent| built.contains_key(&parent.as_u64().unwrap()))
            })
            .expect("oracle test history must be closed and acyclic");
        let row = pending.remove(ready);
        let id = row[0].as_u64().unwrap();
        if built.contains_key(&id) {
            continue;
        }
        let verb = row[1].as_str().unwrap();
        let parents = row[2]
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
        let fields = row[3]
            .as_array()
            .unwrap()
            .iter()
            .map(|p| format!(":{} {}", p[0].as_str().unwrap(), wire(&p[1])))
            .collect::<Vec<_>>()
            .join(" ");
        built.insert(id,make_act(&format!("(lang oracle-demo ({verb} @all {fields} :nonce {id} :caused-by {cause} :thread \"t\" :from @a))")));
    }
    let ids = built
        .iter()
        .map(|(id, a)| (a.address.clone(), *id))
        .collect();
    let delivered = rows
        .iter()
        .map(|row| built[&row[0].as_u64().unwrap()].clone())
        .collect();
    (ids, delivered)
}

fn native(case: &Value) -> Value {
    if case["profile"] == "events-sum" {
        return native_nested(case);
    }
    let text = dialect(case);
    let Ok(sexpr) = parse(&text) else {
        return json!({"installed":false});
    };
    let registry = match state_exports::parse_and_install_dialect(&sexpr) {
        Ok(registry) => registry,
        Err(error) => {
            if std::env::var_os("CBCL_ORACLE_DIAGNOSTICS").is_some() {
                eprintln!("install error: {error:?}; {text}");
            }
            return json!({"installed":false});
        }
    };
    let d = registry.iter().last().unwrap();
    let (ids, acts) = if case["acts"]
        .as_array()
        .unwrap()
        .iter()
        .any(|a| a.as_array().unwrap().len() == 4)
    {
        graph_acts(case)
    } else {
        let open =
            make_act("(lang oracle-demo (open @all :caused-by begin :thread \"t\" :from @a))");
        let mut ids = BTreeMap::new();
        let mut acts = vec![open.clone()];
        for a in case["acts"].as_array().unwrap() {
            let fields = a[1]
                .as_array()
                .unwrap()
                .iter()
                .map(|p| format!(":{} {}", p[0].as_str().unwrap(), wire(&p[1])))
                .collect::<Vec<_>>()
                .join(" ");
            let act = make_act(&format!("(lang oracle-demo (mark @all {fields} :nonce {} :caused-by {} :thread \"t\" :from @a))",a[0],open.address));
            ids.insert(act.address.clone(), a[0].as_u64().unwrap());
            acts.push(act);
        }
        (ids, acts)
    };
    let state: Value = serde_json::from_str(&render_json(&fold(
        d.state.as_ref().unwrap(),
        d.causal_protocol.as_ref(),
        &acts,
    )))
    .unwrap();
    let observation = if state["value"]["status"] == "fault" {
        normalize_fault(&state["value"], &ids)
    } else if state["value"].get("frozen").is_some() {
        let mut excluded: Vec<_> = state["value"]["superseded"]
            .as_array()
            .unwrap()
            .iter()
            .map(|v| ids[v.as_str().unwrap()])
            .collect();
        excluded.sort();
        excluded.dedup();
        json!({"status":"frozen","freezer":ids[state["value"]["frozen"].as_str().unwrap()],"excluded":excluded,"value":state["value"]["value"]})
    } else {
        json!({"status":"snapshot","value":state["value"]})
    };
    let threshold = if case["queries"].is_null() {
        Value::Null
    } else if state["ready"]["status"] == "fault" {
        normalize_fault(&state["ready"], &ids)
    } else {
        state["ready"].clone()
    };
    json!({"installed":true,"observation":observation,"threshold":threshold})
}

fn directed_cases() -> Vec<Case> {
    let base = Case {
        n: 4,
        fan: true,
        mutation: None,
        table_edit: 0,
        projection: 0,
        stable: true,
        values: vec![-4, -3, -2, -1],
        rows: vec![(0, 0, 1), (1, 0, 2)],
        queries: Some(vec![(0, 1)]),
        history: vec![],
    };
    let mut reached = base.clone();
    reached.history = vec![(0, 1, false)];
    let mut fault = base.clone();
    fault.history = vec![(0, 0, false)];
    let mut numeric = reached.clone();
    numeric.projection = 1;
    numeric.queries = Some(vec![(1, -3)]);
    let mut boolean = base.clone();
    boolean.projection = 3;
    boolean.queries = Some(vec![(2, 0)]);
    boolean.history = vec![(1, 0, true)];
    let mut invalid = base.clone();
    invalid.mutation = Some((0, 0, 1));
    vec![base, reached, fault, numeric, boolean, invalid]
}

#[test]
#[ignore = "requires lake build cbcl-state-oracle; explicitly run in Lean CI"]
fn finite_kernel_matches_live_lean_oracle() {
    let oracle = RefCell::new(Oracle::start());
    let comparisons = Cell::new(0usize);
    let mut outcomes = std::collections::BTreeSet::new();
    for (index, case) in directed_cases().into_iter().enumerate() {
        let request = case.request();
        let expected = oracle.borrow_mut().request(&request);
        let actual = native(&request);
        comparisons.set(comparisons.get() + 1);
        assert_eq!(actual, expected, "directed request={request}");
        assert_eq!(expected["installed"], index != 5, "directed acceptance");
        if index != 5 {
            assert_eq!(
                expected["threshold"]["status"],
                ["pending", "reached", "fault", "reached", "reached"][index]
            );
            if index != 2 {
                assert_eq!(
                    expected["observation"]["value"],
                    [
                        json!("e0"),
                        json!("e1"),
                        Value::Null,
                        json!(-3),
                        json!(true)
                    ][index]
                );
            }
        }
        outcomes.insert(
            expected["threshold"]["status"]
                .as_str()
                .unwrap_or("rejected")
                .to_owned(),
        );
    }
    assert_eq!(
        outcomes,
        ["fault", "pending", "reached", "rejected"]
            .into_iter()
            .map(String::from)
            .collect()
    );
    // Equal spelling is insufficient: bare p0 must not match a "p0" row.
    let mut symbolic = directed_cases()[1].request();
    symbolic["acts"][0][1][0][1] = json!(["symbol", "p0"]);
    let expected = oracle.borrow_mut().request(&symbolic);
    assert_eq!(
        native(&symbolic),
        expected,
        "symbolic field request={symbolic}"
    );
    assert_eq!(expected["observation"]["value"], "e0");
    assert_eq!(expected["threshold"]["status"], "pending");
    let mut symbolic_row = directed_cases()[1].request();
    symbolic_row["contributions"][0][1] = json!(["symbol", "p0"]);
    assert_eq!(
        oracle.borrow_mut().request(&symbolic_row),
        json!({"installed":false})
    );
    assert_eq!(native(&symbolic_row), json!({"installed":false}));
    let mut symbolic_projection = directed_cases()[3].request();
    symbolic_projection["projection"]["stable"] = json!(false);
    symbolic_projection["projection"]["rows"][0][1] = json!(["symbol", "p0"]);
    symbolic_projection["queries"] = Value::Null;
    assert_eq!(
        oracle.borrow_mut().request(&symbolic_projection),
        json!({"installed":false})
    );
    assert_eq!(native(&symbolic_projection), json!({"installed":false}));
    // Distinct incompatible named alternatives exercise the predecoded read
    // vector's right index; substituting reads[0] must change installation.
    let mut cached_pair = directed_cases()[0].clone();
    cached_pair.queries = Some(vec![(0, 1), (0, 2)]);
    let request = cached_pair.request();
    let expected = oracle.borrow_mut().request(&request);
    assert_eq!(expected["installed"], true);
    assert_eq!(native(&request), expected, "cached read indices: {request}");

    // R7 permits tightening state bounds, never raising their defaults.
    let mut request = directed_cases()[0].request();
    request["max-list"] = json!(65);
    let actual = native(&request);
    assert_eq!(oracle.borrow_mut().request(&request), actual, "R7 rejects max-list above default");
    assert_eq!(actual["installed"], false);
    request["max-list"] = json!(0);
    assert_eq!(oracle.borrow_mut().request(&request), native(&request), "R7 rejects zero max-list");
    request["max-list"] = json!(3);
    assert_eq!(oracle.borrow_mut().request(&request), native(&request), "configured limit rejects four elements");

    let mut config = proptest::test_runner::Config::default();
    if std::env::var_os("PROPTEST_CASES").is_none() {
        config.cases = 512;
    }
    config.failure_persistence = Some(Box::new(
        proptest::test_runner::FileFailurePersistence::Direct(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/state_kernel_oracle.proptest-regressions"
        )),
    ));
    let mut runner = proptest::test_runner::TestRunner::new(config);
    runner
        .run(&cases(), |generated| {
            let mut request = generated.request();
            for delivery in 0..3 {
                if delivery == 1 {
                    request["acts"].as_array_mut().unwrap().reverse();
                }
                if delivery == 2 {
                    let extra = request["acts"].as_array().unwrap().clone();
                    request["acts"].as_array_mut().unwrap().extend(extra);
                }
                let expected = oracle.borrow_mut().request(&request);
                let actual = native(&request);
                comparisons.set(comparisons.get() + 1);
                prop_assert_eq!(
                    actual,
                    expected,
                    "delivery={}, request={}",
                    delivery,
                    request
                );
            }
            Ok(())
        })
        .unwrap();
    eprintln!("Live Lean oracle: {} comparisons passed", comparisons.get());
}

#[derive(Clone, Debug)]
struct FreezeCase {
    finite: Case,
    fault: bool,
    graph: Vec<(bool, u8, u8, bool)>,
    with_threshold: bool,
}
fn freeze_cases() -> impl Strategy<Value = FreezeCase> {
    (
        cases(),
        any::<bool>(),
        proptest::collection::vec(
            (any::<bool>(), any::<u8>(), any::<u8>(), any::<bool>()),
            0..16,
        ),
        any::<bool>(),
    )
        .prop_map(|(finite, fault, graph, with_threshold)| FreezeCase {
            finite,
            fault,
            graph,
            with_threshold,
        })
}
impl FreezeCase {
    fn request(&self) -> Value {
        let mut request = self.finite.request();
        request["freeze"] = json!(self.fault);
        if !self.with_threshold {
            request["queries"] = Value::Null;
        }
        // Labels deliberately decrease along edges. They identify semantic
        // vertices rather than encode the test builder's causal order.
        let label = |id: usize| (self.graph.len() + 1 - id) * 17 + 11;
        let mut graph = vec![json!([label(0), "open", [], []])];
        for (offset, (close, a, b, two)) in self.graph.iter().enumerate() {
            let id = offset + 1;
            let parent = usize::from(*a) % id;
            let mut parents = vec![label(parent)];
            let second = usize::from(*b) % id;
            if *two && second != parent {
                parents.push(label(second));
            }
            let fields = if *close {
                vec![]
            } else {
                vec![
                    json!([
                        "phase",
                        if a & 128 == 0 {
                            json!(format!("p{}", a % 3))
                        } else {
                            json!(["symbol", format!("p{}", a % 3)])
                        }
                    ]),
                    json!(["amount", i16::from(*b) % 7 - 3]),
                    json!(["flag", two]),
                ]
            };
            graph.push(json!([
                label(id),
                if *close { "close" } else { "mark" },
                parents,
                fields
            ]));
        }
        request["acts"] = json!(graph);
        request
    }
}
fn freeze_directed() -> Vec<Value> {
    let mut finite = directed_cases()[0].clone();
    finite.fan = false;
    let mut base = finite.request();
    base["queries"] = Value::Null;
    base["freeze"] = json!(false);
    base["acts"] = json!([
        [0, "open", [], []],
        [
            1,
            "mark",
            [0],
            [["phase", "p0"], ["amount", 1], ["flag", false]]
        ],
        [2, "close", [1], []],
        [
            3,
            "mark",
            [0],
            [["phase", "p1"], ["amount", 0], ["flag", false]]
        ]
    ]);
    let mut fault = base.clone();
    fault["freeze"] = json!(true);
    fault["queries"] = json!(["e1"]);
    let mut repeated = base.clone();
    repeated["acts"]
        .as_array_mut()
        .unwrap()
        .push(json!([4, "close", [2], []]));
    let mut concurrent = base.clone();
    concurrent["acts"]
        .as_array_mut()
        .unwrap()
        .push(json!([4, "close", [0], []]));
    let mut top = base.clone();
    top["contributions"][0][2] = json!("e3");
    let mut no_freezer = base.clone();
    no_freezer["acts"].as_array_mut().unwrap().remove(2);
    let mut concurrent_fault = concurrent.clone();
    concurrent_fault["freeze"] = json!(true);
    concurrent_fault["queries"] = json!(["e1"]);
    let mut multi_parent = base.clone();
    multi_parent["acts"]
        .as_array_mut()
        .unwrap()
        .push(json!([4, "close", [2, 3], []]));
    let mut combined_fault = concurrent_fault.clone();
    combined_fault["contributions"][0][2] = json!("e3");
    let mut non_writer_fields = top.clone();
    non_writer_fields["acts"][2][3] = json!([["phase", "p0"]]);
    vec![
        base,
        fault,
        repeated,
        concurrent,
        top,
        no_freezer,
        concurrent_fault,
        multi_parent,
        combined_fault,
        non_writer_fields,
    ]
}

#[test]
#[ignore = "requires lake build cbcl-state-oracle; explicitly run in Lean CI"]
fn freeze_kernel_matches_live_lean_oracle() {
    let oracle = RefCell::new(Oracle::start());
    for (index, request) in freeze_directed().iter().enumerate() {
        let expected = oracle.borrow_mut().request(request);
        assert_eq!(
            native(request),
            expected,
            "directed freeze request={request}"
        );
        assert_eq!(expected["installed"], true);
        let status = match index {
            0 | 2 | 7 => "frozen",
            1 | 3 | 4 | 6 | 8 | 9 => "fault",
            5 => "snapshot",
            _ => unreachable!("unclassified directed freeze case"),
        };
        assert_eq!(expected["observation"]["status"], status);
        if index == 0 || index == 2 {
            assert_eq!(expected["observation"]["freezer"], 2);
            assert_eq!(expected["observation"]["excluded"], json!([3]));
            assert_eq!(expected["observation"]["value"], "e1");
        }
        if index == 9 {
            assert_eq!(expected["observation"]["evidence"], json!([1, 3]));
        }
        if index == 6 || index == 8 {
            assert_eq!(expected["observation"]["evidence"], json!([1, 2, 3, 4]));
        }
        if index == 1 || index == 6 {
            assert_eq!(expected["threshold"], expected["observation"]);
        }
    }
    let mut config = proptest::test_runner::Config::default();
    if std::env::var_os("PROPTEST_CASES").is_none() {
        config.cases = 512;
    }
    config.failure_persistence = Some(Box::new(
        proptest::test_runner::FileFailurePersistence::Direct(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/state_freeze_oracle.proptest-regressions"
        )),
    ));
    let mut runner = proptest::test_runner::TestRunner::new(config);
    let comparisons = Cell::new(0usize);
    runner
        .run(&freeze_cases(), |generated| {
            let mut request = generated.request();
            for delivery in 0..3 {
                if delivery == 1 {
                    request["acts"].as_array_mut().unwrap().reverse();
                }
                if delivery == 2 {
                    let extra = request["acts"].as_array().unwrap().clone();
                    request["acts"].as_array_mut().unwrap().extend(extra);
                }
                let expected = oracle.borrow_mut().request(&request);
                let actual = native(&request);
                comparisons.set(comparisons.get() + 1);
                prop_assert_eq!(
                    actual,
                    expected,
                    "delivery={}, request={}",
                    delivery,
                    request
                );
            }
            Ok(())
        })
        .unwrap();
    eprintln!(
        "Live Lean freeze oracle: {} comparisons passed",
        comparisons.get()
    );
}

#[test]
#[ignore = "requires lake build cbcl-state-oracle; explicitly run in Lean CI"]
fn oracle_rejects_ambiguous_or_nonclosed_graphs() {
    let mut oracle = Oracle::start();
    let base = freeze_directed()[0].clone();
    for malformed in [json!(["symbol", "p0)"]), json!(["symbol", "p0", "extra"])] {
        let mut bad_symbol = base.clone();
        bad_symbol["acts"][1][3][0][1] = malformed;
        assert!(oracle.response(&bad_symbol)["error"]
            .as_str()
            .unwrap()
            .contains("finite symbol"));
    }
    let mut cycle = base.clone();
    cycle["acts"][0][2] = json!([2]);
    assert!(oracle.response(&cycle)["error"]
        .as_str()
        .unwrap()
        .contains("causal cycle"));
    let mut missing = base.clone();
    missing["acts"].as_array_mut().unwrap().remove(1);
    assert!(oracle.response(&missing)["error"]
        .as_str()
        .unwrap()
        .contains("missing predecessor"));
    let mut duplicate = base.clone();
    let mut conflicting = duplicate["acts"][0].clone();
    conflicting[1] = json!("close");
    duplicate["acts"].as_array_mut().unwrap().push(conflicting);
    assert!(oracle.response(&duplicate)["error"]
        .as_str()
        .unwrap()
        .contains("conflicting identity"));
    let mut keyword = base;
    keyword["acts"][1][3]
        .as_array_mut()
        .unwrap()
        .push(json!(["phase", "p1"]));
    assert!(oracle.response(&keyword)["error"]
        .as_str()
        .unwrap()
        .contains("duplicate field"));
}

fn normalize_view(
    value: &Value,
    ids: &BTreeMap<String, u64>,
    render: impl Fn(&Value) -> Value,
) -> Value {
    if value["status"] == "fault" {
        return normalize_fault(value, ids);
    }
    if let Some(root) = value.get("frozen") {
        let mut excluded: Vec<_> = value["superseded"]
            .as_array()
            .unwrap()
            .iter()
            .map(|v| ids[v.as_str().unwrap()])
            .collect();
        excluded.sort();
        excluded.dedup();
        json!({"status":"frozen","freezer":ids[root.as_str().unwrap()],"excluded":excluded,"value":render(&value["value"])})
    } else {
        json!({"status":"snapshot","value":render(value)})
    }
}
fn native_nested(case: &Value) -> Value {
    let freeze = |field: &str, verb: &str, policy: &Value| {
        if policy.is_null() {
            String::new()
        } else {
            format!(
                "(freeze {field} {verb} {})",
                if *policy == true {
                    "fault"
                } else {
                    "supersede"
                }
            )
        }
    };
    let source = format!(
        "(define oracle-demo (cbcl) @a (:roles (owner))
      (extend open (to) :from owner :to owner (tell to))
      (extend mark (to amount) :from owner :to owner (tell to :amount amount))
      (extend close (to) :from owner :to owner (tell to))
      (extend seal (to) :from owner :to owner (tell to))
      (shape mark (require :amount number))
      (protocol (then begin open) (then open (repeat 16 mark close seal)))
      (state (source (events mark :amount)) (total (sum source)) {} {}))",
        freeze("source", "close", &case["source_freeze"]),
        freeze("total", "seal", &case["derived_freeze"])
    );
    let registry = state_exports::parse_and_install_dialect(&parse(&source).unwrap())
        .expect("generated events/sum profile installs");
    let d = registry.iter().last().unwrap();
    let (ids, acts) = graph_acts(case);
    let state: Value = serde_json::from_str(&render_json(&fold(
        d.state.as_ref().unwrap(),
        d.causal_protocol.as_ref(),
        &acts,
    )))
    .unwrap();
    let source = normalize_view(&state["source"], &ids, |events| {
        let mut entries: Vec<_> = events
            .as_object()
            .expect("events map")
            .iter()
            .map(|(id, event)| (ids[id], event.clone()))
            .collect();
        entries.sort_by_key(|(id, _)| *id);
        json!(entries)
    });
    let derived = normalize_view(&state["total"], &ids, Value::clone);
    json!({"installed":true,"source":source,"derived":derived})
}

#[derive(Clone, Debug)]
struct NestedCase {
    source_policy: Option<bool>,
    derived_policy: Option<bool>,
    graph: Vec<(u8, u8, u8, bool, i8)>,
}
fn nested_cases() -> impl Strategy<Value = NestedCase> {
    (
        proptest::option::of(any::<bool>()),
        proptest::option::of(any::<bool>()),
        proptest::collection::vec(
            (0u8..5, any::<u8>(), any::<u8>(), any::<bool>(), -8i8..12),
            0..16,
        ),
    )
        .prop_map(|(source_policy, derived_policy, graph)| NestedCase {
            source_policy,
            derived_policy,
            graph,
        })
}
impl NestedCase {
    fn request(&self) -> Value {
        let mut graph = vec![json!([0, "open", [], []])];
        for (offset, (kind, a, b, two, amount)) in self.graph.iter().enumerate() {
            let id = offset + 1;
            let parent = usize::from(*a) % id;
            let other = usize::from(*b) % id;
            let mut parents = vec![parent];
            if *two && parent != other {
                parents.push(other);
            }
            let verb = match kind {
                0 => "close",
                1 => "seal",
                _ => "mark",
            };
            let fields = if verb == "mark" {
                vec![json!(["amount", amount])]
            } else {
                vec![]
            };
            graph.push(json!([id, verb, parents, fields]));
        }
        json!({"profile":"events-sum","source_freeze":self.source_policy,"derived_freeze":self.derived_policy,"acts":graph})
    }
}
fn nested_directed() -> Vec<Value> {
    let base = json!({"profile":"events-sum","source_freeze":false,"derived_freeze":false,
        "acts":[[0,"open",[],[]],[1,"mark",[0],[["amount",2]]],[2,"close",[1],[]],
          [3,"mark",[0],[["amount",7]]],[4,"seal",[3],[]]]});
    let mut inherited_fault = base.clone();
    inherited_fault["source_freeze"] = json!(true);
    let mut own_fault = base.clone();
    own_fault["derived_freeze"] = json!(true);
    let mut both_fault = inherited_fault.clone();
    both_fault["derived_freeze"] = json!(true);
    let mut source_in_cut = base.clone();
    source_in_cut["acts"][4][2] = json!([2, 3]);
    let mut no_target = base.clone();
    no_target["acts"].as_array_mut().unwrap().pop();
    let mut plain = base.clone();
    plain["source_freeze"] = Value::Null;
    plain["derived_freeze"] = Value::Null;
    let mut concurrent_source = base.clone();
    concurrent_source["acts"]
        .as_array_mut()
        .unwrap()
        .push(json!([5, "close", [0], []]));
    vec![
        base,
        inherited_fault,
        own_fault,
        both_fault,
        source_in_cut,
        no_target,
        plain,
        concurrent_source,
    ]
}

#[test]
#[ignore = "requires lake build cbcl-state-oracle; explicitly run in Lean CI"]
fn nested_kernel_matches_live_lean_oracle() {
    let oracle = RefCell::new(Oracle::start());
    for (index, request) in nested_directed().iter().enumerate() {
        let expected = oracle.borrow_mut().request(request);
        assert_eq!(
            native(request),
            expected,
            "directed nested request={request}"
        );
        assert_eq!(expected["installed"], true);
        match index {
            0 => {
                assert_eq!(
                    expected["source"]["value"],
                    json!([[1,{"by":"@a","value":2}]])
                );
                assert_eq!(
                    expected["derived"],
                    json!({"status":"frozen","freezer":4,"excluded":[1],"value":7})
                );
            }
            1 | 2 | 3 | 7 => assert_eq!(expected["derived"]["status"], "fault"),
            4 => assert_eq!(expected["derived"]["value"], 2),
            5 => assert_eq!(expected["derived"], json!({"status":"snapshot","value":2})),
            6 => assert_eq!(expected["derived"], json!({"status":"snapshot","value":9})),
            _ => unreachable!(),
        }
    }
    let mut config = proptest::test_runner::Config::default();
    if std::env::var_os("PROPTEST_CASES").is_none() {
        config.cases = 512;
    }
    config.failure_persistence = Some(Box::new(
        proptest::test_runner::FileFailurePersistence::Direct(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/state_nested_oracle.proptest-regressions"
        )),
    ));
    let mut runner = proptest::test_runner::TestRunner::new(config);
    let comparisons = Cell::new(0usize);
    runner
        .run(&nested_cases(), |generated| {
            let mut request = generated.request();
            for delivery in 0..3 {
                if delivery == 1 {
                    request["acts"].as_array_mut().unwrap().reverse();
                }
                if delivery == 2 {
                    let extra = request["acts"].as_array().unwrap().clone();
                    request["acts"].as_array_mut().unwrap().extend(extra);
                }
                let expected = oracle.borrow_mut().request(&request);
                let actual = native(&request);
                comparisons.set(comparisons.get() + 1);
                prop_assert_eq!(
                    actual,
                    expected,
                    "delivery={}, request={}",
                    delivery,
                    request
                );
            }
            Ok(())
        })
        .unwrap();
    eprintln!(
        "Live Lean nested oracle: {} comparisons passed",
        comparisons.get()
    );
}

#[path = "state_kernel_oracle/context.rs"]
mod context;

#[path = "state_kernel_oracle/shape.rs"]
mod shape;

#[path = "state_kernel_oracle/render.rs"]
mod render;
