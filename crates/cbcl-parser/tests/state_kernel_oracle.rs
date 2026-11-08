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

    fn request(&mut self, case: &Value) -> Value {
        writeln!(self.input, "{case}").unwrap();
        self.input.flush().unwrap();
        let line = self
            .output
            .recv_timeout(std::time::Duration::from_secs(10))
            .expect("Lean oracle exited or failed to respond within 10 seconds")
            .expect("Lean oracle stdout error");
        let reply: Value = serde_json::from_str(&line).expect("Lean JSON response");
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
        proptest::collection::vec((0u8..3, -3i8..4, any::<bool>()), 0..18),
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
            "acts": self.history.iter().enumerate().map(|(i,(p,n,b))| json!([i, [["phase",format!("p{p}")],["amount",n],["flag",b]]])).collect::<Vec<_>>()})
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
    format!("(define oracle-demo (cbcl) @a (extend open (to) (tell to)) (extend mark (to phase amount flag) (tell to :phase phase :amount amount :flag flag)) (shape mark (require :phase string) (require :amount number) (require :flag bool)) (protocol (then begin open) (then open mark)) (state (lattice rank (elements {names}) (bottom e0) (top {}) (join {joins})) (value (lift mark (into rank) (contribute {rows}) {projection})) {threshold}))",table["top"].as_str().unwrap())
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
fn native(case: &Value) -> Value {
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
    let open = make_act("(lang oracle-demo (open @all :caused-by begin :thread \"t\" :from @a))");
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
    let state: Value = serde_json::from_str(&render_json(&fold(
        d.state.as_ref().unwrap(),
        d.causal_protocol.as_ref(),
        &acts,
    )))
    .unwrap();
    let observation = if state["value"]["status"] == "fault" {
        normalize_fault(&state["value"], &ids)
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
