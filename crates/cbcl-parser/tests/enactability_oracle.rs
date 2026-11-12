//! Rust against the executable Lean enactability oracle.
//!
//! The oracle (`lean-cbcl/EnactabilityOracle.lean`) answers with the very
//! definitions `LeanCbcl/DialectEnactability.lean` proves theorems about. It
//! receives `then` edges and questions, never Rust verdicts. This file sends
//! the same inputs through the Rust parser, the Rust R5 acyclicity check and
//! the Rust causal verifier, and compares.
//!
//! | Compared | Rust side | Lean side |
//! |---|---|---|
//! | built steps | `parse_protocol` | `roleOf`, `succsOf`, `graphOf` |
//! | acyclicity | `CausalProtocol::check_acyclicity` | `ProtocolGraph.checkAcyclicity` |
//! | one-step justification | `verify_causal`, searching citations | `R6DCFLPreservation.enabled` |
//! | arrival-order traces | `verify_causal`, replayed message by message | `CausalTrace` |
//! | unenactable steps | least fixed point over `verify_causal` | `unenactableSteps` |
//!
//! The Lean model quantifies over citation shapes: a step is justified when
//! SOME citation is `Valid`. `admits` therefore searches the citations the
//! verifier distinguishes: none, literal `begin`, each present message alone,
//! and one present message per name of the first `(all …)` group. A citation
//! outside that search which the verifier accepted would show up as a
//! mismatch with Lean answering `false`.
//!
//! Not covered: protocols with `(repeat …)`, which `verify_causal` routes to
//! a separate verifier; they are skipped in the corpus test. Role annotations,
//! casts and the admission monitor's resolved-first guard play no part.
//!
//! Build the oracle first: `cd lean-cbcl && lake build cbcl-enactability-oracle`.

use cbcl_core::message::{CausedBy, Message, Performative};
use cbcl_core::protocol::{
    verify_causal, CausalProtocol, NodeRef, VerificationResult, BEGIN_KEYWORD,
};
use cbcl_core::sexpr::{Atom, SExpr};
use cbcl_core::store::{ContentHash, MessageStore, ThreadId, ThreadedMessageStore};
use cbcl_parser::{parse, parse_dialect, parse_protocol};
use proptest::prelude::*;
use proptest::test_runner::{Config, TestRunner};
use serde_json::{json, Value};
use std::cell::RefCell;
use std::collections::BTreeSet;
use std::io::{BufRead, BufReader, Write};
use std::path::PathBuf;
use std::process::{Child, ChildStdin, ChildStdout, Command, Stdio};

type Edge = (NodeRef, NodeRef);

// ----------------------------------------------------------------
// Oracle transport
// ----------------------------------------------------------------

struct Oracle {
    child: Child,
    input: ChildStdin,
    output: BufReader<ChildStdout>,
    count: usize,
}

impl Oracle {
    fn new() -> Self {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../lean-cbcl/.lake/build/bin/cbcl-enactability-oracle");
        let mut child = Command::new(path)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
            .expect("build cbcl-enactability-oracle first");
        Self {
            input: child.stdin.take().unwrap(),
            output: BufReader::new(child.stdout.take().unwrap()),
            child,
            count: 0,
        }
    }

    fn ask(&mut self, request: &Value) -> Value {
        if std::env::var_os("CBCL_ORACLE_TRACE").is_some() {
            eprintln!("{request}");
        }
        writeln!(self.input, "{request}").unwrap();
        self.input.flush().unwrap();
        let mut line = String::new();
        self.output.read_line(&mut line).unwrap();
        self.count += 1;
        let answer: Value = serde_json::from_str(&line).expect("oracle returned JSON");
        assert!(
            answer.get("error").is_none(),
            "oracle error {answer} for {request}"
        );
        answer
    }
}

impl Drop for Oracle {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

// ----------------------------------------------------------------
// Encoding
// ----------------------------------------------------------------

fn sym(s: &str) -> SExpr {
    SExpr::Atom(Atom::Symbol(s.to_string()))
}

fn names(nr: &NodeRef) -> Vec<String> {
    nr.performatives().map(String::from).collect()
}

fn node_sexpr(nr: &NodeRef) -> SExpr {
    let group = |head: &str, set: &BTreeSet<String>| {
        SExpr::List(
            core::iter::once(sym(head))
                .chain(set.iter().map(|s| sym(s)))
                .collect(),
        )
    };
    match nr {
        NodeRef::Single(s) => sym(s),
        NodeRef::Any(set) => group("any", set),
        NodeRef::All(set) => group("all", set),
    }
}

fn node_json(nr: &NodeRef) -> Value {
    let group = |head: &str, set: &BTreeSet<String>| {
        Value::Array(
            core::iter::once(json!(head))
                .chain(set.iter().map(|s| json!(s)))
                .collect(),
        )
    };
    match nr {
        NodeRef::Single(s) => json!(["single", s]),
        NodeRef::Any(set) => group("any", set),
        NodeRef::All(set) => group("all", set),
    }
}

fn protocol_sexpr(edges: &[Edge]) -> SExpr {
    let mut items = vec![sym("protocol")];
    for (pred, succ) in edges {
        items.push(SExpr::List(vec![
            sym("then"),
            node_sexpr(pred),
            node_sexpr(succ),
        ]));
    }
    SExpr::List(items)
}

fn request(edges: &[Edge], words: &[Vec<String>], queries: &[(Vec<String>, String)]) -> Value {
    json!({
        "edges": edges.iter().map(|(p, s)| json!([node_json(p), node_json(s)])).collect::<Vec<_>>(),
        "words": words,
        "queries": queries.iter().map(|(seen, step)| json!({"seen": seen, "step": step})).collect::<Vec<_>>(),
    })
}

fn string_set(v: &Value) -> BTreeSet<String> {
    v.as_array()
        .unwrap()
        .iter()
        .map(|x| x.as_str().unwrap().to_string())
        .collect()
}

// ----------------------------------------------------------------
// The Rust verifier, asked the model's question
// ----------------------------------------------------------------

fn tid() -> ThreadId {
    ThreadId("enactability".into())
}

fn hash(i: usize) -> String {
    format!("h{i:04}")
}

/// A store holding one message per entry of `present`, in order.
fn store_of(present: &[String]) -> ThreadedMessageStore {
    let mut store = ThreadedMessageStore::new();
    for (i, perf) in present.iter().enumerate() {
        store.append(
            ContentHash(hash(i)),
            tid(),
            Message::Simple {
                performative: Performative::Custom(perf.clone()),
                recipient: None,
                content: SExpr::Atom(Atom::Str(format!("{perf}-{i}"))),
                params: Vec::new(),
                thread: None,
                sender: None,
                caused_by: None,
            },
        );
    }
    store
}

/// Does `verify_causal` return `Valid` for a message of performative `t`
/// under some citation, against a store holding `present`?
fn admits(proto: &CausalProtocol, present: &[String], t: &str) -> bool {
    let store = store_of(present);
    let thread = tid();
    let valid = |cb: Option<CausedBy>| {
        matches!(
            verify_causal(t, cb.as_ref(), &store, proto, &thread),
            VerificationResult::Valid
        )
    };
    if valid(None) || valid(Some(CausedBy::Begin)) {
        return true;
    }
    if (0..present.len()).any(|i| valid(Some(CausedBy::Single(hash(i))))) {
        return true;
    }
    let Some(step) = proto.steps.get(t) else {
        return false;
    };
    let Some(group) = step.predecessors.iter().find_map(|c| match c {
        NodeRef::All(set) => Some(set),
        _ => None,
    }) else {
        return false;
    };
    let mut hashes = Vec::new();
    for name in group {
        match present.iter().position(|p| p == name) {
            Some(i) => hashes.push(hash(i)),
            None => return false,
        }
    }
    hashes.sort();
    valid(Some(CausedBy::Multiple(hashes)))
}

/// Replay `w` as an arrival order: each message must be admitted by the
/// messages before it.
fn replays(proto: &CausalProtocol, w: &[String]) -> bool {
    let mut present = Vec::new();
    for t in w {
        if !admits(proto, &present, t) {
            return false;
        }
        present.push(t.clone());
    }
    true
}

/// Least fixed point of "admitted by what is already reachable", using the
/// real verifier. Returns the order found and the declared steps never
/// reached.
fn verifier_enactable(proto: &CausalProtocol) -> (Vec<String>, BTreeSet<String>) {
    let declared: BTreeSet<String> = proto.steps.keys().cloned().collect();
    let mut order: Vec<String> = Vec::new();
    loop {
        let fresh: Vec<String> = declared
            .iter()
            .filter(|t| !order.contains(t) && admits(proto, &order, t))
            .cloned()
            .collect();
        if fresh.is_empty() {
            break;
        }
        order.extend(fresh);
    }
    let reached: BTreeSet<String> = order.iter().cloned().collect();
    (order, declared.difference(&reached).cloned().collect())
}

// ----------------------------------------------------------------
// Comparison
// ----------------------------------------------------------------

/// Compare everything the oracle reports with Rust. `exact_succs` is false
/// when the edges were reconstructed from a parsed protocol, where the
/// grouping and order of successor clauses is not recoverable.
fn compare(
    oracle: &mut Oracle,
    proto: &CausalProtocol,
    edges: &[Edge],
    extra_words: &[Vec<String>],
    queries: &[(Vec<String>, String)],
    exact_succs: bool,
) -> Result<(), String> {
    let (order, unenactable) = verifier_enactable(proto);
    let mut words = vec![order.clone()];
    words.extend(extra_words.iter().cloned());
    let req = request(edges, &words, queries);
    let ans = oracle.ask(&req);
    let fail = |what: &str| Err(format!("{what}\nrequest {req}\nanswer {ans}"));

    // Built steps.
    let steps = ans["steps"].as_array().unwrap();
    let lean_names: BTreeSet<String> = steps
        .iter()
        .map(|s| s["name"].as_str().unwrap().to_string())
        .collect();
    if lean_names != proto.steps.keys().cloned().collect() {
        return fail("declared step names differ");
    }
    for s in steps {
        let step = &proto.steps[s["name"].as_str().unwrap()];
        let preds: Vec<Value> = step.predecessors.iter().map(node_json).collect();
        if s["preds"] != Value::Array(preds) {
            return fail("predecessor declarations differ");
        }
        let succs: Vec<String> = step.successors.iter().flat_map(names).collect();
        let succ_set: BTreeSet<String> = succs.iter().cloned().collect();
        if exact_succs && s["succs"] != json!(succs) {
            return fail("successors differ");
        }
        if string_set(&s["succs"]) != succ_set || string_set(&s["neighbors"]) != succ_set {
            return fail("successor sets differ");
        }
    }

    // R5 acyclicity.
    if ans["acyclic"].as_bool().unwrap() != proto.check_acyclicity().is_empty() {
        return fail("acyclicity verdicts differ");
    }

    // Enactability, with the Rust side computed by the real verifier.
    if string_set(&ans["unenactable"]) != unenactable {
        return fail("unenactable steps differ");
    }

    // Arrival-order traces.
    let traces = ans["traces"].as_array().unwrap();
    if traces[0] != json!(true) {
        return fail("Lean rejects the order the verifier produced");
    }
    for (w, lean) in words.iter().zip(traces) {
        if lean.as_bool().unwrap() != replays(proto, w) {
            return fail(&format!("trace verdicts differ on {w:?}"));
        }
    }

    // One-step justification.
    for ((seen, step), lean) in queries.iter().zip(ans["enabled"].as_array().unwrap()) {
        if lean.as_bool().unwrap() != admits(proto, seen, step) {
            return fail(&format!("justification differs for {step} given {seen:?}"));
        }
    }
    Ok(())
}

// ----------------------------------------------------------------
// Generators
// ----------------------------------------------------------------

const ALPHABET: [&str; 6] = ["a", "b", "c", "d", "e", "f"];

fn arb_name() -> impl Strategy<Value = String> {
    prop::sample::select(ALPHABET.to_vec()).prop_map(String::from)
}

fn arb_word_name() -> impl Strategy<Value = String> {
    prop_oneof![
        1 => Just(BEGIN_KEYWORD.to_string()),
        1 => Just("undeclared".to_string()),
        8 => arb_name(),
    ]
}

fn arb_group() -> impl Strategy<Value = BTreeSet<String>> {
    prop::collection::btree_set(arb_name(), 2..=3)
}

fn arb_succ() -> impl Strategy<Value = NodeRef> {
    prop_oneof![
        3 => arb_name().prop_map(NodeRef::Single),
        1 => arb_group().prop_map(NodeRef::Any),
        1 => arb_group().prop_map(NodeRef::All),
    ]
}

fn arb_pred() -> impl Strategy<Value = NodeRef> {
    prop_oneof![
        1 => Just(NodeRef::Single(BEGIN_KEYWORD.to_string())),
        4 => arb_succ(),
    ]
}

type Case = (Vec<Edge>, Vec<Vec<String>>, Vec<(Vec<String>, String)>);

fn arb_case() -> impl Strategy<Value = Case> {
    (
        prop::collection::vec((arb_pred(), arb_succ()), 1..8),
        prop::collection::vec(prop::collection::vec(arb_word_name(), 0..7), 0..4),
        prop::collection::vec(
            (
                prop::collection::vec(arb_word_name(), 0..5),
                arb_word_name(),
            ),
            0..6,
        ),
    )
}

// ----------------------------------------------------------------
// Tests
// ----------------------------------------------------------------

#[test]
#[ignore = "requires `lake build cbcl-enactability-oracle`"]
fn generated_protocols_agree_with_lean() {
    let oracle = RefCell::new(Oracle::new());
    let mut runner = TestRunner::new(Config::default());
    runner
        .run(&arb_case(), |(edges, words, queries)| {
            let proto = parse_protocol(&protocol_sexpr(&edges)).unwrap();
            compare(
                &mut oracle.borrow_mut(),
                &proto,
                &edges,
                &words,
                &queries,
                true,
            )
            .map_err(TestCaseError::fail)
        })
        .unwrap();
    assert!(oracle.borrow().count > 0);
}

#[test]
#[ignore = "requires `lake build cbcl-enactability-oracle`"]
fn corpus_dialects_agree_with_lean() {
    let mut oracle = Oracle::new();
    let dir = PathBuf::from(concat!(env!("CARGO_MANIFEST_DIR"), "/../../dialects"));
    let mut entries: Vec<PathBuf> = std::fs::read_dir(&dir)
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().is_some_and(|x| x == "cbcl"))
        .collect();
    entries.sort();
    let mut checked = Vec::new();
    let mut skipped_repeat = Vec::new();
    for path in entries {
        let file = path.file_name().unwrap().to_string_lossy().to_string();
        let text = std::fs::read_to_string(&path).unwrap();
        let dialect = parse_dialect(&parse(&text).unwrap()).unwrap();
        let Some(proto) = dialect.causal_protocol else {
            continue;
        };
        // `verify_causal` routes repeat-expanded protocols to a separate verifier.
        if proto.steps.keys().any(|n| n.contains('#')) {
            skipped_repeat.push(file);
            continue;
        }
        // One edge per recorded predecessor clause reproduces the predecessor
        // declarations exactly and the successors up to grouping and order.
        let edges: Vec<Edge> = proto
            .steps
            .iter()
            .flat_map(|(t, step)| {
                step.predecessors
                    .iter()
                    .map(move |c| (c.clone(), NodeRef::Single(t.clone())))
            })
            .collect();
        let queries: Vec<(Vec<String>, String)> = proto
            .steps
            .keys()
            .map(|t| (Vec::new(), t.clone()))
            .collect();
        compare(&mut oracle, &proto, &edges, &[], &queries, false)
            .unwrap_or_else(|e| panic!("{file}: {e}"));
        checked.push(file);
    }
    assert!(
        checked.len() >= 8,
        "only {} corpus protocols checked: {checked:?}; skipped for repeat: {skipped_repeat:?}",
        checked.len()
    );
}
