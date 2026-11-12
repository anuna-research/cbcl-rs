//! Differential parity tests for dialect enactability.
//!
//! Companion to `crates/cbcl-core/tests/lean_parity.rs`. The Lean file
//! `lean-cbcl/LeanCbcl/DialectEnactability.lean` proves that a protocol built
//! from `then` edges which passes R5 acyclicity is enactable: one
//! arrival-order trace contains every declared step. That proof is stated
//! over a model of what `parse_protocol` builds (`graphOf`, `roleOf`), written
//! from the parser source. These tests compare that model, and the properties
//! proved about it, with the Rust parser at the value level.
//!
//! | Test fn | Lean declaration |
//! |---|---|
//! | `built_model_matches_parser` | `graphOf`, `roleOf` (`succsOf`, `predsOf`) |
//! | `parser_output_mirrors` | `built_mirrors` |
//! | `parser_rejects_small_groups` | hypothesis of `built_satisfiable` (no empty `(any)`) |
//! | `acyclic_implies_enactable` | `built_enactable`, `enactable_of_checkAcyclicity` |
//! | `enactable_order_is_a_causal_trace` | `enactable_occurs`, `iter_trace` |
//! | `examples_agree_with_lean` | `Examples.cyclic_enactable`, `Examples.deadlock_unenactable`, `Examples.fanIn_enactable` |
//! | `corpus_dialects_are_enactable` | `built_enactable` on `dialects/*.cbcl` |
//!
//! What these tests do not establish: `justified` below is a transcription of
//! the Lean `R6DCFLPreservation.justified`, which itself models
//! `verify_causal`. The tests here do not run `verify_causal` on messages, so
//! they check the parser model and the enactability argument, not the
//! verifier model. `enactability_oracle.rs` does that comparison, against the
//! executable Lean definitions. `(repeat …)` is covered only through the corpus, where the parser
//! has already expanded it.

use cbcl_core::protocol::{CausalProtocol, NodeRef, BEGIN_KEYWORD};
use cbcl_core::sexpr::{Atom, SExpr};
use cbcl_parser::{parse, parse_dialect, parse_protocol};
use proptest::prelude::*;
use std::collections::BTreeSet;
use std::path::PathBuf;

type Edge = (NodeRef, NodeRef);

fn sym(s: &str) -> SExpr {
    SExpr::Atom(Atom::Symbol(s.to_string()))
}

fn names(nr: &NodeRef) -> Vec<String> {
    nr.performatives().map(String::from).collect()
}

fn node_sexpr(nr: &NodeRef) -> SExpr {
    match nr {
        NodeRef::Single(s) => sym(s),
        NodeRef::Any(set) => SExpr::List(
            core::iter::once(sym("any"))
                .chain(set.iter().map(|s| sym(s)))
                .collect(),
        ),
        NodeRef::All(set) => SExpr::List(
            core::iter::once(sym("all"))
                .chain(set.iter().map(|s| sym(s)))
                .collect(),
        ),
    }
}

/// `(protocol (then pred succ) …)`, one `then` clause per edge.
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

// ----------------------------------------------------------------
// The Lean model, transcribed
// ----------------------------------------------------------------

/// Lean `edgeNames`, as a set.
fn edge_names(edges: &[Edge]) -> BTreeSet<String> {
    edges
        .iter()
        .flat_map(|(p, s)| names(p).into_iter().chain(names(s)))
        .collect()
}

/// Lean `predsOf`: the predecessor clause of each edge whose successor
/// clause mentions `n`, in edge order.
fn model_preds(edges: &[Edge], n: &str) -> Vec<NodeRef> {
    edges
        .iter()
        .filter(|(_, s)| names(s).iter().any(|x| x == n))
        .map(|(p, _)| p.clone())
        .collect()
}

/// Lean `succsOf`, before flattening to names: the successor clause of each
/// edge whose predecessor clause mentions `n`, in edge order.
fn model_succs(edges: &[Edge], n: &str) -> Vec<NodeRef> {
    edges
        .iter()
        .filter(|(p, _)| names(p).iter().any(|x| x == n))
        .map(|(_, s)| s.clone())
        .collect()
}

/// Lean `R6DCFLPreservation.justified`: root, literal `begin`, a single
/// citation into the pooled `Single`/`Any` names, or fan-in over the first
/// `All` declaration.
fn justified(preds: &[NodeRef], seen: &BTreeSet<String>) -> bool {
    if preds.is_empty() {
        return true;
    }
    let pooled: Vec<&str> = preds
        .iter()
        .flat_map(|c| match c {
            NodeRef::Single(s) => vec![s.as_str()],
            NodeRef::Any(set) => set.iter().map(String::as_str).collect(),
            NodeRef::All(_) => vec![],
        })
        .collect();
    if pooled.contains(&BEGIN_KEYWORD) || pooled.iter().any(|x| seen.contains(*x)) {
        return true;
    }
    match preds.iter().find_map(|c| match c {
        NodeRef::All(set) => Some(set),
        _ => None,
    }) {
        Some(group) => group.iter().all(|x| seen.contains(x)),
        None => false,
    }
}

/// Lean `enabled`: an undeclared name is unconstrained.
fn enabled(proto: &CausalProtocol, seen: &BTreeSet<String>, t: &str) -> bool {
    match proto.steps.get(t) {
        None => true,
        Some(step) => justified(&step.predecessors, seen),
    }
}

/// Lean `enactable` and the trace of `iter_trace`: undeclared referenced
/// names first, then one batch per round, each batch justified by what
/// earlier rounds produced. Returns the order and the declared steps never
/// reached (Lean `unenactableSteps`).
fn enactable_order(proto: &CausalProtocol) -> (Vec<String>, BTreeSet<String>) {
    let declared: BTreeSet<String> = proto.steps.keys().cloned().collect();
    let mut order: Vec<String> = proto
        .steps
        .values()
        .flat_map(|s| s.predecessors.iter().flat_map(names))
        .filter(|x| !declared.contains(x))
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();
    let mut seen: BTreeSet<String> = order.iter().cloned().collect();
    for _ in 0..declared.len() {
        let fresh: Vec<String> = declared
            .iter()
            .filter(|t| !seen.contains(*t) && enabled(proto, &seen, t))
            .cloned()
            .collect();
        if fresh.is_empty() {
            break;
        }
        seen.extend(fresh.iter().cloned());
        order.extend(fresh);
    }
    let unenactable = declared.difference(&seen).cloned().collect();
    (order, unenactable)
}

/// Lean `CausalTrace`: every step justified by the names strictly before it.
fn is_causal_trace(proto: &CausalProtocol, w: &[String]) -> bool {
    let mut seen = BTreeSet::new();
    for t in w {
        if !enabled(proto, &seen, t) {
            return false;
        }
        seen.insert(t.clone());
    }
    true
}

/// Lean `Mirrors`: if step `t` names `x` as a predecessor, `x` lists `t` as a
/// successor.
fn mirrors(proto: &CausalProtocol) -> bool {
    proto.steps.iter().all(|(t, step)| {
        step.predecessors.iter().flat_map(names).all(|x| {
            proto
                .steps
                .get(&x)
                .is_some_and(|sx| sx.successors.iter().flat_map(names).any(|s| &s == t))
        })
    })
}

// ----------------------------------------------------------------
// Generators
// ----------------------------------------------------------------

const ALPHABET: [&str; 6] = ["a", "b", "c", "d", "e", "f"];

fn arb_name() -> impl Strategy<Value = String> {
    prop::sample::select(ALPHABET.to_vec()).prop_map(String::from)
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

fn arb_edges() -> impl Strategy<Value = Vec<Edge>> {
    prop::collection::vec((arb_pred(), arb_succ()), 1..8)
}

// ----------------------------------------------------------------
// Tests
// ----------------------------------------------------------------

proptest! {
    /// `graphOf` / `roleOf`: the parser records, for each name, exactly the
    /// successor clauses of the edges whose predecessor mentions it and the
    /// predecessor clauses of the edges whose successor mentions it, in edge
    /// order, and declares a step for every name mentioned.
    #[test]
    fn built_model_matches_parser(edges in arb_edges()) {
        let proto = parse_protocol(&protocol_sexpr(&edges)).unwrap();
        let declared: BTreeSet<String> = proto.steps.keys().cloned().collect();
        prop_assert_eq!(&declared, &edge_names(&edges));
        for (n, step) in &proto.steps {
            prop_assert_eq!(&step.performative, n);
            prop_assert_eq!(&step.predecessors, &model_preds(&edges, n));
            prop_assert_eq!(&step.successors, &model_succs(&edges, n));
        }
    }

    /// `built_mirrors`.
    #[test]
    fn parser_output_mirrors(edges in arb_edges()) {
        let proto = parse_protocol(&protocol_sexpr(&edges)).unwrap();
        prop_assert!(mirrors(&proto));
    }

    /// `built_enactable`: a parser-built protocol that passes R5 acyclicity
    /// has no unenactable step.
    #[test]
    fn acyclic_implies_enactable(edges in arb_edges()) {
        let proto = parse_protocol(&protocol_sexpr(&edges)).unwrap();
        if proto.check_acyclicity().is_empty() {
            let (order, unenactable) = enactable_order(&proto);
            prop_assert!(unenactable.is_empty(), "unenactable: {:?}", unenactable);
            for t in proto.steps.keys() {
                prop_assert!(order.contains(t));
            }
        }
    }

    /// `enactable_occurs`: whatever the checker accepts, acyclic or not, is
    /// produced in an order that is an arrival-order trace.
    #[test]
    fn enactable_order_is_a_causal_trace(edges in arb_edges()) {
        let proto = parse_protocol(&protocol_sexpr(&edges)).unwrap();
        let (order, _) = enactable_order(&proto);
        prop_assert!(is_causal_trace(&proto, &order));
    }
}

/// The hypothesis of `built_satisfiable`: no predecessor clause is an empty
/// `(any)`. The parser rejects `any` and `all` groups with fewer than two
/// members.
#[test]
fn parser_rejects_small_groups() {
    for head in ["any", "all"] {
        for members in [vec![], vec!["a"]] {
            let group = SExpr::List(
                core::iter::once(sym(head))
                    .chain(members.iter().map(|m| sym(m)))
                    .collect(),
            );
            let proto = SExpr::List(vec![
                sym("protocol"),
                SExpr::List(vec![sym("then"), group, sym("b")]),
            ]);
            assert!(
                parse_protocol(&proto).is_err(),
                "({head} {members:?}) was accepted"
            );
        }
    }
}

fn single(s: &str) -> NodeRef {
    NodeRef::Single(s.to_string())
}

fn group(members: &[&str]) -> BTreeSet<String> {
    members.iter().map(|m| m.to_string()).collect()
}

/// The Lean examples, built through the parser.
#[test]
fn examples_agree_with_lean() {
    // `Examples.fanIn_enactable`: z needs both x and y.
    let fan_in = [
        (single("begin"), single("x")),
        (single("begin"), single("y")),
        (NodeRef::All(group(&["x", "y"])), single("z")),
    ];
    let proto = parse_protocol(&protocol_sexpr(&fan_in)).unwrap();
    assert!(proto.check_acyclicity().is_empty());
    assert!(enactable_order(&proto).1.is_empty());

    // `Examples.cyclic_enactable`: x may cite begin or y; y cites x. Cyclic,
    // and still enactable.
    let cyclic = [
        (single("begin"), single("x")),
        (single("y"), single("x")),
        (single("x"), single("y")),
    ];
    let proto = parse_protocol(&protocol_sexpr(&cyclic)).unwrap();
    assert!(!proto.check_acyclicity().is_empty());
    assert!(enactable_order(&proto).1.is_empty());

    // `Examples.deadlock_unenactable`: x and y wait on each other.
    let deadlock = [(single("y"), single("x")), (single("x"), single("y"))];
    let proto = parse_protocol(&protocol_sexpr(&deadlock)).unwrap();
    assert!(!proto.check_acyclicity().is_empty());
    assert_eq!(enactable_order(&proto).1, group(&["x", "y"]));
}

/// `built_enactable` on the shipped dialects: every one that declares a
/// causal protocol mirrors, has no empty group, passes R5 acyclicity, and has
/// one arrival-order trace containing every declared step.
#[test]
fn corpus_dialects_are_enactable() {
    let dir = PathBuf::from(concat!(env!("CARGO_MANIFEST_DIR"), "/../../dialects"));
    let mut checked = Vec::new();
    let mut entries: Vec<PathBuf> = std::fs::read_dir(&dir)
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().is_some_and(|x| x == "cbcl"))
        .collect();
    entries.sort();
    for path in entries {
        let file = path.file_name().unwrap().to_string_lossy().to_string();
        let text = std::fs::read_to_string(&path).unwrap();
        let sexpr = parse(&text).unwrap_or_else(|e| panic!("{file}: {e:?}"));
        let dialect = parse_dialect(&sexpr).unwrap_or_else(|e| panic!("{file}: {e}"));
        let Some(proto) = dialect.causal_protocol else {
            continue;
        };
        assert!(
            mirrors(&proto),
            "{file}: successor graph does not mirror predecessors"
        );
        for step in proto.steps.values() {
            for clause in step.predecessors.iter().chain(step.successors.iter()) {
                if let NodeRef::Any(set) | NodeRef::All(set) = clause {
                    assert!(
                        !set.is_empty(),
                        "{file}: empty group at {}",
                        step.performative
                    );
                }
            }
        }
        assert!(
            proto.check_acyclicity().is_empty(),
            "{file}: fails R5 acyclicity"
        );
        let (order, unenactable) = enactable_order(&proto);
        assert!(
            unenactable.is_empty(),
            "{file}: unenactable steps {unenactable:?}"
        );
        assert!(
            is_causal_trace(&proto, &order),
            "{file}: order is not a causal trace"
        );
        checked.push(file);
    }
    assert!(
        checked.len() >= 10,
        "only {} corpus protocols checked: {checked:?}",
        checked.len()
    );
}
