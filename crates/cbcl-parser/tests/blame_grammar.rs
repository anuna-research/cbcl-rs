//! Round-trip and grammar conformance tests for the REQ-233 violation-error form.
//!
//! REQ-233 claims violation errors are themselves valid CBCL messages, parseable
//! by the same DCFL parser. These tests assert that claim by emitting via
//! `ViolationError::to_sexpr` and parsing back via `cbcl_parser::parser::parse`,
//! then comparing structurally.

use cbcl_core::blame::{BlameParty, ViolationError, ViolationKind};
use cbcl_core::protocol::CausalViolation;
use cbcl_core::sexpr::{Atom, SExpr};
use cbcl_core::shape::ShapeViolation;
use cbcl_parser::parser::parse;

fn fully_populated_shape_error() -> ViolationError {
    let sv = ShapeViolation {
        rule: String::from("require :route string"),
        field: Some(String::from(":route")),
        expected: Some(String::from("string")),
        found: Some(String::from("number")),
        detail: String::from(":route expected string, found number"),
    };
    ViolationError::from_shape_violation(&sv, Some(String::from("sha256:msg")), None, None)
        .with_recipient("@sender")
        .with_verifier("@receiver")
        .with_dialect_context(
            "logistics",
            Some("@consortium"),
            Some("sha256:abc"),
            Some("track-shipment"),
        )
}

fn populated_causal_error() -> ViolationError {
    let cv = CausalViolation::InvalidPredecessor {
        caused_by: String::from("sha256:pred"),
        expected: alloc_vec(&["pause"]),
        found: String::from("ack"),
    };
    ViolationError::from_causal_violation(&cv, Some(String::from("sha256:msg")), None)
        .with_recipient("@sender")
        .with_verifier("@receiver")
        .with_dialect_context(
            "compaction",
            Some("@author"),
            Some("sha256:def"),
            Some("ack"),
        )
}

fn alloc_vec(items: &[&str]) -> Vec<String> {
    items.iter().map(|s| String::from(*s)).collect()
}

#[test]
fn shape_violation_emits_round_trippable_sexpr() {
    let err = fully_populated_shape_error();
    let emitted = format!("{}", err.to_sexpr());

    // Parser must accept the emission without error.
    let reparsed = parse(&emitted).expect("emitted form must parse");

    // And the reparse must equal the original SExpr structurally.
    assert_eq!(reparsed, err.to_sexpr());
}

#[test]
fn causal_violation_emits_round_trippable_sexpr() {
    let err = populated_causal_error();
    let emitted = format!("{}", err.to_sexpr());
    let reparsed = parse(&emitted).expect("emitted form must parse");
    assert_eq!(reparsed, err.to_sexpr());
}

#[test]
fn r5_violation_emits_round_trippable_sexpr() {
    let err = ViolationError::from_r5_violation(
        "broken",
        &alloc_vec(&["cycle: a → b → a", "step c unreachable"]),
    )
    .with_recipient("@installer")
    .with_verifier("@receiver");
    let emitted = format!("{}", err.to_sexpr());
    let reparsed = parse(&emitted).expect("emitted form must parse");
    assert_eq!(reparsed, err.to_sexpr());
}

#[test]
fn unsatisfiable_shape_emits_round_trippable_sexpr() {
    let err = ViolationError::from_unsatisfiable_shape(
        "logistics",
        "require :route string AND require :route number",
        "no value can be both string and number",
    )
    .with_recipient("@installer")
    .with_verifier("@receiver");
    let emitted = format!("{}", err.to_sexpr());
    let reparsed = parse(&emitted).expect("emitted form must parse");
    assert_eq!(reparsed, err.to_sexpr());
}

#[test]
fn shape_violation_grammar_positional_structure() {
    // REQ-233 ABNF requires:
    //   structural-error = "(" "error" WS recipient WS violation-type 1*(WS error-field) ")"
    let err = fully_populated_shape_error();
    let sexpr = err.to_sexpr();

    let items = match sexpr {
        SExpr::List(items) => items,
        _ => panic!("error must be a list"),
    };

    // [0]: "error" symbol
    assert!(matches!(&items[0], SExpr::Atom(Atom::Symbol(s)) if s == "error"));
    // [1]: recipient symbol
    assert!(matches!(&items[1], SExpr::Atom(Atom::Symbol(s)) if s == "@sender"));
    // [2]: violation-type, quoted string
    assert!(matches!(&items[2], SExpr::Atom(Atom::Str(s)) if s == "shape-violation"));

    // [3..]: keyword/value pairs (and the final :blame-chain list).
    // Walk pairs and confirm every keyword found is in the ABNF set.
    let allowed_keywords: &[&str] = &[
        "dialect",
        "dialect-author",
        "dialect-hash",
        "performative",
        "rule",
        "field",
        "expected",
        "found",
        "detail",
        "blamed",
        "verifier",
        "message-hash",
        "caused-by",
        "blame-chain",
    ];
    let mut i = 3;
    while i < items.len() {
        let kw = match &items[i] {
            SExpr::Atom(Atom::Keyword(k)) => k.as_str(),
            other => panic!("expected keyword at index {i}, got {other:?}"),
        };
        assert!(
            allowed_keywords.contains(&kw),
            ":{kw} is not in the REQ-233 ABNF",
        );
        i += 2; // skip value
    }
}

#[test]
fn causal_violation_grammar_positional_structure() {
    let err = populated_causal_error();
    let sexpr = err.to_sexpr();
    let items = match sexpr {
        SExpr::List(items) => items,
        _ => panic!("error must be a list"),
    };
    assert!(matches!(&items[0], SExpr::Atom(Atom::Symbol(s)) if s == "error"));
    assert!(matches!(&items[1], SExpr::Atom(Atom::Symbol(_))));
    assert!(matches!(&items[2], SExpr::Atom(Atom::Str(s)) if s == "causal-violation"));
}

#[test]
fn unspecified_recipient_defaults_to_unknown() {
    let sv = ShapeViolation {
        rule: String::from("require :x string"),
        field: None,
        expected: None,
        found: None,
        detail: String::from("test"),
    };
    let err = ViolationError::from_shape_violation(&sv, None, None, None);
    let sexpr = err.to_sexpr();
    let items = match sexpr {
        SExpr::List(items) => items,
        _ => panic!("error must be a list"),
    };
    assert!(matches!(&items[1], SExpr::Atom(Atom::Symbol(s)) if s == "@unknown"));
}

#[test]
fn ignored_field_kind_in_struct_does_not_appear_in_output() {
    // We retain `thread_id` on the struct for internal use, but it is
    // explicitly excluded from the wire form (not in the REQ-233 ABNF).
    let cv = CausalViolation::MissingCausedBy;
    let err = ViolationError::from_causal_violation(&cv, None, Some(String::from("t1")));
    assert_eq!(err.thread_id.as_deref(), Some("t1"));
    let emitted = format!("{}", err.to_sexpr());
    assert!(!emitted.contains(":thread"));
    // And it must still round-trip.
    let _ = parse(&emitted).expect("parses despite internal thread_id");
}

#[test]
fn violation_kind_in_emitted_form_is_quoted_string() {
    // Each kind emits its dashed string form.
    for (kind, expected) in [
        (ViolationKind::Shape, "shape-violation"),
        (ViolationKind::Causal, "causal-violation"),
        (ViolationKind::R5, "r5-violation"),
    ] {
        assert_eq!(kind.as_violation_type(), expected);
    }
}

#[test]
fn blamed_field_reflects_first_blame_entry() {
    // shape -> sender
    let err = fully_populated_shape_error();
    assert_eq!(err.blame_chain[0].party, BlameParty::Sender);
    let emitted = format!("{}", err.to_sexpr());
    assert!(emitted.contains(":blamed sender"));

    // unsatisfiable shape -> dialect-author
    let err = ViolationError::from_unsatisfiable_shape("d", "x", "y");
    assert_eq!(err.blame_chain[0].party, BlameParty::DialectAuthor);
    let emitted = format!("{}", err.to_sexpr());
    assert!(emitted.contains(":blamed dialect-author"));

    // r5 -> dialect-author (first entry)
    let err = ViolationError::from_r5_violation("d", &alloc_vec(&["bad"]));
    assert_eq!(err.blame_chain[0].party, BlameParty::DialectAuthor);
    let emitted = format!("{}", err.to_sexpr());
    assert!(emitted.contains(":blamed dialect-author"));
}
