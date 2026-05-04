//! Differential parity tests for dialect-clause dispatch (REQ-516 / TEST-518).
//!
//! Companion to `crates/cbcl-core/tests/lean_parity.rs`. The Lean theorems
//!
//!   * `LeanCbcl/DCFLPreservation.lean :: protocol_dispatch_specifies`
//!   * `LeanCbcl/DCFLPreservation.lean :: shape_dispatch_currently_unwired`
//!
//! pin the operational semantics of `applyKeywordClause` for the
//! `protocol` and `shape` keyword tokens: a single string-like value on
//! the `protocol` keyword sets the integrity-protocol field; the `shape`
//! keyword routes to the catch-all error branch (it is not yet wired
//! into the dialect parser).
//!
//! These two tests assert that the Rust dialect parser agrees with the
//! Lean dispatch lemmas at the *keyword* form (`(:protocol …)`,
//! `(:shape …)`). The *symbol* forms `(protocol (then …))` (causal
//! protocol declaration, REQ-200) and `(shape …)` (shape constraint,
//! REQ-220) go through dedicated parsers (`protocol_parser`,
//! `shape_parser`) and are not currently mechanised at the dispatch
//! layer in Lean — they are out of scope for these parity tests but
//! covered by the round-trip checks in `cbcl-core/tests/lean_parity.rs`.
//!
//! See SPEC-005 §"REQ-516", §"TEST-516", and SPEC-002 §"REQ-209" /
//! §"REQ-225" — both are now `verified-by: lean (placeholder)` because
//! the named `dcfl_preserved_under_*` theorems reduce to
//! `allSExpr_isSExpr _`; the substantive content lives in the dispatch
//! lemmas these tests cross-check against the Rust side.

use cbcl_core::sexpr::{Atom, SExpr};
use cbcl_parser::dialect_parser::parse_dialect;

fn sym(s: &str) -> SExpr {
    SExpr::Atom(Atom::Symbol(s.to_string()))
}

fn kw(s: &str) -> SExpr {
    SExpr::Atom(Atom::Keyword(s.to_string()))
}

fn str_expr(s: &str) -> SExpr {
    SExpr::Atom(Atom::Str(s.to_string()))
}

fn list(items: Vec<SExpr>) -> SExpr {
    SExpr::List(items)
}

/// REQ-516 — `DCFLPreservation.lean :: protocol_dispatch_specifies`.
///
/// `applyKeywordClause acc "protocol" [v]` with `sexprToStringLike? v = some s`
/// pins the result to `.ok { acc with protocol := some s }`. The Rust
/// counterpart at `dialect_parser::parse_clause` (line 189) takes a
/// `(:protocol "ed25519")` clause and writes `Some("ed25519")` into the
/// dialect's integrity-protocol field — exactly what the Lean theorem
/// asserts.
#[test]
fn req516_protocol_keyword_dispatch_matches_lean() {
    let definition = list(vec![
        sym("define"),
        sym("test-dialect"),
        list(vec![sym("cbcl")]),
        sym("@author"),
        list(vec![kw("protocol"), str_expr("ed25519")]),
    ]);
    let dialect = parse_dialect(&definition).expect("dialect parses");
    assert_eq!(
        dialect.protocol,
        Some(String::from("ed25519")),
        "Lean `protocol_dispatch_specifies` predicts integrity-protocol = Some(\"ed25519\")",
    );
}

/// REQ-516 — `DCFLPreservation.lean :: shape_dispatch_currently_unwired`.
///
/// `applyKeywordClause acc "shape" vals` routes to the catch-all error
/// branch in Lean. The Rust counterpart in `dialect_parser::parse_clause`
/// likewise rejects the `(:shape …)` keyword form via the catch-all
/// `_ => return Err("unknown keyword clause: :shape")` arm. When `shape`
/// is wired into the keyword dispatch in a later patch, this test should
/// be replaced by a `req516_shape_keyword_dispatch_matches_lean`
/// analogue and the Lean lemma promoted to `shape_dispatch_specifies`.
#[test]
fn req516_shape_keyword_dispatch_currently_unwired() {
    let definition = list(vec![
        sym("define"),
        sym("test-dialect"),
        list(vec![sym("cbcl")]),
        sym("@author"),
        list(vec![kw("shape"), list(vec![])]),
    ]);
    let result = parse_dialect(&definition);
    let err = result.expect_err("`(:shape ...)` keyword form should error");
    assert!(
        err.contains("shape"),
        "Lean `shape_dispatch_currently_unwired` predicts catch-all error referencing `shape`; got: {err}",
    );
}
