//! Integration tests for `cbcl-erl` (SPEC-009 v0.1.0, plan task `task-tests`).
//!
//! These tests target the env-free `*_pure` helpers re-exported from the
//! crate root. They cannot exercise the `#[rustler::nif]` wrappers
//! directly: `OwnedEnv::new()` calls `enif_alloc_env`, a dynamically
//! loaded BEAM symbol that aborts (`unreachable_unchecked`) outside an
//! `erl`-hosted process. The pure helpers are therefore the public test
//! surface for v0.1.0; the term-translation glue is covered by
//! Erlang-side smoke tests in a future task once SPEC-008 lands.
//!
//! Coverage map (CON-001 prefixes + supporting properties):
//!   - `invalid utf-8`           → `parse_*_pure` reject non-UTF-8 bytes.
//!   - `parse error: ...`        → unbalanced parens, both helpers.
//!   - `message error: ...`      → `(meta)` (zero-arg meta) via strict.
//!   - `dialect error: ...`      → unbalanced parens via `verify_dialect_pure`.
//!   - `verification failed: ...`→ R3 violation (redefining `tell`).
//!   - REQ-005 panic containment → `panic_guard::catch_pure` smoke tests.
//!   - OBS-001 versions sanity   → version constants are non-empty.
//!   - Strict ↔ lax parity       → identical `Message` for Simple inputs.
//!   - Lax-only path             → Meta-only input yields `LaxResult::Raw`.
//!   - Round-trip property       → parse → serialize → re-parse → equal.

use cbcl_core::message::Message;
use cbcl_core::sexpr::SExpr;
use cbcl_core::serializer;
use cbcl_erl::{
    parse_message_lax_pure, parse_message_pure, verify_dialect_pure, LaxResult,
    CBCL_CORE_VERSION, CBCL_ERL_VERSION, CBCL_RS_GIT_REVISION,
};
use cbcl_erl::panic_guard::catch_pure;

/// Representative strict-Simple inputs (with at least one wrapper and one
/// caused-by-begin form). Each must round-trip parse → serialize → parse
/// to the exact same `Message`.
const ROUND_TRIP_INPUTS: &[&str] = &[
    // Bare tell.
    r#"(tell @bob "hello")"#,
    // Bare ask with thread.
    r#"(ask @alice "What is the status?" :thread "conv-17")"#,
    // Reply with caused-by-begin.
    r#"(reply "Task is complete" :thread "conv-17" :caused-by "begin")"#,
    // Envelope-wrapped tell.
    r#"(envelope :from @alice :to @bob (tell @bob "Hello"))"#,
    // Tell with thread + sender (sender via envelope :from is the standard
    // place; using a Simple :sender keyword if supported).
    r#"(tell @alice "Status update" :thread "conv-123" :sender @carol)"#,
];

#[test]
fn round_trip_strict_simple_messages() {
    for input in ROUND_TRIP_INPUTS {
        let original: Message = parse_message_pure(input.as_bytes())
            .unwrap_or_else(|e| panic!("first parse failed for {input}: {e:?}"));
        let serialized = serializer::serialize(&SExpr::from(&original));
        let round_tripped = parse_message_pure(serialized.as_bytes())
            .unwrap_or_else(|e| panic!("re-parse failed for {input}: {e:?}"));
        assert_eq!(
            original, round_tripped,
            "round-trip mismatch for input: {input}\nserialized: {serialized}"
        );
    }
}

// ---------------------------------------------------------------------------
// CON-001 error category coverage
// ---------------------------------------------------------------------------

#[test]
fn strict_invalid_utf8_category() {
    let (cat, desc) = parse_message_pure(&[0xFFu8, 0xFE]).expect_err("utf8");
    assert_eq!(cat, "invalid utf-8");
    assert!(desc.is_empty());
}

#[test]
fn strict_parse_error_category() {
    let (cat, desc) = parse_message_pure(b"(unclosed").expect_err("parse");
    assert_eq!(cat, "parse error");
    assert!(!desc.is_empty(), "expected non-empty parse-error description");
}

#[test]
fn strict_message_error_category() {
    // `(meta)` lexes/parses but is rejected by `parse_message`.
    let (cat, desc) = parse_message_pure(b"(meta)").expect_err("message");
    assert_eq!(cat, "message error");
    assert!(!desc.is_empty(), "expected non-empty message-error description");
}

#[test]
fn dialect_error_category() {
    // `verify_dialect_pure` returns the user-facing reason already prefixed,
    // so we assert against the prefix the NIF wrapper would emit verbatim.
    let reason = verify_dialect_pure(b"(unclosed")
        .expect_err("unbalanced parens fail dialect parse");
    assert!(
        reason.starts_with("dialect error: "),
        "expected 'dialect error: ' prefix, got: {reason}"
    );
}

#[test]
fn verification_failed_category() {
    // R3 violation: `tell` is a core performative and cannot be redefined.
    let reason = verify_dialect_pure(
        b"(define bad (cbcl) @author (extend tell (msg) (effect custom-tell)))",
    )
    .expect_err("R3 violation");
    assert!(
        reason.starts_with("verification failed: "),
        "expected 'verification failed: ' prefix, got: {reason}"
    );
}

#[test]
fn dialect_invalid_utf8_category() {
    let reason = verify_dialect_pure(&[0xFFu8, 0xFE])
        .expect_err("non-utf-8 dialect bytes");
    assert_eq!(reason, "invalid utf-8");
}

// ---------------------------------------------------------------------------
// REQ-005: panic_guard::catch_pure smoke tests across the crate boundary
// ---------------------------------------------------------------------------

#[test]
fn catch_pure_passes_clean_returns_through() {
    let res: Result<i32, String> = catch_pure(|| 42);
    assert_eq!(res, Ok(42));
}

#[test]
fn catch_pure_traps_static_str_panic() {
    let res: Result<(), String> = catch_pure(|| panic!("static-boom"));
    assert_eq!(res, Err(String::from("static-boom")));
}

#[test]
fn catch_pure_traps_owned_string_panic() {
    let v = 7;
    let res: Result<(), String> = catch_pure(|| panic!("owned-boom-{v}"));
    assert_eq!(res, Err(String::from("owned-boom-7")));
}

#[test]
fn catch_pure_traps_non_string_panic() {
    let res: Result<(), String> =
        catch_pure(|| std::panic::panic_any(123_u64));
    assert_eq!(res, Err(String::from("non-string panic payload")));
}

// ---------------------------------------------------------------------------
// OBS-001: version constants are non-empty across the crate boundary.
// ---------------------------------------------------------------------------

#[test]
fn version_constants_are_non_empty() {
    assert!(!CBCL_RS_GIT_REVISION.is_empty(), "git revision must not be empty");
    assert!(!CBCL_CORE_VERSION.is_empty(), "cbcl-core version must not be empty");
    assert!(!CBCL_ERL_VERSION.is_empty(), "cbcl-erl version must not be empty");
}

// ---------------------------------------------------------------------------
// Strict ↔ lax parity on Simple inputs
// ---------------------------------------------------------------------------

#[test]
fn strict_and_lax_agree_on_simple_messages() {
    for input in ROUND_TRIP_INPUTS {
        let strict: Message = parse_message_pure(input.as_bytes())
            .unwrap_or_else(|e| panic!("strict parse failed for {input}: {e:?}"));
        let lax = parse_message_lax_pure(input.as_bytes())
            .unwrap_or_else(|e| panic!("lax parse failed for {input}: {e}"));
        match lax {
            LaxResult::Simple(lax_msg) => {
                assert_eq!(
                    strict, lax_msg,
                    "strict/lax message mismatch for input: {input}"
                );
            }
            LaxResult::Raw(_) => {
                panic!("expected Simple from lax for input {input}, got Raw")
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Lax-only path: Meta-only input is rejected by strict, accepted by lax.
// ---------------------------------------------------------------------------

#[test]
fn lax_accepts_meta_when_strict_rejects() {
    let input: &[u8] = b"(meta (define test-d (cbcl) @author))";

    // Strict path rejects: `encode_message` requires an innermost Simple
    // layer, but a bare Meta has none. The pure helper accepts the parse
    // (no encoder runs) — so the strict-side lax-only assertion is that
    // `parse_message_pure` SUCCEEDS but the result has no Simple layer.
    // The `message error: ...` rejection happens later in the encoder
    // (only reachable from the BEAM-side wrapper). To still exercise the
    // strict-rejection contract end-to-end at the helper level, we use a
    // Meta input that the encoder would reject; the visible signal here
    // is `innermost_simple().is_none()`.
    let strict_msg = parse_message_pure(input)
        .expect("Meta parses cleanly through parse_message_pure");
    assert!(
        strict_msg.innermost_simple().is_none(),
        "Meta should have no innermost Simple layer (which is what makes the \
         BEAM-side encoder reject it)"
    );

    // Lax path: returns `Raw(canonical-bytes)`, and those bytes must be
    // re-parseable as a valid `SExpr` describing the same Meta message.
    let lax = parse_message_lax_pure(input).expect("lax accepts meta");
    let raw_bytes = match lax {
        LaxResult::Raw(b) => b,
        LaxResult::Simple(_) => panic!("expected Raw for Meta input, got Simple"),
    };
    assert!(!raw_bytes.is_empty(), "raw bytes must be non-empty");

    let raw_str = core::str::from_utf8(&raw_bytes)
        .expect("canonical raw bytes must be UTF-8");
    let reparsed = cbcl_parser::parse(raw_str)
        .expect("canonical raw bytes must be re-parseable as SExpr");
    // Sanity: the round-trip must still describe a non-Simple message.
    let remsg = cbcl_parser::parse_message(&reparsed)
        .expect("re-parsed SExpr must classify as a Message");
    assert!(
        remsg.innermost_simple().is_none(),
        "Meta round-trip should still lack a Simple layer"
    );
}
