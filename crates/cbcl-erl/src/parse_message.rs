//! NIF: `parse_message/1` — see SPEC-009 §REQ-002 / CON-001.
//!
//! Decodes a `binary()` containing a CBCL message S-expression, parses it
//! through the strict pipeline (`cbcl_parser::parser::parse` then
//! `cbcl_parser::parse_message`), and encodes the resulting `Message` as
//! the CON-001 map term.
//!
//! Return shape: `{ok, Map :: map()} | {error, Reason :: binary()}`.
//!
//! Error categories (CON-001):
//!
//! | Failure                             | Reason binary                     |
//! |-------------------------------------|-----------------------------------|
//! | Non-UTF-8 input                     | `<<"invalid utf-8">>`             |
//! | `parser::parse` fails               | `<<"parse error: <desc>">>`       |
//! | `parse_message` fails               | `<<"message error: <desc>">>`     |
//! | `encoding::encode_message` fails    | `<<"message error: <desc>">>`     |
//!
//! `invalid utf-8` is a single fixed string (no description suffix); the
//! other three are colon-prefixed.
//!
//! Errors are surfaced as binaries (not atoms) because the descriptions
//! are free-form and would otherwise leak into the global atom table — a
//! known BEAM denial-of-service vector.
//!
//! # rustler 0.36 testing pattern
//!
//! Mirrors `verify_dialect.rs`: all real work lives in
//! [`parse_message_pure`] (env-free, plain Rust types). The `#[rustler::nif]`
//! wrapper does only term translation. `OwnedEnv::new()` panics outside a
//! BEAM host so we cannot exercise the wrapper from `cargo test`; the env-
//! free helper is unit-tested instead and the term path is covered by the
//! Erlang-side smoke tests.

use cbcl_core::message::Message;
use cbcl_parser::{parse, parse_message as parser_parse_message};
use rustler::types::atom;
use rustler::{Binary, Encoder, Env, OwnedBinary, Term};

use crate::encoding;
use crate::tracing_hooks;

/// Error category strings used both for the user-facing reason binary
/// and (via `tracing_hooks`) for the telemetry `category` field.
const CATEGORY_INVALID_UTF8: &str = "invalid utf-8";
const CATEGORY_PARSE_ERROR: &str = "parse error";
const CATEGORY_MESSAGE_ERROR: &str = "message error";

/// Pure-Rust core of `parse_message/1`. Returns the parsed `Message` on
/// success, or `(category, description)` on failure where `category` is
/// one of the constants above. For `invalid utf-8` the description is
/// empty (the user-facing reason is the bare category string with no
/// colon-prefixed description).
pub fn parse_message_pure(bytes: &[u8]) -> Result<Message, (&'static str, String)> {
    let input = core::str::from_utf8(bytes).map_err(|_| (CATEGORY_INVALID_UTF8, String::new()))?;
    let sexpr = parse(input).map_err(|e| (CATEGORY_PARSE_ERROR, format!("{e}")))?;
    let msg = parser_parse_message(&sexpr).map_err(|e| (CATEGORY_MESSAGE_ERROR, e))?;
    Ok(msg)
}

/// Build an Erlang binary from an owned Rust `String`. See
/// `verify_dialect::make_binary` for rationale on the OOM fallback.
fn make_binary<'a>(env: Env<'a>, s: String) -> Binary<'a> {
    match OwnedBinary::new(s.len()) {
        Some(mut owned) => {
            owned.as_mut_slice().copy_from_slice(s.as_bytes());
            Binary::from_owned(owned, env)
        }
        None => {
            let mut owned = OwnedBinary::new(3).expect("3-byte allocation");
            owned.as_mut_slice().copy_from_slice(b"oom");
            Binary::from_owned(owned, env)
        }
    }
}

/// Format the `(category, description)` pair into the CON-001 reason
/// binary. `invalid utf-8` is emitted bare; the others are prefixed
/// `"<category>: <description>"`.
fn format_reason(category: &str, description: &str) -> String {
    if category == CATEGORY_INVALID_UTF8 {
        category.to_string()
    } else {
        format!("{category}: {description}")
    }
}

fn err<'a>(env: Env<'a>, category: &str, description: &str) -> Term<'a> {
    let bin = make_binary(env, format_reason(category, description));
    (atom::error(), bin).encode(env)
}

/// Extract the human-readable description from a `rustler::Error::Term`
/// produced by `encoding::encode_message`. The encoder wraps the payload
/// in `Box<dyn Encoder>` which is neither `Debug` nor introspectable, so
/// we round-trip it through the BEAM env: encode the boxed payload to a
/// `Term`, then try to decode it as a `{atom, String}` tagged tuple
/// (the shape `encoding::encode_message` constructs for its
/// `Error::Term`). If the decode fails we fall back to a static
/// description so the user still gets a well-formed reason binary.
fn describe_boxed_encoder<'a>(env: Env<'a>, boxed: Box<dyn rustler::Encoder>) -> String {
    let term = boxed.encode(env);
    if let Ok((_, msg)) = term.decode::<(rustler::types::atom::Atom, String)>() {
        msg
    } else if let Ok(msg) = term.decode::<String>() {
        msg
    } else {
        String::from("<opaque encoder payload>")
    }
}

#[rustler::nif]
pub fn parse_message<'a>(env: Env<'a>, bytes: Binary<'a>) -> Term<'a> {
    // REQ-005: wrap the entire body in `panic_guard::catch` so a panic in
    // `cbcl-parser` / `cbcl-core` becomes `{error, <<"panic: ...">>}`
    // instead of crashing the BEAM scheduler (ADR-001).
    let input = bytes.as_slice();
    crate::panic_guard::catch(env, || {
        let span = tracing_hooks::enter("parse_message", input.len());
        match parse_message_pure(input) {
            Ok(msg) => match encoding::encode_message(env, &msg) {
                Ok(term) => {
                    tracing_hooks::exit_ok(span);
                    (atom::ok(), term).encode(env)
                }
                Err(rustler::Error::Term(boxed)) => {
                    // Defensive: `encode_message` no longer rejects any
                    // current Message variant (Simple/Wrapped/Dialect/Meta
                    // are all handled losslessly), but if a future variant
                    // is added without an encoder arm, the encoder may
                    // return a tagged tuple like `{message_error, <<"...">>}`.
                    // The boxed payload is `Box<dyn Encoder>`, opaque in
                    // Rust; we round-trip via the env to extract the
                    // description.
                    tracing_hooks::exit_err(span, "message_error");
                    let desc = describe_boxed_encoder(env, boxed);
                    err(env, CATEGORY_MESSAGE_ERROR, &desc)
                }
                Err(other) => {
                    tracing_hooks::exit_err(span, "encode_error");
                    err(env, CATEGORY_MESSAGE_ERROR, &format!("{other:?}"))
                }
            },
            Err((category, description)) => {
                // Map free-form category strings to the static slices
                // tracing_hooks::exit_err expects.
                let cat_static: &'static str = match category {
                    CATEGORY_INVALID_UTF8 => "invalid_utf8",
                    CATEGORY_PARSE_ERROR => "parse_error",
                    CATEGORY_MESSAGE_ERROR => "message_error",
                    _ => "unknown",
                };
                tracing_hooks::exit_err(span, cat_static);
                err(env, category, &description)
            }
        }
    })
}

#[cfg(test)]
mod tests {
    //! See `verify_dialect::tests` for why the env-free helper is the
    //! testable surface (rustler 0.36 + non-BEAM-hosted `cargo test`
    //! cannot allocate an `Env`).

    use super::*;
    use cbcl_core::message::{CorePerformative, Message, Performative};
    use cbcl_core::sexpr::SExpr;

    #[test]
    fn ok_on_valid_simple_tell() {
        // REQ-002: a Simple `(tell @bob "hello")` parses to a Tell.
        let msg = parse_message_pure(b"(tell @bob \"hello\")").expect("expected Ok");
        match msg {
            Message::Simple {
                performative,
                ref recipient,
                ref content,
                ..
            } => {
                assert_eq!(performative, Performative::Core(CorePerformative::Tell));
                assert_eq!(recipient.as_ref().and_then(|r| r.as_single()), Some("@bob"));
                // content should be the bare string atom "hello"
                match content {
                    SExpr::Atom(cbcl_core::sexpr::Atom::Str(s)) => {
                        assert_eq!(s, "hello");
                    }
                    other => panic!("expected Str content, got {other:?}"),
                }
            }
            other => panic!("expected Simple, got {other:?}"),
        }
    }

    #[test]
    fn invalid_utf8_returns_bare_category() {
        // CON-001: non-UTF-8 → "invalid utf-8" with empty description
        // (the format helper emits the bare category string for this case).
        let (cat, desc) = parse_message_pure(&[0xFFu8, 0xFE]).expect_err("utf8");
        assert_eq!(cat, CATEGORY_INVALID_UTF8);
        assert!(desc.is_empty());
        assert_eq!(format_reason(cat, &desc), "invalid utf-8");
    }

    #[test]
    fn parse_error_on_unclosed_list() {
        // CON-001: parser failure → "parse error: <desc>".
        let (cat, desc) = parse_message_pure(b"(unclosed").expect_err("parse");
        assert_eq!(cat, CATEGORY_PARSE_ERROR);
        assert!(!desc.is_empty(), "expected non-empty description");
        let formatted = format_reason(cat, &desc);
        assert!(
            formatted.starts_with("parse error: "),
            "expected 'parse error: ' prefix, got: {formatted}"
        );
    }

    #[test]
    fn message_error_on_unparseable_simple() {
        // An SExpr that lexes/parses cleanly but cannot be classified as
        // a Message. `(meta)` (zero-arg meta) is rejected by
        // `Message::try_from` because Meta requires the `dialect_def`
        // operand. If that ever starts succeeding, swap to another
        // input that fails `parse_message` after a successful `parse`.
        let (cat, desc) = parse_message_pure(b"(meta)").expect_err("message");
        assert_eq!(cat, CATEGORY_MESSAGE_ERROR);
        assert!(!desc.is_empty(), "expected non-empty description");
        let formatted = format_reason(cat, &desc);
        assert!(
            formatted.starts_with("message error: "),
            "expected 'message error: ' prefix, got: {formatted}"
        );
    }

    #[test]
    fn round_trip_simple_message() {
        // Parse → SExpr → re-parse → equal Message.
        let original = parse_message_pure(b"(tell @bob \"hello\")").expect("first parse ok");
        let sexpr: SExpr = SExpr::from(&original);
        let serialized = cbcl_core::serializer::serialize(&sexpr);
        let round_tripped = parse_message_pure(serialized.as_bytes()).expect("re-parse ok");
        assert_eq!(original, round_tripped);
    }

    #[test]
    fn format_reason_prefixes_non_utf8_categories() {
        assert_eq!(format_reason("invalid utf-8", ""), "invalid utf-8");
        // Even if a description is somehow supplied, "invalid utf-8" stays bare.
        assert_eq!(format_reason("invalid utf-8", "ignored"), "invalid utf-8");
        assert_eq!(
            format_reason("parse error", "at byte 0: oops"),
            "parse error: at byte 0: oops"
        );
        assert_eq!(
            format_reason("message error", "bad shape"),
            "message error: bad shape"
        );
    }
}
