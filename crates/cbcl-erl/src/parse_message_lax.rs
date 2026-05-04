//! NIF: `parse_message_lax/1` — see SPEC-009 §REQ-003 (lax variant).
//!
//! # v0.1.0 status: behavioural alias of `parse_message/1`
//!
//! REQ-003 mandates that this NIF exist as a distinct export. `cbcl-parser`
//! does not yet expose a separate lax-mode message parser — its public
//! surface is `parse`, `parse_message`, `run_pipeline`, and
//! `run_pipeline_full`, none of which differ in strict-vs-lax behaviour at
//! the message level. Earlier drafts of cbcl-erl tried to invent a
//! relaxation by collapsing non-Simple inputs to `{ok, {raw, <<bytes>>}}`,
//! but `encoding::encode_message` now encodes every `Message` variant
//! losslessly (Simple / Wrapped / Dialect / Meta) — so any divergence from
//! strict would make lax *less* informative than strict, which is the
//! opposite of REQ-003's intent.
//!
//! For v0.1.0 this NIF is therefore a behavioural alias of
//! `parse_message/1`: same return shape, same error categories. SPEC-009
//! §11 lists the open questions that block a meaningful divergence:
//!
//!   1. **Scheduler safety strategy** — whether the binding runs on dirty
//!      schedulers, uses time-budgeted reductions, or is fundamentally a
//!      best-effort entrypoint. The lax variant in particular invites
//!      inputs that exercise heavier code paths.
//!   2. **Error categorisation granularity** — today errors are loose
//!      strings (`"parse error: ..."`, etc.). A real lax mode needs
//!      principled categorisation so callers can tell "rejected by
//!      strict, accepted by lax" from "rejected by both" without
//!      string-matching.
//!
//! Until those land, BEAM consumers can call either NIF interchangeably.
//! The export is kept distinct so a future amendment can grow real lax
//! semantics without breaking consumer call sites.
//!
//! Return shape:
//!
//! ```text
//! {ok, MessageMap}              % CON-001 map for any Message variant.
//! {error, <<reason::binary>>}   % parse / message / utf-8 error.
//! ```

use cbcl_core::message::Message;
use cbcl_parser::{parse, parse_message};
use rustler::types::atom;
use rustler::types::atom::Atom as ErlAtom;
use rustler::{Binary, Encoder, Env, OwnedBinary, Term};

use crate::encoding;
use crate::tracing_hooks;

/// Pure-Rust core of `parse_message_lax/1`. Identical to
/// `parse_message_pure` for v0.1.0; see module docs for the rationale.
/// Reason strings (`"parse error: ..."`, `"message error: ..."`,
/// `"invalid utf-8"`) match the strict NIF byte-for-byte so callers that
/// already pattern-match on strict reasons keep working.
pub fn parse_message_lax_pure(bytes: &[u8]) -> Result<Message, String> {
    let input = core::str::from_utf8(bytes).map_err(|_| String::from("invalid utf-8"))?;
    let sexpr = parse(input).map_err(|e| format!("parse error: {e}"))?;
    parse_message(&sexpr).map_err(|e| format!("message error: {e}"))
}

/// Build an Erlang binary from a byte slice. Mirrors the helper in
/// `verify_dialect.rs`; duplicated here to keep each NIF module
/// self-contained without enlarging the crate's pub API.
fn make_binary<'a>(env: Env<'a>, bytes: &[u8]) -> Binary<'a> {
    match OwnedBinary::new(bytes.len()) {
        Some(mut owned) => {
            owned.as_mut_slice().copy_from_slice(bytes);
            Binary::from_owned(owned, env)
        }
        None => {
            let mut owned = OwnedBinary::new(3).expect("3-byte allocation");
            owned.as_mut_slice().copy_from_slice(b"oom");
            Binary::from_owned(owned, env)
        }
    }
}

fn err<'a>(env: Env<'a>, msg: String) -> Term<'a> {
    let bin = make_binary(env, msg.as_bytes());
    (atom::error(), bin).encode(env)
}

#[rustler::nif]
pub fn parse_message_lax<'a>(env: Env<'a>, bytes: Binary<'a>) -> Term<'a> {
    // REQ-005: wrap the entire body in `panic_guard::catch` so a panic in
    // `cbcl-parser` / `cbcl-core` becomes `{error, <<"panic: ...">>}`
    // instead of crashing the BEAM scheduler (ADR-001).
    let input = bytes.as_slice();
    crate::panic_guard::catch(env, || {
        let span = tracing_hooks::enter("parse_message_lax", input.len());
        match parse_message_lax_pure(input) {
            Ok(msg) => match encoding::encode_message(env, &msg) {
                Ok(map) => {
                    tracing_hooks::exit_ok(span);
                    (atom::ok(), map).encode(env)
                }
                // The encoder no longer rejects any Message variant, but a
                // future encoder change could surface tagged errors. Keep
                // the arm as belt-and-braces.
                Err(rustler::Error::Term(boxed)) => {
                    tracing_hooks::exit_err(span, "message_error");
                    let term = boxed.encode(env);
                    if let Ok((tag, msg)) = term.decode::<(ErlAtom, String)>() {
                        if matches!(
                            tag.to_term(env).atom_to_string().as_deref(),
                            Ok("message_error")
                        ) {
                            return err(env, format!("message error: {msg}"));
                        }
                    }
                    err(env, String::from("message error: unknown"))
                }
                Err(_) => {
                    tracing_hooks::exit_err(span, "encode_error");
                    err(env, String::from("message error: unknown"))
                }
            },
            Err(reason) => {
                // Map free-form reason prefix to the static category strings
                // tracing_hooks::exit_err expects (mirrors parse_message.rs).
                let cat_static: &'static str = if reason == "invalid utf-8" {
                    "invalid_utf8"
                } else if reason.starts_with("parse error") {
                    "parse_error"
                } else if reason.starts_with("message error") {
                    "message_error"
                } else {
                    "unknown"
                };
                tracing_hooks::exit_err(span, cat_static);
                err(env, reason)
            }
        }
    })
}

#[cfg(test)]
mod tests {
    //! See `verify_dialect.rs` and `encoding.rs` for the rationale: the
    //! `#[nif]`-attributed wrapper cannot be exercised from `cargo test`
    //! because `OwnedEnv::new()` aborts outside a BEAM host. We test the
    //! env-free `parse_message_lax_pure` instead; the wrapper is glue.

    use super::*;

    #[test]
    fn simple_message_returns_simple_message() {
        // Strict-equivalent path: a Simple message parses cleanly.
        let msg = parse_message_lax_pure(b"(tell @bob \"hi\")").expect("simple tell parses");
        assert!(
            msg.innermost_simple().is_some(),
            "expected innermost Simple layer"
        );
    }

    #[test]
    fn meta_only_message_parses_to_meta_variant() {
        // v0.1.0: lax is an alias of strict, and strict's encoder now
        // handles Meta natively (returning a {type => meta, ...} map),
        // so lax should likewise accept the Meta variant — the parser
        // produces a Message::Meta which the encoder will surface
        // losslessly. The earlier `LaxResult::Raw` stopgap is gone.
        let msg =
            parse_message_lax_pure(b"(meta (define test-d (cbcl) @author))").expect("meta parses");
        assert!(
            msg.innermost_simple().is_none(),
            "Meta has no Simple layer (encoder uses the meta map shape)"
        );
        assert!(matches!(msg, Message::Meta { .. }));
    }

    #[test]
    fn parse_error_surfaces_parse_error_prefix() {
        let err =
            parse_message_lax_pure(b"(unclosed").expect_err("unbalanced parens fail to parse");
        assert!(
            err.starts_with("parse error: "),
            "expected parse error prefix, got: {err}"
        );
    }

    #[test]
    fn message_error_surfaces_message_error_prefix() {
        // Valid S-expression that is not a valid message — `parse` accepts,
        // `parse_message` rejects. `(meta)` (zero-arg) is the same input
        // the strict module uses for the message-error category test, so
        // both NIFs share a fixture and stay in lockstep on rejection.
        let err = parse_message_lax_pure(b"(meta)").expect_err("zero-arg meta fails message parse");
        assert!(
            err.starts_with("message error: "),
            "expected message error prefix, got: {err}"
        );
    }

    #[test]
    fn invalid_utf8_returns_exact_reason() {
        let err =
            parse_message_lax_pure(&[0xFFu8, 0xFE]).expect_err("non-utf-8 bytes are rejected");
        assert_eq!(err, "invalid utf-8");
    }
}
