//! NIF: `parse_message_lax/1` — see SPEC-009 §REQ-003 (lax variant).
//!
//! # v0.1.0 placeholder — what "lax" means here
//!
//! `cbcl-parser` does **not** currently expose a separate lax-mode message
//! parser. Its public surface is `parse`, `parse_message`, `run_pipeline`,
//! and `run_pipeline_full`; the two pipeline functions differ in whether
//! they enforce R1–R5 verification with a registry/store, not in any
//! strict-vs-lax distinction at the message level. Because of that, the
//! v0.1.0 cbcl-erl lax NIF must invent (and document) a meaningful
//! relaxation versus its strict sibling.
//!
//! The relaxation chosen here:
//!
//! - Strict (`parse_message/1`): when the parsed `Message` has no `Simple`
//!   layer at the bottom (e.g. a bare `Meta` definition), `encoding::
//!   encode_message` returns `Err(message_error, "non-simple message at
//!   innermost layer")`. The NIF surfaces this as
//!   `{error, <<"message error: ...">>}`.
//! - Lax (this NIF): identical behaviour for `Simple`-bearing messages.
//!   For non-`Simple` messages it instead returns the success tuple
//!   `{ok, {raw, <<canonical-bytes>>}}`, where the binary is the
//!   canonical S-expression serialisation of the parsed `Message`. This
//!   lets the BEAM consumer see that a message exists and inspect it as
//!   raw text even though the structured CON-001 map shape is not yet
//!   defined for non-Simple messages.
//!
//! The `{raw, <<bytes>>}` shape is a **v0.1.0 stopgap**. SPEC-009 §11 lists
//! two open questions that block a real implementation and that should be
//! resolved before this NIF is hardened:
//!
//!   1. **Scheduler safety strategy** — whether the binding runs on dirty
//!      schedulers, uses time-budgeted reductions, or is fundamentally a
//!      best-effort entrypoint. The lax variant in particular invites
//!      inputs that exercise heavier code paths.
//!   2. **Error categorisation granularity** — today errors are loose
//!      strings (`"parse error: ..."`, `"message error: ..."`,
//!      `"invalid utf-8"`). A real lax mode needs principled
//!      categorisation so callers can tell "rejected by strict, accepted
//!      by lax" from "rejected by both" without string-matching.
//!
//! Until those land, treat the `{raw, _}` tuple as opaque — its inner
//! shape may change once REQ-003 grows a real definition or cbcl-parser
//! exposes a lax entrypoint. **No `is_raw/1` or other consumer-side
//! contract helpers are exported**, deliberately, so that nobody binds
//! production code to this transient shape.
//!
//! Return shape:
//!
//! ```text
//! {ok, MessageMap}                  % Simple-bearing input (CON-001 map).
//! {ok, {raw, <<canonical-bytes>>}}  % non-Simple input (v0.1.0 stopgap).
//! {error, <<reason::binary>>}       % parse / message / utf-8 error.
//! ```

use cbcl_core::message::Message;
use cbcl_core::sexpr::SExpr;
use cbcl_core::serializer;
use cbcl_parser::{parse, parse_message};
use rustler::types::atom;
use rustler::types::atom::Atom as ErlAtom;
use rustler::{Binary, Encoder, Env, OwnedBinary, Term};

use crate::encoding;

/// Outcome of the env-free lax helper. The NIF wrapper translates this
/// into the Erlang shape; tests assert against the variants directly.
///
/// Why an enum and not a `Result<Term, _>`: building BEAM terms requires
/// an `Env<'a>`, which `cargo test` cannot fabricate on rustler 0.36
/// (see `verify_dialect.rs` and `encoding.rs` for the same finding).
/// Keeping the helper env-free lets us unit-test it directly.
#[derive(Debug)]
pub enum LaxResult {
    /// Parsed message has a `Simple` layer at the innermost position;
    /// strict and lax behave identically and produce the CON-001 map.
    Simple(Message),
    /// Parsed message has no `Simple` layer (e.g. a `Meta` define).
    /// Strict rejects with "non-simple message at innermost layer";
    /// lax accepts and returns the canonical text serialisation as
    /// bytes (UTF-8). Wrapped in `{raw, <<bytes>>}` by the NIF wrapper.
    Raw(Vec<u8>),
}

/// Pure-Rust core of `parse_message_lax/1`. See module docs for the
/// strict-vs-lax contract. Returns:
///
/// - `Ok(LaxResult::Simple(msg))` — caller should encode `msg` via
///   `encoding::encode_message`.
/// - `Ok(LaxResult::Raw(bytes))` — caller should wrap as `{raw, <<bytes>>}`.
/// - `Err(reason)` — caller should wrap as `{error, <<reason>>}`. The
///   reason strings (`"parse error: ..."`, `"message error: ..."`,
///   `"invalid utf-8"`) match the strict NIF byte-for-byte so callers
///   that already pattern-match on the strict reasons keep working.
pub fn parse_message_lax_pure(bytes: &[u8]) -> Result<LaxResult, String> {
    let input = core::str::from_utf8(bytes).map_err(|_| String::from("invalid utf-8"))?;
    let sexpr = parse(input).map_err(|e| format!("parse error: {e}"))?;
    let msg = parse_message(&sexpr).map_err(|e| format!("message error: {e}"))?;

    // Mirror strict's "non-simple" gate without invoking the encoder
    // (the encoder needs an Env). `innermost_simple` is the same gate
    // the encoder uses internally — see `encoding::encode_message`.
    if msg.innermost_simple().is_some() {
        Ok(LaxResult::Simple(msg))
    } else {
        let canonical = serializer::serialize(&SExpr::from(&msg));
        Ok(LaxResult::Raw(canonical.into_bytes()))
    }
}

/// Build an Erlang binary from an owned Rust `String` / byte vector.
/// Mirrors the helper in `verify_dialect.rs`; duplicated here to keep
/// each NIF module self-contained without enlarging the crate's pub API.
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
        match parse_message_lax_pure(input) {
            Ok(LaxResult::Simple(msg)) => match encoding::encode_message(env, &msg) {
                Ok(map) => (atom::ok(), map).encode(env),
                // The encoder can still return Err for shapes that slipped
                // past `innermost_simple` (today: none, but guard anyway so
                // future encoder changes don't silently turn into panics).
                Err(rustler::Error::Term(boxed)) => {
                    // boxed encodes to {message_error, <<"...">>}. Re-shape
                    // it into our user-facing {error, <<"message error: ...">>}.
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
                Err(_) => err(env, String::from("message error: unknown")),
            },
            Ok(LaxResult::Raw(bytes_out)) => {
                let raw_atom =
                    ErlAtom::from_str(env, "raw").expect("'raw' is ASCII");
                let bin = make_binary(env, &bytes_out);
                let inner = (raw_atom, bin).encode(env);
                (atom::ok(), inner).encode(env)
            }
            Err(reason) => err(env, reason),
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
    fn simple_message_returns_simple_variant() {
        // Strict-equivalent path: a Simple message yields `LaxResult::Simple`,
        // which the NIF wrapper would then encode via `encode_message`.
        let res = parse_message_lax_pure(b"(tell @bob \"hi\")")
            .expect("simple tell parses");
        match res {
            LaxResult::Simple(msg) => {
                assert!(
                    msg.innermost_simple().is_some(),
                    "expected innermost Simple layer"
                );
            }
            LaxResult::Raw(_) => panic!("expected Simple, got Raw"),
        }
    }

    #[test]
    fn meta_only_message_returns_raw_variant() {
        // The lax-only path: strict's `encode_message` rejects this
        // because there's no Simple at the innermost layer; lax must
        // accept and return the canonical re-serialisation as bytes.
        let res = parse_message_lax_pure(b"(meta (define test-d (cbcl) @author))")
            .expect("meta parses");
        match res {
            LaxResult::Raw(bytes) => {
                let s = core::str::from_utf8(&bytes).expect("utf-8 canonical");
                // Round-trip property: parse(serialize(e)) == Ok(e).
                // We don't assert the exact byte form (canonical
                // serialisation is the parser/serializer's contract,
                // not this NIF's), but it must be re-parseable and
                // describe a Meta message.
                let reparsed = parse(s).expect("canonical re-parses");
                let remsg = parse_message(&reparsed).expect("reparses as message");
                assert!(
                    remsg.innermost_simple().is_none(),
                    "Meta round-trip should still lack a Simple layer"
                );
            }
            LaxResult::Simple(_) => {
                panic!("expected Raw for Meta-only message, got Simple")
            }
        }
    }

    #[test]
    fn parse_error_surfaces_parse_error_prefix() {
        let err = parse_message_lax_pure(b"(unclosed")
            .expect_err("unbalanced parens fail to parse");
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
        let err = parse_message_lax_pure(b"(meta)")
            .expect_err("zero-arg meta fails message parse");
        assert!(
            err.starts_with("message error: "),
            "expected message error prefix, got: {err}"
        );
    }

    #[test]
    fn invalid_utf8_returns_exact_reason() {
        let err = parse_message_lax_pure(&[0xFFu8, 0xFE])
            .expect_err("non-utf-8 bytes are rejected");
        assert_eq!(err, "invalid utf-8");
    }
}
