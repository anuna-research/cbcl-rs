//! NIF: `verify_dialect/1` — see SPEC-009 §REQ-004 / CON-002.
//!
//! Decodes a `binary()` containing a `(define ...)` S-expression, parses it,
//! and installs it into a fresh `DialectRegistry`. The install path runs the
//! R1/R2/R3 well-formedness checks mandated by CON-002 for cbcl-erl v0.1.0.
//!
//! Return shape: `ok | {error, Reason :: binary()}`.
//!
//! Note on scope: this NIF deliberately does *not* run R5 ancestor resolution
//! or `:hash` consistency — those are recent additions on the cbcl-wasm side
//! and are out of scope for the v0.1.0 Erlang binding per CON-002. If the spec
//! later widens to match cbcl-wasm verbatim, swap to a `parse_and_install`
//! helper that mirrors `crates/cbcl-wasm/src/lib.rs::parse_and_install_dialect`.
//!
//! Errors are surfaced as Erlang binaries (not atoms) because the underlying
//! parse / install errors carry free-form descriptions whose cardinality is
//! unbounded — atoms would leak into the global atom table, which is a
//! well-known BEAM denial-of-service vector.

use cbcl_core::dialect::DialectRegistry;
use cbcl_parser::{parse, parse_dialect};
use rustler::types::atom;
use rustler::{Binary, Encoder, Env, OwnedBinary, Term};

use crate::tracing_hooks;

/// Build an Erlang binary from an owned Rust `String`. We allocate an
/// `OwnedBinary` of the exact size, copy the bytes in, then transfer
/// ownership to the NIF env via `Binary::from_owned`. `OwnedBinary::new`
/// only fails on allocation failure; on that path we fall back to a static
/// short message so the NIF still returns a well-formed `{error, _}` tuple
/// rather than panicking across the FFI boundary.
fn make_binary<'a>(env: Env<'a>, s: String) -> Binary<'a> {
    match OwnedBinary::new(s.len()) {
        Some(mut owned) => {
            owned.as_mut_slice().copy_from_slice(s.as_bytes());
            Binary::from_owned(owned, env)
        }
        None => {
            // Fall back to a 3-byte "oom" — guaranteed to allocate or the
            // VM is already out of memory and we have bigger problems.
            let mut owned = OwnedBinary::new(3).expect("3-byte allocation");
            owned.as_mut_slice().copy_from_slice(b"oom");
            Binary::from_owned(owned, env)
        }
    }
}

fn err<'a>(env: Env<'a>, msg: String) -> Term<'a> {
    let bin = make_binary(env, msg);
    (atom::error(), bin).encode(env)
}

/// The pure-Rust core of `verify_dialect/1`: takes raw bytes, returns either
/// `Ok(())` or `Err(reason_string)`. Lifted out of the NIF wrapper so we can
/// unit-test it without spinning up a BEAM environment. Public so the
/// integration tests in `tests/verify_dialect.rs` can call it.
///
/// **Why this split** (rustler 0.36 ergonomics, hand off to parse_message
/// agent): rustler 0.36's `#[nif]` proc macro inlines the attributed
/// function's body inside an `inventory::submit!` wrapper rather than
/// emitting it at module scope, so calling the `#[nif]`-attributed name
/// from `#[cfg(test)]` fails to resolve. Worse, even if you call it through
/// a thin shim, `OwnedEnv::new()` (suggested by some rustler docs as the
/// way to fabricate a test `Env`) goes through `enif_alloc_env`, which is
/// loaded dynamically and panics with `unreachable_unchecked` when called
/// from a plain `cargo test` binary that isn't hosted by `erl`. The reliable
/// pattern is therefore: keep all real work in env-free helpers like this
/// one, and let the `#[nif]` wrapper do nothing but encode the `Result` to
/// BEAM terms.
pub fn verify_dialect_pure(bytes: &[u8]) -> Result<(), String> {
    let input = core::str::from_utf8(bytes).map_err(|_| String::from("invalid utf-8"))?;
    let sexpr = parse(input).map_err(|e| format!("dialect error: {e}"))?;
    let dialect = parse_dialect(&sexpr).map_err(|e| format!("dialect error: {e}"))?;
    let mut registry = DialectRegistry::new();
    registry
        .install(dialect)
        .map_err(|e| format!("verification failed: {e}"))?;
    Ok(())
}

#[rustler::nif]
pub fn verify_dialect<'a>(env: Env<'a>, bytes: Binary<'a>) -> Term<'a> {
    // REQ-005: wrap the body in `panic_guard::catch` so any panic from
    // the parser / dialect installer becomes `{error, <<"panic: ...">>}`
    // instead of crashing the BEAM scheduler (ADR-001).
    let input = bytes.as_slice();
    crate::panic_guard::catch(env, || {
        let span = tracing_hooks::enter("verify_dialect", input.len());
        match verify_dialect_pure(input) {
            Ok(()) => {
                tracing_hooks::exit_ok(span);
                atom::ok().encode(env)
            }
            Err(msg) => {
                // Map free-form reason prefix to the static category strings
                // tracing_hooks::exit_err expects (mirrors parse_message.rs).
                let cat_static: &'static str = if msg == "invalid utf-8" {
                    "invalid_utf8"
                } else if msg.starts_with("dialect error") {
                    "dialect_error"
                } else if msg.starts_with("verification failed") {
                    "verification_failed"
                } else {
                    "unknown"
                };
                tracing_hooks::exit_err(span, cat_static);
                err(env, msg)
            }
        }
    })
}

#[cfg(test)]
mod tests {
    //! Tests target `verify_dialect_pure` — the env-free core — because
    //! `rustler::env::OwnedEnv::new()` calls `enif_alloc_env`, which is loaded
    //! at runtime by the BEAM and is unavailable in plain `cargo test`
    //! binaries (it panics with `unreachable_unchecked`). The Term-encoding
    //! glue in `verify_dialect/1` is trivial and exercised end-to-end by the
    //! Erlang-side smoke tests in a future task.

    use super::*;

    #[test]
    fn ok_on_valid_dialect() {
        // REQ-004: minimal valid dialect → `ok`.
        let res = verify_dialect_pure(b"(define test-d (cbcl) @author)");
        assert!(res.is_ok(), "expected Ok, got {res:?}");
    }

    #[test]
    fn parse_error_returns_error_tuple() {
        // CON-002: parse failure → "dialect error: ..." reason.
        let res = verify_dialect_pure(b"(unclosed");
        let msg = res.expect_err("expected parse failure");
        assert!(
            msg.starts_with("dialect error: "),
            "expected dialect error prefix, got: {msg}"
        );
    }

    #[test]
    fn r3_violation_returns_verification_failed() {
        // R3: redefining a core performative (`tell`) must be rejected at
        // install time, surfaced as "verification failed: ...".
        let res = verify_dialect_pure(
            b"(define bad (cbcl) @author (extend tell (msg) (effect custom-tell)))",
        );
        let msg = res.expect_err("expected verification failure");
        assert!(
            msg.starts_with("verification failed: "),
            "expected verification-failed prefix, got: {msg}"
        );
    }

    #[test]
    fn invalid_utf8_returns_error() {
        // CON-002: non-UTF-8 bytes → "invalid utf-8" exact reason.
        let res = verify_dialect_pure(&[0xFFu8, 0xFE]);
        let msg = res.expect_err("expected utf-8 failure");
        assert_eq!(msg, "invalid utf-8");
    }
}
