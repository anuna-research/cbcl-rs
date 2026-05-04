//! REQ-005: panic-to-error wrapping at the NIF boundary.
//!
//! A panic in a NIF unwinds through C code into the BEAM scheduler and
//! crashes the entire VM, not just the calling process (SPEC-009 ADR-001).
//! This module provides [`catch`] — a [`std::panic::catch_unwind`] wrapper
//! that converts any panic into an `{error, <<"panic: ...">>}` term so
//! cbcl-erl is crash-safe on the BEAM hot path.
//!
//! Every NIF body MUST go through this wrapper.
//!
//! # Testability
//!
//! [`catch`] is bound to an `Env<'a>`, which `cargo test` cannot fabricate
//! on rustler 0.36 (`OwnedEnv::new()` aborts outside a BEAM host — see
//! `verify_dialect.rs` for the same finding). The actual panic-to-string
//! conversion lives in [`catch_pure`], which has no Env dependency and is
//! exercised directly by the unit tests below.

use core::panic::AssertUnwindSafe;
use rustler::types::atom;
use rustler::{Binary, Encoder, Env, OwnedBinary, Term};
use std::panic;

/// Run `f` under [`std::panic::catch_unwind`]. On panic, encode
/// `{error, <<"panic: <msg>">>}` into `env` and return that term. On
/// success, return `f`'s output unchanged.
///
/// The user-facing reason MUST start with the literal prefix `"panic: "`
/// so consumers can grep for it without ambiguity (see SPEC-009 REQ-005).
pub(crate) fn catch<'a, F>(env: Env<'a>, f: F) -> Term<'a>
where
    F: FnOnce() -> Term<'a> + panic::UnwindSafe,
{
    match panic::catch_unwind(AssertUnwindSafe(f)) {
        Ok(t) => t,
        Err(payload) => {
            let msg = panic_payload_to_string(&payload);
            encode_error(env, &format!("panic: {msg}"))
        }
    }
}

/// Env-free variant: run `f` under `catch_unwind` and return the panic
/// payload as a `String` (without the `"panic: "` prefix). Exposed so the
/// unit tests can exercise the panic-trapping branch without needing a
/// BEAM-hosted `Env`. The runtime callers always go through [`catch`],
/// which is private to the crate.
pub fn catch_pure<F, T>(f: F) -> Result<T, String>
where
    F: FnOnce() -> T + panic::UnwindSafe,
{
    match panic::catch_unwind(AssertUnwindSafe(f)) {
        Ok(t) => Ok(t),
        Err(payload) => Err(panic_payload_to_string(&payload)),
    }
}

fn panic_payload_to_string(payload: &Box<dyn std::any::Any + Send>) -> String {
    if let Some(s) = payload.downcast_ref::<&'static str>() {
        return (*s).to_string();
    }
    if let Some(s) = payload.downcast_ref::<String>() {
        return s.clone();
    }
    "non-string panic payload".to_string()
}

/// Build `{error, <<"reason">>}`. Mirrors the `make_binary` / `err`
/// recipe used in the sibling NIF modules (`verify_dialect`,
/// `parse_message`, `parse_message_lax`). Duplicated locally rather
/// than refactoring those private helpers into a shared module —
/// REQ-005 says "do not touch the pure helpers".
fn encode_error<'a>(env: Env<'a>, reason: &str) -> Term<'a> {
    let bin = make_binary(env, reason.as_bytes());
    (atom::error(), bin).encode(env)
}

fn make_binary<'a>(env: Env<'a>, bytes: &[u8]) -> Binary<'a> {
    match OwnedBinary::new(bytes.len()) {
        Some(mut owned) => {
            owned.as_mut_slice().copy_from_slice(bytes);
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

#[cfg(test)]
mod tests {
    //! `catch` itself takes an `Env<'a>` and so cannot be exercised under
    //! plain `cargo test` (see module docs and `verify_dialect.rs`). We
    //! test [`catch_pure`] and [`panic_payload_to_string`] directly,
    //! which together cover every branch of the panic-trapping logic
    //! that does not involve term construction.
    use super::*;

    #[test]
    fn payload_static_str() {
        let payload: Box<dyn std::any::Any + Send> = Box::new("static-str-panic");
        assert_eq!(panic_payload_to_string(&payload), "static-str-panic");
    }

    #[test]
    fn payload_owned_string() {
        let payload: Box<dyn std::any::Any + Send> = Box::new(String::from("owned-string-panic"));
        assert_eq!(panic_payload_to_string(&payload), "owned-string-panic");
    }

    #[test]
    fn payload_non_string_falls_back() {
        // Anything other than `&'static str` or `String` lands in the
        // catch-all branch.
        let payload: Box<dyn std::any::Any + Send> = Box::new(42_i32);
        assert_eq!(
            panic_payload_to_string(&payload),
            "non-string panic payload"
        );
    }

    #[test]
    fn catch_pure_returns_ok_on_clean_return() {
        let res = catch_pure(|| 7_i32);
        assert_eq!(res, Ok(7));
    }

    #[test]
    fn catch_pure_traps_static_str_panic() {
        let res: Result<i32, String> = catch_pure(|| panic!("boom-static"));
        assert_eq!(res, Err(String::from("boom-static")));
    }

    #[test]
    fn catch_pure_traps_formatted_panic() {
        // `panic!("{}", _)` with a runtime value produces a `String` payload.
        let value = 99;
        let res: Result<(), String> = catch_pure(|| panic!("boom-{value}"));
        assert_eq!(res, Err(String::from("boom-99")));
    }

    #[test]
    fn catch_pure_traps_non_string_payload() {
        // `panic_any` lets us emit a non-string payload so we hit the
        // fallback branch of `panic_payload_to_string`.
        let res: Result<(), String> = catch_pure(|| std::panic::panic_any(123_u64));
        assert_eq!(res, Err(String::from("non-string panic payload")));
    }
}
