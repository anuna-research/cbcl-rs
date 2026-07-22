//! NIF: `mls_ds_run_verify_vector/1` — SPEC-024 REQ-142 / TEST-018.
//!
//! Exposes the cbcl-core mls-ds/v1 verdict VECTOR RUNNER
//! ([`cbcl_core::mls_ds::run_verify_vector`]) across the BEAM NIF boundary. A
//! `binary()` self-describing verify vector goes in; the canonical RFC 9804
//! serialized verdict `binary()` comes out. This binding is a NATIVE compile,
//! so a green parity test proves the binding + serialization boundary is
//! byte-faithful to the in-crate native path — one leg of the REQ-142
//! cross-runtime byte-identity gate (the wasm32 leg is the other).
//!
//! Return shape: `binary()` (the verdict bytes). The runner is total — every
//! malformed input maps to a fixed `vector-error` verdict, never a panic — so
//! there is no `{error, _}` arm.

use rustler::{Binary, Encoder, Env, OwnedBinary, Term};

/// The pure-Rust core: raw vector bytes → canonical verdict bytes. Lifted out
/// of the NIF wrapper (rustler 0.36 ergonomics — see `verify_dialect.rs`) so
/// the integration tests can exercise it without a BEAM host. Public so
/// `tests/mls_ds_parity.rs` can assert byte-equality against the native path.
pub fn run_verify_vector_pure(bytes: &[u8]) -> Vec<u8> {
    cbcl_core::mls_ds::run_verify_vector(bytes)
}

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

#[rustler::nif]
pub fn mls_ds_run_verify_vector<'a>(env: Env<'a>, bytes: Binary<'a>) -> Term<'a> {
    let input = bytes.as_slice();
    crate::panic_guard::catch(env, || {
        let out = run_verify_vector_pure(input);
        make_binary(env, &out).encode(env)
    })
}
