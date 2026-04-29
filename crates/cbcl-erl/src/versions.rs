//! SPEC-009 OBS-001 — version constants and the `versions/0` NIF.
//!
//! Returns a 3-tuple of binaries:
//!   `{<<git-rev>>, <<cbcl-core-version>>, <<cbcl-erl-version>>}`
//!
//! The git revision is populated by `build.rs`; if no git information is
//! available at build time it falls back to the literal `"unknown"` so the
//! NIF never returns an empty binary in that slot.

use rustler::types::tuple::make_tuple;
use rustler::{Env, NewBinary, Term};

/// Workspace git SHA at the time `cbcl-erl` was built (or `"unknown"` for
/// source-tarball / shallow-clone builds). Populated by `build.rs`.
pub const CBCL_RS_GIT_REVISION: &str = env!("CBCL_RS_GIT_REVISION");

/// Version of the `cbcl-core` crate this binding is linked against.
///
/// Re-exported from `cbcl_core::VERSION` so a single source of truth
/// (`cbcl-core/Cargo.toml` via `CARGO_PKG_VERSION`) drives the value.
pub const CBCL_CORE_VERSION: &str = cbcl_core::VERSION;

/// Version of this binding crate (`cbcl-erl`).
pub const CBCL_ERL_VERSION: &str = env!("CARGO_PKG_VERSION");

/// `cbcl_erl:versions/0` — returns a 3-tuple of binaries
/// `{git_rev, cbcl_core_version, cbcl_erl_version}`.
#[rustler::nif]
pub fn versions(env: Env<'_>) -> Term<'_> {
    // REQ-005: wrap the body in `panic_guard::catch` for parity with the
    // other NIFs. The body itself is not panic-prone (constant strings,
    // infallible binary copies), but the wrapper costs effectively nothing
    // and keeps the "every NIF entrypoint goes through `catch`" invariant
    // mechanical to verify (see SPEC-009 ADR-001).
    crate::panic_guard::catch(env, || {
        let git = make_binary(env, CBCL_RS_GIT_REVISION.as_bytes());
        let core = make_binary(env, CBCL_CORE_VERSION.as_bytes());
        let erl = make_binary(env, CBCL_ERL_VERSION.as_bytes());
        make_tuple(env, &[git, core, erl])
    })
}

fn make_binary<'a>(env: Env<'a>, bytes: &[u8]) -> Term<'a> {
    let mut bin = NewBinary::new(env, bytes.len());
    bin.as_mut().copy_from_slice(bytes);
    bin.into()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn consts_are_non_empty() {
        assert!(!CBCL_RS_GIT_REVISION.is_empty());
        assert!(!CBCL_CORE_VERSION.is_empty());
        assert!(!CBCL_ERL_VERSION.is_empty());
        // CARGO_PKG_VERSION for a workspace member that inherits
        // `version.workspace = true` resolves to the workspace version.
        assert_eq!(CBCL_ERL_VERSION, "0.1.0");
    }

    // The end-to-end test of `versions/0` requires `OwnedEnv::new()`, which
    // calls `enif_alloc_env` — loaded dynamically by the BEAM and panicking
    // with `unreachable_unchecked` from a plain `cargo test` binary. We follow
    // the encoding.rs convention and gate it `#[ignore]`. Additionally,
    // rustler 0.36's `#[nif]` macro inlines the attributed function inside
    // an `inventory::submit!` block rather than emitting it at module scope,
    // so calling `versions(env)` directly from `#[cfg(test)]` won't resolve
    // even under a BEAM host — the call below is kept as documentation of the
    // intended assertion shape and is excluded from compilation accordingly.
    #[test]
    #[ignore = "requires BEAM host (enif_alloc_env) and rustler-emitted NIF function visible at module scope; see encoding.rs for the same constraint"]
    #[cfg(any())]
    fn versions_returns_three_binaries() {
        use rustler::env::OwnedEnv;
        use rustler::types::tuple;
        use rustler::Binary;

        let owned = OwnedEnv::new();
        owned.run(|env| {
            let term = versions(env);
            let elements = tuple::get_tuple(term).expect("tuple");
            assert_eq!(elements.len(), 3);

            let git: Binary = elements[0].decode().expect("git binary");
            let core: Binary = elements[1].decode().expect("core binary");
            let erl: Binary = elements[2].decode().expect("erl binary");

            assert!(!git.as_slice().is_empty());
            assert!(!core.as_slice().is_empty());
            assert_eq!(erl.as_slice(), CBCL_ERL_VERSION.as_bytes());
        });
    }
}
