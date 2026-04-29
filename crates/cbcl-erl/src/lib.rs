#![forbid(unsafe_code)]
//! cbcl-erl: Erlang/BEAM NIF binding for CBCL — see SPEC-009.
//!
//! Currently exported NIFs: `verify_dialect/1`, `versions/0` (SPEC-009
//! OBS-001), `parse_message/1`, `parse_message_lax/1`. The BEAM
//! module name is `cbcl_erl`, loaded from `libcbcl_erl.{so,dylib}`. NIFs are
//! added per task; rustler 0.36 auto-discovers them via inventory so `init!`
//! only needs the BEAM module name.
//!
//! # Public Rust surface (`*_pure` helpers)
//!
//! Each NIF is split into a `#[rustler::nif]` term-translation wrapper and
//! an env-free `*_pure` helper carrying the real logic. The pure helpers
//! ([`parse_message_pure`], [`parse_message_lax_pure`],
//! [`verify_dialect_pure`], [`panic_guard::catch_pure`]) are deliberately
//! `pub` so the integration tests in `tests/integration.rs` can exercise
//! them — `OwnedEnv::new()` aborts with `unreachable_unchecked` outside a
//! BEAM host, so the term-bound NIF wrappers cannot run under `cargo test`
//! and the pure helpers are the only testable surface for v0.1.0.

mod encoding;
pub mod panic_guard;
pub mod parse_message;
pub mod parse_message_lax;
pub mod verify_dialect;
mod versions;

// Helpers consumed by the panic-guard NIF wrapping task (SPEC-009 OBS-002);
// included now so the surface is ready when those wrappers land.
#[allow(dead_code)]
mod tracing_hooks;

pub use parse_message::parse_message_pure;
pub use parse_message_lax::{parse_message_lax_pure, LaxResult};
pub use verify_dialect::verify_dialect_pure;
pub use versions::{CBCL_CORE_VERSION, CBCL_ERL_VERSION, CBCL_RS_GIT_REVISION};

rustler::init!("cbcl_erl");

#[cfg(test)]
mod tests {
    #[test]
    fn smoke() {
        assert_eq!(2 + 2, 4);
    }
}
