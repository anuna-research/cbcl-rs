//! Consensus-free bounded counters with multi-parent DAG adoption (SPEC-031).
//!
//! Keys, networking and durable storage are host responsibilities. The engine
//! returns signing requests only after a successful atomic journal append.
#![forbid(unsafe_code)]
mod context;
mod engine;
mod types;
pub use context::Context;
pub use engine::Replica;
pub use types::*;
