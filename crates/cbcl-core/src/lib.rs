//! cbcl-core: Pure core library for the CBCL language runtime.
//!
//! This crate contains all deterministic, effect-free modules that form the
//! verified core of CBCL. Every module is `#![forbid(unsafe_code)]` and
//! `no_std`-compatible (with `alloc`).
//!
//! # Modules
//!
//! - `sexpr` — S-expression data types (Atom, SExpr)
//! - `message` — Message types and core performatives
//! - `dialect` — Dialect definitions and resource bounds
//! - `agent` — Agent with beliefs, dialect registry, message queue, threads
//! - `evaluator` — Message evaluator: dispatch, template expansion, effect interpretation
//! - `serializer` — Canonical S-expression serialization
//! - `r1` — R1: No recursion safety constraint
//! - `r2` — R2: Resource bounds safety constraint
//! - `r3` — R3: Core preservation safety constraint
//! - `r4` — R4: Integrity (Signer trait)
//! - `template` — Template expansion
//! - `pattern` — Pattern matching for message dispatch
//! - `msg_tag` — Deterministic message tagging (DCFL)
//! - `shape` — Structural shape constraints (REQ-220)
//! - `gossip` — Epidemic gossip protocol for dialect propagation

#![forbid(unsafe_code)]
#![cfg_attr(not(feature = "std"), no_std)]

extern crate alloc;

pub mod agent;
pub mod canonical;
pub mod dialect;
pub mod evaluator;
pub mod gossip;
pub mod message;
pub mod msg_tag;
pub mod pattern;
pub mod r1;
pub mod r2;
pub mod r3;
pub mod r4;
pub mod serializer;
pub mod sexpr;
pub mod shape;
pub mod template;

/// Prelude re-exporting the most-used types.
pub mod prelude {
    pub use crate::agent::Agent;
    pub use crate::dialect::{
        Dialect, DialectInstallError, DialectRegistry, PerformativeDef, ResourceBounds,
    };
    pub use crate::evaluator::{Effect, EvalError, EvalResult};
    pub use crate::gossip::{GossipConfig, GossipNetwork, GossipStats, PropagationState, Topology};
    pub use crate::message::{
        CorePerformative, Message, MessageParseError, MessageType, Performative, WrapperType,
    };
    pub use crate::r4::{R4Result, Signer};
    pub use crate::sexpr::{Atom, SExpr};
    pub use crate::shape::{ShapeConstraint, ShapeRule, ShapeViolation, TypeConstraint};
}
