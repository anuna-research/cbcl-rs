//! cbcl-core: Pure core library for the CBCL language runtime.
//!
//! This crate contains all deterministic, effect-free modules that form the
//! verified core of CBCL. Every module is `#![forbid(unsafe_code)]` and
//! `no_std`-compatible (with `alloc`).
//!
//! # Modules
//!
//! - `sexpr` — S-expression data types (Atom, SExpr)
//! - `blame` — Violation blame attribution (REQ-230, REQ-232, REQ-233, CON-205)
//! - `message` — Message types and core performatives
//! - `dialect` — Dialect definitions and resource bounds
//! - `agent` — Agent with beliefs, dialect registry, message queue, threads
//! - `evaluator` — Message evaluator: dispatch, template expansion, effect interpretation
//! - `serializer` — Canonical S-expression serialization
//! - `r1` — R1: No recursion safety constraint
//! - `r2` — R2: Resource bounds safety constraint
//! - `r3` — R3: Core preservation safety constraint
//! - `r4` — R4: Integrity (Signer trait)
//! - `r5` — R5: Shape well-formedness (REQ-222)
//! - `template` — Template expansion
//! - `pattern` — Pattern matching for message dispatch
//! - `msg_tag` — Deterministic message tagging (DCFL)
//! - `shape` — Structural shape constraints (REQ-220)
//! - `gossip` — Epidemic gossip protocol for dialect propagation
//! - `keyid` — Canonical suite-typed key identity (SPEC-015 REQ-708)
//! - `attest` — R4 v2 attestation signing discipline (SPEC-015 REQ-701, ADR-700)
//! - `envelope` — Redacted envelopes: payload-free evidence widening (SPEC-015 REQ-700..703)
//! - `equivocation` — Equivocation accountability: predicate, proof object, lint (SPEC-015 REQ-705..707)

#![forbid(unsafe_code)]
#![cfg_attr(not(feature = "std"), no_std)]

extern crate alloc;

/// Crate version, taken from `Cargo.toml` at compile time.
///
/// Re-exported by downstream bindings (e.g. `cbcl-erl`'s `versions/0` NIF —
/// SPEC-009 OBS-001) so callers can identify the exact `cbcl-core` build the
/// runtime was linked against without parsing the workspace manifest.
pub const VERSION: &str = env!("CARGO_PKG_VERSION");

pub mod agent;
pub mod attest;
pub mod blame;
pub mod canonical;
pub mod clock;
pub mod dialect;
pub mod envelope;
pub mod equivocation;
pub mod evaluator;
pub mod gossip;
pub mod keyid;
pub mod message;
pub mod msg_tag;
pub mod pattern;
pub mod policy;
pub mod projection;
pub mod protocol;
pub mod r1;
pub mod r2;
pub mod r3;
pub mod r4;
pub mod r5;
pub mod r6;
pub mod role;
pub mod serializer;
pub mod sexpr;
pub mod shape;
pub mod store;
pub mod template;

/// Prelude re-exporting the most-used types.
pub mod prelude {
    pub use crate::agent::{Agent, AgentOutcome, MergePolicy};
    pub use crate::blame::{BlameEntry, BlameParty, ViolationError, ViolationKind};
    #[cfg(feature = "std")]
    pub use crate::clock::SystemClock;
    pub use crate::clock::{Clock, NoClock};
    pub use crate::dialect::{
        Dialect, DialectInstallError, DialectRegistry, PerformativeDef, ResourceBounds,
    };
    pub use crate::envelope::{parse_envelope, redact, EnvelopeParseError, RedactedEnvelope};
    pub use crate::evaluator::{Effect, EvalError, EvalResult};
    pub use crate::gossip::{GossipConfig, GossipNetwork, GossipStats, PropagationState, Topology};
    pub use crate::message::{
        CausedBy, CorePerformative, Message, MessageParseError, MessageType, Performative,
        WrapperType,
    };
    pub use crate::policy::{
        apply_policy, DropReason, PendingEntry, PendingQueue, PendingReason, PolicyOutcome,
        UnknownPredecessorPolicy,
    };
    pub use crate::protocol::{
        verify_causal, CausalProtocol, CausalViolation, NodeRef, ProtocolViolation, StepDecl,
        VerificationResult, BEGIN_KEYWORD,
    };
    pub use crate::r4::{R4Result, Signer};
    pub use crate::sexpr::{Atom, SExpr};
    pub use crate::shape::{ShapeConstraint, ShapeRule, ShapeViolation, TypeConstraint};
    pub use crate::store::{
        BundleVerificationError, CausalClosureBundle, ClosureError, ContentHash, HashIndex,
        MergeResult, MessageStore, ThreadId, ThreadedMessageStore,
    };
}
