//! common: SPEC-011 stub (filled in subsequent IMPL waves).
//!
//! Re-exports the `ChallengeKind` marker enum from [`crate::operator`] so
//! that future code can refer to it via the architectural location specified
//! in SPEC-011 §Module Layout. The canonical definition currently lives in
//! `operator::mod` for the duration of the parallel-implementation wave; this
//! re-export keeps the eventual move source-compatible.

pub use crate::operator::ChallengeKind;
