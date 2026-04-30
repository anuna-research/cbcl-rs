//! SPEC-011: Multi-agent arena challenge simulator.
//!
//! Implements the deterministic local simulator specified in
//! `cbcl-rs/specs/SPEC-011-arena-simulator.md`. Three challenges
//! (PSI, Yao's Millionaire, Dining Cryptographers), two agent
//! strategies (CBCL-disciplined, Vanilla NL-chat), three attacker
//! categories (Honest-cooperative, Malicious-published,
//! Malicious-novel).
//!
//! # Module layout (per SPEC-011 §Purity Boundary Map)
//!
//! Pure core (no I/O, deterministic):
//! - [`statistics`] — Wilson 95% confidence intervals (NFR-1115)
//! - [`common`] — base types and traits (CON-1100)
//! - [`operator`] — per-challenge operator implementations (REQ-1110/1111/1112)
//! - [`agents`] — CBCL-disciplined and vanilla NL-chat strategies (REQ-1120/1121)
//! - [`attackers`] — attack-pattern registry (REQ-1130/1131)
//!
//! Effectful shell:
//! - [`driver`] — per-game loop (CON-1100)
//! - [`measurement`] — full-matrix measurement orchestrator (REQ-1150/CON-1150)
//! - [`manifest`] — reproducibility manifest (REQ-1151)
//! - [`artefact`] — paper-table emission (REQ-1160/CON-1160)
//! - [`isolation`] — network-isolation wrapper (NFR-1114/CON-1190)

#![forbid(unsafe_code)]
#![warn(missing_docs)]
#![warn(rust_2018_idioms)]

// Pure core
pub mod statistics;
pub mod common;
pub mod operator;
pub mod agents;
pub mod attackers;

// Effectful shell
pub mod driver;
pub mod measurement;
pub mod manifest;
pub mod artefact;
pub mod isolation;
