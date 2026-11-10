//! cbcl-parser: Pure S-expression parser and pipeline for CBCL.
//!
//! This crate implements the hand-rolled recursive-descent parser (ADR-001)
//! and the full verified pipeline (parse -> parse_message -> validate -> verify).

#![forbid(unsafe_code)]
#![cfg_attr(not(feature = "std"), no_std)]

extern crate alloc;

pub mod checkpoint_dialect;

#[cfg(feature = "std")]
pub mod contract;
#[cfg(feature = "std")]
pub mod describe;
pub mod dialect_parser;
pub mod message_parser;
pub mod parser;
pub mod pipeline;
pub mod protocol_parser;
pub mod read;
pub mod shape_exports;
pub mod shape_parser;
pub mod state_exports;
pub mod state_parser;

#[cfg(feature = "std")]
pub use contract::compile_contract_str;
#[cfg(feature = "std")]
pub use describe::{define_text_str, describe_dialect_str, read_act_str};
pub use dialect_parser::{parse_dialect, parse_meta_define};
pub use message_parser::{parse_message, parse_message_lax};
pub use parser::{parse, ParseError};
pub use pipeline::{
    run_pipeline, run_pipeline_full, PipelineContext, PipelineResult, ValidationError,
};
pub use protocol_parser::{parse_protocol, ProtocolParseError};
pub use read::read_str;
pub use shape_exports::verify_message_shape_str;
pub use shape_parser::parse_shape;
pub use state_exports::parse_and_install_dialect;
pub use state_parser::{parse_state, parse_state_bounds};

/// Parse once and return the canonical signed-envelope audience (`@` retained).
/// No dialect installation or field declaration order is required.
pub fn recipient_of(input: &str) -> Result<alloc::string::String, alloc::string::String> {
    let form = parse(input).map_err(|e| alloc::format!("parse error: {e}"))?;
    let message = parse_message(&form)?;
    message
        .canonical_recipient()
        .map(alloc::string::String::from)
        .map_err(alloc::string::String::from)
}

/// Audience accessor for hosts that already allow bare custom control verbs.
/// This recognizes syntax only; the host must still authorize the verb.
pub fn recipient_of_lax(input: &str) -> Result<alloc::string::String, alloc::string::String> {
    let form = parse(input).map_err(|e| alloc::format!("parse error: {e}"))?;
    let message = parse_message_lax(&form)?;
    message
        .canonical_recipient()
        .map(alloc::string::String::from)
        .map_err(alloc::string::String::from)
}
