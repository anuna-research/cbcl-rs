//! cbcl-parser: Pure S-expression parser and pipeline for CBCL.
//!
//! This crate implements the hand-rolled recursive-descent parser (ADR-001)
//! and the full verified pipeline (parse -> parse_message -> validate -> verify).

#![forbid(unsafe_code)]
#![cfg_attr(not(feature = "std"), no_std)]

extern crate alloc;

pub mod dialect_parser;
pub mod message_parser;
pub mod parser;
pub mod pipeline;

pub use dialect_parser::{parse_dialect, parse_meta_define};
pub use message_parser::parse_message;
pub use parser::{parse, ParseError};
pub use pipeline::{run_pipeline, PipelineResult};
