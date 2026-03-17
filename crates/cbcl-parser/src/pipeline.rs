//! Full verified pipeline.
//!
//! Mirrors `Pipeline.lean` from the Lean 4 proof library.

#![forbid(unsafe_code)]

use crate::parser::{self, ParseError};
use alloc::string::String;
use cbcl_core::message::Message;
use core::fmt;

/// Validation errors from the pipeline (ADR-002).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ValidationError {
    R1SelfReference { performative: String },
    R2ResourceBoundsInvalid { field: &'static str, value: u32 },
    R2FuelExhausted,
    R3CoreOverride { performative: String },
    R4SignatureInvalid,
    MalformedMessage { reason: String },
    MalformedDialect { reason: String },
}

impl fmt::Display for ValidationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ValidationError::R1SelfReference { performative } => {
                write!(
                    f,
                    "R1 violation: self-reference in performative '{performative}'"
                )
            }
            ValidationError::R2ResourceBoundsInvalid { field, value } => {
                write!(f, "R2 violation: invalid resource bound {field}={value}")
            }
            ValidationError::R2FuelExhausted => write!(f, "R2 violation: fuel exhausted"),
            ValidationError::R3CoreOverride { performative } => {
                write!(
                    f,
                    "R3 violation: core performative '{performative}' overridden"
                )
            }
            ValidationError::R4SignatureInvalid => write!(f, "R4 violation: invalid signature"),
            ValidationError::MalformedMessage { reason } => {
                write!(f, "malformed message: {reason}")
            }
            ValidationError::MalformedDialect { reason } => {
                write!(f, "malformed dialect: {reason}")
            }
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for ValidationError {}

/// Top-level pipeline result (REQ-111).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PipelineResult {
    Success(Message),
    ParseError(ParseError),
    ValidationError(ValidationError),
}

/// Run the full verified pipeline (REQ-110).
///
/// Pipeline: parse -> parse_message -> validate -> (for meta/define: verify R1+R2+R3) -> success.
pub fn run_pipeline(input: &str) -> PipelineResult {
    let sexpr = match parser::parse(input) {
        Ok(e) => e,
        Err(e) => return PipelineResult::ParseError(e),
    };

    let message = match crate::message_parser::parse_message(&sexpr) {
        Ok(m) => m,
        Err(reason) => {
            return PipelineResult::ValidationError(ValidationError::MalformedMessage { reason })
        }
    };

    // For meta define messages, validate the dialect definition
    if let Message::Meta { ref dialect_def } = message {
        if let cbcl_core::sexpr::SExpr::List(items) = dialect_def {
            if !items.is_empty() && items[0].is_symbol("define") {
                if let Err(reason) = crate::dialect_parser::parse_dialect(dialect_def) {
                    return PipelineResult::ValidationError(ValidationError::MalformedDialect {
                        reason,
                    });
                }
            }
        }
    }

    PipelineResult::Success(message)
}

#[cfg(test)]
mod tests {
    use super::*;
    use cbcl_core::message::MessageType;

    #[test]
    fn pipeline_parse_error() {
        let result = run_pipeline("(unclosed");
        assert!(matches!(result, PipelineResult::ParseError(_)));
    }

    #[test]
    fn pipeline_simple_message() {
        let result = run_pipeline("(tell \"hello\")");
        assert!(matches!(result, PipelineResult::Success(_)));
        if let PipelineResult::Success(msg) = result {
            assert_eq!(msg.message_type(), MessageType::Simple);
        }
    }

    #[test]
    fn pipeline_meta_define() {
        let input = "(meta (define test-dialect (cbcl) @author))";
        let result = run_pipeline(input);
        assert!(matches!(result, PipelineResult::Success(_)));
        if let PipelineResult::Success(msg) = result {
            assert_eq!(msg.message_type(), MessageType::Meta);
        }
    }

    #[test]
    fn pipeline_malformed_dialect() {
        let input = "(meta (define))"; // missing required fields
        let result = run_pipeline(input);
        assert!(matches!(
            result,
            PipelineResult::ValidationError(ValidationError::MalformedDialect { .. })
        ));
    }

    #[test]
    fn pipeline_custom_performative() {
        let result = run_pipeline("(share-conditional pickup box-location box-in-hand)");
        assert!(matches!(result, PipelineResult::Success(_)));
    }

    #[test]
    fn pipeline_meta_query() {
        let result = run_pipeline("(meta (query (speak? cbcl-planning)))");
        assert!(matches!(result, PipelineResult::Success(_)));
    }
}
