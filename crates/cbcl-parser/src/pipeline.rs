//! Full verified pipeline.
//!
//! Mirrors `Pipeline.lean` from the Lean 4 proof library.
//!
//! The pipeline chains: parse → parse_message → validate → expand →
//! causal verify (6a) → shape check (6b) → success.
//!
//! Two entry points:
//! - [`run_pipeline`] — lightweight parse + validate (no runtime context).
//! - [`run_pipeline_full`] — full verification with dialect registry and
//!   message store, including causal verification and shape checking
//!   (REQ-231: fail-closed, no bypass, no partial checks).

#![forbid(unsafe_code)]

use crate::parser::{self, ParseError};
use alloc::string::String;
use alloc::vec::Vec;
use cbcl_core::blame::ViolationError;
use cbcl_core::dialect::{Dialect, DialectRegistry};
use cbcl_core::evaluator::{evaluate_without_shape_check, EvalError};
use cbcl_core::message::{Message, Performative};
use cbcl_core::protocol::{CausalViolation, VerificationResult};
use cbcl_core::r1;
use cbcl_core::r3;
use cbcl_core::r5;
use cbcl_core::sexpr::SExpr;
use cbcl_core::shape::ShapeViolation;
use cbcl_core::store::{MessageStore, ThreadId};
use core::fmt;

/// Validation errors from the pipeline (ADR-002).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ValidationError {
    R1RecursivePerformative { performatives: Vec<String> },
    R2ResourceBoundsInvalid { field: &'static str, value: u32 },
    R2FuelExhausted,
    R3CoreOverride { performatives: Vec<String> },
    R4SignatureInvalid,
    /// R5 shape/protocol well-formedness violation (REQ-208, REQ-222).
    R5Violation { errors: Vec<String> },
    /// Causal protocol violation (REQ-231, step 6a).
    CausalViolation {
        violation: CausalViolation,
        blame: ViolationError,
    },
    /// Shape constraint violation (REQ-231, step 6b).
    ShapeViolation {
        violation: ShapeViolation,
        blame: ViolationError,
    },
    MalformedMessage { reason: String },
    MalformedDialect { reason: String },
}

impl fmt::Display for ValidationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ValidationError::R1RecursivePerformative { performatives } => {
                write!(
                    f,
                    "R1 violation: recursive performative(s): {}",
                    performatives.join(", ")
                )
            }
            ValidationError::R2ResourceBoundsInvalid { field, value } => {
                write!(f, "R2 violation: invalid resource bound {field}={value}")
            }
            ValidationError::R2FuelExhausted => write!(f, "R2 violation: fuel exhausted"),
            ValidationError::R3CoreOverride { performatives } => {
                write!(
                    f,
                    "R3 violation: core performative(s) overridden: {}",
                    performatives.join(", ")
                )
            }
            ValidationError::R4SignatureInvalid => write!(f, "R4 violation: invalid signature"),
            ValidationError::R5Violation { errors } => {
                write!(f, "R5 violation: {}", errors.join("; "))
            }
            ValidationError::CausalViolation { blame, .. } => {
                write!(f, "causal violation: {}", blame)
            }
            ValidationError::ShapeViolation { blame, .. } => {
                write!(f, "shape violation: {}", blame)
            }
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

/// Runtime context for the full pipeline (REQ-231).
///
/// Provides the dialect registry and message store needed for causal
/// verification (step 6a) and shape checking (step 6b).
pub struct PipelineContext<'a, S: MessageStore> {
    pub registry: &'a DialectRegistry,
    pub store: &'a S,
}

/// Run the lightweight verified pipeline (REQ-110).
///
/// Pipeline: parse → parse_message → validate → (for meta/define/teach: verify R1–R5) → success.
///
/// This entry point does **not** perform causal verification or shape checking
/// on simple messages (no runtime context). Use [`run_pipeline_full`] for
/// complete monitoring.
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

    // For meta define/teach messages, validate the dialect definition (REQ-208, REQ-210).
    if let Err(err) = validate_meta_dialect(&message) {
        return PipelineResult::ValidationError(err);
    }

    PipelineResult::Success(message)
}

/// Run the full verified pipeline with runtime context (REQ-231).
///
/// Pipeline: parse → parse_message → validate → (for meta/define/teach: verify R1–R5)
/// → evaluate (expand) → causal verify (6a) → shape check (6b) → success.
///
/// **Fail-closed**: any error at any step produces a `ValidationError`. No code
/// path from receive to deliver skips verification (CON-206).
pub fn run_pipeline_full<S: MessageStore>(
    input: &str,
    ctx: &PipelineContext<'_, S>,
) -> PipelineResult {
    // Step 1: Parse text → S-expression
    let sexpr = match parser::parse(input) {
        Ok(e) => e,
        Err(e) => return PipelineResult::ParseError(e),
    };

    // Step 2: Parse S-expression → Message
    let message = match crate::message_parser::parse_message(&sexpr) {
        Ok(m) => m,
        Err(reason) => {
            return PipelineResult::ValidationError(ValidationError::MalformedMessage { reason })
        }
    };

    // Step 3: For meta define/teach messages, validate R1–R5 (REQ-208, REQ-210).
    if let Err(err) = validate_meta_dialect(&message) {
        return PipelineResult::ValidationError(err);
    }

    // Steps 4–6: For simple messages, causal verify (6a) → evaluate (4) → shape check (6b).
    //
    // Causal verification runs before evaluation so a causal failure cannot be
    // masked by a downstream shape error, and so callers always see the most
    // specific violation first (REQ-231 fail-closed ordering).
    if let Message::Simple {
        ref caused_by,
        ref thread,
        ..
    } = message
    {
        let performative = message.performative();

        // Step 6a: Causal verification (REQ-231).
        if let Some(perf) = performative {
            let perf_name = perf.name();
            let dialect = match &perf {
                Performative::Core(_) => ctx.registry.find_performative_dialect(perf_name),
                Performative::Custom(_) => ctx.registry.find_performative_dialect(perf_name),
            };

            if let Some(d) = dialect {
                if let Some(ref proto) = d.causal_protocol {
                    let thread_id = ThreadId(
                        thread
                            .clone()
                            .unwrap_or_else(|| String::from("default")),
                    );

                    let result = cbcl_core::protocol::verify_causal(
                        perf_name,
                        caused_by.as_ref(),
                        ctx.store,
                        proto,
                        &thread_id,
                    );

                    match result {
                        VerificationResult::Violation(cv) => {
                            let blame = ViolationError::from_causal_violation(
                                &cv,
                                None,
                                thread.clone(),
                            );
                            blame.record_metrics(&d.name);
                            return PipelineResult::ValidationError(
                                ValidationError::CausalViolation {
                                    violation: cv,
                                    blame,
                                },
                            );
                        }
                        // Valid or Unknown — proceed (Unknown is not a rejection per lattice semantics).
                        _ => {}
                    }
                }
            }
        }

        // Step 4: Evaluate (template expansion). Shape checking is deferred to
        // step 6b so blame can include the expanded form.
        let eval_result = match evaluate_without_shape_check(&message, ctx.registry) {
            Ok(r) => r,
            Err(eval_err) => {
                return PipelineResult::ValidationError(eval_error_to_validation(
                    eval_err,
                    thread.clone(),
                ))
            }
        };

        // Step 6b: Shape checking on expanded message (REQ-223, REQ-224, REQ-231).
        // Compose via conjunction: every matching shape constraint must pass.
        if let Some(perf) = performative {
            let perf_name = perf.name();
            for dialect in ctx.registry.iter() {
                for shape in &dialect.shapes {
                    if shape.performative == perf_name {
                        if let Err(sv) = shape.check(&eval_result.expanded) {
                            let blame = ViolationError::from_shape_violation(
                                &sv,
                                None,
                                thread.clone(),
                                Some(eval_result.expanded.clone()),
                            );
                            blame.record_metrics(&dialect.name);
                            return PipelineResult::ValidationError(
                                ValidationError::ShapeViolation {
                                    violation: sv,
                                    blame,
                                },
                            );
                        }
                    }
                }
            }
        }
    }

    PipelineResult::Success(message)
}

/// Validate meta define/teach dialect definitions (REQ-208, REQ-210).
///
/// Both `(meta (define ...))` and `(meta (teach ...))` carry dialect definitions
/// that must pass R1–R5 before acceptance. The teach form includes protocol and
/// shape declarations for gossip propagation.
fn validate_meta_dialect(message: &Message) -> Result<(), ValidationError> {
    if let Message::Meta { ref dialect_def } = message {
        if let SExpr::List(items) = dialect_def {
            if items.is_empty() {
                return Ok(());
            }

            // (meta (define ...)) — direct dialect definition
            if items[0].is_symbol("define") {
                return validate_define_dialect(dialect_def);
            }

            // (meta (teach <recipient> <define-form>)) — gossip propagation (REQ-210).
            // The teach form wraps a define; extract and validate the inner definition.
            if items[0].is_symbol("teach") {
                // (teach <recipient> (define ...))
                // Find the inner define form — it's the first list element after the symbol.
                for item in items.iter().skip(1) {
                    if let SExpr::List(inner_items) = item {
                        if !inner_items.is_empty() && inner_items[0].is_symbol("define") {
                            return validate_define_dialect(item);
                        }
                    }
                }
                // teach without define — no dialect to validate, pass through.
            }
        }
    }
    Ok(())
}

fn validate_define_dialect(dialect_def: &SExpr) -> Result<(), ValidationError> {
    let dialect = crate::dialect_parser::parse_dialect(dialect_def)
        .map_err(|reason| ValidationError::MalformedDialect { reason })?;

    let recursive = r1::r1_violations(&dialect);
    if !recursive.is_empty() {
        return Err(ValidationError::R1RecursivePerformative {
            performatives: recursive,
        });
    }

    if let Some((field, value)) = invalid_resource_bound(&dialect) {
        return Err(ValidationError::R2ResourceBoundsInvalid { field, value });
    }

    let overrides = r3::r3_violations(&dialect);
    if !overrides.is_empty() {
        return Err(ValidationError::R3CoreOverride {
            performatives: overrides,
        });
    }

    // R5: shape + protocol well-formedness (REQ-208, REQ-222).
    //
    // At parse time there is no registry, so we credit the base dialect for
    // any `extends` entry that names it (the dialect literal might use either
    // "cbcl" or "cbcl-base"). Dialects that extend other named parents must be
    // re-validated at install time via `DialectRegistry::install`, where the
    // registry resolves the full ancestor chain (REQ-206).
    let base = cbcl_core::dialect::base_dialect();
    let extends_base = dialect
        .extends
        .iter()
        .any(|name| name == "cbcl" || name == &base.name);
    let ancestors: alloc::vec::Vec<&cbcl_core::dialect::Dialect> = if extends_base {
        alloc::vec![&base]
    } else {
        alloc::vec![]
    };
    let r5_errors = r5::r5_violations_with_ancestors(&dialect, &ancestors);
    if !r5_errors.is_empty() {
        return Err(ValidationError::R5Violation { errors: r5_errors });
    }

    Ok(())
}

fn invalid_resource_bound(dialect: &Dialect) -> Option<(&'static str, u32)> {
    let bounds = &dialect.resources;
    if bounds.max_depth == 0 || bounds.max_depth > 64 {
        return Some(("max_depth", bounds.max_depth));
    }
    if bounds.max_expansion_size == 0 || bounds.max_expansion_size > 8192 {
        return Some(("max_expansion_size", bounds.max_expansion_size));
    }
    if bounds.verification_time_ms == 0 || bounds.verification_time_ms > 1000 {
        return Some(("verification_time_ms", bounds.verification_time_ms));
    }
    None
}

/// Map evaluator errors to pipeline validation errors.
///
/// `thread` is the originating message's thread, threaded through so blame
/// records carry it even when the evaluator surfaces a violation before the
/// pipeline reaches its dedicated shape-check step (REQ-231).
fn eval_error_to_validation(err: EvalError, thread: Option<String>) -> ValidationError {
    match err {
        EvalError::UnknownPerformative(name) => ValidationError::MalformedMessage {
            reason: alloc::format!("unknown performative: {name}"),
        },
        EvalError::TemplateExpansionFailed { performative: _ } => ValidationError::R2FuelExhausted,
        EvalError::UnknownDialect(name) => ValidationError::MalformedMessage {
            reason: alloc::format!("unknown dialect: {name}"),
        },
        EvalError::MalformedMessage(reason) => ValidationError::MalformedMessage { reason },
        EvalError::ShapeViolation(sv) => {
            let blame = ViolationError::from_shape_violation(&sv, None, thread, None);
            ValidationError::ShapeViolation {
                violation: sv,
                blame,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use cbcl_core::dialect::{DialectRegistry, PerformativeDef, ResourceBounds};
    use cbcl_core::message::{CausedBy, MessageType};
    use cbcl_core::protocol::{CausalProtocol, NodeRef, StepDecl};
    use cbcl_core::sexpr::Atom;
    use cbcl_core::shape::{ShapeConstraint, ShapeRule, TypeConstraint};
    use cbcl_core::store::{ContentHash, ThreadedMessageStore, ThreadId};
    use alloc::collections::BTreeMap;

    fn effect_template(action: &str) -> SExpr {
        SExpr::List(alloc::vec![
            SExpr::Atom(Atom::Symbol(String::from("effect"))),
            SExpr::Atom(Atom::Symbol(String::from(action))),
        ])
    }

    fn make_simple_msg(perf: &str, caused_by: Option<CausedBy>) -> Message {
        Message::Simple {
            performative: Performative::Custom(String::from(perf)),
            recipient: None,
            content: SExpr::Atom(Atom::Str(String::from("test"))),
            params: alloc::vec![],
            thread: None,
            sender: None,
            caused_by,
        }
    }

    // -- Basic pipeline (no context) --

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

    #[test]
    fn pipeline_rejects_r3_core_override() {
        let result = run_pipeline("(meta (define bad (cbcl) @author (extend tell () x)))");
        assert!(matches!(
            result,
            PipelineResult::ValidationError(ValidationError::R3CoreOverride { .. })
        ));
    }

    #[test]
    fn pipeline_rejects_mutual_recursion() {
        let result = run_pipeline(
            "(meta (define cyclic (cbcl) @author (extend ping () (pong)) (extend pong () (ping))))",
        );
        assert!(matches!(
            result,
            PipelineResult::ValidationError(ValidationError::R1RecursivePerformative { .. })
        ));
    }

    // -- REQ-210: teach messages validated same as define --

    #[test]
    fn pipeline_teach_validates_r3() {
        let result =
            run_pipeline("(meta (teach @bob (define bad (cbcl) @author (extend tell () x))))");
        assert!(matches!(
            result,
            PipelineResult::ValidationError(ValidationError::R3CoreOverride { .. })
        ));
    }

    #[test]
    fn pipeline_teach_valid_passes() {
        let result =
            run_pipeline("(meta (teach @bob (define good-dialect (cbcl) @author)))");
        assert!(matches!(result, PipelineResult::Success(_)));
    }

    // -- REQ-231: full pipeline with context --

    #[test]
    fn full_pipeline_simple_message_passes() {
        let registry = DialectRegistry::new();
        let store = ThreadedMessageStore::new();
        let ctx = PipelineContext {
            registry: &registry,
            store: &store,
        };
        let result = run_pipeline_full("(tell \"hello\")", &ctx);
        assert!(matches!(result, PipelineResult::Success(_)));
    }

    #[test]
    fn full_pipeline_rejects_causal_violation() {
        let mut registry = DialectRegistry::new();

        // Install a dialect with a causal protocol: begin → greet
        let mut steps = BTreeMap::new();
        steps.insert(
            "begin".into(),
            StepDecl {
                performative: "begin".into(),
                predecessors: alloc::vec![],
                successors: alloc::vec![NodeRef::Single("greet".into())],
            },
        );
        steps.insert(
            "greet".into(),
            StepDecl {
                performative: "greet".into(),
                predecessors: alloc::vec![NodeRef::Single("begin".into())],
                successors: alloc::vec![],
            },
        );
        let proto = CausalProtocol { steps };

        registry
            .install(cbcl_core::dialect::Dialect {
                name: String::from("proto-dialect"),
                extends: alloc::vec![String::from("cbcl")],
                author: None,
                performatives: alloc::vec![PerformativeDef {
                    name: String::from("greet"),
                    params: alloc::vec![],
                    template: effect_template("greet-action"),
                }],
                resources: ResourceBounds {
                    max_depth: 8,
                    max_expansion_size: 512,
                    verification_time_ms: 10,
                },
                examples: alloc::vec![],
                signature: None,
                hash: None,
                protocol: None,
                causal_protocol: Some(proto),
                shapes: alloc::vec![],
            })
            .unwrap();

        let store = ThreadedMessageStore::new();
        let ctx = PipelineContext {
            registry: &registry,
            store: &store,
        };

        // Send "greet" without :caused-by — protocol requires begin as predecessor.
        let result = run_pipeline_full("(greet \"hi\")", &ctx);
        assert!(
            matches!(
                result,
                PipelineResult::ValidationError(ValidationError::CausalViolation { .. })
            ),
            "expected causal violation, got {:?}",
            result
        );
    }

    #[test]
    fn full_pipeline_shape_violation_rejected() {
        let mut registry = DialectRegistry::new();

        // Install dialect with shape constraint requiring :target string
        registry
            .install(cbcl_core::dialect::Dialect {
                name: String::from("shape-dialect"),
                extends: alloc::vec![String::from("cbcl")],
                author: None,
                performatives: alloc::vec![PerformativeDef {
                    name: String::from("propose"),
                    params: alloc::vec![],
                    template: effect_template("propose-action"),
                }],
                resources: ResourceBounds {
                    max_depth: 8,
                    max_expansion_size: 512,
                    verification_time_ms: 10,
                },
                examples: alloc::vec![],
                signature: None,
                hash: None,
                protocol: None,
                causal_protocol: None,
                shapes: alloc::vec![ShapeConstraint {
                    performative: String::from("propose"),
                    rules: alloc::vec![ShapeRule::Require {
                        keyword: String::from("target"),
                        type_constraint: Some(TypeConstraint::String),
                        children: alloc::vec![],
                    }],
                }],
            })
            .unwrap();

        let store = ThreadedMessageStore::new();
        let ctx = PipelineContext {
            registry: &registry,
            store: &store,
        };

        // "propose" without :target — shape requires it.
        let result = run_pipeline_full("(propose \"idea\")", &ctx);
        assert!(
            matches!(
                result,
                PipelineResult::ValidationError(ValidationError::ShapeViolation { .. })
            ),
            "expected shape violation, got {:?}",
            result
        );
    }

    #[test]
    fn full_pipeline_causal_valid_with_predecessor() {
        let mut registry = DialectRegistry::new();

        // Protocol: begin → ack
        let mut steps = BTreeMap::new();
        steps.insert(
            "begin".into(),
            StepDecl {
                performative: "begin".into(),
                predecessors: alloc::vec![],
                successors: alloc::vec![NodeRef::Single("ack".into())],
            },
        );
        steps.insert(
            "ack".into(),
            StepDecl {
                performative: "ack".into(),
                predecessors: alloc::vec![NodeRef::Single("begin".into())],
                successors: alloc::vec![],
            },
        );
        let proto = CausalProtocol { steps };

        registry
            .install(cbcl_core::dialect::Dialect {
                name: String::from("ack-dialect"),
                extends: alloc::vec![String::from("cbcl")],
                author: None,
                performatives: alloc::vec![PerformativeDef {
                    name: String::from("ack"),
                    params: alloc::vec![],
                    template: effect_template("ack-action"),
                }],
                resources: ResourceBounds {
                    max_depth: 8,
                    max_expansion_size: 512,
                    verification_time_ms: 10,
                },
                examples: alloc::vec![],
                signature: None,
                hash: None,
                protocol: None,
                causal_protocol: Some(proto),
                shapes: alloc::vec![],
            })
            .unwrap();

        let thread = ThreadId(String::from("default"));
        let mut store = ThreadedMessageStore::new();
        // Insert a "begin" message that the ack can reference.
        store.append(
            ContentHash(String::from("abc123")),
            thread.clone(),
            make_simple_msg("begin", Some(CausedBy::Begin)),
        );

        let ctx = PipelineContext {
            registry: &registry,
            store: &store,
        };

        // "ack" with :caused-by pointing to the begin message.
        let result = run_pipeline_full("(ack \"done\" :caused-by \"abc123\")", &ctx);
        assert!(
            matches!(result, PipelineResult::Success(_)),
            "expected success, got {:?}",
            result
        );
    }

    #[test]
    fn full_pipeline_meta_define_still_validated() {
        let registry = DialectRegistry::new();
        let store = ThreadedMessageStore::new();
        let ctx = PipelineContext {
            registry: &registry,
            store: &store,
        };
        // R3 violation via full pipeline
        let result = run_pipeline_full(
            "(meta (define bad (cbcl) @author (extend tell () x)))",
            &ctx,
        );
        assert!(matches!(
            result,
            PipelineResult::ValidationError(ValidationError::R3CoreOverride { .. })
        ));
    }

    #[test]
    fn full_pipeline_teach_validated() {
        let registry = DialectRegistry::new();
        let store = ThreadedMessageStore::new();
        let ctx = PipelineContext {
            registry: &registry,
            store: &store,
        };
        let result = run_pipeline_full(
            "(meta (teach @bob (define bad (cbcl) @author (extend tell () x))))",
            &ctx,
        );
        assert!(matches!(
            result,
            PipelineResult::ValidationError(ValidationError::R3CoreOverride { .. })
        ));
    }

    // -- REQ-231: Pipeline orders causal before shape so a causal violation
    // is not masked by an inline shape failure (was: shape ran inside evaluate
    // before causal verification). --

    #[test]
    fn full_pipeline_causal_violation_takes_precedence_over_shape() {
        let mut registry = DialectRegistry::new();

        // Protocol requires "begin" before "ack". Shape requires :target string.
        let mut steps = BTreeMap::new();
        steps.insert(
            "begin".into(),
            StepDecl {
                performative: "begin".into(),
                predecessors: alloc::vec![],
                successors: alloc::vec![NodeRef::Single("ack".into())],
            },
        );
        steps.insert(
            "ack".into(),
            StepDecl {
                performative: "ack".into(),
                predecessors: alloc::vec![NodeRef::Single("begin".into())],
                successors: alloc::vec![],
            },
        );
        let proto = CausalProtocol { steps };

        registry
            .install(cbcl_core::dialect::Dialect {
                name: String::from("ack-with-shape"),
                extends: alloc::vec![String::from("cbcl")],
                author: None,
                performatives: alloc::vec![PerformativeDef {
                    name: String::from("ack"),
                    params: alloc::vec![],
                    template: effect_template("ack-action"),
                }],
                resources: ResourceBounds {
                    max_depth: 8,
                    max_expansion_size: 512,
                    verification_time_ms: 10,
                },
                examples: alloc::vec![],
                signature: None,
                hash: None,
                protocol: None,
                causal_protocol: Some(proto),
                shapes: alloc::vec![ShapeConstraint {
                    performative: String::from("ack"),
                    rules: alloc::vec![ShapeRule::Require {
                        keyword: String::from("target"),
                        type_constraint: Some(TypeConstraint::String),
                        children: alloc::vec![],
                    }],
                }],
            })
            .unwrap();

        let store = ThreadedMessageStore::new();
        let ctx = PipelineContext {
            registry: &registry,
            store: &store,
        };

        // ack with no :caused-by AND no :target — both causal and shape would fail.
        // We must see CausalViolation, not ShapeViolation, because causal is checked first.
        let result = run_pipeline_full("(ack \"done\")", &ctx);
        assert!(
            matches!(
                result,
                PipelineResult::ValidationError(ValidationError::CausalViolation { .. })
            ),
            "expected CausalViolation to take precedence, got {:?}",
            result
        );
    }
}
