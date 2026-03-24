//! Message evaluator: dispatch, template expansion, effect interpretation, thread tracking.
//!
//! The evaluator is a pure function that takes a message and a dialect registry,
//! and returns a result containing the expanded effect form and a list of
//! concrete effects to be applied by the caller (typically an Agent).
//!
//! Evaluation flow by message type:
//! - **Simple**: look up performative → expand template → interpret effect form
//! - **Meta**: produce an `InstallDialect` effect with the dialect definition
//! - **Dialect**: resolve named dialect → evaluate inner message in that scope
//! - **Wrapped**: unwrap and evaluate the inner message

#![forbid(unsafe_code)]

use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

use crate::dialect::{Dialect, DialectRegistry};
use crate::message::{Message, MessageType, Performative};
use crate::r2::ResourceState;
use crate::sexpr::{Atom, SExpr};
use crate::shape::ShapeViolation;
use crate::template::expand_template;

// ---------------------------------------------------------------------------
// Effect
// ---------------------------------------------------------------------------

/// A concrete effect produced by message evaluation.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Effect {
    /// Send a message to a recipient.
    SendMessage {
        recipient: Option<String>,
        content: SExpr,
    },
    /// Send a query to a recipient.
    SendQuery {
        recipient: Option<String>,
        content: SExpr,
    },
    /// Send a reply.
    SendReply {
        recipient: Option<String>,
        content: SExpr,
    },
    /// Signal an error.
    SignalError { content: SExpr },
    /// Acknowledge receipt.
    Acknowledge,
    /// Cancel a conversation.
    CancelConversation,
    /// Announce agent presence.
    AnnouncePresence,
    /// Announce agent departure.
    AnnounceDeparture,
    /// Store a belief (content of a tell message).
    StoreBelief(SExpr),
    /// Remove a belief.
    RemoveBelief(SExpr),
    /// Install a dialect from a meta message (carries the raw S-expression definition).
    InstallDialect(SExpr),
    /// A custom effect from a dialect-defined performative.
    Custom(SExpr),
}

// ---------------------------------------------------------------------------
// EvalError
// ---------------------------------------------------------------------------

/// Errors that can occur during message evaluation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EvalError {
    /// The performative is not defined in any installed dialect.
    UnknownPerformative(String),
    /// Template expansion failed (e.g. resource bounds exceeded, no matching cond branch).
    TemplateExpansionFailed { performative: String },
    /// The named dialect is not installed.
    UnknownDialect(String),
    /// The message is malformed.
    MalformedMessage(String),
    /// The expanded message violates a shape constraint (REQ-223).
    ShapeViolation(ShapeViolation),
}

impl fmt::Display for EvalError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            EvalError::UnknownPerformative(name) => {
                write!(f, "unknown performative: {name}")
            }
            EvalError::TemplateExpansionFailed { performative } => {
                write!(
                    f,
                    "template expansion failed for performative: {performative}"
                )
            }
            EvalError::UnknownDialect(name) => {
                write!(f, "unknown dialect: {name}")
            }
            EvalError::MalformedMessage(msg) => {
                write!(f, "malformed message: {msg}")
            }
            EvalError::ShapeViolation(v) => {
                write!(f, "{v}")
            }
        }
    }
}

// ---------------------------------------------------------------------------
// EvalResult
// ---------------------------------------------------------------------------

/// The result of evaluating a message.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EvalResult {
    /// The expanded effect form (S-expression from template expansion).
    pub expanded: SExpr,
    /// Concrete effects to be applied.
    pub effects: Vec<Effect>,
    /// Thread ID for conversation tracking, if present on the source message.
    pub thread: Option<String>,
}

// ---------------------------------------------------------------------------
// Core evaluation
// ---------------------------------------------------------------------------

/// Evaluate a message against a dialect registry.
///
/// This is a pure function: it inspects the message, expands templates using
/// the registry, and returns the resulting effects without mutating any state.
pub fn evaluate(msg: &Message, registry: &DialectRegistry) -> Result<EvalResult, EvalError> {
    evaluate_with_scope(msg, registry, None)
}

fn evaluate_with_scope(
    msg: &Message,
    registry: &DialectRegistry,
    scope: Option<&Dialect>,
) -> Result<EvalResult, EvalError> {
    match msg.message_type() {
        MessageType::Simple => evaluate_simple(msg, registry, scope),
        MessageType::Meta => evaluate_meta(msg),
        MessageType::Dialect => evaluate_dialect(msg, registry),
        MessageType::Wrapped => evaluate_wrapped(msg, registry, scope),
    }
}

/// Evaluate a simple message: look up performative, expand template, interpret effects.
fn evaluate_simple(
    msg: &Message,
    registry: &DialectRegistry,
    scope: Option<&Dialect>,
) -> Result<EvalResult, EvalError> {
    let performative = msg
        .performative()
        .ok_or_else(|| EvalError::MalformedMessage(String::from("missing performative")))?;

    let perf_name = performative.name();

    let dialect = resolve_performative_dialect(performative, registry, scope)
        .ok_or_else(|| EvalError::UnknownPerformative(String::from(perf_name)))?;

    let def = dialect
        .find_performative(perf_name)
        .ok_or_else(|| EvalError::UnknownPerformative(String::from(perf_name)))?;

    // Build arguments from the message content and params.
    let mut args = Vec::new();
    if let Some(content) = msg.content() {
        args.push(content.clone());
    }
    if let Message::Simple { params, .. } = msg {
        args.extend(params.iter().cloned());
    }

    // Expand the template with resource bounds from the dialect.
    let mut rs = ResourceState::initial(&dialect.resources);
    let expanded =
        expand_template(def, &args, &mut rs).ok_or_else(|| EvalError::TemplateExpansionFailed {
            performative: String::from(perf_name),
        })?;

    // Shape checking on expanded message (REQ-223, REQ-224).
    // All shape constraints matching the performative compose via conjunction:
    // every matching constraint must pass.
    check_shapes(perf_name, &expanded, registry)?;

    // Interpret the expanded form into concrete effects.
    let recipient = msg.recipient().map(String::from);
    let content = msg.content().cloned().unwrap_or(SExpr::List(Vec::new()));
    let effects = interpret_effects(&expanded, recipient, content, performative);

    Ok(EvalResult {
        expanded,
        effects,
        thread: msg.thread().map(String::from),
    })
}

/// Evaluate a meta message: produce an InstallDialect effect.
fn evaluate_meta(msg: &Message) -> Result<EvalResult, EvalError> {
    let dialect_def = msg.dialect_def().ok_or_else(|| {
        EvalError::MalformedMessage(String::from("meta message missing dialect definition"))
    })?;

    let expanded = SExpr::List(vec![
        SExpr::Atom(Atom::Symbol(String::from("effect"))),
        SExpr::Atom(Atom::Symbol(String::from("install-dialect"))),
    ]);

    Ok(EvalResult {
        expanded: expanded.clone(),
        effects: vec![Effect::InstallDialect(dialect_def.clone())],
        thread: None,
    })
}

/// Evaluate a dialect-scoped message: resolve dialect, then evaluate inner message.
fn evaluate_dialect(msg: &Message, registry: &DialectRegistry) -> Result<EvalResult, EvalError> {
    let dialect_name = msg
        .dialect_name()
        .ok_or_else(|| EvalError::MalformedMessage(String::from("dialect message missing name")))?;

    let dialect = registry
        .find_by_name(dialect_name)
        .ok_or_else(|| EvalError::UnknownDialect(String::from(dialect_name)))?;

    // Evaluate the inner message (which may use performatives from the named dialect).
    let inner = msg.inner_message().ok_or_else(|| {
        EvalError::MalformedMessage(String::from("dialect message missing inner"))
    })?;

    evaluate_with_scope(inner, registry, Some(dialect))
}

/// Evaluate a wrapped message: unwrap and evaluate the inner message.
fn evaluate_wrapped(
    msg: &Message,
    registry: &DialectRegistry,
    scope: Option<&Dialect>,
) -> Result<EvalResult, EvalError> {
    let inner = msg.inner_message().ok_or_else(|| {
        EvalError::MalformedMessage(String::from("wrapped message missing inner"))
    })?;

    evaluate_with_scope(inner, registry, scope)
}

fn resolve_performative_dialect<'a>(
    performative: &Performative,
    registry: &'a DialectRegistry,
    scope: Option<&'a Dialect>,
) -> Option<&'a Dialect> {
    if !performative.is_core() {
        if let Some(dialect) = scope {
            if dialect.defines_performative(performative.name()) {
                return Some(dialect);
            }
            return None;
        }
    }

    registry.find_performative_dialect(performative.name())
}

// ---------------------------------------------------------------------------
// Shape checking (REQ-223, REQ-224)
// ---------------------------------------------------------------------------

/// Check all shape constraints for a performative across all installed dialects.
///
/// Multiple constraints compose via conjunction (REQ-224): every matching
/// constraint must pass. This is a VPL tree-walking operation and trivially
/// preserves DCFL membership (REQ-225).
fn check_shapes(
    performative: &str,
    expanded: &SExpr,
    registry: &DialectRegistry,
) -> Result<(), EvalError> {
    for dialect in registry.iter() {
        for shape in &dialect.shapes {
            if shape.performative == performative {
                shape.check(expanded).map_err(EvalError::ShapeViolation)?;
            }
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Effect interpretation
// ---------------------------------------------------------------------------

/// Interpret an expanded template form into concrete effects.
///
/// The base dialect templates expand to `(effect <action>)`. Custom dialect
/// templates may expand to arbitrary S-expressions, which become `Custom` effects.
fn interpret_effects(
    expanded: &SExpr,
    recipient: Option<String>,
    content: SExpr,
    _performative: &Performative,
) -> Vec<Effect> {
    // Check for (effect <action>) form.
    if let Some(action) = extract_effect_action(expanded) {
        return match action.as_str() {
            "send-message" => {
                // A tell also stores the content as a belief for the receiver.
                vec![
                    Effect::SendMessage {
                        recipient,
                        content: content.clone(),
                    },
                    Effect::StoreBelief(content),
                ]
            }
            "send-query" => vec![Effect::SendQuery { recipient, content }],
            "send-reply" => vec![Effect::SendReply { recipient, content }],
            "signal-error" => vec![Effect::SignalError { content }],
            "acknowledge" => vec![Effect::Acknowledge],
            "cancel-conversation" => vec![Effect::CancelConversation],
            "announce-presence" => vec![Effect::AnnouncePresence],
            "announce-departure" => vec![Effect::AnnounceDeparture],
            _ => vec![Effect::Custom(expanded.clone())],
        };
    }

    // Not an (effect ...) form — treat as a custom effect from a dialect template.
    vec![Effect::Custom(expanded.clone())]
}

/// Extract the action name from an `(effect <action>)` form.
fn extract_effect_action(expr: &SExpr) -> Option<String> {
    if let SExpr::List(items) = expr {
        if items.len() == 2 && items[0].is_symbol("effect") {
            if let SExpr::Atom(Atom::Symbol(action)) = &items[1] {
                return Some(action.clone());
            }
        }
    }
    None
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dialect::{Dialect, PerformativeDef, ResourceBounds};
    use crate::message::{CorePerformative, WrapperType};
    use alloc::boxed::Box;

    fn make_registry() -> DialectRegistry {
        DialectRegistry::new()
    }

    fn make_registry_with_custom() -> DialectRegistry {
        let mut reg = DialectRegistry::new();
        reg.install(Dialect {
            name: String::from("logistics"),
            extends: vec![String::from("cbcl")],
            author: None,
            performatives: vec![PerformativeDef {
                name: String::from("ship"),
                params: vec![
                    SExpr::Atom(Atom::Symbol(String::from("package"))),
                    SExpr::Atom(Atom::Symbol(String::from("destination"))),
                ],
                template: SExpr::List(vec![
                    SExpr::Atom(Atom::Symbol(String::from("effect"))),
                    SExpr::Atom(Atom::Symbol(String::from("dispatch-shipment"))),
                ]),
            }],
            resources: ResourceBounds {
                max_depth: 8,
                max_expansion_size: 512,
                verification_time_ms: 10,
            },
            examples: Vec::new(),
            signature: None,
            hash: None,
            protocol: None, shapes: Vec::new(),
        })
        .unwrap();
        reg
    }

    fn make_registry_with_duplicate_customs() -> DialectRegistry {
        let mut reg = make_registry_with_custom();
        reg.install(Dialect {
            name: String::from("warehouse"),
            extends: vec![String::from("cbcl")],
            author: None,
            performatives: vec![PerformativeDef {
                name: String::from("ship"),
                params: vec![
                    SExpr::Atom(Atom::Symbol(String::from("package"))),
                    SExpr::Atom(Atom::Symbol(String::from("destination"))),
                ],
                template: SExpr::List(vec![
                    SExpr::Atom(Atom::Symbol(String::from("effect"))),
                    SExpr::Atom(Atom::Symbol(String::from("warehouse-dispatch"))),
                ]),
            }],
            resources: ResourceBounds {
                max_depth: 8,
                max_expansion_size: 512,
                verification_time_ms: 10,
            },
            examples: Vec::new(),
            signature: None,
            hash: None,
            protocol: None, shapes: Vec::new(),
        })
        .unwrap();
        reg
    }

    // -- Simple message evaluation --

    #[test]
    fn eval_tell_produces_send_message_and_store_belief() {
        let reg = make_registry();
        let msg = Message::Simple {
            performative: Performative::Core(CorePerformative::Tell),
            recipient: Some(String::from("@bob")),
            content: SExpr::Atom(Atom::Str(String::from("hello"))),
            params: Vec::new(),
            thread: None,
            sender: None,
        };
        let result = evaluate(&msg, &reg).unwrap();
        assert_eq!(result.effects.len(), 2);
        assert_eq!(
            result.effects[0],
            Effect::SendMessage {
                recipient: Some(String::from("@bob")),
                content: SExpr::Atom(Atom::Str(String::from("hello"))),
            }
        );
        assert_eq!(
            result.effects[1],
            Effect::StoreBelief(SExpr::Atom(Atom::Str(String::from("hello")))),
        );
        // Expanded form is (effect send-message)
        assert!(result.expanded.is_symbol("effect") == false);
        assert!(extract_effect_action(&result.expanded) == Some(String::from("send-message")));
    }

    #[test]
    fn eval_ask_produces_send_query() {
        let reg = make_registry();
        let msg = Message::Simple {
            performative: Performative::Core(CorePerformative::Ask),
            recipient: Some(String::from("@alice")),
            content: SExpr::Atom(Atom::Str(String::from("what time?"))),
            params: Vec::new(),
            thread: None,
            sender: None,
        };
        let result = evaluate(&msg, &reg).unwrap();
        assert_eq!(result.effects.len(), 1);
        assert_eq!(
            result.effects[0],
            Effect::SendQuery {
                recipient: Some(String::from("@alice")),
                content: SExpr::Atom(Atom::Str(String::from("what time?"))),
            }
        );
    }

    #[test]
    fn eval_reply_produces_send_reply() {
        let reg = make_registry();
        let msg = Message::Simple {
            performative: Performative::Core(CorePerformative::Reply),
            recipient: None,
            content: SExpr::Atom(Atom::Str(String::from("done"))),
            params: Vec::new(),
            thread: Some(String::from("conv-1")),
            sender: None,
        };
        let result = evaluate(&msg, &reg).unwrap();
        assert_eq!(result.effects.len(), 1);
        assert_eq!(
            result.effects[0],
            Effect::SendReply {
                recipient: None,
                content: SExpr::Atom(Atom::Str(String::from("done"))),
            }
        );
        assert_eq!(result.thread, Some(String::from("conv-1")));
    }

    #[test]
    fn eval_error_produces_signal_error() {
        let reg = make_registry();
        let msg = Message::Simple {
            performative: Performative::Core(CorePerformative::Error),
            recipient: None,
            content: SExpr::Atom(Atom::Str(String::from("fail"))),
            params: Vec::new(),
            thread: None,
            sender: None,
        };
        let result = evaluate(&msg, &reg).unwrap();
        assert_eq!(
            result.effects[0],
            Effect::SignalError {
                content: SExpr::Atom(Atom::Str(String::from("fail"))),
            }
        );
    }

    #[test]
    fn eval_ok_produces_acknowledge() {
        let reg = make_registry();
        let msg = Message::Simple {
            performative: Performative::Core(CorePerformative::Ok),
            recipient: None,
            content: SExpr::List(Vec::new()),
            params: Vec::new(),
            thread: None,
            sender: None,
        };
        let result = evaluate(&msg, &reg).unwrap();
        assert_eq!(result.effects[0], Effect::Acknowledge);
    }

    #[test]
    fn eval_cancel_produces_cancel_conversation() {
        let reg = make_registry();
        let msg = Message::Simple {
            performative: Performative::Core(CorePerformative::Cancel),
            recipient: None,
            content: SExpr::List(Vec::new()),
            params: Vec::new(),
            thread: Some(String::from("conv-2")),
            sender: None,
        };
        let result = evaluate(&msg, &reg).unwrap();
        assert_eq!(result.effects[0], Effect::CancelConversation);
        assert_eq!(result.thread, Some(String::from("conv-2")));
    }

    #[test]
    fn eval_hello_produces_announce_presence() {
        let reg = make_registry();
        let msg = Message::Simple {
            performative: Performative::Core(CorePerformative::Hello),
            recipient: None,
            content: SExpr::List(Vec::new()),
            params: Vec::new(),
            thread: None,
            sender: None,
        };
        let result = evaluate(&msg, &reg).unwrap();
        assert_eq!(result.effects[0], Effect::AnnouncePresence);
    }

    #[test]
    fn eval_bye_produces_announce_departure() {
        let reg = make_registry();
        let msg = Message::Simple {
            performative: Performative::Core(CorePerformative::Bye),
            recipient: None,
            content: SExpr::List(Vec::new()),
            params: Vec::new(),
            thread: None,
            sender: None,
        };
        let result = evaluate(&msg, &reg).unwrap();
        assert_eq!(result.effects[0], Effect::AnnounceDeparture);
    }

    #[test]
    fn eval_unknown_performative_errors() {
        let reg = make_registry();
        let msg = Message::Simple {
            performative: Performative::Custom(String::from("nonexistent")),
            recipient: None,
            content: SExpr::List(Vec::new()),
            params: Vec::new(),
            thread: None,
            sender: None,
        };
        let err = evaluate(&msg, &reg).unwrap_err();
        assert!(matches!(err, EvalError::UnknownPerformative(_)));
    }

    // -- Custom dialect performative --

    #[test]
    fn eval_custom_performative() {
        let reg = make_registry_with_custom();
        let msg = Message::Simple {
            performative: Performative::Custom(String::from("ship")),
            recipient: None,
            content: SExpr::Atom(Atom::Str(String::from("PKG-123"))),
            params: vec![SExpr::Atom(Atom::Symbol(String::from("warehouse-A")))],
            thread: None,
            sender: None,
        };
        let result = evaluate(&msg, &reg).unwrap();
        // Template expands to (effect dispatch-shipment) — a custom effect action
        assert_eq!(
            extract_effect_action(&result.expanded),
            Some(String::from("dispatch-shipment"))
        );
        assert_eq!(result.effects.len(), 1);
        assert_eq!(result.effects[0], Effect::Custom(result.expanded.clone()));
    }

    // -- Meta message evaluation --

    #[test]
    fn eval_meta_produces_install_dialect() {
        let reg = make_registry();
        let dialect_def = SExpr::List(vec![
            SExpr::Atom(Atom::Symbol(String::from("define"))),
            SExpr::Atom(Atom::Symbol(String::from("test-dialect"))),
        ]);
        let msg = Message::Meta {
            dialect_def: dialect_def.clone(),
        };
        let result = evaluate(&msg, &reg).unwrap();
        assert_eq!(result.effects.len(), 1);
        assert_eq!(result.effects[0], Effect::InstallDialect(dialect_def));
    }

    // -- Dialect message evaluation --

    #[test]
    fn eval_dialect_message_delegates_to_inner() {
        let reg = make_registry_with_custom();
        let inner = Message::Simple {
            performative: Performative::Custom(String::from("ship")),
            recipient: None,
            content: SExpr::Atom(Atom::Str(String::from("PKG-456"))),
            params: vec![SExpr::Atom(Atom::Symbol(String::from("depot-B")))],
            thread: Some(String::from("shipment-thread")),
            sender: None,
        };
        let msg = Message::Dialect {
            dialect_name: String::from("logistics"),
            inner: Box::new(inner),
        };
        let result = evaluate(&msg, &reg).unwrap();
        assert_eq!(
            extract_effect_action(&result.expanded),
            Some(String::from("dispatch-shipment"))
        );
        assert_eq!(result.thread, Some(String::from("shipment-thread")));
    }

    #[test]
    fn eval_dialect_message_uses_named_scope_for_custom_performatives() {
        let reg = make_registry_with_duplicate_customs();
        let inner = Message::Simple {
            performative: Performative::Custom(String::from("ship")),
            recipient: None,
            content: SExpr::Atom(Atom::Str(String::from("PKG-789"))),
            params: vec![SExpr::Atom(Atom::Symbol(String::from("dock-C")))],
            thread: None,
            sender: None,
        };
        let msg = Message::Dialect {
            dialect_name: String::from("logistics"),
            inner: Box::new(inner),
        };

        let result = evaluate(&msg, &reg).unwrap();
        assert_eq!(
            extract_effect_action(&result.expanded),
            Some(String::from("dispatch-shipment"))
        );
    }

    #[test]
    fn eval_dialect_message_rejects_custom_performative_outside_scope() {
        let reg = make_registry_with_duplicate_customs();
        let inner = Message::Simple {
            performative: Performative::Custom(String::from("ship")),
            recipient: None,
            content: SExpr::Atom(Atom::Str(String::from("PKG-000"))),
            params: vec![SExpr::Atom(Atom::Symbol(String::from("dock-D")))],
            thread: None,
            sender: None,
        };
        let msg = Message::Dialect {
            dialect_name: String::from("cbcl-base"),
            inner: Box::new(inner),
        };

        let err = evaluate(&msg, &reg).unwrap_err();
        assert!(matches!(err, EvalError::UnknownPerformative(_)));
    }

    #[test]
    fn eval_dialect_unknown_dialect_errors() {
        let reg = make_registry();
        let inner = Message::Simple {
            performative: Performative::Core(CorePerformative::Tell),
            recipient: None,
            content: SExpr::Atom(Atom::Str(String::from("hi"))),
            params: Vec::new(),
            thread: None,
            sender: None,
        };
        let msg = Message::Dialect {
            dialect_name: String::from("nonexistent"),
            inner: Box::new(inner),
        };
        let err = evaluate(&msg, &reg).unwrap_err();
        assert!(matches!(err, EvalError::UnknownDialect(_)));
    }

    // -- Wrapped message evaluation --

    #[test]
    fn eval_wrapped_evaluates_inner() {
        let reg = make_registry();
        let inner = Message::Simple {
            performative: Performative::Core(CorePerformative::Tell),
            recipient: Some(String::from("@bob")),
            content: SExpr::Atom(Atom::Str(String::from("secret"))),
            params: Vec::new(),
            thread: None,
            sender: None,
        };
        let msg = Message::Wrapped {
            wrapper: WrapperType::Envelope,
            params: vec![
                SExpr::Atom(Atom::Keyword(String::from("from"))),
                SExpr::Atom(Atom::Symbol(String::from("@alice"))),
            ],
            content: Box::new(inner),
        };
        let result = evaluate(&msg, &reg).unwrap();
        assert_eq!(
            extract_effect_action(&result.expanded),
            Some(String::from("send-message"))
        );
        assert_eq!(result.effects.len(), 2); // SendMessage + StoreBelief
    }

    // -- Thread tracking --

    #[test]
    fn eval_preserves_thread_id() {
        let reg = make_registry();
        let msg = Message::Simple {
            performative: Performative::Core(CorePerformative::Tell),
            recipient: Some(String::from("@bob")),
            content: SExpr::Atom(Atom::Str(String::from("hi"))),
            params: Vec::new(),
            thread: Some(String::from("thread-42")),
            sender: None,
        };
        let result = evaluate(&msg, &reg).unwrap();
        assert_eq!(result.thread, Some(String::from("thread-42")));
    }

    #[test]
    fn eval_no_thread_when_absent() {
        let reg = make_registry();
        let msg = Message::Simple {
            performative: Performative::Core(CorePerformative::Tell),
            recipient: None,
            content: SExpr::Atom(Atom::Str(String::from("hi"))),
            params: Vec::new(),
            thread: None,
            sender: None,
        };
        let result = evaluate(&msg, &reg).unwrap();
        assert!(result.thread.is_none());
    }

    // -- EvalError Display --

    #[test]
    fn eval_error_display() {
        let e1 = EvalError::UnknownPerformative(String::from("foo"));
        assert!(alloc::format!("{e1}").contains("foo"));

        let e2 = EvalError::TemplateExpansionFailed {
            performative: String::from("bar"),
        };
        assert!(alloc::format!("{e2}").contains("bar"));

        let e3 = EvalError::UnknownDialect(String::from("baz"));
        assert!(alloc::format!("{e3}").contains("baz"));

        let e4 = EvalError::MalformedMessage(String::from("oops"));
        assert!(alloc::format!("{e4}").contains("oops"));
    }

    // -- extract_effect_action helper --

    #[test]
    fn extract_effect_action_valid() {
        let expr: SExpr = "(effect send-message)".parse().unwrap();
        assert_eq!(
            extract_effect_action(&expr),
            Some(String::from("send-message"))
        );
    }

    #[test]
    fn extract_effect_action_non_effect() {
        let expr: SExpr = "(tell @bob \"hi\")".parse().unwrap();
        assert_eq!(extract_effect_action(&expr), None);
    }

    #[test]
    fn extract_effect_action_atom() {
        let expr: SExpr = "hello".parse().unwrap();
        assert_eq!(extract_effect_action(&expr), None);
    }

    // -- Shape checking integration (REQ-223, REQ-224, REQ-225) --

    use crate::shape::{ShapeConstraint, ShapeRule, TypeConstraint};

    fn make_registry_with_shape() -> DialectRegistry {
        let mut reg = DialectRegistry::new();
        // Template: (ship-effect :package <pkg> :dest <dst>)
        // Params bind: pkg = args[0], dst = args[1]
        reg.install(Dialect {
            name: String::from("logistics"),
            extends: vec![String::from("cbcl")],
            author: None,
            performatives: vec![PerformativeDef {
                name: String::from("ship"),
                params: vec![
                    SExpr::Atom(Atom::Symbol(String::from("pkg"))),
                    SExpr::Atom(Atom::Symbol(String::from("dst"))),
                ],
                template: SExpr::List(vec![
                    SExpr::Atom(Atom::Symbol(String::from("ship-effect"))),
                    SExpr::Atom(Atom::Keyword(String::from("package"))),
                    SExpr::Atom(Atom::Symbol(String::from("pkg"))),
                    SExpr::Atom(Atom::Keyword(String::from("dest"))),
                    SExpr::Atom(Atom::Symbol(String::from("dst"))),
                ]),
            }],
            resources: ResourceBounds {
                max_depth: 8,
                max_expansion_size: 512,
                verification_time_ms: 10,
            },
            examples: Vec::new(),
            signature: None,
            hash: None,
            protocol: None,
            shapes: vec![ShapeConstraint {
                performative: String::from("ship"),
                rules: vec![
                    ShapeRule::Require {
                        keyword: String::from("package"),
                        type_constraint: Some(TypeConstraint::String),
                        children: vec![],
                    },
                    ShapeRule::Require {
                        keyword: String::from("dest"),
                        type_constraint: Some(TypeConstraint::String),
                        children: vec![],
                    },
                ],
            }],
        })
        .unwrap();
        reg
    }

    #[test]
    fn shape_check_passes_when_satisfied() {
        let reg = make_registry_with_shape();
        let msg = Message::Simple {
            performative: Performative::Custom(String::from("ship")),
            recipient: None,
            content: SExpr::Atom(Atom::Str(String::from("PKG-1"))),
            params: vec![SExpr::Atom(Atom::Str(String::from("warehouse-A")))],
            thread: None,
            sender: None,
        };
        let result = evaluate(&msg, &reg);
        assert!(result.is_ok());
    }

    #[test]
    fn shape_check_fails_when_type_mismatch() {
        let reg = make_registry_with_shape();
        // Pass a number where string is expected for :package
        let msg = Message::Simple {
            performative: Performative::Custom(String::from("ship")),
            recipient: None,
            content: SExpr::Atom(Atom::Num(42)),
            params: vec![SExpr::Atom(Atom::Str(String::from("warehouse-A")))],
            thread: None,
            sender: None,
        };
        let result = evaluate(&msg, &reg);
        match result {
            Err(EvalError::ShapeViolation(v)) => {
                assert!(v.detail.contains(":package"));
            }
            other => panic!("expected ShapeViolation, got {:?}", other),
        }
    }

    #[test]
    fn shape_check_no_shapes_passes() {
        // Base dialect has no shapes — core performatives should pass
        let reg = make_registry();
        let msg = Message::Simple {
            performative: Performative::Core(CorePerformative::Tell),
            recipient: Some(String::from("@bob")),
            content: SExpr::Atom(Atom::Str(String::from("hello"))),
            params: Vec::new(),
            thread: None,
            sender: None,
        };
        assert!(evaluate(&msg, &reg).is_ok());
    }

    #[test]
    fn shape_conjunction_both_must_pass() {
        // Two shape constraints on same performative compose via conjunction (REQ-224)
        let mut reg = DialectRegistry::new();
        reg.install(Dialect {
            name: String::from("logistics"),
            extends: vec![String::from("cbcl")],
            author: None,
            performatives: vec![PerformativeDef {
                name: String::from("ship"),
                params: vec![
                    SExpr::Atom(Atom::Symbol(String::from("pkg"))),
                    SExpr::Atom(Atom::Symbol(String::from("dst"))),
                ],
                template: SExpr::List(vec![
                    SExpr::Atom(Atom::Symbol(String::from("ship-effect"))),
                    SExpr::Atom(Atom::Keyword(String::from("package"))),
                    SExpr::Atom(Atom::Symbol(String::from("pkg"))),
                    SExpr::Atom(Atom::Keyword(String::from("dest"))),
                    SExpr::Atom(Atom::Symbol(String::from("dst"))),
                ]),
            }],
            resources: ResourceBounds {
                max_depth: 8,
                max_expansion_size: 512,
                verification_time_ms: 10,
            },
            examples: Vec::new(),
            signature: None,
            hash: None,
            protocol: None,
            shapes: vec![
                // First shape: require :package string
                ShapeConstraint {
                    performative: String::from("ship"),
                    rules: vec![ShapeRule::Require {
                        keyword: String::from("package"),
                        type_constraint: Some(TypeConstraint::String),
                        children: vec![],
                    }],
                },
                // Second shape: require :dest string
                ShapeConstraint {
                    performative: String::from("ship"),
                    rules: vec![ShapeRule::Require {
                        keyword: String::from("dest"),
                        type_constraint: Some(TypeConstraint::String),
                        children: vec![],
                    }],
                },
            ],
        })
        .unwrap();

        // Message that satisfies both shapes
        let msg = Message::Simple {
            performative: Performative::Custom(String::from("ship")),
            recipient: None,
            content: SExpr::Atom(Atom::Str(String::from("PKG-1"))),
            params: vec![SExpr::Atom(Atom::Str(String::from("warehouse-A")))],
            thread: None,
            sender: None,
        };
        assert!(evaluate(&msg, &reg).is_ok());
    }

    #[test]
    fn shape_check_max_depth() {
        let mut reg = DialectRegistry::new();
        reg.install(Dialect {
            name: String::from("shallow"),
            extends: vec![String::from("cbcl")],
            author: None,
            performatives: vec![PerformativeDef {
                name: String::from("nest"),
                params: vec![],
                // Template that expands to deeply nested structure
                template: SExpr::List(vec![
                    SExpr::Atom(Atom::Symbol(String::from("nested"))),
                    SExpr::List(vec![
                        SExpr::Atom(Atom::Symbol(String::from("deep"))),
                        SExpr::List(vec![SExpr::Atom(Atom::Symbol(String::from("deeper")))]),
                    ]),
                ]),
            }],
            resources: ResourceBounds {
                max_depth: 8,
                max_expansion_size: 512,
                verification_time_ms: 10,
            },
            examples: Vec::new(),
            signature: None,
            hash: None,
            protocol: None,
            shapes: vec![ShapeConstraint {
                performative: String::from("nest"),
                rules: vec![ShapeRule::MaxDepth(1)],
            }],
        })
        .unwrap();

        let msg = Message::Simple {
            performative: Performative::Custom(String::from("nest")),
            recipient: None,
            content: SExpr::List(Vec::new()),
            params: vec![],
            thread: None,
            sender: None,
        };
        let result = evaluate(&msg, &reg);
        match result {
            Err(EvalError::ShapeViolation(v)) => {
                assert!(v.detail.contains("exceeds"));
            }
            other => panic!("expected ShapeViolation for max-depth, got {:?}", other),
        }
    }

    #[test]
    fn shape_violation_display() {
        let v = ShapeViolation {
            rule: String::from("require :x"),
            field: Some(String::from(":x")),
            expected: Some(String::from("present")),
            found: Some(String::from("missing")),
            detail: String::from("required parameter :x is missing"),
        };
        let err = EvalError::ShapeViolation(v);
        let msg = alloc::format!("{err}");
        assert!(msg.contains("shape violation"));
        assert!(msg.contains(":x"));
    }
}
