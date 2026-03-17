//! Message types and core performatives.
//!
//! Mirrors `Message.lean` from the Lean 4 proof library.

#![forbid(unsafe_code)]

use crate::sexpr::{Atom, SExpr};
use alloc::boxed::Box;
use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

/// The 8 core performatives (REQ-010).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum CorePerformative {
    Tell,
    Ask,
    Reply,
    Error,
    Ok,
    Cancel,
    Hello,
    Bye,
}

impl CorePerformative {
    /// Returns the string name of this core performative.
    pub fn as_str(&self) -> &'static str {
        match self {
            CorePerformative::Tell => "tell",
            CorePerformative::Ask => "ask",
            CorePerformative::Reply => "reply",
            CorePerformative::Error => "error",
            CorePerformative::Ok => "ok",
            CorePerformative::Cancel => "cancel",
            CorePerformative::Hello => "hello",
            CorePerformative::Bye => "bye",
        }
    }

    /// Parse a string into a core performative, if valid.
    pub fn parse(s: &str) -> Option<Self> {
        match s {
            "tell" => Some(CorePerformative::Tell),
            "ask" => Some(CorePerformative::Ask),
            "reply" => Some(CorePerformative::Reply),
            "error" => Some(CorePerformative::Error),
            "ok" => Some(CorePerformative::Ok),
            "cancel" => Some(CorePerformative::Cancel),
            "hello" => Some(CorePerformative::Hello),
            "bye" => Some(CorePerformative::Bye),
            _ => None,
        }
    }
}

/// Core performative names (REQ-014).
pub const CORE_PERFORMATIVE_NAMES: &[&str] = &[
    "tell", "ask", "reply", "error", "ok", "cancel", "hello", "bye",
];

/// Check if a string is a core performative name (REQ-014).
pub fn is_core_performative_name(s: &str) -> bool {
    CORE_PERFORMATIVE_NAMES.contains(&s)
}

/// Either a core or custom performative (REQ-011).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Performative {
    Core(CorePerformative),
    Custom(String),
}

impl Performative {
    /// Returns the string name of this performative.
    pub fn name(&self) -> &str {
        match self {
            Performative::Core(c) => c.as_str(),
            Performative::Custom(s) => s.as_str(),
        }
    }

    /// Returns true if this is a core performative.
    pub fn is_core(&self) -> bool {
        matches!(self, Performative::Core(_))
    }
}

/// Message type classification (REQ-012).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum MessageType {
    Simple,
    Meta,
    Dialect,
    Wrapped,
}

/// Wrapper type for wrapped messages (REQ-012).
///
/// Three wrapper forms: `envelope`, `signed`, `with-limits`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum WrapperType {
    Envelope,
    Signed,
    WithLimits,
}

impl WrapperType {
    /// Returns the canonical string name of this wrapper type.
    pub fn as_str(&self) -> &'static str {
        match self {
            WrapperType::Envelope => "envelope",
            WrapperType::Signed => "signed",
            WrapperType::WithLimits => "with-limits",
        }
    }

    /// Parse a string into a wrapper type, if valid.
    pub fn parse(s: &str) -> Option<Self> {
        match s {
            "envelope" => Some(WrapperType::Envelope),
            "signed" => Some(WrapperType::Signed),
            "with-limits" => Some(WrapperType::WithLimits),
            _ => None,
        }
    }
}

/// A CBCL message (REQ-013).
///
/// Four variants matching the CBCL grammar:
/// - `Simple`: `(performative [recipient] content [:key val ...])`
/// - `Meta`: `(meta <operation>)`
/// - `Dialect`: `(lang <dialect-name> <inner-message>)`
/// - `Wrapped`: `(envelope|signed|with-limits <params...> <inner-message>)`
///
/// Mirrors `CBCL.Message` in `Message.lean:41–47` and
/// `CBCL.MessageType` in `Message.lean:33–37`.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Message {
    /// Simple message: `(performative [recipient] content [:key val ...])`
    Simple {
        performative: Performative,
        recipient: Option<String>,
        content: SExpr,
        params: Vec<SExpr>,
        thread: Option<String>,
        sender: Option<String>,
    },
    /// Meta message: `(meta <dialect_def>)`
    Meta { dialect_def: SExpr },
    /// Dialect-scoped message: `(lang <dialect_name> <inner>)`
    Dialect {
        dialect_name: String,
        inner: Box<Message>,
    },
    /// Wrapped message: `(envelope|signed|with-limits <params...> <content>)`
    Wrapped {
        wrapper: WrapperType,
        params: Vec<SExpr>,
        content: Box<Message>,
    },
}

// ---------------------------------------------------------------------------
// Typed extraction methods
// ---------------------------------------------------------------------------

impl Message {
    /// Returns the message type classification.
    pub fn message_type(&self) -> MessageType {
        match self {
            Message::Simple { .. } => MessageType::Simple,
            Message::Meta { .. } => MessageType::Meta,
            Message::Dialect { .. } => MessageType::Dialect,
            Message::Wrapped { .. } => MessageType::Wrapped,
        }
    }

    /// Returns the performative if this is a Simple message.
    pub fn performative(&self) -> Option<&Performative> {
        match self {
            Message::Simple { performative, .. } => Some(performative),
            _ => None,
        }
    }

    /// Returns the recipient if this is a Simple message with one.
    pub fn recipient(&self) -> Option<&str> {
        match self {
            Message::Simple {
                recipient: Some(r), ..
            } => Some(r.as_str()),
            _ => None,
        }
    }

    /// Returns the content if this is a Simple message.
    pub fn content(&self) -> Option<&SExpr> {
        match self {
            Message::Simple { content, .. } => Some(content),
            _ => None,
        }
    }

    /// Returns the thread if this is a Simple message with one.
    pub fn thread(&self) -> Option<&str> {
        match self {
            Message::Simple {
                thread: Some(t), ..
            } => Some(t.as_str()),
            _ => None,
        }
    }

    /// Returns the sender if this is a Simple message with one.
    pub fn sender(&self) -> Option<&str> {
        match self {
            Message::Simple {
                sender: Some(s), ..
            } => Some(s.as_str()),
            _ => None,
        }
    }

    /// Returns the dialect definition if this is a Meta message.
    pub fn dialect_def(&self) -> Option<&SExpr> {
        match self {
            Message::Meta { dialect_def } => Some(dialect_def),
            _ => None,
        }
    }

    /// Returns the dialect name if this is a Dialect message.
    pub fn dialect_name(&self) -> Option<&str> {
        match self {
            Message::Dialect { dialect_name, .. } => Some(dialect_name.as_str()),
            _ => None,
        }
    }

    /// Returns the inner message for Dialect or Wrapped messages.
    pub fn inner_message(&self) -> Option<&Message> {
        match self {
            Message::Dialect { inner, .. } => Some(inner),
            Message::Wrapped { content, .. } => Some(content),
            _ => None,
        }
    }

    /// Returns the wrapper type if this is a Wrapped message.
    pub fn wrapper_type(&self) -> Option<WrapperType> {
        match self {
            Message::Wrapped { wrapper, .. } => Some(*wrapper),
            _ => None,
        }
    }
}

// ---------------------------------------------------------------------------
// From<Message> for SExpr
// ---------------------------------------------------------------------------

impl From<Message> for SExpr {
    fn from(msg: Message) -> SExpr {
        match msg {
            Message::Simple {
                performative,
                recipient,
                content,
                params,
                thread,
                sender,
            } => {
                let mut items = vec![SExpr::Atom(Atom::Symbol(String::from(performative.name())))];
                if let Some(r) = recipient {
                    items.push(SExpr::Atom(Atom::Symbol(r)));
                }
                items.push(content);
                items.extend(params);
                if let Some(t) = thread {
                    items.push(SExpr::Atom(Atom::Keyword(String::from("thread"))));
                    items.push(SExpr::Atom(Atom::Str(t)));
                }
                if let Some(s) = sender {
                    items.push(SExpr::Atom(Atom::Keyword(String::from("sender"))));
                    items.push(SExpr::Atom(Atom::Str(s)));
                }
                SExpr::List(items)
            }
            Message::Meta { dialect_def } => SExpr::List(vec![
                SExpr::Atom(Atom::Symbol(String::from("meta"))),
                dialect_def,
            ]),
            Message::Dialect {
                dialect_name,
                inner,
            } => SExpr::List(vec![
                SExpr::Atom(Atom::Symbol(String::from("lang"))),
                SExpr::Atom(Atom::Symbol(dialect_name)),
                SExpr::from(*inner),
            ]),
            Message::Wrapped {
                wrapper,
                params,
                content,
            } => {
                let mut items = vec![SExpr::Atom(Atom::Symbol(String::from(wrapper.as_str())))];
                items.extend(params);
                items.push(SExpr::from(*content));
                SExpr::List(items)
            }
        }
    }
}

impl From<&Message> for SExpr {
    fn from(msg: &Message) -> SExpr {
        SExpr::from(msg.clone())
    }
}

// ---------------------------------------------------------------------------
// TryFrom<&SExpr> for Message
// ---------------------------------------------------------------------------

/// Error returned when converting an SExpr to a Message fails.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MessageParseError(pub String);

impl fmt::Display for MessageParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

impl TryFrom<&SExpr> for Message {
    type Error = MessageParseError;

    fn try_from(sexpr: &SExpr) -> Result<Self, Self::Error> {
        let items = match sexpr {
            SExpr::List(items) if !items.is_empty() => items,
            SExpr::List(_) => return Err(MessageParseError(String::from("empty message"))),
            _ => return Err(MessageParseError(String::from("message must be a list"))),
        };

        let head = match &items[0] {
            SExpr::Atom(Atom::Symbol(s)) => s.as_str(),
            _ => {
                return Err(MessageParseError(String::from(
                    "message head must be a symbol",
                )))
            }
        };

        match head {
            "meta" => parse_meta(&items[1..]),
            "lang" => parse_dialect_msg(&items[1..]),
            w if WrapperType::parse(w).is_some() => {
                parse_wrapped(WrapperType::parse(w).unwrap(), &items[1..])
            }
            _ => parse_simple(head, &items[1..]),
        }
    }
}

fn parse_meta(tail: &[SExpr]) -> Result<Message, MessageParseError> {
    if tail.is_empty() {
        return Err(MessageParseError(String::from(
            "meta message requires an operation",
        )));
    }
    Ok(Message::Meta {
        dialect_def: tail[0].clone(),
    })
}

fn parse_dialect_msg(tail: &[SExpr]) -> Result<Message, MessageParseError> {
    if tail.len() < 2 {
        return Err(MessageParseError(String::from(
            "dialect message requires dialect name and inner message",
        )));
    }
    let dialect_name = match &tail[0] {
        SExpr::Atom(Atom::Symbol(s)) => s.clone(),
        _ => {
            return Err(MessageParseError(String::from(
                "dialect name must be a symbol",
            )))
        }
    };
    let inner = Message::try_from(&tail[1])?;
    Ok(Message::Dialect {
        dialect_name,
        inner: Box::new(inner),
    })
}

fn parse_wrapped(wrapper: WrapperType, tail: &[SExpr]) -> Result<Message, MessageParseError> {
    // The last list element is the inner message; everything before it is params.
    let inner_idx = tail.iter().rposition(|item| matches!(item, SExpr::List(_)));
    match inner_idx {
        Some(idx) => {
            let inner = Message::try_from(&tail[idx])?;
            let params = tail[..idx].to_vec();
            Ok(Message::Wrapped {
                wrapper,
                params,
                content: Box::new(inner),
            })
        }
        None => Err(MessageParseError(String::from(
            "wrapped message requires an inner message",
        ))),
    }
}

fn parse_simple(head: &str, tail: &[SExpr]) -> Result<Message, MessageParseError> {
    let performative = match CorePerformative::parse(head) {
        Some(cp) => Performative::Core(cp),
        None => Performative::Custom(String::from(head)),
    };

    let mut recipient = None;
    let mut content = None;
    let mut thread = None;
    let mut sender_val = None;
    let mut params = Vec::new();
    let mut i = 0;

    // Check for @-prefixed recipient as the first arg.
    if i < tail.len() {
        if let SExpr::Atom(Atom::Symbol(s)) = &tail[i] {
            if s.starts_with('@') {
                recipient = Some(s.clone());
                i += 1;
            }
        }
    }

    // Parse remaining args: first non-keyword is content, rest are params.
    while i < tail.len() {
        match &tail[i] {
            SExpr::Atom(Atom::Keyword(k)) => {
                if i + 1 >= tail.len() {
                    return Err(MessageParseError(alloc::format!(
                        "keyword :{k} missing value"
                    )));
                }
                let val = &tail[i + 1];
                if k == "thread" {
                    thread = Some(extract_string_or_symbol(val));
                } else if k == "sender" {
                    sender_val = Some(extract_string_or_symbol(val));
                } else {
                    params.push(tail[i].clone());
                    params.push(val.clone());
                }
                i += 2;
            }
            _ => {
                if content.is_none() {
                    content = Some(tail[i].clone());
                } else {
                    params.push(tail[i].clone());
                }
                i += 1;
            }
        }
    }

    Ok(Message::Simple {
        performative,
        recipient,
        content: content.unwrap_or(SExpr::List(Vec::new())),
        params,
        thread,
        sender: sender_val,
    })
}

fn extract_string_or_symbol(sexpr: &SExpr) -> String {
    match sexpr {
        SExpr::Atom(Atom::Str(s)) | SExpr::Atom(Atom::Symbol(s)) => s.clone(),
        other => alloc::format!("{other}"),
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::string::ToString;

    #[test]
    fn core_performative_names_count() {
        assert_eq!(CORE_PERFORMATIVE_NAMES.len(), 8);
    }

    #[test]
    fn is_core_performative() {
        assert!(is_core_performative_name("tell"));
        assert!(is_core_performative_name("bye"));
        assert!(!is_core_performative_name("custom-perf"));
    }

    #[test]
    fn core_performative_roundtrip() {
        for name in CORE_PERFORMATIVE_NAMES {
            let cp = CorePerformative::parse(name).unwrap();
            assert_eq!(cp.as_str(), *name);
        }
    }

    #[test]
    fn performative_name() {
        assert_eq!(Performative::Core(CorePerformative::Tell).name(), "tell");
        assert_eq!(
            Performative::Custom(String::from("propose-step")).name(),
            "propose-step"
        );
    }

    #[test]
    fn wrapper_type_roundtrip() {
        for (s, w) in [
            ("envelope", WrapperType::Envelope),
            ("signed", WrapperType::Signed),
            ("with-limits", WrapperType::WithLimits),
        ] {
            assert_eq!(WrapperType::parse(s), Some(w));
            assert_eq!(w.as_str(), s);
        }
        assert_eq!(WrapperType::parse("unknown"), None);
    }

    #[test]
    fn message_type_classification() {
        let simple = Message::Simple {
            performative: Performative::Core(CorePerformative::Tell),
            recipient: None,
            content: SExpr::Atom(Atom::Str("hi".into())),
            params: vec![],
            thread: None,
            sender: None,
        };
        assert_eq!(simple.message_type(), MessageType::Simple);

        let meta = Message::Meta {
            dialect_def: SExpr::List(vec![]),
        };
        assert_eq!(meta.message_type(), MessageType::Meta);

        let dialect = Message::Dialect {
            dialect_name: "test".into(),
            inner: Box::new(simple.clone()),
        };
        assert_eq!(dialect.message_type(), MessageType::Dialect);

        let wrapped = Message::Wrapped {
            wrapper: WrapperType::Envelope,
            params: vec![],
            content: Box::new(simple),
        };
        assert_eq!(wrapped.message_type(), MessageType::Wrapped);
    }

    // -- Typed extraction --

    #[test]
    fn simple_extraction_methods() {
        let msg = Message::Simple {
            performative: Performative::Core(CorePerformative::Tell),
            recipient: Some("@bob".into()),
            content: SExpr::Atom(Atom::Str("hello".into())),
            params: vec![],
            thread: Some("conv-1".into()),
            sender: Some("@alice".into()),
        };
        assert_eq!(msg.performative().unwrap().name(), "tell");
        assert_eq!(msg.recipient(), Some("@bob"));
        assert_eq!(msg.content(), Some(&SExpr::Atom(Atom::Str("hello".into()))));
        assert_eq!(msg.thread(), Some("conv-1"));
        assert_eq!(msg.sender(), Some("@alice"));
        assert!(msg.dialect_def().is_none());
        assert!(msg.inner_message().is_none());
        assert!(msg.wrapper_type().is_none());
    }

    #[test]
    fn meta_extraction_methods() {
        let def = SExpr::List(vec![
            SExpr::Atom(Atom::Symbol("define".into())),
            SExpr::Atom(Atom::Symbol("test-dialect".into())),
        ]);
        let msg = Message::Meta {
            dialect_def: def.clone(),
        };
        assert_eq!(msg.dialect_def(), Some(&def));
        assert!(msg.performative().is_none());
    }

    #[test]
    fn dialect_extraction_methods() {
        let inner = Message::Simple {
            performative: Performative::Core(CorePerformative::Tell),
            recipient: None,
            content: SExpr::Atom(Atom::Str("hi".into())),
            params: vec![],
            thread: None,
            sender: None,
        };
        let msg = Message::Dialect {
            dialect_name: "logistics".into(),
            inner: Box::new(inner.clone()),
        };
        assert_eq!(msg.dialect_name(), Some("logistics"));
        assert_eq!(msg.inner_message(), Some(&inner));
    }

    #[test]
    fn wrapped_extraction_methods() {
        let inner = Message::Simple {
            performative: Performative::Core(CorePerformative::Tell),
            recipient: None,
            content: SExpr::Atom(Atom::Str("hi".into())),
            params: vec![],
            thread: None,
            sender: None,
        };
        let msg = Message::Wrapped {
            wrapper: WrapperType::Signed,
            params: vec![SExpr::Atom(Atom::Str("sig".into()))],
            content: Box::new(inner.clone()),
        };
        assert_eq!(msg.wrapper_type(), Some(WrapperType::Signed));
        assert_eq!(msg.inner_message(), Some(&inner));
    }

    // -- TryFrom<&SExpr> for Message --

    fn sym(s: &str) -> SExpr {
        SExpr::Atom(Atom::Symbol(String::from(s)))
    }

    fn str_expr(s: &str) -> SExpr {
        SExpr::Atom(Atom::Str(String::from(s)))
    }

    fn kw(s: &str) -> SExpr {
        SExpr::Atom(Atom::Keyword(String::from(s)))
    }

    fn list(items: Vec<SExpr>) -> SExpr {
        SExpr::List(items)
    }

    #[test]
    fn try_from_simple_tell() {
        let sexpr = list(vec![sym("tell"), sym("@bob"), str_expr("hello")]);
        let msg = Message::try_from(&sexpr).unwrap();
        assert_eq!(msg.message_type(), MessageType::Simple);
        assert_eq!(msg.performative().unwrap().name(), "tell");
        assert_eq!(msg.recipient(), Some("@bob"));
        assert_eq!(msg.content(), Some(&str_expr("hello")));
    }

    #[test]
    fn try_from_simple_no_recipient() {
        let sexpr = list(vec![sym("reply"), str_expr("done")]);
        let msg = Message::try_from(&sexpr).unwrap();
        assert!(msg.recipient().is_none());
        assert_eq!(msg.content(), Some(&str_expr("done")));
    }

    #[test]
    fn try_from_simple_with_thread() {
        let sexpr = list(vec![
            sym("tell"),
            str_expr("hello"),
            kw("thread"),
            sym("conv-17"),
        ]);
        let msg = Message::try_from(&sexpr).unwrap();
        assert_eq!(msg.thread(), Some("conv-17"));
    }

    #[test]
    fn try_from_simple_with_keyword_params() {
        let sexpr = list(vec![
            sym("ask"),
            sym("@alice"),
            str_expr("What?"),
            kw("timeout"),
            SExpr::Atom(Atom::Num(30)),
        ]);
        let msg = Message::try_from(&sexpr).unwrap();
        if let Message::Simple { params, .. } = &msg {
            assert_eq!(params.len(), 2); // :timeout and 30
        } else {
            panic!("expected Simple");
        }
    }

    #[test]
    fn try_from_meta() {
        let op = list(vec![sym("define"), sym("test-dialect")]);
        let sexpr = list(vec![sym("meta"), op.clone()]);
        let msg = Message::try_from(&sexpr).unwrap();
        assert_eq!(msg.message_type(), MessageType::Meta);
        assert_eq!(msg.dialect_def(), Some(&op));
    }

    #[test]
    fn try_from_dialect() {
        let inner = list(vec![sym("tell"), sym("@system"), str_expr("PKG-123")]);
        let sexpr = list(vec![sym("lang"), sym("logistics"), inner]);
        let msg = Message::try_from(&sexpr).unwrap();
        assert_eq!(msg.message_type(), MessageType::Dialect);
        assert_eq!(msg.dialect_name(), Some("logistics"));
        let inner_msg = msg.inner_message().unwrap();
        assert_eq!(inner_msg.message_type(), MessageType::Simple);
        assert_eq!(inner_msg.performative().unwrap().name(), "tell");
    }

    #[test]
    fn try_from_wrapped_envelope() {
        let inner = list(vec![sym("tell"), sym("@bob"), str_expr("Hello")]);
        let sexpr = list(vec![
            sym("envelope"),
            kw("from"),
            sym("@alice"),
            kw("to"),
            sym("@bob"),
            inner,
        ]);
        let msg = Message::try_from(&sexpr).unwrap();
        assert_eq!(msg.message_type(), MessageType::Wrapped);
        assert_eq!(msg.wrapper_type(), Some(WrapperType::Envelope));
        if let Message::Wrapped { params, .. } = &msg {
            assert_eq!(params.len(), 4); // :from @alice :to @bob
        }
    }

    #[test]
    fn try_from_wrapped_signed() {
        let inner = list(vec![sym("tell"), sym("@bob"), str_expr("Verified")]);
        let sexpr = list(vec![sym("signed"), str_expr("base64sig"), inner]);
        let msg = Message::try_from(&sexpr).unwrap();
        assert_eq!(msg.wrapper_type(), Some(WrapperType::Signed));
        if let Message::Wrapped { params, .. } = &msg {
            assert_eq!(params, &[str_expr("base64sig")]);
        }
    }

    #[test]
    fn try_from_wrapped_with_limits() {
        let inner = list(vec![sym("tell"), sym("@bob"), str_expr("Constrained")]);
        let sexpr = list(vec![
            sym("with-limits"),
            kw("depth"),
            SExpr::Atom(Atom::Num(10)),
            kw("cpu"),
            SExpr::Atom(Atom::Num(100)),
            inner,
        ]);
        let msg = Message::try_from(&sexpr).unwrap();
        assert_eq!(msg.wrapper_type(), Some(WrapperType::WithLimits));
    }

    #[test]
    fn try_from_errors() {
        // Empty list
        assert!(Message::try_from(&list(vec![])).is_err());
        // Non-list
        assert!(Message::try_from(&sym("hello")).is_err());
        // Non-symbol head
        assert!(Message::try_from(&list(vec![str_expr("tell")])).is_err());
        // Meta without operation
        assert!(Message::try_from(&list(vec![sym("meta")])).is_err());
        // Dialect without inner
        assert!(Message::try_from(&list(vec![sym("lang"), sym("d")])).is_err());
    }

    #[test]
    fn message_parse_error_display() {
        let err = MessageParseError(String::from("test error"));
        assert_eq!(err.to_string(), "test error");
    }

    // -- From<Message> for SExpr --

    #[test]
    fn simple_to_sexpr() {
        let msg = Message::Simple {
            performative: Performative::Core(CorePerformative::Tell),
            recipient: Some("@bob".into()),
            content: str_expr("hello"),
            params: vec![],
            thread: None,
            sender: None,
        };
        let sexpr = SExpr::from(msg);
        assert_eq!(sexpr.to_string(), "(tell @bob \"hello\")");
    }

    #[test]
    fn simple_with_thread_to_sexpr() {
        let msg = Message::Simple {
            performative: Performative::Core(CorePerformative::Reply),
            recipient: None,
            content: str_expr("done"),
            params: vec![],
            thread: Some("conv-17".into()),
            sender: None,
        };
        let sexpr = SExpr::from(msg);
        assert_eq!(sexpr.to_string(), "(reply \"done\" :thread \"conv-17\")");
    }

    #[test]
    fn meta_to_sexpr() {
        let msg = Message::Meta {
            dialect_def: list(vec![sym("define"), sym("test-dialect")]),
        };
        let sexpr = SExpr::from(msg);
        assert_eq!(sexpr.to_string(), "(meta (define test-dialect))");
    }

    #[test]
    fn dialect_to_sexpr() {
        let msg = Message::Dialect {
            dialect_name: "logistics".into(),
            inner: Box::new(Message::Simple {
                performative: Performative::Core(CorePerformative::Tell),
                recipient: Some("@system".into()),
                content: str_expr("PKG-123"),
                params: vec![],
                thread: None,
                sender: None,
            }),
        };
        let sexpr = SExpr::from(msg);
        assert_eq!(
            sexpr.to_string(),
            "(lang logistics (tell @system \"PKG-123\"))"
        );
    }

    #[test]
    fn wrapped_to_sexpr() {
        let msg = Message::Wrapped {
            wrapper: WrapperType::Signed,
            params: vec![str_expr("base64sig")],
            content: Box::new(Message::Simple {
                performative: Performative::Core(CorePerformative::Tell),
                recipient: Some("@bob".into()),
                content: str_expr("Verified"),
                params: vec![],
                thread: None,
                sender: None,
            }),
        };
        let sexpr = SExpr::from(msg);
        assert_eq!(
            sexpr.to_string(),
            "(signed \"base64sig\" (tell @bob \"Verified\"))"
        );
    }

    // -- Round-trip tests --

    #[test]
    fn roundtrip_simple() {
        let original = list(vec![sym("tell"), sym("@bob"), str_expr("hello")]);
        let msg = Message::try_from(&original).unwrap();
        let back = SExpr::from(msg);
        assert_eq!(back, original);
    }

    #[test]
    fn roundtrip_meta() {
        let original = list(vec![
            sym("meta"),
            list(vec![sym("query"), list(vec![sym("speak?"), sym("cbcl")])]),
        ]);
        let msg = Message::try_from(&original).unwrap();
        let back = SExpr::from(msg);
        assert_eq!(back, original);
    }

    #[test]
    fn roundtrip_dialect() {
        let original = list(vec![
            sym("lang"),
            sym("logistics"),
            list(vec![sym("tell"), sym("@system"), str_expr("PKG-123")]),
        ]);
        let msg = Message::try_from(&original).unwrap();
        let back = SExpr::from(msg);
        assert_eq!(back, original);
    }

    #[test]
    fn roundtrip_wrapped() {
        let original = list(vec![
            sym("signed"),
            str_expr("base64sig"),
            list(vec![sym("tell"), sym("@bob"), str_expr("Verified")]),
        ]);
        let msg = Message::try_from(&original).unwrap();
        let back = SExpr::from(msg);
        assert_eq!(back, original);
    }

    #[test]
    fn custom_performative() {
        let sexpr = list(vec![sym("propose-step"), sym("s1"), sym("pickup")]);
        let msg = Message::try_from(&sexpr).unwrap();
        assert_eq!(
            msg.performative(),
            Some(&Performative::Custom(String::from("propose-step")))
        );
    }
}
