//! Message types and core performatives.
//!
//! Mirrors `Message.lean` from the Lean 4 proof library.

#![forbid(unsafe_code)]

use crate::protocol::BEGIN_KEYWORD;
use crate::sexpr::{Atom, SExpr};
use alloc::boxed::Box;
use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

/// Causal predecessor reference for a message (REQ-202).
///
/// Encodes the `:caused-by` keyword parameter:
/// - `Begin` — this message starts a new causal chain (`:caused-by "begin"`)
/// - `Single(hash)` — single predecessor (`:caused-by <hash>`)
/// - `Multiple(hashes)` — multiple predecessors (`:caused-by (<h1> <h2> ...)`)
///
/// For the `Multiple` variant, hashes are stored in canonical (sorted) order
/// to ensure deterministic hashing.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum CausedBy {
    /// This message begins a new causal chain.
    Begin,
    /// Single causal predecessor, identified by content hash.
    Single(String),
    /// Multiple causal predecessors, sorted lexicographically for canonical ordering.
    Multiple(Vec<String>),
}

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

/// Recipient position of a Simple message (SPEC-014 REQ-622).
///
/// A bare `@key` symbol is a single recipient (the pre-SPEC-014 form,
/// byte-identical on re-serialisation); a non-empty list of `@key` symbols
/// is a multicast, serialised in canonical (sorted) order. A performative
/// whose `:to` annotation is the empty set simply carries no recipient
/// position.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Recipients {
    /// Single recipient: `(perf @r …)`.
    One(String),
    /// Multicast: `(perf (@r1 @r2) …)`; canonical order via `BTreeSet`.
    Set(alloc::collections::BTreeSet<String>),
}

impl Recipients {
    /// The single recipient, if this is the `One` form.
    pub fn as_single(&self) -> Option<&str> {
        match self {
            Recipients::One(r) => Some(r.as_str()),
            Recipients::Set(_) => None,
        }
    }

    /// All recipients as a normalized sorted set.
    pub fn as_set(&self) -> alloc::collections::BTreeSet<&str> {
        match self {
            Recipients::One(r) => {
                let mut s = alloc::collections::BTreeSet::new();
                s.insert(r.as_str());
                s
            }
            Recipients::Set(rs) => rs.iter().map(|r| r.as_str()).collect(),
        }
    }
}

impl From<String> for Recipients {
    fn from(r: String) -> Self {
        Recipients::One(r)
    }
}

impl From<&str> for Recipients {
    fn from(r: &str) -> Self {
        Recipients::One(String::from(r))
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
/// Four wrapper forms: `envelope`, `signed`, `with-limits`, and the
/// cast-bearing `with-roles` thread root (SPEC-014 REQ-625).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum WrapperType {
    Envelope,
    Signed,
    WithLimits,
    /// `(with-roles (<bindings>) <signed-message>)` — the cast nomination
    /// wrapper at a thread's causal root (SPEC-014 REQ-611/625, CON-601).
    /// The bindings list travels in `params`; the inner signed message is
    /// carried unchanged.
    WithRoles,
}

impl WrapperType {
    /// Returns the canonical string name of this wrapper type.
    pub fn as_str(&self) -> &'static str {
        match self {
            WrapperType::Envelope => "envelope",
            WrapperType::Signed => "signed",
            WrapperType::WithLimits => "with-limits",
            WrapperType::WithRoles => "with-roles",
        }
    }

    /// Parse a string into a wrapper type, if valid.
    pub fn parse(s: &str) -> Option<Self> {
        match s {
            "envelope" => Some(WrapperType::Envelope),
            "signed" => Some(WrapperType::Signed),
            "with-limits" => Some(WrapperType::WithLimits),
            "with-roles" => Some(WrapperType::WithRoles),
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
        recipient: Option<Recipients>,
        content: SExpr,
        params: Vec<SExpr>,
        thread: Option<String>,
        sender: Option<String>,
        caused_by: Option<CausedBy>,
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

    /// Returns the recipient if this is a Simple message with exactly one.
    pub fn recipient(&self) -> Option<&str> {
        match self {
            Message::Simple {
                recipient: Some(r), ..
            } => r.as_single(),
            _ => None,
        }
    }

    /// Returns all recipients of a Simple message as a normalized set
    /// (empty when the recipient position is absent) — SPEC-014 REQ-622.
    pub fn recipient_set(&self) -> alloc::collections::BTreeSet<&str> {
        match self {
            Message::Simple {
                recipient: Some(r), ..
            } => r.as_set(),
            _ => alloc::collections::BTreeSet::new(),
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

    /// Returns the caused-by reference if this is a Simple message with one.
    pub fn caused_by(&self) -> Option<&CausedBy> {
        match self {
            Message::Simple {
                caused_by: Some(cb),
                ..
            } => Some(cb),
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

    /// Walk through `Wrapped` and `Dialect` envelopes to the innermost
    /// `Message::Simple`. Returns `None` if no Simple is found (e.g. a `Meta`
    /// message). Used by the parser pipeline and the agent to ensure
    /// wrappers cannot be used to bypass causal/shape verification.
    pub fn innermost_simple(&self) -> Option<&Message> {
        let mut cur = self;
        loop {
            match cur {
                Message::Simple { .. } => return Some(cur),
                Message::Wrapped { content, .. } => cur = content,
                Message::Dialect { inner, .. } => cur = inner,
                Message::Meta { .. } => return None,
            }
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
                caused_by,
            } => {
                let mut items = vec![SExpr::Atom(Atom::Symbol(String::from(performative.name())))];
                match recipient {
                    Some(Recipients::One(r)) => {
                        items.push(SExpr::Atom(Atom::Symbol(r)));
                    }
                    Some(Recipients::Set(rs)) => {
                        items.push(SExpr::List(
                            rs.into_iter()
                                .map(|r| SExpr::Atom(Atom::Symbol(r)))
                                .collect(),
                        ));
                    }
                    None => {}
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
                if let Some(cb) = caused_by {
                    items.push(SExpr::Atom(Atom::Keyword(String::from("caused-by"))));
                    match cb {
                        CausedBy::Begin => {
                            items.push(SExpr::Atom(Atom::Symbol(String::from(BEGIN_KEYWORD))));
                        }
                        CausedBy::Single(h) => {
                            items.push(SExpr::Atom(Atom::Symbol(h)));
                        }
                        CausedBy::Multiple(hs) => {
                            let hash_exprs = hs
                                .iter()
                                .map(|h| SExpr::Atom(Atom::Symbol(h.clone())))
                                .collect();
                            items.push(SExpr::List(hash_exprs));
                        }
                    }
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

/// Whether an S-expression is a single address token (`@key`).
fn is_address(s: &SExpr) -> bool {
    matches!(s, SExpr::Atom(Atom::Symbol(sym)) if sym.starts_with('@'))
}

/// Whether an S-expression is an *address group*: a single address `@x` or a
/// non-empty list of addresses `(@a @b)`. These are exactly the forms the
/// recipient position accepts, so they are forbidden as positional content
/// (which is what keeps `@` sigil-disciplined and serialise ∘ parse injective).
/// A mixed list like `(introduce @bob)` is not an address group — it is
/// ordinary content with a nested address.
fn is_address_group(s: &SExpr) -> bool {
    match s {
        SExpr::Atom(Atom::Symbol(sym)) => sym.starts_with('@'),
        SExpr::List(items) => !items.is_empty() && items.iter().all(is_address),
        _ => false,
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
    let mut caused_by = None;
    let mut params = Vec::new();
    let mut i = 0;

    // Check for a recipient as the first arg: an @-prefixed symbol
    // (single) or a non-empty list of @-prefixed symbols (multicast,
    // SPEC-014 REQ-622). An empty list stays content (pre-SPEC-014 form).
    if i < tail.len() {
        match &tail[i] {
            SExpr::Atom(Atom::Symbol(s)) if s.starts_with('@') => {
                recipient = Some(Recipients::One(s.clone()));
                i += 1;
            }
            SExpr::List(items) if !items.is_empty() && items.iter().all(is_address) => {
                let set: alloc::collections::BTreeSet<String> = items
                    .iter()
                    .map(|it| match it {
                        SExpr::Atom(Atom::Symbol(s)) => s.clone(),
                        _ => unreachable!("guarded by the match arm"),
                    })
                    .collect();
                recipient = Some(Recipients::Set(set));
                i += 1;
            }
            _ => {}
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
                } else if k == "caused-by" {
                    caused_by = Some(parse_caused_by(val)?);
                } else {
                    params.push(tail[i].clone());
                    params.push(val.clone());
                }
                i += 2;
            }
            // An address group — a bare `@x` or an all-`@` list `(@a @b)` —
            // is not data. These are exactly the forms the recipient parser
            // accepts above, so admitting them as content would overload the
            // surface syntax and break serialise ∘ parse (a content address
            // group re-parses as the recipient). Reject them in the positional
            // slot; addresses belong in the recipient slot or a keyword value.
            // A *mixed* list (e.g. `(introduce @bob)`) is ordinary content —
            // nested addresses are fine — as are `@`-runs inside a string.
            positional if is_address_group(positional) => {
                return Err(MessageParseError(alloc::format!(
                    "address(es) '{positional}' in content position; addresses \
                     go in the recipient slot or a keyword value"
                )));
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
        caused_by,
    })
}

/// Parse the value of a `:caused-by` keyword parameter.
///
/// Accepts three forms:
/// - `"begin"` or `begin` symbol → `CausedBy::Begin`
/// - Single atom (hash) → `CausedBy::Single(hash)`
/// - List of atoms (hashes) → `CausedBy::Multiple(sorted_hashes)`
fn parse_caused_by(val: &SExpr) -> Result<CausedBy, MessageParseError> {
    match val {
        SExpr::Atom(Atom::Symbol(s)) if s == BEGIN_KEYWORD => Ok(CausedBy::Begin),
        SExpr::Atom(Atom::Str(s)) if s == BEGIN_KEYWORD => Ok(CausedBy::Begin),
        SExpr::Atom(Atom::Symbol(s)) => Ok(CausedBy::Single(s.clone())),
        SExpr::Atom(Atom::Str(s)) => Ok(CausedBy::Single(s.clone())),
        SExpr::List(items) => {
            if items.is_empty() {
                return Err(MessageParseError(String::from(
                    ":caused-by list must not be empty",
                )));
            }
            let mut hashes = Vec::with_capacity(items.len());
            for item in items {
                match item {
                    SExpr::Atom(Atom::Symbol(s)) | SExpr::Atom(Atom::Str(s)) => {
                        hashes.push(s.clone());
                    }
                    _ => {
                        return Err(MessageParseError(String::from(
                            ":caused-by list elements must be symbols or strings",
                        )));
                    }
                }
            }
            // Canonical ordering: sort lexicographically (REQ-202)
            hashes.sort();
            Ok(CausedBy::Multiple(hashes))
        }
        _ => Err(MessageParseError(String::from(
            ":caused-by value must be a symbol, string, or list of hashes",
        ))),
    }
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
            caused_by: None,
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
            caused_by: None,
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
            caused_by: None,
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
            caused_by: None,
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
            caused_by: None,
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
            caused_by: None,
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
                caused_by: None,
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
                caused_by: None,
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

    // -- CausedBy (REQ-202, TEST-202) --

    #[test]
    fn caused_by_begin_symbol() {
        let sexpr = list(vec![
            sym("tell"),
            str_expr("hello"),
            kw("caused-by"),
            sym("begin"),
        ]);
        let msg = Message::try_from(&sexpr).unwrap();
        assert_eq!(msg.caused_by(), Some(&CausedBy::Begin));
    }

    #[test]
    fn caused_by_begin_string() {
        let sexpr = list(vec![
            sym("tell"),
            str_expr("hello"),
            kw("caused-by"),
            str_expr("begin"),
        ]);
        let msg = Message::try_from(&sexpr).unwrap();
        assert_eq!(msg.caused_by(), Some(&CausedBy::Begin));
    }

    #[test]
    fn caused_by_single_hash() {
        let sexpr = list(vec![
            sym("reply"),
            str_expr("done"),
            kw("caused-by"),
            sym("sha256:abc123"),
        ]);
        let msg = Message::try_from(&sexpr).unwrap();
        assert_eq!(
            msg.caused_by(),
            Some(&CausedBy::Single(String::from("sha256:abc123")))
        );
    }

    #[test]
    fn caused_by_single_hash_string() {
        let sexpr = list(vec![
            sym("reply"),
            str_expr("done"),
            kw("caused-by"),
            str_expr("sha256:abc123"),
        ]);
        let msg = Message::try_from(&sexpr).unwrap();
        assert_eq!(
            msg.caused_by(),
            Some(&CausedBy::Single(String::from("sha256:abc123")))
        );
    }

    #[test]
    fn caused_by_multiple_hashes() {
        let sexpr = list(vec![
            sym("ok"),
            str_expr("ack"),
            kw("caused-by"),
            list(vec![sym("sha256:bbb"), sym("sha256:aaa")]),
        ]);
        let msg = Message::try_from(&sexpr).unwrap();
        // Multiple hashes are sorted lexicographically
        assert_eq!(
            msg.caused_by(),
            Some(&CausedBy::Multiple(vec![
                String::from("sha256:aaa"),
                String::from("sha256:bbb"),
            ]))
        );
    }

    #[test]
    fn caused_by_multiple_canonical_sort() {
        // Verify that different input orderings produce the same canonical form
        let sexpr1 = list(vec![
            sym("ok"),
            str_expr("ack"),
            kw("caused-by"),
            list(vec![sym("c"), sym("a"), sym("b")]),
        ]);
        let sexpr2 = list(vec![
            sym("ok"),
            str_expr("ack"),
            kw("caused-by"),
            list(vec![sym("b"), sym("c"), sym("a")]),
        ]);
        let msg1 = Message::try_from(&sexpr1).unwrap();
        let msg2 = Message::try_from(&sexpr2).unwrap();
        assert_eq!(msg1.caused_by(), msg2.caused_by());
        assert_eq!(
            msg1.caused_by(),
            Some(&CausedBy::Multiple(vec![
                String::from("a"),
                String::from("b"),
                String::from("c"),
            ]))
        );
    }

    #[test]
    fn caused_by_none_when_absent() {
        let sexpr = list(vec![sym("tell"), str_expr("hello")]);
        let msg = Message::try_from(&sexpr).unwrap();
        assert!(msg.caused_by().is_none());
    }

    #[test]
    fn caused_by_empty_list_error() {
        let sexpr = list(vec![
            sym("tell"),
            str_expr("hello"),
            kw("caused-by"),
            list(vec![]),
        ]);
        assert!(Message::try_from(&sexpr).is_err());
    }

    #[test]
    fn caused_by_invalid_type_error() {
        let sexpr = list(vec![
            sym("tell"),
            str_expr("hello"),
            kw("caused-by"),
            SExpr::Atom(Atom::Num(42)),
        ]);
        assert!(Message::try_from(&sexpr).is_err());
    }

    #[test]
    fn caused_by_roundtrip_begin() {
        let original = list(vec![
            sym("tell"),
            str_expr("hello"),
            kw("caused-by"),
            sym("begin"),
        ]);
        let msg = Message::try_from(&original).unwrap();
        let back = SExpr::from(msg);
        assert_eq!(back, original);
    }

    #[test]
    fn caused_by_roundtrip_single() {
        let original = list(vec![
            sym("reply"),
            str_expr("done"),
            kw("caused-by"),
            sym("sha256:abc"),
        ]);
        let msg = Message::try_from(&original).unwrap();
        let back = SExpr::from(msg);
        assert_eq!(back, original);
    }

    #[test]
    fn caused_by_roundtrip_multiple_sorted() {
        // Input already sorted → roundtrip exact match
        let original = list(vec![
            sym("ok"),
            str_expr("ack"),
            kw("caused-by"),
            list(vec![sym("aaa"), sym("bbb"), sym("ccc")]),
        ]);
        let msg = Message::try_from(&original).unwrap();
        let back = SExpr::from(msg);
        assert_eq!(back, original);
    }

    #[test]
    fn caused_by_roundtrip_multiple_canonicalized() {
        // Input unsorted → extract canonicalizes → roundtrip produces sorted form
        let input = list(vec![
            sym("ok"),
            str_expr("ack"),
            kw("caused-by"),
            list(vec![sym("ccc"), sym("aaa"), sym("bbb")]),
        ]);
        let msg = Message::try_from(&input).unwrap();
        let back = SExpr::from(msg);
        let expected = list(vec![
            sym("ok"),
            str_expr("ack"),
            kw("caused-by"),
            list(vec![sym("aaa"), sym("bbb"), sym("ccc")]),
        ]);
        assert_eq!(back, expected);
    }

    #[test]
    fn caused_by_with_thread_and_sender() {
        let sexpr = list(vec![
            sym("tell"),
            sym("@bob"),
            str_expr("hello"),
            kw("thread"),
            sym("conv-1"),
            kw("sender"),
            sym("@alice"),
            kw("caused-by"),
            sym("sha256:xyz"),
        ]);
        let msg = Message::try_from(&sexpr).unwrap();
        assert_eq!(msg.thread(), Some("conv-1"));
        assert_eq!(msg.sender(), Some("@alice"));
        assert_eq!(
            msg.caused_by(),
            Some(&CausedBy::Single(String::from("sha256:xyz")))
        );
    }

    #[test]
    fn caused_by_extract_hash_deterministic() {
        // REQ-202: extract → canonical → hash is deterministic
        use crate::canonical::canonical_encode;

        let sexpr1 = list(vec![
            sym("ok"),
            str_expr("ack"),
            kw("caused-by"),
            list(vec![sym("z"), sym("a"), sym("m")]),
        ]);
        let sexpr2 = list(vec![
            sym("ok"),
            str_expr("ack"),
            kw("caused-by"),
            list(vec![sym("m"), sym("z"), sym("a")]),
        ]);
        let msg1 = Message::try_from(&sexpr1).unwrap();
        let msg2 = Message::try_from(&sexpr2).unwrap();
        let bytes1 = canonical_encode(&SExpr::from(msg1));
        let bytes2 = canonical_encode(&SExpr::from(msg2));
        assert_eq!(
            bytes1, bytes2,
            "canonical encoding must be deterministic after sorting"
        );
    }

    // ---- SPEC-014 REQ-622: recipient sets ----

    #[test]
    fn multicast_recipient_parses_and_roundtrips() {
        let sexpr: SExpr = "(login (@cli @as) \"n-42\" :caused-by h0)".parse().unwrap();
        let msg = Message::try_from(&sexpr).unwrap();
        let set = msg.recipient_set();
        assert_eq!(set.len(), 2);
        assert!(set.contains("@cli") && set.contains("@as"));
        // round-trip: serialise and re-parse preserves the set
        let back = SExpr::from(&msg);
        let msg2 = Message::try_from(&back).unwrap();
        assert_eq!(msg, msg2);
    }

    #[test]
    fn multicast_serialisation_is_canonical_sorted() {
        let a: SExpr = "(login (@b @a) \"x\")".parse().unwrap();
        let b: SExpr = "(login (@a @b) \"x\")".parse().unwrap();
        let ma = Message::try_from(&a).unwrap();
        let mb = Message::try_from(&b).unwrap();
        assert_eq!(SExpr::from(&ma), SExpr::from(&mb));
    }

    #[test]
    fn single_recipient_form_is_unchanged() {
        let sexpr: SExpr = "(tell @bob \"hi\")".parse().unwrap();
        let msg = Message::try_from(&sexpr).unwrap();
        assert_eq!(msg.recipient(), Some("@bob"));
        assert_eq!(SExpr::from(&msg), sexpr);
    }

    #[test]
    fn empty_list_stays_content_not_recipient() {
        let sexpr: SExpr = "(tell () :thread \"t\")".parse().unwrap();
        let msg = Message::try_from(&sexpr).unwrap();
        assert!(msg.recipient_set().is_empty());
        assert_eq!(msg.content(), Some(&SExpr::List(Vec::new())));
    }

    #[test]
    fn non_recipient_list_stays_content() {
        let sexpr: SExpr = "(tell (a b) \"x\")".parse().unwrap();
        let msg = Message::try_from(&sexpr).unwrap();
        assert!(msg.recipient_set().is_empty());
    }

    // ---- Addresses are sigil-disciplined: a bare `@`-symbol is an address,
    // never positional content. Found by the role_layer round-trip fuzzer. ----

    fn parses(src: &str) -> bool {
        let sexpr: SExpr = src.parse().unwrap();
        Message::try_from(&sexpr).is_ok()
    }

    fn round_trips(src: &str) {
        let sexpr: SExpr = src.parse().unwrap();
        let msg = Message::try_from(&sexpr).unwrap();
        let back = SExpr::from(&msg);
        let msg2 = Message::try_from(&back).unwrap();
        assert_eq!(msg, msg2, "round-trip must be identity for {src}");
    }

    #[test]
    fn address_group_in_content_position_is_rejected() {
        // Bare address after keyword params, no recipient (fuzzer find #1).
        assert!(!parses("(tell :session \"foo\" @key)"));
        // A second bare address after the recipient.
        assert!(!parses("(reply @alice @bob)"));
        // A bare address in a positional param slot (after content).
        assert!(!parses("(tell @client \"msg\" @extra)"));
        // An all-`@` *list* in the content position collides with the
        // recipient set form `(@a @b)` (fuzzer find #2).
        assert!(!parses("(tell :kw \"v\" (@a @b))"));
        assert!(!parses("(reply @dest (@a @b))"));
        // ...but the same list *leading* is a legitimate recipient set.
        assert!(parses("(tell (@@@))"));
        assert!(parses("(tell (@a @b) \"content\")"));
    }

    #[test]
    fn addresses_in_content_are_fine_when_tagged_or_wrapped() {
        // Keyword value.
        assert!(parses("(tell @client :ref @bob :action \"review\")"));
        round_trips("(tell @client :ref @bob :action \"review\")");
        // Nested inside a structured (list) content.
        assert!(parses("(tell @client (introduce @bob))"));
        round_trips("(tell @client (introduce @bob))");
        // Inside a string literal — just text, not an address token.
        assert!(parses("(tell @client \"ping @bob\")"));
        round_trips("(tell @client \"ping @bob\")");
        // Multicast recipient set + string content (the paper's OAuth trace).
        assert!(parses("(login (@cli @as) \"n-42\" \"profile\")"));
        round_trips("(login (@cli @as) \"n-42\" \"profile\")");
    }

    #[test]
    fn two_recipients_must_use_the_set_form() {
        // The nudge: `(@a @b)` is unambiguous; `@a @b` is not (and is rejected).
        assert!(parses("(reply (@alice @bob) \"ok\")"));
        assert!(!parses("(reply @alice @bob \"ok\")"));
    }

    // ---- SPEC-014 REQ-625: with-roles typed wrapper ----

    #[test]
    fn with_roles_parses_as_typed_wrapper() {
        let sexpr: SExpr =
            "(with-roles ((auctioneer @auc) (bidder @b1 @b2)) (signed @auc \"sig\" (hello :thread \"conv-7\" :caused-by begin)))"
                .parse()
                .unwrap();
        let msg = Message::try_from(&sexpr).unwrap();
        let Message::Wrapped {
            wrapper,
            params,
            content,
        } = &msg
        else {
            panic!("with-roles must parse as Wrapped, got {msg:?}");
        };
        assert_eq!(*wrapper, WrapperType::WithRoles);
        assert_eq!(params.len(), 1, "bindings list travels in params");
        // inner signed message carried unchanged
        let Message::Wrapped {
            wrapper: inner_w, ..
        } = content.as_ref()
        else {
            panic!("inner must be the signed wrapper");
        };
        assert_eq!(*inner_w, WrapperType::Signed);
        // round-trip
        let back = SExpr::from(&msg);
        assert_eq!(Message::try_from(&back).unwrap(), msg);
    }

    #[test]
    fn with_roles_bindings_parse_into_cast() {
        use crate::role::{parse_cast, parse_roles};
        let sexpr: SExpr =
            "(with-roles ((auctioneer @auc) (bidder @b1 @b2)) (signed @auc \"sig\" (hello :caused-by begin)))"
                .parse()
                .unwrap();
        let msg = Message::try_from(&sexpr).unwrap();
        let Message::Wrapped { params, .. } = &msg else {
            unreachable!()
        };
        let roles = parse_roles(&"(auctioneer (* bidder))".parse().unwrap()).unwrap();
        let cast = parse_cast(&params[0], &roles).unwrap();
        assert_eq!(cast.indexed.get("bidder").unwrap().len(), 2);
    }
}
