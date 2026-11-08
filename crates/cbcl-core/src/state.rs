//! State layer (SPEC-019 R.1–R.3): the `(state …)` clause, fixed kernel
//! selections and reductions (including protocol-position maximum), the fold, and the
//! canonical JSON rendering.
//!
//! Every function here is a pure set function of a thread's accepted acts:
//! permuting or duplicating the input leaves the output unchanged (R7).
//! No clock, no randomness, no other thread.

#![forbid(unsafe_code)]

use crate::equivocation::message_content_hash;
use crate::message::{CausedBy, Message};
use crate::protocol::{CausalProtocol, NodeRef, BEGIN_KEYWORD};
use crate::sexpr::{Atom, SExpr};
use crate::shape::{ShapeRule, TypeConstraint};
use alloc::collections::{BTreeMap, BTreeSet};
use alloc::format;
use alloc::string::{String, ToString};
use alloc::vec::Vec;

/// The reserved bookkeeping keyword (SPEC-019 ADR-1901). Inserted into the
/// shapes of every writer, delete, and remove verb by the compiler; never
/// declared by an author; never read as data by any rule.
pub const RESERVED_REPLACES: &str = "replaces";

/// Routing keywords that a closed shape admits beside the declared fields.
pub const ROUTING_KEYWORDS: &[&str] = &["caused-by", "thread", "from", "to", "sender"];

// ---------------------------------------------------------------------------
// Clause types
// ---------------------------------------------------------------------------

/// `(:state-bounds …)` (SPEC-019 R.1, ADR-1911). Defaults apply when absent.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct StateBounds {
    pub max_string: u32,
    pub max_list: u32,
    pub max_number: i64,
    pub max_fields: u32,
}

impl Default for StateBounds {
    fn default() -> Self {
        Self {
            max_string: 2048,
            max_list: 64,
            max_number: 1_000_000_000_000,
            max_fields: 32,
        }
    }
}

/// One author-facing rule (SPEC-019 R.1). Defined by desugaring to the
/// kernel (R.2); see [`fold`].
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Rule {
    Context {
        path: Vec<String>,
        definition: Option<alloc::boxed::Box<crate::context::Definition>>,
    },
    /// A finite lattice and contribution table verified at installation.
    Lift(alloc::boxed::Box<crate::finite::Lift>),
    BoundedCounter(alloc::boxed::Box<crate::escrow::CounterRule>),
    /// Clock-trusting last-writer-wins over domain-admitted writes.
    LwwRegister {
        verb: String,
        key: String,
        clock: String,
    },
    /// Own observed replacement, then clock arbitration among survivors.
    LwwPerSigner {
        verb: String,
        key: String,
        clock: String,
    },
    /// Keyed observed replacement/deletion, then clock arbitration.
    LwwMap {
        verb: String,
        key: String,
        value: String,
        clock: String,
        delete: Option<String>,
    },
    /// Immutable field of the unique accepted opener; no arbitration.
    Initial {
        verb: String,
        key: String,
    },
    Exists {
        verb: String,
    },
    Count {
        verb: String,
    },
    /// Greatest established position of a verb in its ordered protocol chain.
    Progress {
        verb: String,
    },
    Events {
        verb: String,
        key: String,
    },
    SetUnion {
        verb: String,
        key: String,
    },
    Values {
        verb: String,
        key: String,
    },
    ValuesPerKey {
        verb: String,
        key: String,
        value: String,
        delete: Option<String>,
    },
    ObservedSet {
        add: String,
        remove: String,
        key: String,
    },
    Counter {
        inc: String,
        dec: String,
        key: String,
    },
    Histogram {
        field: String,
    },
    Sum {
        field: String,
    },
}

impl Rule {
    /// The head symbol of this rule in the clause grammar.
    pub fn head(&self) -> &'static str {
        match self {
            Rule::Context { .. } => "context",
            Rule::Lift(_) => "lift",
            Rule::BoundedCounter(_) => "bounded-counter",
            Rule::LwwRegister { .. } => "lww-register",
            Rule::LwwPerSigner { .. } => "lww-per-signer",
            Rule::LwwMap { .. } => "lww-map",
            Rule::Initial { .. } => "initial",

            Rule::Exists { .. } => "exists",
            Rule::Count { .. } => "count",
            Rule::Progress { .. } => "progress",
            Rule::Events { .. } => "events",
            Rule::SetUnion { .. } => "set-union",
            Rule::Values { .. } => "values",
            Rule::ValuesPerKey { .. } => "values-per-key",

            Rule::ObservedSet { .. } => "observed-set",
            Rule::Counter { .. } => "counter",
            Rule::Histogram { .. } => "histogram",
            Rule::Sum { .. } => "sum",
        }
    }

    /// Every performative this rule names.
    pub fn verbs(&self) -> Vec<&str> {
        match self {
            Rule::Context { .. } => Vec::new(),
            Rule::Lift(lift) => alloc::vec![lift.verb.as_str()],
            Rule::BoundedCounter(c) => c.verbs(),
            Rule::LwwRegister { verb, .. }
            | Rule::LwwPerSigner { verb, .. }
            | Rule::Initial { verb, .. }
            | Rule::Exists { verb }
            | Rule::Count { verb }
            | Rule::Progress { verb }
            | Rule::Events { verb, .. }
            | Rule::SetUnion { verb, .. }
            | Rule::Values { verb, .. } => alloc::vec![verb.as_str()],
            Rule::ValuesPerKey { verb, delete, .. } | Rule::LwwMap { verb, delete, .. } => {
                let mut v = alloc::vec![verb.as_str()];
                if let Some(d) = delete {
                    v.push(d.as_str());
                }
                v
            }
            Rule::ObservedSet { add, remove, .. } => alloc::vec![add.as_str(), remove.as_str()],
            Rule::Counter { inc, dec, .. } => alloc::vec![inc.as_str(), dec.as_str()],
            Rule::Histogram { .. } | Rule::Sum { .. } => Vec::new(),
        }
    }

    /// Declared clock evidence of an explicit LWW rule, if any.
    pub fn clock_field(&self) -> Option<(&str, &str)> {
        match self {
            Rule::LwwRegister { verb, clock, .. }
            | Rule::LwwPerSigner { verb, clock, .. }
            | Rule::LwwMap { verb, clock, .. } => Some((verb, clock)),
            _ => None,
        }
    }

    /// Every `(verb, key)` pair this rule reads as data.
    pub fn data_fields(&self) -> Vec<(&str, &str)> {
        match self {
            Rule::Context { .. } => Vec::new(),
            Rule::Lift(lift) => lift
                .rows
                .iter()
                .map(|row| (lift.verb.as_str(), row.key.as_str()))
                .collect(),
            Rule::BoundedCounter(c) => c.data_fields(),
            Rule::LwwRegister { verb, key, clock } | Rule::LwwPerSigner { verb, key, clock } => {
                alloc::vec![(verb, key), (verb, clock)]
            }
            Rule::LwwMap {
                verb,
                key,
                value,
                clock,
                delete,
            } => {
                let mut fields = alloc::vec![
                    (verb.as_str(), key.as_str()),
                    (verb.as_str(), value.as_str()),
                    (verb.as_str(), clock.as_str())
                ];
                if let Some(d) = delete {
                    fields.push((d, key));
                }
                fields
            }
            Rule::Initial { verb, key }
            | Rule::Events { verb, key }
            | Rule::SetUnion { verb, key }
            | Rule::Values { verb, key } => alloc::vec![(verb.as_str(), key.as_str())],

            Rule::ValuesPerKey {
                verb,
                key,
                value,
                delete,
            } => {
                let mut v = alloc::vec![
                    (verb.as_str(), key.as_str()),
                    (verb.as_str(), value.as_str())
                ];
                if let Some(d) = delete {
                    v.push((d.as_str(), key.as_str()));
                }
                v
            }
            Rule::ObservedSet { add, remove, key } => {
                alloc::vec![
                    (add.as_str(), key.as_str()),
                    (remove.as_str(), key.as_str())
                ]
            }
            Rule::Counter { inc, dec, key } => {
                alloc::vec![(inc.as_str(), key.as_str()), (dec.as_str(), key.as_str())]
            }
            Rule::Exists { .. }
            | Rule::Count { .. }
            | Rule::Progress { .. }
            | Rule::Histogram { .. }
            | Rule::Sum { .. } => Vec::new(),
        }
    }

    /// The verbs whose shape must carry the reserved `:replaces` field:
    /// writers and delete verbs of registers, signer writers, and observed-set removals.
    pub fn replaces_verbs(&self) -> Vec<&str> {
        match self {
            Rule::Values { verb, .. } | Rule::LwwPerSigner { verb, .. } => {
                alloc::vec![verb.as_str()]
            }
            Rule::ValuesPerKey { verb, delete, .. } | Rule::LwwMap { verb, delete, .. } => {
                let mut v = alloc::vec![verb.as_str()];
                if let Some(d) = delete {
                    v.push(d.as_str());
                }
                v
            }
            Rule::ObservedSet { remove, .. } => alloc::vec![remove.as_str()],
            _ => Vec::new(),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum FreezePolicy {
    Supersede,
    Fault,
}

impl FreezePolicy {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Supersede => "supersede",
            Self::Fault => "fault",
        }
    }
}

/// One entry of the state clause.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Entry {
    Lattice(crate::finite::Definition),
    Field {
        name: String,
        rule: Rule,
    },
    /// `(domain verb key field)`: acts of `verb` whose `key` is not an
    /// element of the list-valued `field` contribute nothing.
    Domain {
        verb: String,
        key: String,
        field: String,
    },
    /// `(threshold name field element+)`: a threshold read over `field`'s
    /// carrier (SPEC-038 REQ-3802, CON-3801), rendered as a field named
    /// `name` in clause order: `reached` with the unique element at or below
    /// the carrier's current element, or `pending`.
    Threshold {
        name: String,
        field: String,
        elements: Vec<crate::lattice::Element>,
    },
    Freeze {
        field: String,
        verb: String,
        policy: FreezePolicy,
    },
}

/// The parsed `(state …)` clause (SPEC-019 R.1).
#[derive(Debug, Clone, PartialEq, Eq, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct StateClause {
    pub entries: Vec<Entry>,
}

impl StateClause {
    pub fn lattices(&self) -> impl Iterator<Item = &crate::finite::Definition> {
        self.entries.iter().filter_map(|entry| match entry {
            Entry::Lattice(d) => Some(d),
            _ => None,
        })
    }

    /// Rebuild implementation-only table indexes from recognized declarations.
    pub fn resolve_lattices(&mut self) {
        let definitions: BTreeMap<String, crate::finite::Definition> = self
            .lattices()
            .map(|d| (d.name.clone(), d.clone()))
            .collect();
        for entry in &mut self.entries {
            if let Entry::Field {
                rule: Rule::Lift(lift),
                ..
            } = entry
            {
                lift.table = definitions
                    .get(&lift.lattice)
                    .and_then(|d| d.compile().ok())
                    .map(alloc::boxed::Box::new);
            }
        }
    }
    /// Field entries in clause order.
    pub fn fields(&self) -> impl Iterator<Item = (&str, &Rule)> {
        self.entries.iter().filter_map(|e| match e {
            Entry::Field { name, rule } => Some((name.as_str(), rule)),
            _ => None,
        })
    }

    /// Domain entries in clause order.
    pub fn domains(&self) -> impl Iterator<Item = (&str, &str, &str)> {
        self.entries.iter().filter_map(|e| match e {
            Entry::Domain { verb, key, field } => {
                Some((verb.as_str(), key.as_str(), field.as_str()))
            }
            _ => None,
        })
    }

    /// Threshold entries in clause order: `(name, field, elements)`
    /// (SPEC-038 CON-3801).
    pub fn thresholds(&self) -> impl Iterator<Item = (&str, &str, &[crate::lattice::Element])> {
        self.entries.iter().filter_map(|e| match e {
            Entry::Threshold {
                name,
                field,
                elements,
            } => Some((name.as_str(), field.as_str(), elements.as_slice())),
            _ => None,
        })
    }

    pub fn freezes(&self) -> impl Iterator<Item = (&str, &str, FreezePolicy)> {
        self.entries.iter().filter_map(|e| match e {
            Entry::Freeze {
                field,
                verb,
                policy,
            } => Some((field.as_str(), verb.as_str(), *policy)),
            _ => None,
        })
    }

    /// Every performative the clause names (state-bearing verbs).
    pub fn state_bearing_verbs(&self) -> BTreeSet<&str> {
        let mut out = BTreeSet::new();
        for (_, rule) in self.fields() {
            out.extend(rule.verbs());
        }
        for (verb, _, _) in self.domains() {
            out.insert(verb);
        }
        for (_, verb, _) in self.freezes() {
            out.insert(verb);
        }
        out
    }

    /// Verbs whose shape carries the reserved `:replaces` field.
    pub fn replaces_verbs(&self) -> BTreeSet<&str> {
        let mut out = BTreeSet::new();
        for (_, rule) in self.fields() {
            out.extend(rule.replaces_verbs());
        }
        out
    }

    /// Every `(verb, key)` pair any rule or domain reads.
    pub fn data_fields(&self) -> BTreeSet<(&str, &str)> {
        let mut out = BTreeSet::new();
        for (_, rule) in self.fields() {
            out.extend(rule.data_fields());
        }
        for (verb, key, _) in self.domains() {
            out.insert((verb, key));
        }
        out
    }

    /// The rule of a named field, if any.
    pub fn rule_of(&self, field: &str) -> Option<&Rule> {
        self.fields().find(|(n, _)| *n == field).map(|(_, r)| r)
    }
}

/// The opener of a protocol: the one performative whose only predecessor
/// is `begin`, when exactly one exists.
pub fn opener_verb(protocol: &CausalProtocol) -> Option<&str> {
    let mut found = None;
    for (name, step) in &protocol.steps {
        if name == BEGIN_KEYWORD {
            continue;
        }
        let only_begin = step.predecessors.len() == 1
            && matches!(&step.predecessors[0], NodeRef::Single(s) if s == BEGIN_KEYWORD);
        if only_begin {
            if found.is_some() {
                return None;
            }
            found = Some(crate::protocol::repeat_base_name(name));
        }
    }
    found
}

// ---------------------------------------------------------------------------
// Acts
// ---------------------------------------------------------------------------

/// An accepted message as the fold sees it (SPEC-019 Reference, "act").
///
/// The signer is supplied by the host's authentication gate, never read
/// from the payload. `message` is the complete received message, wrappers
/// included, so a store can be rebuilt from acts for the binder's
/// verification step and the cast can be read from the root wrapper.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Act {
    /// `message_content_hash` of the innermost simple message.
    pub address: String,
    pub verb: String,
    pub signer: String,
    pub predecessors: Vec<String>,
    pub recipients: BTreeSet<String>,
    /// Keyword fields of the innermost simple message, routing keywords
    /// excluded.
    pub fields: BTreeMap<String, SExpr>,
    pub message: Message,
}

impl Act {
    /// View a received message as an act. `signer` is the authenticated
    /// sender established by the host.
    pub fn from_message(message: Message, signer: &str) -> Result<Act, String> {
        let simple = message
            .innermost_simple()
            .ok_or_else(|| String::from("an act must contain a simple message"))?;
        let verb = simple
            .performative()
            .ok_or_else(|| String::from("an act must have a performative"))?
            .name()
            .to_string();
        let predecessors = match simple.caused_by() {
            None | Some(CausedBy::Begin) => Vec::new(),
            Some(CausedBy::Single(h)) => alloc::vec![h.clone()],
            Some(CausedBy::Multiple(hs)) => hs.clone(),
        };
        let recipients = simple
            .recipient_set()
            .into_iter()
            .map(String::from)
            .collect();
        let fields = keyword_fields(simple);
        let address = wire_address(simple);
        Ok(Act {
            address,
            verb,
            signer: String::from(signer),
            predecessors,
            recipients,
            fields,
            message,
        })
    }

    /// Check derived metadata against the message without cloning an owned Act.
    /// The signer remains host-supplied; this check does not authenticate it.
    pub(crate) fn validate_identity(&self) -> Result<(), String> {
        let simple = self
            .message
            .innermost_simple()
            .ok_or_else(|| String::from("an act must contain a simple message"))?;
        let verb = simple
            .performative()
            .ok_or_else(|| String::from("an act must have a performative"))?;
        let predecessors_match = match simple.caused_by() {
            None | Some(CausedBy::Begin) => self.predecessors.is_empty(),
            Some(CausedBy::Single(h)) => self.predecessors.as_slice() == core::slice::from_ref(h),
            Some(CausedBy::Multiple(hs)) => self.predecessors == *hs,
        };
        // Mirror keyword_fields exactly, including last-value-wins and its
        // permissive scan of malformed lists. Structural admission checks the
        // complete parameter grammar afterward, at the original rejection point.
        let mut fields = BTreeMap::new();
        if let Message::Simple { params, .. } = simple {
            let mut i = 0;
            while i + 1 < params.len() {
                if let SExpr::Atom(Atom::Keyword(k)) = &params[i] {
                    if !ROUTING_KEYWORDS.contains(&k.as_str()) {
                        fields.insert(k.as_str(), &params[i + 1]);
                    }
                    i += 2;
                } else {
                    i += 1;
                }
            }
        }
        let fields_match = fields.len() == self.fields.len()
            && fields
                .into_iter()
                .all(|(k, v)| self.fields.get(k) == Some(v));
        let recipients = simple.recipient_set();
        let recipients_match = self.recipients.iter().map(String::as_str).eq(recipients);
        let address = wire_address(simple);
        if self.address != address
            || self.verb != verb.name()
            || !predecessors_match
            || !recipients_match
            || !fields_match
        {
            return Err(String::from("inconsistent act identity"));
        }
        Ok(())
    }

    /// The innermost simple message.
    pub fn simple(&self) -> &Message {
        self.message
            .innermost_simple()
            .expect("an Act always wraps a simple message")
    }
}

/// The content address of an act as it is spelled on the wire:
/// `sha256-<64 lowercase hex>`. The digest is `message_content_hash`'s
/// (SPEC-017); the separator differs because the wire lexer reads `:` as
/// the start of a keyword, so `sha256:<hex>` cannot appear in a message.
/// Every address the state layer stores, compares, or emits uses this
/// spelling (SPEC-019 R.6).
pub fn wire_address(simple: &Message) -> String {
    let h = message_content_hash(simple);
    match h.strip_prefix("sha256:") {
        Some(hex) => format!("sha256-{hex}"),
        None => h,
    }
}

/// The keyword parameters of a simple message as a map, routing keywords
/// excluded.
pub fn keyword_fields(simple: &Message) -> BTreeMap<String, SExpr> {
    let mut out = BTreeMap::new();
    if let Message::Simple { params, .. } = simple {
        let mut i = 0;
        while i + 1 < params.len() {
            if let SExpr::Atom(Atom::Keyword(k)) = &params[i] {
                if !ROUTING_KEYWORDS.contains(&k.as_str()) {
                    out.insert(k.clone(), params[i + 1].clone());
                }
                i += 2;
            } else {
                i += 1;
            }
        }
    }
    out
}

/// The accepted opener, if present: the act of the protocol's opener verb.
/// Role-free, its predecessor is `begin`; under R6 it names the thread's
/// cast-bearing root ([[SPEC-014]] REQ-623), which is not an act of the
/// dialect. Several openers in one thread cannot verify, so the least
/// address is a deterministic tie-break, never a semantic one.
pub fn opener<'a>(protocol: &CausalProtocol, acts: &'a [Act]) -> Option<&'a Act> {
    let verb = opener_verb(protocol)?;
    let repeated = protocol.steps.keys().any(|name| {
        name.contains(crate::protocol::REPEAT_SEPARATOR)
            && crate::protocol::repeat_base_name(name) == verb
    });
    let root = root(acts);
    acts.iter()
        .filter(|a| {
            a.verb == verb
                && (!repeated
                    || matches!(
                        a.simple().caused_by(),
                        Some(crate::message::CausedBy::Begin)
                    )
                    || root.is_some_and(|r| a.predecessors == alloc::vec![r.address.clone()]))
        })
        .min_by(|a, b| a.address.cmp(&b.address))
}

/// The thread's R6 root: the act whose message carries the `with-roles`
/// wrapper (the cast) and no predecessor. `None` for a role-free thread.
pub fn root(acts: &[Act]) -> Option<&Act> {
    acts.iter()
        .filter(|a| {
            a.predecessors.is_empty()
                && a.message.wrapper_type() == Some(crate::message::WrapperType::WithRoles)
        })
        .min_by(|a, b| a.address.cmp(&b.address))
}

/// The frontier: addresses no accepted act names in `:caused-by`, sorted.
pub fn frontier(acts: &[Act]) -> Vec<String> {
    let named: BTreeSet<&str> = acts
        .iter()
        .flat_map(|a| a.predecessors.iter().map(|p| p.as_str()))
        .collect();
    let mut out: Vec<String> = acts
        .iter()
        .filter(|a| !named.contains(a.address.as_str()))
        .map(|a| a.address.clone())
        .collect();
    out.sort();
    out.dedup();
    out
}

// ---------------------------------------------------------------------------
// Values
// ---------------------------------------------------------------------------

/// A state value (SPEC-019 R.3).
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Value {
    Absent,
    Str(String),
    Int(i128),
    Bool(bool),
    /// A scalar list as a field value (never sorted; it is data).
    List(Vec<Value>),
    /// A set: distinct elements sorted by rendering.
    Set(Vec<Value>),
    /// A map: distinct keys sorted by rendering.
    Map(Vec<(Value, Value)>),
    /// A contribution of `events`: who supplied a value.
    Pair {
        by: String,
        value: alloc::boxed::Box<Value>,
    },
}

impl Value {
    pub(crate) fn unfrozen(&self) -> &Value {
        if let Value::Map(entries) = self {
            if entries
                .iter()
                .any(|(k, v)| matches!((k,v), (Value::Str(k),Value::Str(_)) if k == "frozen"))
                && entries.iter().any(
                    |(k, v)| matches!((k,v), (Value::Str(k),Value::List(_)) if k == "superseded"),
                )
            {
                if let Some((_, value)) = entries
                    .iter()
                    .find(|(k, _)| matches!(k, Value::Str(k) if k == "value"))
                {
                    return value;
                }
            }
        }
        self
    }
    /// Evidence of a kernel fault. Installed scalar-map types cannot mimic
    /// the mixed scalar/list structure of this marker.
    pub fn fault_evidence(&self) -> Option<Vec<String>> {
        let Value::Map(entries) = self else {
            return None;
        };
        if !entries.iter().any(|(k, v)| {
            matches!((k, v),
            (Value::Str(k), Value::Str(v)) if k == "status" && v == "fault")
        }) {
            return None;
        }
        let (_, Value::List(addresses)) = entries
            .iter()
            .find(|(k, _)| matches!(k, Value::Str(k) if k == "evidence"))?
        else {
            return None;
        };
        addresses
            .iter()
            .map(|v| match v {
                Value::Str(address) => Some(address.clone()),
                _ => None,
            })
            .collect()
    }

    /// Convert a field value. Symbols and keywords, which typing forbids on
    /// state-bearing fields, render as their text so the fold stays total.
    pub fn from_sexpr(s: &SExpr) -> Value {
        match s {
            SExpr::Atom(Atom::Str(x)) => Value::Str(x.clone()),
            SExpr::Atom(Atom::Num(n)) => Value::Int(*n as i128),
            SExpr::Atom(Atom::Bool(b)) => Value::Bool(*b),
            SExpr::Atom(Atom::Symbol(x)) => Value::Str(x.clone()),
            SExpr::Atom(Atom::Keyword(x)) => Value::Str(format!(":{x}")),
            SExpr::List(items) => Value::List(items.iter().map(Value::from_sexpr).collect()),
        }
    }

    /// The canonical JSON rendering (R.3).
    pub fn render(&self) -> String {
        let mut out = String::new();
        self.render_into(&mut out);
        out
    }

    fn render_into(&self, out: &mut String) {
        match self {
            Value::Absent => out.push_str("null"),
            Value::Str(s) => json_string(s, out),
            Value::Int(n) => out.push_str(&n.to_string()),
            Value::Bool(b) => out.push_str(if *b { "true" } else { "false" }),
            Value::List(items) => {
                out.push('[');
                for (i, v) in items.iter().enumerate() {
                    if i > 0 {
                        out.push(',');
                    }
                    v.render_into(out);
                }
                out.push(']');
            }
            Value::Set(items) => {
                out.push('[');
                for (i, v) in items.iter().enumerate() {
                    if i > 0 {
                        out.push(',');
                    }
                    v.render_into(out);
                }
                out.push(']');
            }
            Value::Map(entries) => {
                out.push('{');
                for (i, (k, v)) in entries.iter().enumerate() {
                    if i > 0 {
                        out.push(',');
                    }
                    json_string(&map_key_text(k), out);
                    out.push(':');
                    v.render_into(out);
                }
                out.push('}');
            }
            Value::Pair { by, value } => {
                out.push_str("{\"by\":");
                json_string(by, out);
                out.push_str(",\"value\":");
                value.render_into(out);
                out.push('}');
            }
        }
    }

    pub fn as_int(&self) -> Option<i128> {
        match self {
            Value::Int(n) => Some(*n),
            Value::Pair { value, .. } => value.as_int(),
            _ => None,
        }
    }
}

/// The text a scalar contributes as a map key: a string as itself, a
/// number or boolean as its rendering. A key field has one declared type,
/// so no collision arises.
fn map_key_text(k: &Value) -> String {
    match k {
        Value::Str(s) => s.clone(),
        other => other.render(),
    }
}

/// RFC 8259 string escaping: the two-character forms where they exist,
/// `\u00XX` (lowercase hex) for other control characters.
fn json_string(s: &str, out: &mut String) {
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            '\u{8}' => out.push_str("\\b"),
            '\u{c}' => out.push_str("\\f"),
            c if (c as u32) < 0x20 => {
                out.push_str(&format!("\\u{:04x}", c as u32));
            }
            c => out.push(c),
        }
    }
    out.push('"');
}

/// Distinct values sorted by the UTF-8 bytes of their rendering.
fn sorted_distinct(values: Vec<Value>) -> Vec<Value> {
    let mut keyed: Vec<(String, Value)> = values.into_iter().map(|v| (v.render(), v)).collect();
    keyed.sort_by(|a, b| a.0.as_bytes().cmp(b.0.as_bytes()));
    keyed.dedup_by(|a, b| a.0 == b.0);
    keyed.into_iter().map(|(_, v)| v).collect()
}

/// The conflict top ⊤ of a field, rendered uniformly across heads as
/// `{"evidence":[addresses],"reason":…,"status":"fault"}` with the members
/// in key order and the evidence sorted (SPEC-038 REQ-3804, ADR-3803): the
/// same member set a `bounded-counter` resource fault carries.
pub(crate) fn conflict_top(reason: &str, mut evidence: Vec<String>) -> Value {
    sort_addresses(&mut evidence);
    evidence.dedup();
    Value::Map(alloc::vec![
        (
            Value::Str(String::from("evidence")),
            Value::List(evidence.into_iter().map(Value::Str).collect()),
        ),
        (
            Value::Str(String::from("reason")),
            Value::Str(String::from(reason)),
        ),
        (
            Value::Str(String::from("status")),
            Value::Str(String::from("fault"))
        ),
    ])
}

/// Byte-order radix sort for bounded content addresses (SPEC-038 NFR-3800).
/// Sorting indices avoids cloning addresses on every digit pass. A missing
/// byte sorts before any byte, preserving ordinary lexicographic prefix order.
pub(crate) fn sort_addresses(addresses: &mut Vec<String>) {
    if addresses.len() < 2 {
        return;
    }
    let width = addresses.iter().map(|s| s.len()).max().unwrap_or(0);
    let mut order: Vec<usize> = (0..addresses.len()).collect();
    let mut scratch = alloc::vec![0usize; addresses.len()];
    for digit in (0..width).rev() {
        let key = |i: usize| {
            addresses[i]
                .as_bytes()
                .get(digit)
                .map(|b| *b as usize + 1)
                .unwrap_or(0)
        };
        let mut counts = [0usize; 257];
        for &i in &order {
            counts[key(i)] += 1;
        }
        let mut next = [0usize; 257];
        for k in 1..257 {
            next[k] = next[k - 1] + counts[k - 1];
        }
        for &i in &order {
            let k = key(i);
            scratch[next[k]] = i;
            next[k] += 1;
        }
        core::mem::swap(&mut order, &mut scratch);
    }
    let mut values: Vec<Option<String>> =
        core::mem::take(addresses).into_iter().map(Some).collect();
    addresses.extend(order.into_iter().map(|i| values[i].take().unwrap()));
}

#[cfg(test)]
mod address_sort_tests {
    use super::*;
    use proptest::prelude::*;

    proptest! {
        #[test]
        fn radix_address_order_matches_byte_lexicographic_order(
            mut addresses in proptest::collection::vec(prop_oneof![
                "[a-f0-9]{0,71}",
                proptest::collection::vec(any::<char>(), 0..24)
                    .prop_map(|chars| chars.into_iter().collect::<String>()),
                Just(String::new()), Just(String::from("\0")), Just(String::from("a\0")),
            ], 0..64)
        ) {
            let mut expected = addresses.clone();
            expected.sort();
            sort_addresses(&mut addresses);
            prop_assert_eq!(addresses, expected);
        }
    }
}

/// Render a whole state (R.3): an object in clause order.
pub fn render_json(state: &[(String, Value)]) -> String {
    let mut out = String::from("{");
    for (i, (name, value)) in state.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        json_string(name, &mut out);
        out.push(':');
        value.render_into(&mut out);
    }
    out.push('}');
    out
}

// ---------------------------------------------------------------------------
// The kernel (R.2)
// ---------------------------------------------------------------------------

struct Kernel<'a> {
    /// The accepted set: one act per address, in slice order.
    acts: Vec<&'a Act>,
    /// Domain filters resolved against the opener: `(verb, key) → allowed`.
    domains: Vec<(String, String, Vec<Value>)>,
}

/// The accepted set as a slice presents it: one act per content address,
/// first occurrence kept. A store keyed by address never holds two, so
/// this is the identity on a store's contents; on an arbitrary slice it
/// is what makes `fold` a set function of the slice itself (SPEC-019 R7,
/// REQ-1930 `fold_dedup_invariant`).
fn dedup_by_address(acts: &[Act]) -> Vec<&Act> {
    let mut seen: hashbrown::HashSet<&str> = hashbrown::HashSet::new();
    acts.iter()
        .filter(|a| seen.insert(a.address.as_str()))
        .collect()
}

/// The signer's live writes, using the fold's accepted set and domains.
/// SPEC-019 REQ-1933/1934: supersession requires the same verb and signer.
pub(crate) fn current_by_signer<'a>(
    clause: &StateClause,
    acts: &'a [Act],
    verb: &str,
) -> Vec<&'a Act> {
    kernel_for(clause, acts).current_by_signer(verb)
}

/// The binder and fold share domain-aware keyed replacement selection.
/// Excluded acts contribute neither values nor retirement references.
pub(crate) fn current_writes<'a>(
    clause: &StateClause,
    acts: &'a [Act],
    verb: &str,
    key: Option<&str>,
    delete: Option<&str>,
) -> Vec<&'a Act> {
    kernel_for(clause, acts).current(verb, key, delete)
}

fn kernel_for<'a>(clause: &StateClause, acts: &'a [Act]) -> Kernel<'a> {
    // Domains read a list-valued field defined over the opener only, so
    // resolve them first with no domain in force.
    let set = dedup_by_address(acts);
    let bare = Kernel {
        acts: set.clone(),
        domains: Vec::new(),
    };
    let mut domains = Vec::new();
    for (verb, key, field) in clause.domains() {
        let allowed = match clause.rule_of(field) {
            Some(rule) => match bare.eval(rule, &[], None) {
                Value::List(items) => items,
                Value::Set(items) => items,
                _ => Vec::new(),
            },
            None => Vec::new(),
        };
        domains.push((String::from(verb), String::from(key), allowed));
    }
    Kernel { acts: set, domains }
}

impl<'a> Kernel<'a> {
    fn field(&self, act: &Act, key: &str) -> Option<Value> {
        act.fields.get(key).map(Value::from_sexpr)
    }

    /// `acts v`: the accepted acts of a verb, minus those a domain excludes.
    fn acts(&self, verb: &str) -> Vec<&'a Act> {
        self.acts
            .iter()
            .copied()
            .filter(|a| a.verb == verb)
            .filter(|a| {
                self.domains.iter().all(|(v, key, allowed)| {
                    if v != verb {
                        return true;
                    }
                    match self.field(a, key) {
                        Some(val) => {
                            let r = val.render();
                            allowed.iter().any(|x| x.render() == r)
                        }
                        None => false,
                    }
                })
            })
            .collect()
    }

    /// `current v kk d`: the writes of `v` no accepted write or deletion of
    /// the same key names in `:replaces`.
    fn current(&self, verb: &str, key: Option<&str>, delete: Option<&str>) -> Vec<&'a Act> {
        let writes = self.acts(verb);
        let mut replacers: Vec<&Act> = writes.clone();
        if let Some(d) = delete {
            replacers.extend(self.acts(d));
        }
        let key_of = |a: &Act| -> String {
            match key {
                Some(k) => self.field(a, k).map(|v| v.render()).unwrap_or_default(),
                None => String::new(),
            }
        };
        let mut replaced: BTreeSet<(String, String)> = BTreeSet::new();
        for r in &replacers {
            if let Some(SExpr::List(items)) = r.fields.get(RESERVED_REPLACES) {
                let k = key_of(r);
                for item in items {
                    if let SExpr::Atom(Atom::Symbol(a)) | SExpr::Atom(Atom::Str(a)) = item {
                        replaced.insert((k.clone(), a.clone()));
                    }
                }
            }
        }
        writes
            .into_iter()
            .filter(|w| !replaced.contains(&(key_of(w), w.address.clone())))
            .collect()
    }

    /// Current writes under signer-owned replacement addresses.
    fn current_by_signer(&self, verb: &str) -> Vec<&'a Act> {
        let writes = self.acts(verb);
        let mut replaced: BTreeSet<(&str, &str)> = BTreeSet::new();
        for r in &writes {
            if let Some(SExpr::List(items)) = r.fields.get(RESERVED_REPLACES) {
                for item in items {
                    if let SExpr::Atom(Atom::Symbol(address)) | SExpr::Atom(Atom::Str(address)) =
                        item
                    {
                        replaced.insert((r.signer.as_str(), address.as_str()));
                    }
                }
            }
        }
        writes
            .into_iter()
            .filter(|w| !replaced.contains(&(w.signer.as_str(), w.address.as_str())))
            .collect()
    }

    /// Read the sole initializer. No opener has no value; two or more
    /// distinct openers are the conflict top, rendered as a fault naming
    /// them (SPEC-038 REQ-3804, ADR-3803). The display is therefore
    /// monotone: absent, then a value, then fault, never back.
    fn initial(&self, table: &[&Act], key: &str) -> Value {
        match table {
            [] => Value::Absent,
            [act] => self.field(act, key).unwrap_or(Value::Absent),
            many => conflict_top(
                "opener fork",
                many.iter().map(|a| a.address.clone()).collect(),
            ),
        }
    }

    /// `group T g` by signer.
    fn group_by_signer<'b>(&self, table: &[&'b Act]) -> BTreeMap<String, Vec<&'b Act>> {
        let mut out: BTreeMap<String, Vec<&Act>> = BTreeMap::new();
        for a in table {
            out.entry(a.signer.clone()).or_default().push(a);
        }
        out
    }

    /// `group T g` by a key field: rendering → (key value, acts).
    fn group_by_key<'b>(&self, table: &[&'b Act], key: &str) -> Vec<(Value, Vec<&'b Act>)> {
        let mut out: BTreeMap<Vec<u8>, (Value, Vec<&Act>)> = BTreeMap::new();
        for a in table {
            if let Some(k) = self.field(a, key) {
                out.entry(k.render().into_bytes())
                    .or_insert_with(|| (k.clone(), Vec::new()))
                    .1
                    .push(a);
            }
        }
        out.into_values().collect()
    }

    /// `distinct T k`.
    fn distinct(&self, table: &[&Act], key: &str) -> Value {
        Value::Set(sorted_distinct(
            table.iter().filter_map(|a| self.field(a, key)).collect(),
        ))
    }

    /// `sum T k` over integer fields.
    fn sum(&self, table: &[&Act], key: &str) -> i128 {
        table
            .iter()
            .filter_map(|a| self.field(a, key))
            .filter_map(|v| v.as_int())
            .sum()
    }

    /// One rule, by the sugar table of R.2.
    /// Select only canonical HLC candidates. Ties are signer, then address.
    /// Low-level fold stays total; receipt/intent enforce clock shape separately.
    fn pick_lww(&self, acts: &[&Act], key: &str, clock: &str) -> Value {
        acts.iter()
            .filter_map(|a| {
                let SExpr::Atom(Atom::Str(text)) = a.fields.get(clock)? else {
                    return None;
                };
                let timestamp = crate::hlc::Hlc::parse(text)?;
                Some(((timestamp, a.signer.as_str(), a.address.as_str()), *a))
            })
            .max_by(|(x, _), (y, _)| x.cmp(y))
            .map(|(_, a)| self.field(a, key).unwrap_or(Value::Absent))
            .unwrap_or(Value::Absent)
    }

    fn eval(
        &self,
        rule: &Rule,
        done: &[(String, Value)],
        protocol: Option<&CausalProtocol>,
    ) -> Value {
        match rule {
            Rule::Context { path, definition } => definition
                .as_ref()
                .map(|d| {
                    d.read(
                        path,
                        &self.acts.iter().map(|a| (*a).clone()).collect::<Vec<_>>(),
                    )
                })
                .unwrap_or(Value::Absent),
            Rule::Lift(lift) => lift.evaluate(self.acts(&lift.verb)),
            Rule::BoundedCounter(c) => crate::escrow::observe(
                c,
                &self.acts.iter().map(|a| (*a).clone()).collect::<Vec<_>>(),
            )
            .value(),
            Rule::LwwRegister { verb, key, clock } => self.pick_lww(&self.acts(verb), key, clock),
            Rule::LwwPerSigner { verb, key, clock } => Value::Map(
                self.group_by_signer(&self.current_by_signer(verb))
                    .into_iter()
                    .map(|(s, t)| (Value::Str(s), self.pick_lww(&t, key, clock)))
                    .collect(),
            ),
            Rule::LwwMap {
                verb,
                key,
                value,
                clock,
                delete,
            } => Value::Map(
                self.group_by_key(&self.current(verb, Some(key), delete.as_deref()), key)
                    .into_iter()
                    .map(|(k, t)| (k, self.pick_lww(&t, value, clock)))
                    .collect(),
            ),
            Rule::Initial { verb, key } => self.initial(
                &self
                    .acts
                    .iter()
                    .copied()
                    .filter(|a| a.verb == *verb)
                    .collect::<Vec<_>>(),
                key,
            ),

            Rule::Exists { verb } => Value::Bool(!self.acts(verb).is_empty()),
            Rule::Count { verb } => Value::Int(self.acts(verb).len() as i128),
            Rule::Progress { verb } => {
                let positions = protocol
                    .map(|p| crate::repeat::accepted_positions(p, verb, &self.acts))
                    .unwrap_or_default();
                Value::Int(positions.into_iter().max().unwrap_or(0) as i128)
            }
            Rule::Events { verb, key } => {
                let mut entries: Vec<(Value, Value)> = self
                    .acts(verb)
                    .into_iter()
                    .filter_map(|a| {
                        self.field(a, key).map(|v| {
                            (
                                Value::Str(a.address.clone()),
                                Value::Pair {
                                    by: a.signer.clone(),
                                    value: alloc::boxed::Box::new(v),
                                },
                            )
                        })
                    })
                    .collect();
                entries.sort_by(|a, b| a.0.render().as_bytes().cmp(b.0.render().as_bytes()));
                Value::Map(entries)
            }
            Rule::SetUnion { verb, key } => self.distinct(&self.acts(verb), key),
            Rule::Values { verb, key } => self.distinct(&self.current(verb, None, None), key),
            Rule::ValuesPerKey {
                verb,
                key,
                value,
                delete,
            } => Value::Map(
                self.group_by_key(&self.current(verb, Some(key), delete.as_deref()), key)
                    .into_iter()
                    .map(|(k, t)| (k, self.distinct(&t, value)))
                    .collect(),
            ),

            Rule::ObservedSet { add, remove, key } => {
                self.distinct(&self.current(add, Some(key), Some(remove)), key)
            }
            Rule::Counter { inc, dec, key } => {
                Value::Int(self.sum(&self.acts(inc), key) - self.sum(&self.acts(dec), key))
            }
            Rule::Histogram { field } => {
                let mut counts: BTreeMap<Vec<u8>, (Value, i128)> = BTreeMap::new();
                if let Some((_, Value::Map(entries))) = done.iter().find(|(n, _)| n == field) {
                    for (_, v) in entries {
                        let v = match v {
                            Value::Pair { value, .. } => (**value).clone(),
                            other => other.clone(),
                        };
                        if v == Value::Absent {
                            continue;
                        }
                        counts
                            .entry(v.render().into_bytes())
                            .or_insert_with(|| (v.clone(), 0))
                            .1 += 1;
                    }
                }
                Value::Map(
                    counts
                        .into_values()
                        .map(|(v, n)| (v, Value::Int(n)))
                        .collect(),
                )
            }
            Rule::Sum { field } => {
                let total = match done.iter().find(|(n, _)| n == field) {
                    Some((_, Value::Map(entries))) => {
                        entries.iter().filter_map(|(_, v)| v.as_int()).sum()
                    }
                    _ => 0,
                };
                Value::Int(total)
            }
        }
    }
}

/// The fold (SPEC-019 R.2): every field of the clause over the accepted
/// acts, in clause order. Total on any finite slice; a set function of it.
pub fn fold(
    clause: &StateClause,
    protocol: Option<&CausalProtocol>,
    acts: &[Act],
) -> Vec<(String, Value)> {
    if clause.freezes().next().is_some() {
        return crate::freeze::fold(clause, protocol, acts);
    }
    fold_unfrozen(clause, protocol, acts)
}

pub(crate) fn fold_unfrozen(
    clause: &StateClause,
    protocol: Option<&CausalProtocol>,
    acts: &[Act],
) -> Vec<(String, Value)> {
    let mut done: Vec<(String, Value)> = Vec::new();
    let ctx = crate::lattice::Ctx::with_protocol(clause, acts, protocol);
    for entry in &clause.entries {
        match entry {
            Entry::Field { name, rule } => {
                let v = crate::lattice::factor(rule)
                    .map(|f| ctx.display(&f, &done))
                    .unwrap_or(Value::Absent);
                done.push((name.clone(), v));
            }
            Entry::Domain { .. } | Entry::Freeze { .. } | Entry::Lattice(_) => {}
            Entry::Threshold {
                name,
                field,
                elements,
            } => {
                let v = threshold_read(&ctx, clause, field, elements, &done);
                done.push((name.clone(), v));
            }
        }
    }
    done
}

/// Independent pre-factorization evaluator for legacy conformance checks.
/// New threshold/freeze declarations are exercised by their dedicated suites.
#[doc(hidden)]
pub fn fold_reference(
    clause: &StateClause,
    protocol: Option<&CausalProtocol>,
    acts: &[Act],
) -> Vec<(String, Value)> {
    let kernel = kernel_for(clause, acts);
    let ctx = crate::lattice::Ctx::with_protocol(clause, acts, protocol);
    let mut done: Vec<(String, Value)> = Vec::new();
    for entry in &clause.entries {
        match entry {
            Entry::Field { name, rule } => {
                let fault = ctx.rule_fault(rule).or_else(|| match rule {
                    Rule::Histogram { field } | Rule::Sum { field } => done
                        .iter()
                        .find(|(n, _)| n == field)
                        .filter(|(_, v)| v.fault_evidence().is_some())
                        .map(|(_, v)| v.clone()),
                    _ => None,
                });
                let value = fault.unwrap_or_else(|| match rule {
                    Rule::BoundedCounter(c) => crate::escrow::observe(c, acts).value(),
                    _ => kernel.eval(rule, &done, protocol),
                });
                done.push((name.clone(), value));
            }
            Entry::Threshold {
                name,
                field,
                elements,
            } => {
                let value = threshold_read(&ctx, clause, field, elements, &done);
                done.push((name.clone(), value));
            }
            _ => {}
        }
    }
    done
}

/// Evaluate one field in a causal scope. Dependency values are supplied in
/// clause order; the freeze evaluator memoizes these scoped evaluations.
pub(crate) fn scoped_rule(
    clause: &StateClause,
    protocol: Option<&CausalProtocol>,
    acts: &[Act],
    rule: &Rule,
    done: &[(String, Value)],
) -> Value {
    let ctx = crate::lattice::Ctx::with_protocol(clause, acts, protocol);
    crate::lattice::factor(rule)
        .map(|f| ctx.display(&f, done))
        .unwrap_or(Value::Absent)
}

/// Closure projections share the history carrier, retaining their existing
/// protocol-position and escrow validators as pure native algorithms.
pub(crate) fn closure_value(
    clause: &StateClause,
    protocol: Option<&CausalProtocol>,
    acts: &[Act],
    rule: &Rule,
) -> Value {
    match rule {
        Rule::Context { path, definition } => definition
            .as_ref()
            .map(|d| d.read(path, acts))
            .unwrap_or(Value::Absent),
        Rule::Progress { .. } => kernel_for(clause, acts).eval(rule, &[], protocol),
        Rule::BoundedCounter(c) => crate::escrow::observe(c, acts).value(),
        _ => Value::Absent,
    }
}

pub(crate) fn contribution_addresses(
    clause: &StateClause,
    acts: &[Act],
    verbs: &[String],
) -> hashbrown::HashSet<String> {
    // A field also depends on its domain's initializer or sealed roster root.
    // A freezer missing that support must fault/supersede it, rather than make
    // an already reached threshold pending when the domain disappears at cut.
    let mut support = hashbrown::HashSet::new();
    // Freeze witnesses must survive a later initializer fork. Retain every
    // contribution admitted by any observed initializer, rather than applying
    // the now-faulting domain's empty successful display.
    let domains: Vec<(&str, &str, hashbrown::HashSet<String>)> = clause
        .domains()
        .filter(|(verb, _, _)| verbs.iter().any(|v| v == verb))
        .map(|(verb, key, field)| {
            let mut allowed = hashbrown::HashSet::new();
            if let Some(Rule::Initial {
                verb: opener,
                key: source,
            }) = clause.rule_of(field)
            {
                for act in acts.iter().filter(|a| a.verb == *opener) {
                    support.insert(act.address.clone());
                    if let Some(SExpr::List(values)) = act.fields.get(source) {
                        allowed.extend(values.iter().map(|v| Value::from_sexpr(v).render()));
                    }
                }
            }
            if let Some(Rule::Context {
                path,
                definition: Some(metadata),
            }) = clause.rule_of(field)
            {
                for root in acts.iter().filter(|a| a.predecessors.is_empty()) {
                    support.insert(root.address.clone());
                    if let Value::Set(members) = metadata.read(path, core::slice::from_ref(root)) {
                        allowed.extend(members.iter().map(Value::render));
                    }
                }
            }
            (verb, key, allowed)
        })
        .collect();
    let writers: hashbrown::HashSet<String> = acts
        .iter()
        .filter(|a| verbs.contains(&a.verb))
        .filter(|a| {
            domains.iter().all(|(verb, key, allowed)| {
                a.verb != *verb
                    || a.fields
                        .get(*key)
                        .is_some_and(|v| allowed.contains(&Value::from_sexpr(v).render()))
            })
        })
        .map(|a| a.address.clone())
        .collect();
    support.extend(writers);
    support
}

/// A threshold read (SPEC-038 REQ-3802, CON-3801): the unique element of the
/// declared set at or below the field's carrier element, or `pending`.
/// Uniqueness is what installation's pairwise-incompatibility check buys, so
/// the first reached element is the only one. A lift's carrier element is
/// evaluated by the lattice context; a closure head's position or ⊤ is read
/// from its display (REQ-3808).
pub(crate) fn threshold_read(
    ctx: &crate::lattice::Ctx<'_>,
    clause: &StateClause,
    field: &str,
    elements: &[crate::lattice::Element],
    done: &[(String, Value)],
) -> Value {
    if let Some((_, fault)) = done
        .iter()
        .find(|(n, v)| n == field && v.fault_evidence().is_some())
    {
        return fault.clone();
    }
    let reached = match clause.rule_of(field).map(crate::lattice::factor) {
        Some(Some(f)) if matches!(f.post, crate::lattice::Post::Closure(_)) => done
            .iter()
            .find(|(n, _)| n == field)
            .and_then(|(_, shown)| elements.iter().find(|e| e.le_display(shown.unfrozen()))),
        Some(Some(f)) => {
            let sigma = ctx.read_carrier(&f.term);
            elements.iter().find(|e| e.le_with_post(&sigma, &f.post))
        }
        Some(None) => done
            .iter()
            .find(|(n, _)| n == field)
            .and_then(|(_, shown)| elements.iter().find(|e| e.le_display(shown.unfrozen()))),
        None => None,
    };
    let status = |s: &str| {
        (
            Value::Str(String::from("status")),
            Value::Str(String::from(s)),
        )
    };
    match reached {
        Some(e) => Value::Map(alloc::vec![
            (Value::Str(String::from("element")), e.render()),
            status("reached"),
        ]),
        None => Value::Map(alloc::vec![status("pending")]),
    }
}

// ---------------------------------------------------------------------------
// State schema (R.7 `state_schema`)
// ---------------------------------------------------------------------------

/// Scalar types of state-bearing fields.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScalarType {
    Str,
    Hlc,
    Int,
    Bool,
    /// A list of scalars (a `list` shape type).
    List,
}

impl ScalarType {
    pub fn from_constraint(tc: &TypeConstraint) -> Option<ScalarType> {
        match tc {
            TypeConstraint::String => Some(ScalarType::Str),
            TypeConstraint::Hlc => Some(ScalarType::Hlc),
            TypeConstraint::Number | TypeConstraint::Nonnegative => Some(ScalarType::Int),
            TypeConstraint::Bool => Some(ScalarType::Bool),
            TypeConstraint::List => Some(ScalarType::List),
            TypeConstraint::Symbol | TypeConstraint::Keyword => None,
        }
    }

    pub fn as_str(&self) -> &'static str {
        match self {
            ScalarType::Str => "string",
            ScalarType::Hlc => "hlc",
            ScalarType::Int => "number",
            ScalarType::Bool => "bool",
            ScalarType::List => "list",
        }
    }
}

/// The type of a state field, derived from its rule and the shapes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StateType {
    Object(Vec<(String, StateType)>),
    /// Immutable installed metadata or a sealed thread-context projection.
    Context(alloc::boxed::Box<StateType>),
    /// A current observation. A declared freezer can later produce an exact cut.
    Snapshot {
        value: alloc::boxed::Box<StateType>,
        freeze: Option<(String, FreezePolicy)>,
    },
    BoundedCounter,
    /// A value that may be absent (`last`).
    OptScalar(ScalarType),
    Int,
    Bool,
    Set(ScalarType),
    /// A map from a key type to values.
    Map(ScalarType, alloc::boxed::Box<StateType>),
    /// `events`: address → `{by, value}`.
    Events(ScalarType),
    /// `histogram`: value → count.
    Histogram(ScalarType),
    /// The referenced field's type could not be derived.
    Unknown,
    /// A threshold read over `field` (SPEC-038 CON-3801).
    Threshold {
        field: String,
        elements: Vec<crate::lattice::Element>,
    },
}

impl StateType {
    /// JSON rendering of a type, for the export.
    pub fn render(&self) -> String {
        match self {
            StateType::Object(fields) => format!(
                "{{\"type\":\"object\",\"fields\":{}}}",
                render_schema(fields)
            ),
            StateType::Context(value) => {
                let mut out = value.render();
                out.pop();
                out.push_str(",\"observation\":\"context\"}");
                out
            }
            StateType::Snapshot { value, freeze } => {
                let mut out = value.render();
                out.pop();
                out.push_str(",\"observation\":\"snapshot\"");
                if let Some((verb, policy)) = freeze {
                    out.push_str(",\"freeze\":{\"verb\":");
                    json_string(verb, &mut out);
                    out.push_str(",\"policy\":");
                    json_string(policy.as_str(), &mut out);
                    out.push('}');
                }
                out.push('}');
                out
            }
            StateType::Threshold { field, elements } => {
                let mut out = String::from("{\"type\":\"threshold\",\"field\":");
                json_string(field, &mut out);
                out.push_str(",\"elements\":[");
                for (i, e) in elements.iter().enumerate() {
                    if i > 0 {
                        out.push(',');
                    }
                    out.push_str(&e.render().render());
                }
                out.push_str("]}");
                out
            }
            StateType::BoundedCounter => String::from("{\"type\":\"bounded-counter\"}"),
            StateType::OptScalar(t) => {
                format!("{{\"type\":\"opt-scalar\",\"of\":\"{}\"}}", t.as_str())
            }
            StateType::Int => String::from("{\"type\":\"int\"}"),
            StateType::Bool => String::from("{\"type\":\"bool\"}"),
            StateType::Set(t) => format!("{{\"type\":\"set\",\"of\":\"{}\"}}", t.as_str()),
            StateType::Map(k, v) => {
                format!(
                    "{{\"type\":\"map\",\"key\":\"{}\",\"value\":{}}}",
                    k.as_str(),
                    v.render()
                )
            }
            StateType::Events(t) => format!("{{\"type\":\"events\",\"of\":\"{}\"}}", t.as_str()),
            StateType::Histogram(t) => {
                format!("{{\"type\":\"histogram\",\"of\":\"{}\"}}", t.as_str())
            }
            StateType::Unknown => String::from("{\"type\":\"unknown\"}"),
        }
    }
}

/// The declared type of `(verb, key)` from the dialect's shapes.
pub fn field_type(
    shapes: &[crate::shape::ShapeConstraint],
    verb: &str,
    key: &str,
) -> Option<TypeConstraint> {
    for shape in shapes.iter().filter(|s| s.performative == verb) {
        for rule in &shape.rules {
            match rule {
                ShapeRule::Require {
                    keyword,
                    type_constraint,
                    ..
                }
                | ShapeRule::Optional {
                    keyword,
                    type_constraint,
                    ..
                } => {
                    if keyword == key {
                        return *type_constraint;
                    }
                }
                ShapeRule::MaxDepth(_) => {}
            }
        }
    }
    None
}

/// `state_schema` (R.7): each field's type from its rule and the shapes.
pub fn state_schema(
    clause: &StateClause,
    shapes: &[crate::shape::ShapeConstraint],
) -> Vec<(String, StateType)> {
    let scalar = |verb: &str, key: &str| -> ScalarType {
        field_type(shapes, verb, key)
            .as_ref()
            .and_then(ScalarType::from_constraint)
            .unwrap_or(ScalarType::Str)
    };
    let mut out: Vec<(String, StateType)> = Vec::new();
    for entry in &clause.entries {
        let (name, rule) = match entry {
            Entry::Field { name, rule } => (name, rule),
            Entry::Domain { .. } | Entry::Freeze { .. } | Entry::Lattice(_) => continue,
            Entry::Threshold {
                name,
                field,
                elements,
            } => {
                out.push((
                    name.clone(),
                    StateType::Threshold {
                        field: field.clone(),
                        elements: elements.clone(),
                    },
                ));
                continue;
            }
        };
        let ty = match rule {
            Rule::Context { path, .. } => crate::context::schema(path),
            Rule::Lift(lift) => match &lift.projection {
                None => StateType::OptScalar(ScalarType::Str),
                Some(p)
                    if p.rows
                        .iter()
                        .all(|(_, v)| matches!(v, SExpr::Atom(Atom::Bool(_)))) =>
                {
                    StateType::Bool
                }
                Some(p)
                    if p.rows
                        .iter()
                        .all(|(_, v)| matches!(v, SExpr::Atom(Atom::Num(_)))) =>
                {
                    StateType::Int
                }
                Some(p)
                    if p.rows
                        .iter()
                        .all(|(_, v)| matches!(v, SExpr::Atom(Atom::Str(_)))) =>
                {
                    StateType::OptScalar(ScalarType::Str)
                }
                Some(_) => StateType::Unknown,
            },
            Rule::BoundedCounter(_) => StateType::BoundedCounter,
            Rule::Initial { verb, key } | Rule::LwwRegister { verb, key, .. } => {
                StateType::OptScalar(scalar(verb, key))
            }
            Rule::LwwPerSigner { verb, key, .. } => StateType::Map(
                ScalarType::Str,
                alloc::boxed::Box::new(StateType::OptScalar(scalar(verb, key))),
            ),
            Rule::LwwMap {
                verb, key, value, ..
            } => StateType::Map(
                scalar(verb, key),
                alloc::boxed::Box::new(StateType::OptScalar(scalar(verb, value))),
            ),
            Rule::Exists { .. } => StateType::Bool,
            Rule::Count { .. }
            | Rule::Progress { .. }
            | Rule::Counter { .. }
            | Rule::Sum { .. } => StateType::Int,
            Rule::Events { verb, key } => StateType::Events(scalar(verb, key)),
            Rule::SetUnion { verb, key } | Rule::Values { verb, key } => {
                StateType::Set(scalar(verb, key))
            }
            Rule::ValuesPerKey {
                verb, key, value, ..
            } => StateType::Map(
                scalar(verb, key),
                alloc::boxed::Box::new(StateType::Set(scalar(verb, value))),
            ),
            Rule::ObservedSet { add, key, .. } => StateType::Set(scalar(add, key)),
            Rule::Histogram { field } => {
                let of = out.iter().find(|(n, _)| n == field).map(|(_, t)| t.clone());
                match of {
                    Some(StateType::Map(_, v)) => match *v {
                        StateType::OptScalar(t) => StateType::Histogram(t),
                        _ => StateType::Unknown,
                    },
                    _ => StateType::Unknown,
                }
            }
        };
        out.push((String::from(name), ty));
    }
    out.into_iter()
        .map(|(name, ty)| {
            if matches!(ty, StateType::Threshold { .. }) {
                (name, ty)
            } else if matches!(clause.rule_of(&name),Some(Rule::Context {path,..}) if crate::context::stable_path(path)) {
                (name,StateType::Context(alloc::boxed::Box::new(ty)))
            } else {
                let freeze = clause
                    .freezes()
                    .find(|(field, _, _)| *field == name)
                    .map(|(_, verb, policy)| (verb.to_string(), policy));
                (
                    name,
                    StateType::Snapshot {
                        value: alloc::boxed::Box::new(ty),
                        freeze,
                    },
                )
            }
        })
        .collect()
}

/// JSON rendering of a schema.
pub fn render_schema(schema: &[(String, StateType)]) -> String {
    let mut out = String::from("{");
    for (i, (name, ty)) in schema.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        json_string(name, &mut out);
        out.push(':');
        out.push_str(&ty.render());
    }
    out.push('}');
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::message::{Performative, Recipients};

    fn act(addr: &str, verb: &str, signer: &str, preds: &[&str], fields: &[(&str, SExpr)]) -> Act {
        let mut params = Vec::new();
        for (k, v) in fields {
            params.push(SExpr::Atom(Atom::Keyword(String::from(*k))));
            params.push(v.clone());
        }
        params.push(SExpr::Atom(Atom::Keyword("clock".into())));
        params.push(SExpr::Atom(Atom::Str(
            "hlc-0000000000000000-00000000".into(),
        )));
        let message = Message::Simple {
            performative: Performative::Custom(String::from(verb)),
            recipient: Some(Recipients::One(String::from("@list"))),
            content: SExpr::List(Vec::new()),
            params,
            thread: Some(String::from("t")),
            sender: None,
            caused_by: Some(if preds.is_empty() {
                CausedBy::Begin
            } else {
                CausedBy::Single(String::from(preds[0]))
            }),
        };
        let mut a = Act::from_message(message, signer).unwrap();
        a.address = String::from(addr);
        a
    }

    fn s(x: &str) -> SExpr {
        SExpr::Atom(Atom::Str(String::from(x)))
    }
    fn b(x: bool) -> SExpr {
        SExpr::Atom(Atom::Bool(x))
    }
    fn addrs(xs: &[&str]) -> SExpr {
        SExpr::List(
            xs.iter()
                .map(|x| SExpr::Atom(Atom::Symbol(String::from(*x))))
                .collect(),
        )
    }

    fn checklist() -> StateClause {
        StateClause {
            entries: alloc::vec![
                Entry::Field {
                    name: "title".into(),
                    rule: Rule::Initial {
                        verb: "open".into(),
                        key: "title".into()
                    }
                },
                Entry::Field {
                    name: "items".into(),
                    rule: Rule::LwwMap {
                        verb: "check".into(),
                        key: "item".into(),
                        value: "done".into(),
                        delete: Some("drop".into()),
                        clock: "clock".into(),
                    },
                },
            ],
        }
    }

    #[test]
    fn register_replaced_never_wins_and_delete_removes_key() {
        let m1 = act("sha256:1", "open", "@aria", &[], &[("title", s("Launch"))]);
        let m2 = act(
            "sha256:2",
            "check",
            "@bo",
            &["sha256:1"],
            &[
                ("item", s("venue")),
                ("done", b(false)),
                ("replaces", addrs(&[])),
            ],
        );
        let m3 = act(
            "sha256:3",
            "check",
            "@bo",
            &["sha256:1"],
            &[
                ("item", s("venue")),
                ("done", b(true)),
                ("replaces", addrs(&["sha256:2"])),
            ],
        );
        let m4 = act(
            "sha256:4",
            "drop",
            "@aria",
            &["sha256:1"],
            &[("item", s("venue")), ("replaces", addrs(&["sha256:3"]))],
        );
        let clause = checklist();
        let st = fold(&clause, None, &[m1.clone(), m2.clone(), m3.clone()]);
        assert_eq!(
            render_json(&st),
            "{\"title\":\"Launch\",\"items\":{\"venue\":true}}"
        );
        let st = fold(
            &clause,
            None,
            &[m1.clone(), m2.clone(), m3.clone(), m4.clone()],
        );
        assert_eq!(render_json(&st), "{\"title\":\"Launch\",\"items\":{}}");
        // permutation and duplication invariance
        let st2 = fold(
            &clause,
            None,
            &[m4.clone(), m3.clone(), m1.clone(), m2.clone(), m3.clone()],
        );
        assert_eq!(render_json(&st2), "{\"title\":\"Launch\",\"items\":{}}");
        // M2 missing: identical
        let st3 = fold(&clause, None, &[m1, m3, m4]);
        assert_eq!(render_json(&st3), "{\"title\":\"Launch\",\"items\":{}}");
    }

    #[test]
    fn frontier_and_opener() {
        let m1 = act("sha256:1", "open", "@aria", &[], &[("title", s("Launch"))]);
        let m2 = act(
            "sha256:2",
            "check",
            "@bo",
            &["sha256:1"],
            &[("item", s("venue")), ("done", b(false))],
        );
        assert_eq!(
            frontier(&[m1.clone(), m2.clone()]),
            alloc::vec![String::from("sha256:2")]
        );
        assert_eq!(
            frontier(core::slice::from_ref(&m1)),
            alloc::vec![String::from("sha256:1")]
        );
    }

    #[test]
    fn histogram_over_per_signer_and_domain_filter() {
        let clause = StateClause {
            entries: alloc::vec![
                Entry::Field {
                    name: "options".into(),
                    rule: Rule::Initial {
                        verb: "propose".into(),
                        key: "options".into()
                    }
                },
                Entry::Domain {
                    verb: "vote".into(),
                    key: "choice".into(),
                    field: "options".into()
                },
                Entry::Field {
                    name: "ballots".into(),
                    rule: Rule::LwwPerSigner {
                        verb: "vote".into(),
                        key: "choice".into(),
                        clock: "clock".into(),
                    }
                },
                Entry::Field {
                    name: "tally".into(),
                    rule: Rule::Histogram {
                        field: "ballots".into()
                    }
                },
            ],
        };
        let p = act(
            "sha256:1",
            "propose",
            "@aria",
            &[],
            &[("options", SExpr::List(alloc::vec![s("Pizza"), s("Sushi")]))],
        );
        let v1 = act(
            "sha256:2",
            "vote",
            "@bo",
            &["sha256:1"],
            &[("choice", s("Pizza"))],
        );
        let v2 = act(
            "sha256:3",
            "vote",
            "@bo",
            &["sha256:1"],
            &[("choice", s("Sushi"))],
        ); // greater address wins
        let v3 = act(
            "sha256:4",
            "vote",
            "@cy",
            &["sha256:1"],
            &[("choice", s("Tacos"))],
        ); // out of domain
        let st = fold(&clause, None, &[p, v1, v2, v3]);
        assert_eq!(
            render_json(&st),
            "{\"options\":[\"Pizza\",\"Sushi\"],\"ballots\":{\"@bo\":\"Sushi\"},\"tally\":{\"Sushi\":1}}"
        );
    }

    #[test]
    fn json_escaping_is_minimal_and_lowercase() {
        let mut out = String::new();
        json_string("a\"b\\c\n\u{1}", &mut out);
        assert_eq!(out, "\"a\\\"b\\\\c\\n\\u0001\"");
    }
}

#[cfg(test)]
mod act_identity_tests {
    use super::*;
    use crate::message::{Performative, Recipients, WrapperType};
    use proptest::prelude::*;

    fn reference(act: &Act) -> Result<(), String> {
        if Act::from_message(act.message.clone(), &act.signer)? == *act {
            Ok(())
        } else {
            Err("inconsistent act identity".into())
        }
    }
    fn expr() -> impl Strategy<Value = SExpr> {
        prop_oneof![
            any::<i64>().prop_map(|n| SExpr::Atom(Atom::Num(n))),
            any::<bool>().prop_map(|v| SExpr::Atom(Atom::Bool(v))),
            ".{0,16}".prop_map(|s| SExpr::Atom(Atom::Symbol(s))),
            ".{0,16}".prop_map(|s| SExpr::Atom(Atom::Keyword(s))),
            ".{0,16}".prop_map(|s| SExpr::Atom(Atom::Str(s))),
        ]
        .prop_recursive(3, 32, 4, |inner| {
            proptest::collection::vec(inner, 0..4).prop_map(SExpr::List)
        })
    }
    proptest! {
        #[test]
        fn borrowed_identity_matches_owned_reconstruction(
            content in expr(), params in proptest::collection::vec(expr(), 0..24),
            replacement in expr(), verb in ".{0,16}",
            recipients in proptest::collection::vec(".{0,12}", 0..5),
            predecessors in proptest::collection::vec(".{0,12}", 0..5),
            thread in proptest::option::of(".{0,12}"),
            sender in proptest::option::of(".{0,12}"),
            recipient_kind in 0usize..3, cause_kind in 0usize..4,
            wrapper in 0usize..3, tamper in 0usize..9,
        ) {
            let recipient = match recipient_kind {
                0 => None,
                1 => Some(Recipients::One(recipients.first().cloned().unwrap_or_default())),
                _ => Some(Recipients::Set(recipients.into_iter().collect())),
            };
            let caused_by = match cause_kind {
                0 => None, 1 => Some(CausedBy::Begin),
                2 => Some(CausedBy::Single(predecessors.first().cloned().unwrap_or_default())),
                _ => Some(CausedBy::Multiple(predecessors)),
            };
            let mut message = Message::Simple {
                performative: Performative::Custom(verb), recipient, content,
                params, thread, sender, caused_by,
            };
            if wrapper == 1 {
                message = Message::Dialect { dialect_name: "probe".into(), inner: alloc::boxed::Box::new(message) };
            } else if wrapper == 2 {
                message = Message::Wrapped { wrapper: WrapperType::Signed,
                    params: alloc::vec![SExpr::Atom(Atom::Symbol("@host".into()))],
                    content: alloc::boxed::Box::new(message) };
            }
            let mut act = Act::from_message(message, "@host").unwrap();
            match tamper {
                1 => act.address.push('x'),
                2 => act.verb.push('x'),
                // Signer is supplied by the host, not derived from the message.
                3 => act.signer.push('x'),
                4 => act.predecessors.push("extra".into()),
                5 => { act.recipients.insert("extra".into()); },
                6 => { act.fields.insert("injected".into(), replacement); },
                7 => act.message = Message::Meta { dialect_def: replacement },
                8 => { act.fields.clear(); },
                _ => (),
            }
            prop_assert_eq!(act.validate_identity(), reference(&act));
        }
    }
    #[test]
    fn borrowed_identity_preserves_keyword_scan_and_duplicate_semantics() {
        let kw = |s: &str| SExpr::Atom(Atom::Keyword(s.into()));
        let cases = [
            alloc::vec![],
            alloc::vec![kw("tail")],
            alloc::vec![
                SExpr::Atom(Atom::Num(7)),
                kw("x"),
                kw("y"),
                kw("x"),
                SExpr::Atom(Atom::Num(2)),
                kw("tail")
            ],
            alloc::vec![
                kw("from"),
                SExpr::Atom(Atom::Symbol("@sender".into())),
                kw("thread"),
                SExpr::Atom(Atom::Str("t".into()))
            ],
        ];
        for params in cases {
            let message = Message::Simple {
                performative: Performative::Core(crate::message::CorePerformative::Tell),
                recipient: None,
                content: SExpr::List(alloc::vec![]),
                params,
                thread: None,
                sender: None,
                caused_by: Some(CausedBy::Multiple(alloc::vec![
                    "z".into(),
                    "a".into(),
                    "z".into()
                ])),
            };
            let mut act = Act::from_message(message, "@host").unwrap();
            assert_eq!(act.validate_identity(), reference(&act));
            assert!(act.validate_identity().is_ok());
            act.fields
                .insert("forged".into(), SExpr::Atom(Atom::Bool(true)));
            assert_eq!(act.validate_identity(), reference(&act));
            assert!(act.validate_identity().is_err());
        }
    }
}
