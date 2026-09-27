//! State layer (SPEC-019 R.1–R.3): the `(state …)` clause, the kernel of two
//! selections and five reductions, the fold, the value model, and the
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
    Last {
        verb: String,
        key: String,
    },
    LatestPerSigner {
        verb: String,
        key: String,
    },
    LatestPerKey {
        verb: String,
        key: String,
        value: String,
    },
    Exists {
        verb: String,
    },
    Count {
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
    RegisterPerKey {
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
            Rule::Last { .. } => "last",
            Rule::LatestPerSigner { .. } => "latest-per-signer",
            Rule::LatestPerKey { .. } => "latest-per-key",
            Rule::Exists { .. } => "exists",
            Rule::Count { .. } => "count",
            Rule::Events { .. } => "events",
            Rule::SetUnion { .. } => "set-union",
            Rule::Values { .. } => "values",
            Rule::ValuesPerKey { .. } => "values-per-key",
            Rule::RegisterPerKey { .. } => "register-per-key",
            Rule::ObservedSet { .. } => "observed-set",
            Rule::Counter { .. } => "counter",
            Rule::Histogram { .. } => "histogram",
            Rule::Sum { .. } => "sum",
        }
    }

    /// Every performative this rule names.
    pub fn verbs(&self) -> Vec<&str> {
        match self {
            Rule::Last { verb, .. }
            | Rule::LatestPerSigner { verb, .. }
            | Rule::LatestPerKey { verb, .. }
            | Rule::Exists { verb }
            | Rule::Count { verb }
            | Rule::Events { verb, .. }
            | Rule::SetUnion { verb, .. }
            | Rule::Values { verb, .. } => alloc::vec![verb.as_str()],
            Rule::ValuesPerKey { verb, delete, .. } | Rule::RegisterPerKey { verb, delete, .. } => {
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

    /// Every `(verb, key)` pair this rule reads as data.
    pub fn data_fields(&self) -> Vec<(&str, &str)> {
        match self {
            Rule::Last { verb, key }
            | Rule::LatestPerSigner { verb, key }
            | Rule::Events { verb, key }
            | Rule::SetUnion { verb, key }
            | Rule::Values { verb, key } => alloc::vec![(verb.as_str(), key.as_str())],
            Rule::LatestPerKey { verb, key, value } => {
                alloc::vec![
                    (verb.as_str(), key.as_str()),
                    (verb.as_str(), value.as_str())
                ]
            }
            Rule::ValuesPerKey {
                verb,
                key,
                value,
                delete,
            }
            | Rule::RegisterPerKey {
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
            | Rule::Histogram { .. }
            | Rule::Sum { .. } => Vec::new(),
        }
    }

    /// The verbs whose shape must carry the reserved `:replaces` field:
    /// writers and delete verbs of registers, remove verbs of observed sets.
    pub fn replaces_verbs(&self) -> Vec<&str> {
        match self {
            Rule::Values { verb, .. } => alloc::vec![verb.as_str()],
            Rule::ValuesPerKey { verb, delete, .. } | Rule::RegisterPerKey { verb, delete, .. } => {
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

/// One entry of the clause: a field or a domain filter.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Entry {
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
}

/// The parsed `(state …)` clause (SPEC-019 R.1).
#[derive(Debug, Clone, PartialEq, Eq, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct StateClause {
    pub entries: Vec<Entry>,
}

impl StateClause {
    /// Field entries in clause order.
    pub fn fields(&self) -> impl Iterator<Item = (&str, &Rule)> {
        self.entries.iter().filter_map(|e| match e {
            Entry::Field { name, rule } => Some((name.as_str(), rule)),
            Entry::Domain { .. } => None,
        })
    }

    /// Domain entries in clause order.
    pub fn domains(&self) -> impl Iterator<Item = (&str, &str, &str)> {
        self.entries.iter().filter_map(|e| match e {
            Entry::Domain { verb, key, field } => {
                Some((verb.as_str(), key.as_str(), field.as_str()))
            }
            Entry::Field { .. } => None,
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
            found = Some(name.as_str());
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
    acts.iter()
        .filter(|a| a.verb == verb)
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

    fn as_int(&self) -> Option<i128> {
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
    acts: &'a [Act],
    /// Domain filters resolved against the opener: `(verb, key) → allowed`.
    domains: Vec<(String, String, Vec<Value>)>,
}

impl<'a> Kernel<'a> {
    fn field(&self, act: &Act, key: &str) -> Option<Value> {
        act.fields.get(key).map(Value::from_sexpr)
    }

    /// `acts v`: the accepted acts of a verb, minus those a domain excludes.
    fn acts(&self, verb: &str) -> Vec<&'a Act> {
        self.acts
            .iter()
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

    /// `pick T k`: the value of `k` on the greatest-address act.
    fn pick(&self, table: &[&Act], key: &str) -> Value {
        table
            .iter()
            .max_by(|a, b| a.address.as_bytes().cmp(b.address.as_bytes()))
            .and_then(|a| self.field(a, key))
            .unwrap_or(Value::Absent)
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
    fn eval(&self, rule: &Rule, done: &[(String, Value)]) -> Value {
        match rule {
            Rule::Last { verb, key } => self.pick(&self.acts(verb), key),
            Rule::LatestPerSigner { verb, key } => Value::Map(
                self.group_by_signer(&self.acts(verb))
                    .into_iter()
                    .map(|(s, t)| (Value::Str(s), self.pick(&t, key)))
                    .collect(),
            ),
            Rule::LatestPerKey { verb, key, value } => Value::Map(
                self.group_by_key(&self.acts(verb), key)
                    .into_iter()
                    .map(|(k, t)| (k, self.pick(&t, value)))
                    .collect(),
            ),
            Rule::Exists { verb } => Value::Bool(!self.acts(verb).is_empty()),
            Rule::Count { verb } => Value::Int(self.acts(verb).len() as i128),
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
            Rule::RegisterPerKey {
                verb,
                key,
                value,
                delete,
            } => Value::Map(
                self.group_by_key(&self.current(verb, Some(key), delete.as_deref()), key)
                    .into_iter()
                    .map(|(k, t)| (k, self.pick(&t, value)))
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
    // Domains read a list-valued field defined over the opener only, so
    // resolve them first with no domain in force.
    let bare = Kernel {
        acts,
        domains: Vec::new(),
    };
    let mut domains = Vec::new();
    for (verb, key, field) in clause.domains() {
        let allowed = match clause.rule_of(field) {
            Some(rule) => match bare.eval(rule, &[]) {
                Value::List(items) => items,
                Value::Set(items) => items,
                _ => Vec::new(),
            },
            None => Vec::new(),
        };
        domains.push((String::from(verb), String::from(key), allowed));
    }
    let _ = protocol;
    let kernel = Kernel { acts, domains };
    let mut done: Vec<(String, Value)> = Vec::new();
    for (name, rule) in clause.fields() {
        let v = kernel.eval(rule, &done);
        done.push((String::from(name), v));
    }
    done
}

// ---------------------------------------------------------------------------
// State schema (R.7 `state_schema`)
// ---------------------------------------------------------------------------

/// Scalar types of state-bearing fields.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScalarType {
    Str,
    Int,
    Bool,
    /// A list of scalars (a `list` shape type).
    List,
}

impl ScalarType {
    pub fn from_constraint(tc: &TypeConstraint) -> Option<ScalarType> {
        match tc {
            TypeConstraint::String => Some(ScalarType::Str),
            TypeConstraint::Number => Some(ScalarType::Int),
            TypeConstraint::Bool => Some(ScalarType::Bool),
            TypeConstraint::List => Some(ScalarType::List),
            TypeConstraint::Symbol | TypeConstraint::Keyword => None,
        }
    }

    pub fn as_str(&self) -> &'static str {
        match self {
            ScalarType::Str => "string",
            ScalarType::Int => "number",
            ScalarType::Bool => "bool",
            ScalarType::List => "list",
        }
    }
}

/// The type of a state field, derived from its rule and the shapes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StateType {
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
}

impl StateType {
    /// JSON rendering of a type, for the export.
    pub fn render(&self) -> String {
        match self {
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
    for (name, rule) in clause.fields() {
        let ty = match rule {
            Rule::Last { verb, key } => StateType::OptScalar(scalar(verb, key)),
            Rule::LatestPerSigner { verb, key } => StateType::Map(
                ScalarType::Str,
                alloc::boxed::Box::new(StateType::OptScalar(scalar(verb, key))),
            ),
            Rule::LatestPerKey { verb, key, value }
            | Rule::RegisterPerKey {
                verb, key, value, ..
            } => StateType::Map(
                scalar(verb, key),
                alloc::boxed::Box::new(StateType::OptScalar(scalar(verb, value))),
            ),
            Rule::Exists { .. } => StateType::Bool,
            Rule::Count { .. } | Rule::Counter { .. } | Rule::Sum { .. } => StateType::Int,
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
    out
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
                    rule: Rule::Last {
                        verb: "open".into(),
                        key: "title".into()
                    }
                },
                Entry::Field {
                    name: "items".into(),
                    rule: Rule::RegisterPerKey {
                        verb: "check".into(),
                        key: "item".into(),
                        value: "done".into(),
                        delete: Some("drop".into()),
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
                    rule: Rule::Last {
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
                    rule: Rule::LatestPerSigner {
                        verb: "vote".into(),
                        key: "choice".into()
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
