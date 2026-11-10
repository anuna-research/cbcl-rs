//! SPEC-019 CON-1907..1909: pure escrow verification over authenticated acts.
//! Protocol admission remains independent. A ready verdict is conditional on
//! nonforking account issuance; it does not prove absence of undisclosed forks.
#![forbid(unsafe_code)]
use crate::message::{Message, WrapperType};
use crate::sexpr::{Atom, SExpr};
use crate::state::{Act, Value};
use alloc::collections::{BTreeMap, BTreeSet};
use alloc::format;
use alloc::string::{String, ToString};
use alloc::vec::Vec;

pub const PREV: &str = "escrow-prev";
pub const DEPS: &str = "escrow-deps";
pub const NONCE: &str = "escrow-nonce";

/// The default preserves existing per-signer resource ownership.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Ownership {
    #[default]
    Account,
    Collective,
}

#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct CounterRule {
    #[cfg_attr(feature = "serde", serde(default))]
    pub ownership: Ownership,
    #[cfg_attr(feature = "serde", serde(default))]
    pub certification: crate::certification::Certification,
    pub floor: i64,
    pub ceiling: Option<i64>,
    pub initial_verb: String,
    pub initial_key: String,
    pub headroom_key: Option<String>,
    pub issuer: String,
    pub increment: (String, String),
    pub decrement: (String, String),
    pub transfer: Option<(String, String, String)>,
    pub transfer_headroom: Option<(String, String, String)>,
}
impl CounterRule {
    pub fn operation_verbs(&self) -> Vec<&str> {
        let mut out = alloc::vec![self.increment.0.as_str(), self.decrement.0.as_str()];
        if let Some(t) = &self.transfer {
            out.push(&t.0);
        }
        if let Some(t) = &self.transfer_headroom {
            out.push(&t.0);
        }
        out
    }
    pub fn verbs(&self) -> Vec<&str> {
        let mut v = self.operation_verbs();
        v.push(&self.initial_verb);
        v
    }
    pub fn data_fields(&self) -> Vec<(&str, &str)> {
        let mut v = alloc::vec![
            (self.initial_verb.as_str(), self.initial_key.as_str()),
            (&self.increment.0, &self.increment.1),
            (&self.decrement.0, &self.decrement.1)
        ];
        if let Some((verb, r, k)) = &self.transfer {
            v.push((verb, r));
            v.push((verb, k));
        }
        if let Some(k) = &self.headroom_key {
            v.push((&self.initial_verb, k));
        }
        if let Some((a, b, c)) = &self.transfer_headroom {
            v.push((a, b));
            v.push((a, c));
        }
        v
    }
    pub fn canonical_options(&self) -> Vec<SExpr> {
        let sym = |x: &str| SExpr::Atom(Atom::Symbol(x.into()));
        let key = |x: &str| SExpr::Atom(Atom::Keyword(x.into()));
        let mut v = alloc::vec![SExpr::List(alloc::vec![
            sym("floor"),
            SExpr::Atom(Atom::Num(self.floor))
        ])];
        if let Some(n) = self.ceiling {
            v.push(SExpr::List(alloc::vec![
                sym("ceiling"),
                SExpr::Atom(Atom::Num(n))
            ]));
        }
        if let Some(profile) = self.certification.canonical_option() {
            v.push(profile);
        }
        if self.ownership == Ownership::Collective {
            v.push(SExpr::List(alloc::vec![
                sym("ownership"),
                sym("collective")
            ]));
        }
        v.push(SExpr::List(alloc::vec![
            sym(if self.ownership == Ownership::Collective {
                "initial"
            } else {
                "initial-rights"
            }),
            sym(&self.initial_verb),
            key(&self.initial_key)
        ]));
        if let Some(k) = &self.headroom_key {
            v.push(SExpr::List(alloc::vec![
                sym("initial-headroom"),
                sym(&self.initial_verb),
                key(k)
            ]));
        }
        v.push(SExpr::List(alloc::vec![
            sym("issuers"),
            if self.issuer.is_empty() {
                SExpr::List(Vec::new())
            } else {
                sym(&self.issuer)
            }
        ]));
        for (name, (verb, k)) in [
            ("increment", &self.increment),
            ("decrement", &self.decrement),
        ] {
            v.push(SExpr::List(alloc::vec![sym(name), sym(verb), key(k)]));
        }
        if let Some((a, b, c)) = &self.transfer {
            v.push(SExpr::List(alloc::vec![
                sym("transfer"),
                sym(a),
                key(b),
                key(c)
            ]));
        }
        if let Some((a, b, c)) = &self.transfer_headroom {
            v.push(SExpr::List(alloc::vec![
                sym("transfer-headroom"),
                sym(a),
                key(b),
                key(c)
            ]));
        }
        v
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Snapshot {
    pub value: i128,
    pub rights: BTreeMap<String, i128>,
    pub headroom: Option<BTreeMap<String, i128>>,
    pub tips: BTreeMap<String, String>,
    pub opener: String,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Outcome {
    Ready(Snapshot),
    Pending(Vec<String>),
    Fault {
        reason: String,
        evidence: Vec<String>,
    },
}
impl Outcome {
    pub fn value(&self) -> Value {
        let text = |s: &str| Value::Str(s.into());
        let mut entries = BTreeMap::<String, Value>::new();
        match self {
            Self::Ready(s) => {
                entries.insert(String::from("status"), text("ready"));
                entries.insert(String::from("value"), Value::Int(s.value));
                let balances = |m: &BTreeMap<String, i128>| {
                    Value::Map(m.iter().map(|(k, v)| (text(k), Value::Int(*v))).collect())
                };
                entries.insert(String::from("rights"), balances(&s.rights));
                if let Some(h) = &s.headroom {
                    entries.insert(String::from("headroom"), balances(h));
                }
            }
            Self::Pending(xs) => {
                entries.insert(String::from("status"), text("pending"));
                entries.insert(
                    String::from("evidence"),
                    Value::List(xs.iter().map(|s| text(s)).collect()),
                );
            }
            Self::Fault { reason, evidence } => {
                entries.insert(String::from("status"), text("fault"));
                entries.insert(String::from("reason"), text(reason));
                entries.insert(
                    String::from("evidence"),
                    Value::List(evidence.iter().map(|s| text(s)).collect()),
                );
            }
        }
        Value::Map(
            entries
                .into_iter()
                .map(|(k, v)| (Value::Str(k), v))
                .collect(),
        )
    }
}
fn fault(reason: &str, evidence: Vec<String>) -> Outcome {
    Outcome::Fault {
        reason: reason.into(),
        evidence,
    }
}
fn text(x: &SExpr) -> Option<&str> {
    match x {
        SExpr::Atom(Atom::Symbol(s)) | SExpr::Atom(Atom::Str(s)) => Some(s),
        _ => None,
    }
}
fn number(x: &SExpr) -> Option<i64> {
    if let SExpr::Atom(Atom::Num(n)) = x {
        Some(*n)
    } else {
        None
    }
}
fn account(x: &SExpr) -> Option<&str> {
    text(x).filter(|s| s.starts_with('@') && s.len() > 1)
}
fn lang(msg: &Message) -> Option<&str> {
    match msg {
        Message::Dialect { dialect_name, .. } => Some(dialect_name),
        Message::Wrapped { content, .. } => lang(content),
        _ => None,
    }
}
fn cast(msg: &Message) -> Option<&[SExpr]> {
    match msg {
        Message::Wrapped {
            wrapper: WrapperType::WithRoles,
            params,
            ..
        } => match params.first()? {
            SExpr::List(xs) => Some(xs),
            _ => None,
        },
        Message::Wrapped { content, .. } | Message::Dialect { inner: content, .. } => cast(content),
        _ => None,
    }
}
/// Recognize allocation pairs before use, including exact account spelling.
pub fn allocations(x: &SExpr) -> Result<BTreeMap<String, i128>, String> {
    let SExpr::List(xs) = x else {
        return Err("allocations must be a list".into());
    };
    if xs.is_empty() {
        return Err("allocations must be nonempty".into());
    }
    let mut m = BTreeMap::new();
    for x in xs {
        let SExpr::List(pair) = x else {
            return Err("allocation must be (account natural)".into());
        };
        if pair.len() != 2 {
            return Err("allocation must be (account natural)".into());
        }
        let a = account(&pair[0]).ok_or("allocation account must start with @")?;
        let n = number(&pair[1])
            .filter(|n| *n >= 0)
            .ok_or("allocation amount must be a natural integer")?;
        if m.insert(a.into(), i128::from(n)).is_some() {
            return Err("duplicate allocation account".into());
        }
    }
    Ok(m)
}
/// Rule-relevant projection of an authenticated, identity-checked native act.
/// No Message or application content is retained. `identity` commits the original
/// canonical Simple identity for duplicate checks; signature bytes are absent.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(deny_unknown_fields))]
pub struct ResourceFact {
    pub address: String,
    pub verb: String,
    pub signer: String,
    pub predecessors: Vec<String>,
    pub fields: BTreeMap<String, SExpr>,
    pub language: Option<String>,
    pub thread: Option<String>,
    pub from: Option<SExpr>,
    pub bindings: Option<Vec<SExpr>>,
    pub identity: [u8; 32],
}

/// Check a complete incoming Act before discarding any of its payload.
pub fn project_resource_fact(c: &CounterRule, a: &Act) -> Result<Option<ResourceFact>, String> {
    let rebuilt = Act::from_message(a.message.clone(), &a.signer)?;
    if rebuilt != *a {
        return Err(String::from("inconsistent act identity"));
    }
    Ok(project_unchecked(c, a))
}
/// Native and state resource links now share one canonical multihash spelling.
pub fn resource_state_id(id: &str) -> String {
    id.into()
}
fn projected_link(x: &SExpr) -> SExpr {
    match x {
        SExpr::Atom(Atom::Str(s)) => SExpr::Atom(Atom::Str(resource_state_id(s))),
        SExpr::Atom(Atom::Symbol(s)) => SExpr::Atom(Atom::Symbol(resource_state_id(s))),
        _ => x.clone(),
    }
}
// Canonical native Simple identity, not a wire-AST representation tag. Native
// typed identity already equates One/singleton Set, None/empty Set, and core/
// custom performative aliases. Fact snapshots must not split on those aliases.
// observe() retains its separate raw-attempt conflict diagnostics; projection
// continuation is over the identity-consistent accepted store. A raw attempt
// list is a diagnostic input to observe(), not this accepted-store contract.
fn simple_identity(m: &Message) -> [u8; 32] {
    use sha2::{Digest, Sha256};
    Sha256::digest(crate::equivocation::message_content_hash(m).as_bytes()).into()
}
fn project_unchecked(c: &CounterRule, a: &Act) -> Option<ResourceFact> {
    let bindings = cast(&a.message);
    if !c.verbs().contains(&a.verb.as_str()) && bindings.is_none() {
        return None;
    }
    let identity = simple_identity(a.simple());
    let mut names: BTreeSet<&str> = c
        .data_fields()
        .into_iter()
        .filter(|(v, _)| *v == a.verb)
        .map(|(_, k)| k)
        .collect();
    names.extend([PREV, DEPS]);
    Some(ResourceFact {
        address: a.address.clone(),
        verb: a.verb.clone(),
        signer: a.signer.clone(),
        predecessors: a
            .predecessors
            .iter()
            .map(|id| resource_state_id(id))
            .collect(),
        fields: a
            .fields
            .iter()
            .filter(|(k, _)| names.contains(k.as_str()))
            .map(|(k, v)| {
                (
                    k.clone(),
                    if k == PREV {
                        projected_link(v)
                    } else if k == DEPS {
                        match v {
                            SExpr::List(xs) => SExpr::List(xs.iter().map(projected_link).collect()),
                            _ => v.clone(),
                        }
                    } else {
                        v.clone()
                    },
                )
            })
            .collect(),
        language: lang(&a.message).map(String::from),
        thread: a.simple().thread().map(String::from),
        from: raw_field(a.simple(), "from").cloned(),
        bindings: bindings.map(|xs| xs.to_vec()),
        identity,
    })
}

#[derive(Clone, Copy)]
enum Kind {
    Increment,
    Decrement,
    Transfer,
    Headroom,
}
struct Node<'a> {
    act: &'a ResourceFact,
    prev: String,
    deps: Vec<String>,
    kind: Kind,
    amount: i128,
    recipient: Option<String>,
}
fn operation<'a>(
    c: &CounterRule,
    a: &'a ResourceFact,
) -> Option<(Kind, &'a SExpr, Option<&'a SExpr>)> {
    let (kind, key, recipient) = if a.verb == c.increment.0 {
        (Kind::Increment, c.increment.1.as_str(), None)
    } else if a.verb == c.decrement.0 {
        (Kind::Decrement, c.decrement.1.as_str(), None)
    } else if let Some((_, r, k)) = c.transfer.as_ref().filter(|(v, _, _)| a.verb == *v) {
        (Kind::Transfer, k.as_str(), Some(r.as_str()))
    } else if let Some((v, r, k)) = &c.transfer_headroom {
        if &a.verb == v {
            (Kind::Headroom, k.as_str(), Some(r.as_str()))
        } else {
            return None;
        }
    } else {
        return None;
    };
    Some((
        kind,
        a.fields.get(key)?,
        recipient.and_then(|k| a.fields.get(k)),
    ))
}
fn add(m: &mut BTreeMap<String, i128>, owner: &str, n: i128) -> Result<(), String> {
    let v = m.get_mut(owner).ok_or("unknown account")?;
    *v = v.checked_add(n).ok_or("arithmetic overflow")?;
    Ok(())
}
fn apply(
    n: &Node,
    rights: &mut BTreeMap<String, i128>,
    headroom: &mut Option<BTreeMap<String, i128>>,
) -> Result<(), String> {
    let owner = &n.act.signer;
    let amount = n.amount;
    match n.kind {
        Kind::Increment => {
            if let Some(h) = headroom {
                add(h, owner, -amount)?;
            }
            add(rights, owner, amount)?;
        }
        Kind::Decrement => {
            add(rights, owner, -amount)?;
            if let Some(h) = headroom {
                add(h, owner, amount)?;
            }
        }
        Kind::Transfer => {
            add(rights, owner, -amount)?;
            add(
                rights,
                n.recipient.as_deref().ok_or("missing recipient")?,
                amount,
            )?;
        }
        Kind::Headroom => {
            let h = headroom
                .as_mut()
                .ok_or("headroom transfer requires ceiling")?;
            add(h, owner, -amount)?;
            add(
                h,
                n.recipient.as_deref().ok_or("missing recipient")?,
                amount,
            )?;
        }
    }
    Ok(())
}
fn total(m: &BTreeMap<String, i128>) -> Option<i128> {
    m.values().try_fold(0i128, |sum, n| sum.checked_add(*n))
}

#[derive(Clone, Default)]
struct Summary {
    sequence: usize,
    tips: BTreeMap<String, String>,
    credited: i128,
    debited: i128,
    sent_rights: BTreeMap<String, i128>,
    sent_headroom: BTreeMap<String, i128>,
}
impl Summary {
    fn record(&mut self, n: &Node) -> Result<(), String> {
        self.sequence = self.sequence.checked_add(1).ok_or("sequence overflow")?;
        match n.kind {
            Kind::Increment => {
                self.credited = self
                    .credited
                    .checked_add(n.amount)
                    .ok_or("arithmetic overflow")?
            }
            Kind::Decrement => {
                self.debited = self
                    .debited
                    .checked_add(n.amount)
                    .ok_or("arithmetic overflow")?
            }
            Kind::Transfer | Kind::Headroom => {
                let to = n.recipient.as_ref().ok_or("missing recipient")?;
                let map = if matches!(n.kind, Kind::Transfer) {
                    &mut self.sent_rights
                } else {
                    &mut self.sent_headroom
                };
                let entry = map.entry(to.clone()).or_default();
                *entry = entry.checked_add(n.amount).ok_or("arithmetic overflow")?;
            }
        }
        Ok(())
    }
}
fn local_budgets(
    owner: &str,
    initial: &BTreeMap<String, i128>,
    headroom: Option<&BTreeMap<String, i128>>,
    own: &Summary,
    tips: &BTreeMap<String, String>,
    summaries: &BTreeMap<String, Summary>,
) -> Result<(i128, Option<i128>), String> {
    let outgoing = total(&own.sent_rights).ok_or("arithmetic overflow")?;
    let mut rights = initial[owner]
        .checked_add(own.credited)
        .and_then(|v| v.checked_sub(own.debited))
        .and_then(|v| v.checked_sub(outgoing))
        .ok_or("arithmetic overflow")?;
    let mut space = if let Some(h) = headroom {
        let outgoing = total(&own.sent_headroom).ok_or("arithmetic overflow")?;
        Some(
            h[owner]
                .checked_add(own.debited)
                .and_then(|v| v.checked_sub(own.credited))
                .and_then(|v| v.checked_sub(outgoing))
                .ok_or("arithmetic overflow")?,
        )
    } else {
        None
    };
    for (other, tip) in tips {
        if other == owner {
            continue;
        }
        let summary = &summaries[tip];
        rights = rights
            .checked_add(*summary.sent_rights.get(owner).unwrap_or(&0))
            .ok_or("arithmetic overflow")?;
        if let Some(h) = space.as_mut() {
            *h = h
                .checked_add(*summary.sent_headroom.get(owner).unwrap_or(&0))
                .ok_or("arithmetic overflow")?;
        }
    }
    Ok((rights, space))
}

/// Observe the complete supplied accepted history. Invalid acts fault rather than
/// disappearing. Missing evidence returns pending; no partial balance is exposed.
/// Inputs must be authenticated and protocol accepted by the host.
pub fn observe(c: &CounterRule, acts: &[Act]) -> Outcome {
    if c.ownership == Ownership::Collective {
        return fault(
            "collective counter requires the certificate runtime",
            Vec::new(),
        );
    }
    if c.certification.is_quorum() {
        return fault("quorum-budget requires an explicit certificate runtime; legacy fold cannot prove finality", Vec::new());
    }
    let mut all: BTreeMap<&str, &Act> = BTreeMap::new();
    for a in acts {
        let rebuilt = match Act::from_message(a.message.clone(), &a.signer) {
            Ok(x) => x,
            Err(e) => return fault(&e, alloc::vec![a.address.clone()]),
        };
        if a.address != rebuilt.address
            || a.verb != rebuilt.verb
            || a.fields != rebuilt.fields
            || a.predecessors != rebuilt.predecessors
            || a.recipients != rebuilt.recipients
        {
            return fault("inconsistent act identity", alloc::vec![a.address.clone()]);
        }
        if let Some(prev) = all.insert(&a.address, a) {
            if prev.signer != a.signer
                || prev.simple() != a.simple()
                || lang(&prev.message) != lang(&a.message)
                || cast(&prev.message) != cast(&a.message)
            {
                return fault(
                    "conflicting authenticated identity",
                    alloc::vec![a.address.clone()],
                );
            }
        }
    }
    let facts: BTreeMap<String, ResourceFact> = all
        .values()
        .filter_map(|a| project_unchecked(c, a).map(|f| (f.address.clone(), f)))
        .collect();
    observe_facts(c, &facts, |id| all.contains_key(id))
}

/// Minimal observation inputs, not signed evidence or resource finality authority.
/// `present` denotes accepted identities, including non-resource dependencies.
/// Callers importing a certified projection must pin its rule and provenance.
pub fn observe_facts<F: Fn(&str) -> bool>(
    c: &CounterRule,
    all: &BTreeMap<String, ResourceFact>,
    present: F,
) -> Outcome {
    let mut outcome = observe_facts_inner(c, all, &present);
    // Unsupported profiles have a history-independent native fault. Preserve
    // that boundary (and compact checkpoint compatibility) across projections.
    if c.ownership == Ownership::Collective || c.certification.is_quorum() {
        return outcome;
    }
    if let Outcome::Fault { evidence, .. } = &mut outcome {
        // SPEC-038 REQ-3806: a later diagnosis must not erase an earlier
        // witness. Evidence is a contextual certificate, not a minimal blame
        // set: retain all accepted resource facts and accepted cited context.
        evidence.extend(all.keys().cloned());
        for fact in all.values() {
            evidence.extend(fact.predecessors.iter().filter(|id| present(id)).cloned());
            if let Some(id) = fact
                .fields
                .get(PREV)
                .and_then(text)
                .filter(|id| present(id))
            {
                evidence.push(id.to_string());
            }
            if let Some(SExpr::List(deps)) = fact.fields.get(DEPS) {
                evidence.extend(
                    deps.iter()
                        .filter_map(text)
                        .filter(|id| present(id))
                        .map(String::from),
                );
            }
        }
        crate::state::sort_addresses(evidence);
        evidence.dedup();
    }
    outcome
}

fn observe_facts_inner<F: Fn(&str) -> bool>(
    c: &CounterRule,
    all: &BTreeMap<String, ResourceFact>,
    present: F,
) -> Outcome {
    if c.ownership == Ownership::Collective {
        return fault(
            "collective counter requires the certificate runtime",
            Vec::new(),
        );
    }
    if c.certification.is_quorum() {
        return fault("quorum-budget requires an explicit certificate runtime; legacy fold cannot prove finality", Vec::new());
    }
    let openers: Vec<_> = all.values().filter(|a| a.verb == c.initial_verb).collect();
    if openers.is_empty() {
        return Outcome::Pending(Vec::new());
    }
    if openers.len() != 1 {
        return fault(
            "multiple resource openers",
            openers.iter().map(|a| a.address.clone()).collect(),
        );
    }
    let op = openers[0];
    if op.predecessors.len() != 1 {
        return fault(
            "resource opener needs a cast-bearing root",
            alloc::vec![op.address.clone()],
        );
    }
    let Some(root) = all.get(op.predecessors[0].as_str()) else {
        return if present(&op.predecessors[0]) {
            fault("missing authenticated cast", op.predecessors.clone())
        } else {
            Outcome::Pending(op.predecessors.clone())
        };
    };
    let Some(bindings) = root.bindings.as_deref() else {
        return fault(
            "missing authenticated cast",
            alloc::vec![root.address.clone()],
        );
    };
    let mut members = BTreeSet::new();
    let mut issuers = BTreeSet::new();
    for binding in bindings {
        let SExpr::List(xs) = binding else {
            return fault("malformed cast", alloc::vec![root.address.clone()]);
        };
        let Some(role) = xs.first().and_then(text) else {
            return fault("malformed cast role", alloc::vec![root.address.clone()]);
        };
        for key in &xs[1..] {
            let Some(key) = account(key) else {
                return fault("malformed cast account", alloc::vec![root.address.clone()]);
            };
            members.insert(key.to_string());
            if role == c.issuer {
                issuers.insert(key.to_string());
            }
        }
    }
    if !members.contains(&op.signer) {
        return fault(
            "resource opener signer is outside the cast",
            alloc::vec![op.address.clone()],
        );
    }
    let initial = match op
        .fields
        .get(&c.initial_key)
        .ok_or("missing initial allocations")
        .and_then(|x| allocations(x).map_err(|_| "invalid initial allocations"))
    {
        Ok(x) => x,
        Err(e) => return fault(e, alloc::vec![op.address.clone()]),
    };
    if initial.keys().any(|k| !members.contains(k))
        || issuers.iter().any(|k| !initial.contains_key(k))
    {
        return fault(
            "allocation accounts and issuer cast disagree",
            alloc::vec![op.address.clone()],
        );
    }
    let initial_headroom = if let Some(key) = &c.headroom_key {
        match op
            .fields
            .get(key)
            .ok_or("missing headroom allocations")
            .and_then(|x| allocations(x).map_err(|_| "invalid headroom allocations"))
        {
            Ok(h) if h.keys().eq(initial.keys()) => Some(h),
            _ => {
                return fault(
                    "headroom accounts must match allocations",
                    alloc::vec![op.address.clone()],
                )
            }
        }
    } else {
        None
    };
    let Some(initial_total) = total(&initial).and_then(|v| v.checked_add(i128::from(c.floor)))
    else {
        return fault("arithmetic overflow", alloc::vec![op.address.clone()]);
    };
    if let Some(ceiling) = c.ceiling {
        if ceiling < c.floor
            || initial_headroom
                .as_ref()
                .and_then(total)
                .and_then(|h| h.checked_add(initial_total))
                != Some(i128::from(ceiling))
        {
            return fault(
                "initial rights plus headroom must equal ceiling minus floor",
                alloc::vec![op.address.clone()],
            );
        }
    }
    let mut nodes: BTreeMap<String, Node> = BTreeMap::new();
    let mut children: BTreeMap<(String, String), String> = BTreeMap::new();
    for a in all
        .values()
        .filter(|a| c.operation_verbs().contains(&a.verb.as_str()))
    {
        if a.thread != op.thread || a.language != op.language || !initial.contains_key(&a.signer) {
            return fault(
                "foreign resource instance or account",
                alloc::vec![a.address.clone()],
            );
        }
        if a.from.as_ref().and_then(text) != Some(a.signer.as_str()) {
            return fault(
                "resource signer disagrees with :from",
                alloc::vec![a.address.clone()],
            );
        }
        let Some((kind, amount, recipient)) = operation(c, a) else {
            return fault(
                "malformed resource operation",
                alloc::vec![a.address.clone()],
            );
        };
        let Some(amount) = number(amount).filter(|n| *n > 0) else {
            return fault(
                "resource amount must be positive",
                alloc::vec![a.address.clone()],
            );
        };
        if matches!(kind, Kind::Increment) && !issuers.contains(&a.signer) {
            return fault("unauthorized increment", alloc::vec![a.address.clone()]);
        }
        let recipient = if matches!(kind, Kind::Transfer | Kind::Headroom) {
            match recipient.and_then(account) {
                Some(r) if initial.contains_key(r) && r != a.signer => Some(r.to_string()),
                _ => return fault("invalid resource recipient", alloc::vec![a.address.clone()]),
            }
        } else {
            None
        };
        let Some(prev) = a
            .fields
            .get(PREV)
            .and_then(text)
            .filter(|s| crate::r7::is_address(s))
        else {
            return fault(
                "missing escrow previous address",
                alloc::vec![a.address.clone()],
            );
        };
        let Some(SExpr::List(xs)) = a.fields.get(DEPS) else {
            return fault(
                "missing escrow dependencies",
                alloc::vec![a.address.clone()],
            );
        };
        let mut deps = Vec::new();
        let mut seen = BTreeSet::new();
        for x in xs {
            let Some(dep) = text(x).filter(|s| crate::r7::is_address(s) && *s != prev) else {
                return fault("invalid escrow dependency", alloc::vec![a.address.clone()]);
            };
            if !seen.insert(dep) {
                return fault(
                    "duplicate escrow dependency",
                    alloc::vec![a.address.clone()],
                );
            }
            deps.push(dep.to_string());
        }
        if let Some(other) = children.insert((a.signer.clone(), prev.into()), a.address.clone()) {
            let mut evidence = alloc::vec![other, a.address.clone()];
            evidence.sort();
            return fault("owner fork", evidence);
        }
        nodes.insert(
            a.address.clone(),
            Node {
                act: a,
                prev: prev.into(),
                deps,
                kind,
                amount: i128::from(amount),
                recipient,
            },
        );
    }
    let mut missing = BTreeSet::new();
    for n in nodes.values() {
        for dep in core::iter::once(&n.prev).chain(n.deps.iter()) {
            if dep == &op.address {
                continue;
            }
            if let Some(parent) = nodes.get(dep) {
                if dep == &n.prev && parent.act.signer != n.act.signer {
                    return fault(
                        "wrong owner previous link",
                        alloc::vec![n.act.address.clone(), dep.clone()],
                    );
                }
            } else if all.contains_key(dep.as_str()) || present(dep) {
                return fault(
                    "foreign resource dependency",
                    alloc::vec![n.act.address.clone(), dep.clone()],
                );
            } else {
                missing.insert(dep.clone());
            }
        }
    }
    // Validate every dependency-closed component before reporting missing
    // evidence elsewhere. Otherwise an unrelated pending account could hide
    // an already established budget fault (SPEC-038 REQ-3806).
    // Kahn traversal plus bounded account frontiers. Each summary stores only
    // the latest observed operation per account and that owner's cumulative
    // transfers. Installed profiles bound accounts and dependencies by max-list;
    // no quadratic ancestor sets or recursive traversal are required.
    let mut waiting: BTreeMap<String, Vec<String>> = BTreeMap::new();
    let mut remaining = BTreeMap::new();
    let mut ready = BTreeSet::new();
    for (address, n) in &nodes {
        let dependencies: BTreeSet<_> = core::iter::once(&n.prev)
            .chain(n.deps.iter())
            .filter(|d| *d != &op.address)
            .cloned()
            .collect();
        remaining.insert(address.clone(), dependencies.len());
        if dependencies.is_empty() {
            ready.insert(address.clone());
        }
        for parent in dependencies {
            waiting.entry(parent).or_default().push(address.clone());
        }
    }
    let mut summaries: BTreeMap<String, Summary> = BTreeMap::new();
    while let Some(address) = ready.pop_first() {
        let n = &nodes[&address];
        let own = if n.prev == op.address {
            Summary::default()
        } else {
            summaries[&n.prev].clone()
        };
        let mut tips = own.tips.clone();
        for dep in &n.deps {
            if dep == &op.address {
                continue;
            }
            for (owner, tip) in &summaries[dep].tips {
                if tips.get(owner).map_or(true, |old| {
                    summaries[old].sequence < summaries[tip].sequence
                }) {
                    tips.insert(owner.clone(), tip.clone());
                }
            }
        }
        let (rights_budget, headroom_budget) = match local_budgets(
            &n.act.signer,
            &initial,
            initial_headroom.as_ref(),
            &own,
            &tips,
            &summaries,
        ) {
            Ok(b) => b,
            Err(e) => return fault(&e, alloc::vec![address.clone()]),
        };
        let budget = if matches!(n.kind, Kind::Increment | Kind::Headroom) {
            headroom_budget
        } else {
            Some(rights_budget)
        };
        if budget.is_some_and(|b| b < n.amount) {
            return fault(
                if matches!(n.kind, Kind::Increment | Kind::Headroom) {
                    "insufficient headroom"
                } else {
                    "insufficient rights"
                },
                alloc::vec![address.clone()],
            );
        }
        let mut next = own;
        if let Err(e) = next.record(n) {
            return fault(&e, alloc::vec![address.clone()]);
        }
        next.tips = tips;
        next.tips.insert(n.act.signer.clone(), address.clone());
        summaries.insert(address.clone(), next);
        if let Some(children) = waiting.remove(&address) {
            for child in children {
                let count = remaining.get_mut(&child).expect("known dependent");
                *count -= 1;
                if *count == 0 {
                    ready.insert(child);
                }
            }
        }
    }
    if !missing.is_empty() {
        // Missing references block budget evaluation, but cannot hide an
        // independent cycle. Release their graph edges without inventing
        // resource summaries, then finish the structural Kahn traversal.
        for dependency in &missing {
            if let Some(children) = waiting.remove(dependency) {
                for child in children {
                    let count = remaining.get_mut(&child).expect("known dependent");
                    *count -= 1;
                    if *count == 0 {
                        ready.insert(child);
                    }
                }
            }
        }
        let mut reached = summaries.len();
        while let Some(address) = ready.pop_first() {
            reached += 1;
            if let Some(children) = waiting.remove(&address) {
                for child in children {
                    let count = remaining.get_mut(&child).expect("known dependent");
                    *count -= 1;
                    if *count == 0 {
                        ready.insert(child);
                    }
                }
            }
        }
        if reached != nodes.len() {
            return fault(
                "cyclic escrow dependencies",
                nodes.keys().cloned().collect(),
            );
        }
        return Outcome::Pending(missing.into_iter().collect());
    }
    if summaries.len() != nodes.len() {
        return fault(
            "cyclic escrow dependencies",
            nodes.keys().cloned().collect(),
        );
    }
    let mut rights = initial;
    let mut headroom = initial_headroom;
    for n in nodes.values() {
        if let Err(e) = apply(n, &mut rights, &mut headroom) {
            return fault(&e, alloc::vec![n.act.address.clone()]);
        }
    }
    if rights.values().any(|n| *n < 0)
        || headroom
            .as_ref()
            .is_some_and(|h| h.values().any(|n| *n < 0))
    {
        return fault("negative escrow budget", nodes.keys().cloned().collect());
    }
    let Some(value) = total(&rights).and_then(|v| v.checked_add(i128::from(c.floor))) else {
        return fault("arithmetic overflow", Vec::new());
    };
    if let Some(c) = c.ceiling {
        if headroom
            .as_ref()
            .and_then(total)
            .and_then(|h| value.checked_add(h))
            != Some(i128::from(c))
        {
            return fault("headroom conservation failure", Vec::new());
        }
    }
    let mut tips = BTreeMap::new();
    for n in nodes.values() {
        if !children.contains_key(&(n.act.signer.clone(), n.act.address.clone())) {
            tips.insert(n.act.signer.clone(), n.act.address.clone());
        }
    }
    Outcome::Ready(Snapshot {
        value,
        rights,
        headroom,
        tips,
        opener: op.address.clone(),
    })
}

/// Install-time validation, including collisions and role/shape references.
pub fn declaration_errors(d: &crate::dialect::Dialect) -> Vec<String> {
    use crate::shape::TypeConstraint as T;
    use crate::state::{opener_verb, Rule};
    let mut errors = Vec::new();
    let mut operation_owner = BTreeMap::new();
    let Some(clause) = &d.state else {
        return errors;
    };
    let reserved = |key: &str| {
        [PREV, DEPS, NONCE, crate::state::RESERVED_REPLACES].contains(&key)
            || crate::state::ROUTING_KEYWORDS.contains(&key)
    };
    for (name, rule) in clause.fields() {
        let Rule::BoundedCounter(c) = rule else {
            continue;
        };
        if let Err(error) = c.certification.validate() {
            errors.push(error);
        }
        if d.roles.is_empty() {
            errors.push("bounded counters require an authenticated role cast".into());
        }
        if d.causal_protocol.as_ref().and_then(opener_verb) != Some(c.initial_verb.as_str()) {
            errors.push(format!(
                "bounded-counter '{name}' must initialize from the unique opener"
            ));
        }
        if !c.issuer.is_empty() && !d.roles.iter().any(|r| r.name == c.issuer) {
            errors.push(format!(
                "unknown bounded-counter issuer role '{}'",
                c.issuer
            ));
        }
        let bounds = crate::r7::bounds_of(d);
        if c.floor.unsigned_abs() > bounds.max_number as u64
            || c.ceiling
                .is_some_and(|n| n < c.floor || n.unsigned_abs() > bounds.max_number as u64)
        {
            errors.push("counter bounds exceed numeric limits or ceiling is below floor".into());
        }
        if (c.ownership == Ownership::Account && c.ceiling.is_some() != c.headroom_key.is_some())
            || c.transfer_headroom.is_some() && c.ceiling.is_none()
        {
            errors.push(
                "ceiling requires initial-headroom; headroom transfers require ceiling".into(),
            );
        }
        if c.ownership == Ownership::Collective {
            if !c.certification.is_quorum()
                || c.headroom_key.is_some()
                || c.transfer.is_some()
                || c.transfer_headroom.is_some()
            {
                errors.push("collective counters require quorum-budget and scalar initialization without account transfers".into());
            }
            for verb in c.verbs() {
                if d.find_performative(verb)
                    .and_then(|p| p.role.as_ref())
                    .is_none()
                {
                    errors.push(format!(
                        "collective verb '{verb}' requires an explicit from role"
                    ));
                }
            }
        } else if c.transfer.is_none() {
            errors.push("account counters require a transfer mapping".into());
        }
        for verb in c.operation_verbs() {
            if verb == c.initial_verb || operation_owner.insert(verb, name).is_some() {
                errors.push(format!(
                    "operation '{verb}' must serve exactly one counter and operation kind"
                ));
            }
        }
        let mut expected = alloc::vec![
            (
                c.initial_verb.as_str(),
                c.initial_key.as_str(),
                alloc::vec![if c.ownership == Ownership::Collective {
                    T::Integer
                } else {
                    T::List
                }]
            ),
            (&c.increment.0, &c.increment.1, alloc::vec![T::Integer]),
            (&c.decrement.0, &c.decrement.1, alloc::vec![T::Integer])
        ];
        if let Some((v, r, k)) = &c.transfer {
            expected.push((v, r, alloc::vec![T::Symbol, T::String]));
            expected.push((v, k, alloc::vec![T::Integer]));
            if r == k {
                errors.push("counter data fields must be distinct".into());
            }
        }
        if c.headroom_key.as_ref() == Some(&c.initial_key) {
            errors.push("counter data fields must be distinct".into());
        }
        if let Some(k) = &c.headroom_key {
            expected.push((&c.initial_verb, k, alloc::vec![T::List]));
        }
        if let Some((v, r, k)) = &c.transfer_headroom {
            if r == k {
                errors.push("headroom recipient and amount fields must differ".into());
            }
            expected.push((v, r, alloc::vec![T::Symbol, T::String]));
            expected.push((v, k, alloc::vec![T::Integer]));
        }
        for (v, k, types) in expected {
            if reserved(k) {
                errors.push(format!("counter data may not read reserved :{k}"));
            }
            if !d.shapes.iter().filter(|shape|shape.performative==v).any(|shape|shape.rules.iter().any(|rule|matches!(rule,crate::shape::ShapeRule::Require{keyword,type_constraint:Some(t),..} if keyword==k&&t.representation().as_ref().is_some_and(|base|types.contains(base) || types.contains(&T::Integer) && *base == T::Nonnegative)))) {
                errors.push(format!(
                    "counter '{name}': '{v}' requires an appropriately typed :{k}"
                ));
            }
        }
        for (v, _, _) in clause.domains() {
            if c.verbs().contains(&v) {
                errors.push(format!("domain may not hide resource acts of '{v}'"));
            }
        }
    }
    // No ordinary state rule can interpret compiler-owned resource evidence.
    for (_, rule) in clause.fields() {
        for (_, k) in rule.data_fields() {
            if [PREV, DEPS, NONCE].contains(&k) {
                errors.push("state data may not read escrow bookkeeping".into());
            }
        }
    }
    for (_, k, _) in clause.domains() {
        if [PREV, DEPS, NONCE].contains(&k) {
            errors.push("domain may not read escrow bookkeeping".into());
        }
    }
    errors
}
/// The resource operation bound to a verb, if any (installation ensures unique).
pub fn rule_for<'a>(
    d: &'a crate::dialect::Dialect,
    verb: &str,
) -> Option<(&'a str, &'a CounterRule)> {
    d.state.as_ref()?.fields().find_map(|(name, r)| match r {
        crate::state::Rule::BoundedCounter(c) if c.operation_verbs().contains(&verb) => {
            Some((name, c.as_ref()))
        }
        _ => None,
    })
}
/// Shape typing exception: a resource recipient is an authenticated account key.
pub fn recipient_field(d: &crate::dialect::Dialect, verb: &str, key: &str) -> bool {
    rule_for(d, verb).is_some_and(|(_, c)| {
        c.transfer
            .as_ref()
            .is_some_and(|(v, r, _)| v == verb && r == key)
            || c.transfer_headroom
                .as_ref()
                .is_some_and(|(v, r, _)| v == verb && r == key)
    })
}
/// Resource candidate check. A faulted base cannot authorize any candidate.
pub fn check(c: &CounterRule, acts: &[Act], candidate: &Act) -> Outcome {
    match observe(c, acts) {
        Outcome::Ready(_) => {}
        other => return other,
    }
    let mut with = acts.to_vec();
    with.push(candidate.clone());
    observe(c, &with)
}
/// Pure candidate completion. Durable issuance is a separate required host gate.
pub fn bookkeeping(
    d: &crate::dialect::Dialect,
    acts: &[Act],
    thread: &str,
    signer: &str,
    verb: &str,
) -> Result<Vec<(String, SExpr)>, String> {
    let Some((_, c)) = rule_for(d, verb) else {
        return Ok(Vec::new());
    };
    let snapshot = match observe_in(d, thread, c, acts) {
        Outcome::Ready(s) => s,
        other => return Err(other.value().render()),
    };
    if !snapshot.rights.contains_key(signer) {
        return Err("signer is not a resource account".into());
    }
    let prev = snapshot
        .tips
        .get(signer)
        .unwrap_or(&snapshot.opener)
        .clone();
    let deps: BTreeSet<_> = snapshot
        .tips
        .iter()
        .filter(|(owner, _)| owner.as_str() != signer)
        .map(|(_, a)| a.clone())
        .collect();
    if deps.len() > crate::r7::bounds_of(d).max_list as usize {
        return Err("escrow dependency limit exceeded".into());
    }
    Ok(alloc::vec![
        (PREV.into(), SExpr::Atom(Atom::Symbol(prev))),
        (
            DEPS.into(),
            SExpr::List(
                deps.into_iter()
                    .map(|a| SExpr::Atom(Atom::Symbol(a)))
                    .collect()
            )
        )
    ])
}

/// Host capability required for durable issuance. All operation kinds share
/// the same (dialect, thread, opener, field, account) lane. Implementations must
/// atomically persist the FULL candidate against `expected_previous` and never
/// sign/publish a losing candidate. Recovery reuses the persisted candidate.
pub trait IssuanceGate {
    fn compare_and_append(
        &mut self,
        lane: &IssuanceLane,
        expected_previous: &str,
        candidate: &Act,
    ) -> Result<(), String>;
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IssuanceLane {
    pub dialect: String,
    pub thread: String,
    pub opener: String,
    pub field: String,
    pub account: String,
}
/// Complete and reserve one resource act before returning it for signing.
/// Authentication, protocol admission and idempotent effect delivery remain
/// host duties. This helper does not provide a default, non-durable gate.
pub fn issue<G: IssuanceGate>(
    inst: &crate::intend::Instance,
    signer: &crate::role::AgentKey,
    verb: &str,
    fields: BTreeMap<String, SExpr>,
    gate: &mut G,
) -> Result<Message, String> {
    let (field, c) = rule_for(inst.dialect, verb).ok_or("not a resource operation")?;
    if c.certification.is_quorum() {
        return Err("quorum-budget uses independent validator votes, not IssuanceGate".into());
    }
    let message = crate::intend::intend(inst, signer, verb, fields).map_err(|e| e.to_string())?;
    let candidate = Act::from_message(message.clone(), &signer.0)?;
    let Outcome::Ready(s) = observe_in(inst.dialect, &inst.thread.0, c, inst.acts) else {
        return Err("resource history is not ready".into());
    };
    let previous = candidate
        .fields
        .get(PREV)
        .and_then(text)
        .ok_or("missing escrow previous")?;
    let lane = IssuanceLane {
        dialect: crate::canonical::dialect_name(inst.dialect),
        thread: inst.thread.0.clone(),
        opener: s.opener,
        field: field.into(),
        account: signer.0.clone(),
    };
    gate.compare_and_append(&lane, previous, &candidate)?;
    Ok(message)
}

fn raw_field<'a>(msg: &'a Message, key: &str) -> Option<&'a SExpr> {
    let Message::Simple { params, .. } = msg else {
        return None;
    };
    params.windows(2).find_map(|xs| {
        if matches!(&xs[0],SExpr::Atom(Atom::Keyword(k)) if k==key) {
            Some(&xs[1])
        } else {
            None
        }
    })
}

/// Context-pinned observation for bindings and business authorization. The
/// lower-level `observe` is a mathematical observation under a caller-supplied
/// pinned-history premise; this entry checks that premise's structural portion.
pub fn observe_in(
    d: &crate::dialect::Dialect,
    thread: &str,
    c: &CounterRule,
    acts: &[Act],
) -> Outcome {
    for a in acts.iter().filter(|a| c.verbs().contains(&a.verb.as_str())) {
        if crate::r7::verify_state_shape(d, &a.message).is_err()
            || d.shapes
                .iter()
                .filter(|shape| shape.performative == a.verb)
                .any(|shape| shape.check(&SExpr::from(a.simple())).is_err())
        {
            return fault(
                "invalid resource message shape",
                alloc::vec![a.address.clone()],
            );
        }
        if let Message::Simple { params, .. } = a.simple() {
            let mut seen = BTreeSet::new();
            for pair in params.chunks(2) {
                if let Some(SExpr::Atom(Atom::Keyword(key))) = pair.first() {
                    if !seen.insert(key) {
                        return fault("duplicate resource keyword", alloc::vec![a.address.clone()]);
                    }
                }
            }
        }
        if a.simple().thread() != Some(thread) || lang(&a.message) != Some(d.name.as_str()) {
            return fault(
                "resource history context mismatch",
                alloc::vec![a.address.clone()],
            );
        }
    }
    // Validate the actual cast against installed role cardinalities, rather
    // than interpreting arbitrary binding lists as a valid cast.
    for opener in acts.iter().filter(|a| a.verb == c.initial_verb) {
        for root in acts.iter().filter(|a| {
            opener
                .predecessors
                .iter()
                .any(|id| resource_state_id(id) == a.address)
        }) {
            if root.verb != "hello"
                || root.simple().thread() != Some(thread)
                || !root.predecessors.is_empty()
                || crate::intend::cast_of(&root.message, d).is_err()
            {
                return fault(
                    "resource root context mismatch",
                    alloc::vec![root.address.clone()],
                );
            }
        }
    }
    observe(c, acts)
}

/// Context-pinned fold; existing pure `state::fold` retains its precondition
/// that the supplied accepted acts already belong to the chosen instance.
pub fn fold_instance(
    d: &crate::dialect::Dialect,
    thread: &str,
    acts: &[Act],
) -> Vec<(String, Value)> {
    let Some(clause) = &d.state else {
        return Vec::new();
    };
    let mut result = crate::state::fold(clause, d.causal_protocol.as_ref(), acts);
    for ((_, rule), (_, value)) in clause.fields().zip(result.iter_mut()) {
        if let crate::state::Rule::BoundedCounter(c) = rule {
            *value = observe_in(d, thread, c, acts).value();
        }
    }
    result
}
