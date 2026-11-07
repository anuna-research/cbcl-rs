//! Version-2 per-rule checkpoint summaries. Inputs must already be authenticated
//! and admitted. Coverage queries use wire (`sha256-`) identities at the pre-root.
//! Stored contributions are semantic projections, never Message/signature evidence.
//! Binary and serde recognition establish structure, not accepted-history authority.
use crate::{Error, Hash, Result};
use alloc::{
    boxed::Box,
    collections::{BTreeMap, BTreeSet},
    string::{String, ToString},
    vec,
    vec::Vec,
};
use cbcl_core::{
    canonical::{canonical_encode, to_signable_sexpr},
    dialect::base_dialect,
    hlc::Hlc,
    message::{Message, Performative},
    protocol::CausalProtocol,
    sexpr::{Atom, SExpr},
    state::{self, Act, Entry, Rule, StateClause, Value},
};
use serde::{Deserialize, Deserializer, Serialize};

// Test-only instrumentation counts maintenance work, never snapshot rendering.
#[cfg(all(test, feature = "std"))]
mod work {
    use core::cell::Cell;
    #[derive(Clone, Copy, Debug, Default)]
    pub(super) struct Counts {
        pub incoming_metadata: usize,
        pub live_comparisons: usize,
        pub pending_comparisons: usize,
        pub coverage_queries: usize,
    }
    std::thread_local! { static COUNTS: Cell<Counts> = Cell::new(Counts::default()); }
    pub(super) fn record(incoming: usize, live: usize, pending: usize, queries: usize) {
        COUNTS.with(|c| {
            let mut n = c.get();
            n.incoming_metadata += incoming;
            n.live_comparisons += live;
            n.pending_comparisons += pending;
            n.coverage_queries += queries;
            c.set(n);
        });
    }
    pub(super) fn take() -> Counts {
        COUNTS.with(|c| c.replace(Counts::default()))
    }
}
#[inline]
fn record_work(incoming: usize, live: usize, pending: usize, queries: usize) {
    #[cfg(all(test, feature = "std"))]
    work::record(incoming, live, pending, queries);
    #[cfg(not(all(test, feature = "std")))]
    let _ = (incoming, live, pending, queries);
}

/// Rule-read semantic data only; identity is certified by the surrounding cut.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Contribution {
    pub id: String,
    pub signer: String,
    pub key: Option<SExpr>,
    pub value: Option<SExpr>,
    pub clock: Option<String>,
}
/// Events necessarily grow with output; no full bodies or unrelated fields survive.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Event {
    pub id: String,
    pub signer: String,
    pub selected_value: SExpr,
}
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Pending {
    scope: Vec<u8>,
    target: String,
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ScopedRow {
    live: Vec<Contribution>,
    pending: BTreeSet<Pending>,
}
impl<'de> Deserialize<'de> for ScopedRow {
    fn deserialize<D: Deserializer<'de>>(d: D) -> core::result::Result<Self, D::Error> {
        #[derive(Deserialize)]
        #[serde(deny_unknown_fields)]
        struct Wire {
            live: Vec<Contribution>,
            pending: Vec<Pending>,
        }
        let w = Wire::deserialize(d)?;
        if w.pending.windows(2).any(|p| p[0] >= p[1]) {
            return Err(serde::de::Error::custom("pending order"));
        }
        Ok(Self {
            live: w.live,
            pending: w.pending.into_iter().collect(),
        })
    }
}
/// Runtime state follows each rule's continuation footprint, not total history.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub enum RowData {
    Initial(Vec<Contribution>),
    Scoped(ScopedRow),
    LwwRegister(Option<Contribution>),
    Exists(bool),
    Count(u64),
    Counter(i128),
    SetUnion(Vec<Vec<u8>>),
    Events(Vec<Event>),
    Derived,
    Progress(crate::progress_resume::ProgressResume),
    Resource(crate::resource_resume::Summary),
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct Summary {
    clause: StateClause,
    protocol: Option<CausalProtocol>,
    global_progress: Option<crate::progress_resume::ProgressResume>,
    rows: Vec<RowData>,
}
impl<'de> Deserialize<'de> for Summary {
    fn deserialize<D: Deserializer<'de>>(d: D) -> core::result::Result<Self, D::Error> {
        #[derive(Deserialize)]
        #[serde(deny_unknown_fields)]
        struct Wire {
            clause: StateClause,
            protocol: Option<CausalProtocol>,
            global_progress: Option<crate::progress_resume::ProgressResume>,
            rows: Vec<RowData>,
        }
        let w = Wire::deserialize(d)?;
        let s = Self {
            clause: w.clause,
            protocol: w.protocol,
            global_progress: w.global_progress,
            rows: w.rows,
        };
        s.validate().map_err(serde::de::Error::custom)?;
        Ok(s)
    }
}
fn wire_id(s: &str) -> bool {
    s.strip_prefix("sha256-").is_some_and(|s| {
        s.len() == 64
            && s.bytes()
                .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
    })
}
fn check_act(a: &Act) -> Result<()> {
    let derived = Act::from_message(a.message.clone(), &a.signer)
        .map_err(|_| Error::Invalid("act payload"))?;
    if derived != *a {
        return Err(Error::Invalid("act metadata"));
    }
    Ok(())
}
fn native(v: &SExpr) -> SExpr {
    match v {
        SExpr::Atom(Atom::Symbol(s)) => SExpr::Atom(Atom::Str(s.clone())),
        SExpr::Atom(Atom::Keyword(s)) => SExpr::Atom(Atom::Str(alloc::format!(":{s}"))),
        SExpr::List(xs) => SExpr::List(xs.iter().map(native).collect()),
        _ => v.clone(),
    }
}
fn field(a: &Act, k: &str) -> Option<SExpr> {
    a.fields.get(k).map(native)
}
fn replacing(r: &Rule, a: &Act) -> bool {
    matches!(
        r,
        Rule::Values { .. }
            | Rule::ValuesPerKey { .. }
            | Rule::ObservedSet { .. }
            | Rule::LwwMap { .. }
            | Rule::LwwPerSigner { .. }
    ) && r.verbs().contains(&a.verb.as_str())
}
fn writer(r: &Rule, a: &Act) -> bool {
    match r {
        Rule::ObservedSet { add, .. } => a.verb == *add,
        _ => r.verbs().first().is_some_and(|v| *v == a.verb),
    }
}
fn references(a: &Act) -> impl Iterator<Item = &String> {
    let xs = match a.fields.get(state::RESERVED_REPLACES) {
        Some(SExpr::List(xs)) => xs.as_slice(),
        _ => &[],
    };
    xs.iter().filter_map(|v| match v {
        SExpr::Atom(Atom::Str(s) | Atom::Symbol(s)) => Some(s),
        _ => None,
    })
}
fn check_references(r: &Rule, a: &Act) -> Result<()> {
    if replacing(r, a) {
        if let Some(v) = a.fields.get(state::RESERVED_REPLACES) {
            let SExpr::List(xs) = v else {
                return Err(Error::Invalid("replacements"));
            };
            if xs
                .iter()
                .any(|v| !matches!(v,SExpr::Atom(Atom::Str(s)|Atom::Symbol(s)) if wire_id(s)))
            {
                return Err(Error::Invalid("replacement identity"));
            }
        }
    }
    Ok(())
}
fn project(r: &Rule, a: &Act) -> Contribution {
    let (key, value, clock, signer) = match r {
        Rule::Initial { key, .. } | Rule::Values { key, .. } => {
            (None, field(a, key), None, String::new())
        }
        Rule::ObservedSet { key, .. } => (field(a, key), None, None, String::new()),
        Rule::ValuesPerKey { key, value, .. } => {
            (field(a, key), field(a, value), None, String::new())
        }
        Rule::LwwMap {
            key, value, clock, ..
        } => (
            field(a, key),
            field(a, value),
            clock_text(a, clock),
            a.signer.clone(),
        ),
        Rule::LwwRegister { key, clock, .. } | Rule::LwwPerSigner { key, clock, .. } => {
            (None, field(a, key), clock_text(a, clock), a.signer.clone())
        }
        _ => (None, None, None, String::new()),
    };
    Contribution {
        id: a.address.clone(),
        signer,
        key,
        value,
        clock,
    }
}
fn clock_text(a: &Act, k: &str) -> Option<String> {
    match a.fields.get(k) {
        Some(SExpr::Atom(Atom::Str(s))) if Hlc::parse(s).is_some() => Some(s.clone()),
        _ => None,
    }
}
fn stamp(c: &Contribution) -> Option<(Hlc, &str, &str)> {
    Some((Hlc::parse(c.clock.as_ref()?)?, &c.signer, &c.id))
}
fn scope(r: &Rule, c: &Contribution) -> Vec<u8> {
    match r {
        Rule::ValuesPerKey { .. } | Rule::LwwMap { .. } | Rule::ObservedSet { .. } => {
            c.key.as_ref().map(canonical_encode).unwrap_or_default()
        }
        Rule::LwwPerSigner { .. } => canonical_encode(&SExpr::Atom(Atom::Str(c.signer.clone()))),
        _ => Vec::new(),
    }
}
fn synthetic(r: &Rule, c: &Contribution) -> Act {
    let mut fields = BTreeMap::new();
    let mut set = |key: &str, v: &Option<SExpr>| {
        if let Some(v) = v {
            fields.insert(key.to_string(), v.clone());
        }
    };
    let verb = match r {
        Rule::Initial { verb, key } | Rule::Values { verb, key } => {
            set(key, &c.value);
            verb
        }
        Rule::ValuesPerKey {
            verb, key, value, ..
        } => {
            set(key, &c.key);
            set(value, &c.value);
            verb
        }
        Rule::ObservedSet { add, key, .. } => {
            set(key, &c.key);
            add
        }
        Rule::LwwMap {
            verb,
            key,
            value,
            clock,
            ..
        } => {
            set(key, &c.key);
            set(value, &c.value);
            set(
                clock,
                &c.clock.as_ref().map(|s| SExpr::Atom(Atom::Str(s.clone()))),
            );
            verb
        }
        Rule::LwwRegister { verb, key, clock } | Rule::LwwPerSigner { verb, key, clock } => {
            set(key, &c.value);
            set(
                clock,
                &c.clock.as_ref().map(|s| SExpr::Atom(Atom::Str(s.clone()))),
            );
            verb
        }
        _ => "",
    };
    // Ephemeral fold input only, never retained or used for authentication.
    Act {
        address: c.id.clone(),
        verb: verb.into(),
        signer: c.signer.clone(),
        predecessors: Vec::new(),
        recipients: BTreeSet::new(),
        fields,
        message: Message::Simple {
            performative: Performative::Custom(verb.into()),
            recipient: None,
            content: SExpr::List(vec![]),
            params: vec![],
            thread: None,
            sender: None,
            caused_by: None,
        },
    }
}
fn int_value(v: &Value) -> Option<i128> {
    match v {
        Value::Int(n) => Some(*n),
        Value::Pair { value, .. } => int_value(value),
        _ => None,
    }
}
fn integer_delta(r: &Rule, a: &Act) -> i128 {
    match r {
        Rule::Count { verb } => i128::from(a.verb == *verb),
        Rule::Counter { inc, dec, key } => {
            let n = a
                .fields
                .get(key)
                .map(Value::from_sexpr)
                .and_then(|v| int_value(&v))
                .unwrap_or(0);
            n * i128::from(a.verb == *inc) - n * i128::from(a.verb == *dec)
        }
        _ => 0,
    }
}
fn sorted_values(xs: impl Iterator<Item = Value>) -> Vec<Value> {
    let mut xs: Vec<_> = xs.map(|v| (v.render(), v)).collect();
    xs.sort_by(|a, b| a.0.cmp(&b.0));
    xs.dedup_by(|a, b| a.0 == b.0);
    xs.into_iter().map(|(_, v)| v).collect()
}

impl Summary {
    /// Domains remain a separate unsupported profile gate. The supplied protocol
    /// is always pinned; native metadata is retained only for repeats or Progress.
    pub fn new(clause: &StateClause, protocol: Option<&CausalProtocol>) -> Result<Self> {
        let mut names = BTreeSet::new();
        let mut rows = Vec::new();
        for e in &clause.entries {
            let Entry::Field { name, rule } = e else {
                return Err(Error::Unsupported);
            };
            if !names.insert(name) {
                return Err(Error::Invalid("duplicate state field"));
            }
            if let Rule::Histogram { field } | Rule::Sum { field } = rule {
                let source = clause.entries[..rows.len()].iter().find_map(|e| match e {
                    Entry::Field { name, rule } if name == field => Some(rule),
                    _ => None,
                });
                if !(matches!(
                    source,
                    Some(Rule::LwwMap { .. } | Rule::LwwPerSigner { .. })
                ) || matches!(rule, Rule::Sum { .. })
                    && matches!(source, Some(Rule::Events { .. })))
                {
                    return Err(Error::Invalid("derived source"));
                }
            }
            rows.push(match rule {
                // These terms require raw history or a finite-table checkpoint profile.
                Rule::Context { .. } | Rule::Lift(_) => return Err(Error::Unsupported),
                Rule::Initial { .. } => RowData::Initial(vec![]),
                Rule::LwwRegister { .. } => RowData::LwwRegister(None),
                Rule::Values { .. }
                | Rule::ValuesPerKey { .. }
                | Rule::ObservedSet { .. }
                | Rule::LwwMap { .. }
                | Rule::LwwPerSigner { .. } => RowData::Scoped(ScopedRow {
                    live: vec![],
                    pending: BTreeSet::new(),
                }),
                Rule::Exists { .. } => RowData::Exists(false),
                Rule::Count { .. } => RowData::Count(0),
                Rule::Counter { .. } => RowData::Counter(0),
                Rule::SetUnion { .. } => RowData::SetUnion(vec![]),
                Rule::Events { .. } => RowData::Events(vec![]),
                Rule::Histogram { .. } | Rule::Sum { .. } => RowData::Derived,
                Rule::Progress { verb } => {
                    RowData::Progress(crate::progress_resume::ProgressResume::new(protocol, verb)?)
                }
                Rule::BoundedCounter(_) => {
                    RowData::Resource(crate::resource_resume::Summary::default())
                }
            });
        }
        let global_progress = protocol
            .filter(|p| {
                p.steps.keys().any(|s| s.contains('#'))
                    || clause
                        .fields()
                        .any(|(_, r)| matches!(r, Rule::Progress { .. }))
            })
            .map(|p| crate::progress_resume::ProgressResume::new(Some(p), ""))
            .transpose()?;
        let protocol = protocol.cloned();
        Ok(Self {
            clause: clause.clone(),
            protocol,
            global_progress,
            rows,
        })
    }
    /// Global native R5 materialization, including profiles without Progress output.
    /// Installing this cache still requires the enclosing verified certificate.
    pub fn global_progress_resume(&self) -> Option<&crate::progress_resume::ProgressResume> {
        self.global_progress.as_ref()
    }
    /// Exact distinct wire identities required by this update's pre-root queries.
    pub fn query_ids(&self, act: &Act) -> Result<Vec<String>> {
        check_act(act)?;
        let mut ids = BTreeSet::new();

        for ((_, r), data) in self.clause.fields().zip(&self.rows) {
            check_references(r, act)?;
            if replacing(r, act) {
                ids.extend(references(act).cloned());
            }
            if let (Rule::BoundedCounter(rule), RowData::Resource(resume)) = (r, data) {
                ids.extend(resume.query_ids(rule, act)?);
            }
        }
        ids.remove(&act.address);
        Ok(ids.into_iter().collect())
    }
    pub fn progress_resume(&self, verb: &str) -> Option<&crate::progress_resume::ProgressResume> {
        self.clause
            .fields()
            .zip(&self.rows)
            .find_map(|((_, r), d)| match (r, d) {
                (Rule::Progress { verb: v }, RowData::Progress(s)) if v == verb => Some(s),
                _ => None,
            })
    }
    pub fn clause(&self) -> &StateClause {
        &self.clause
    }
    pub fn profile_hash(&self) -> Hash {
        self.schema_hash()
    }
    pub fn expected_profile_hash(clause: &StateClause) -> Result<Hash> {
        Ok(Self::new(clause, None)?.profile_hash())
    }
    pub fn expected_profile_hash_for(
        clause: &StateClause,
        protocol: Option<&CausalProtocol>,
    ) -> Result<Hash> {
        Ok(Self::new(clause, protocol)?.profile_hash())
    }
    pub fn schema_hash(&self) -> Hash {
        let mut d = base_dialect();
        d.state = Some(self.clause.clone());
        d.causal_protocol = self.protocol.clone();
        crate::hash(
            b"cbcl/checkpoint/summary-schema/v2",
            &canonical_encode(&to_signable_sexpr(&d)),
        )
    }
    pub fn validate(&self) -> Result<()> {
        let expected = Self::new(&self.clause, self.protocol.as_ref())?;
        if expected.protocol != self.protocol || expected.rows.len() != self.rows.len() {
            return Err(Error::Invalid("summary shape"));
        }
        match (&self.global_progress, &self.protocol) {
            (None, _) if expected.global_progress.is_none() => {}
            (Some(resume), Some(protocol))
                if expected.global_progress.is_some()
                    && resume.verb().is_empty()
                    && resume.protocol() == Some(protocol) =>
            {
                if crate::progress_resume::ProgressResume::decode(&resume.encode(), Some(protocol))?
                    != *resume
                {
                    return Err(Error::Invalid("global resume"));
                }
            }
            _ => return Err(Error::Invalid("global resume binding")),
        }
        for (((_, r), data), empty) in self.clause.fields().zip(&self.rows).zip(&expected.rows) {
            if core::mem::discriminant(data) != core::mem::discriminant(empty) {
                return Err(Error::Invalid("summary row tag"));
            }
            let lives: &[Contribution] = match data {
                RowData::Initial(xs) => {
                    if xs.len() > 2 {
                        return Err(Error::Invalid("initial bound"));
                    }
                    xs
                }
                RowData::Scoped(row) => &row.live,
                RowData::LwwRegister(c) => c.as_ref().map(core::slice::from_ref).unwrap_or(&[]),
                _ => &[],
            };
            if lives.windows(2).any(|w| w[0].id >= w[1].id) {
                return Err(Error::Invalid("live order"));
            }
            for c in lives {
                if !wire_id(&c.id) {
                    return Err(Error::Invalid("live identity"));
                }
                for v in [&c.key, &c.value].into_iter().flatten() {
                    if native(v) != *v {
                        return Err(Error::Invalid("native value"));
                    }
                }
                if c.clock.as_ref().is_some_and(|s| Hlc::parse(s).is_none()) {
                    return Err(Error::Invalid("clock"));
                }
                let valid = match r {
                    Rule::Initial { .. } | Rule::Values { .. } => {
                        c.key.is_none() && c.signer.is_empty() && c.clock.is_none()
                    }
                    Rule::ObservedSet { .. } => {
                        c.value.is_none() && c.signer.is_empty() && c.clock.is_none()
                    }
                    Rule::ValuesPerKey { .. } => c.signer.is_empty() && c.clock.is_none(),
                    Rule::LwwRegister { .. } => c.key.is_none() && c.clock.is_some(),
                    Rule::LwwPerSigner { .. } => c.key.is_none(),
                    Rule::LwwMap { .. } => true,
                    _ => false,
                };
                if !valid {
                    return Err(Error::Invalid("contribution footprint"));
                }
            }
            match data {
                RowData::Scoped(row) => {
                    for p in &row.pending {
                        if !wire_id(&p.target) || row.live.iter().any(|c| c.id == p.target) {
                            return Err(Error::Invalid("pending target"));
                        }
                        if !p.scope.is_empty() {
                            let v = crate::codec::decode_sexpr(&p.scope, 256 * 1024)?;
                            if native(&v) != v {
                                return Err(Error::Invalid("scope"));
                            }
                        }
                        if matches!(r, Rule::Values { .. }) && !p.scope.is_empty() {
                            return Err(Error::Invalid("scope"));
                        }
                        if matches!(r, Rule::LwwPerSigner { .. })
                            && !matches!(
                                crate::codec::decode_sexpr(&p.scope, 256 * 1024)?,
                                SExpr::Atom(Atom::Str(_))
                            )
                        {
                            return Err(Error::Invalid("signer scope"));
                        }
                    }
                }
                RowData::SetUnion(xs) => {
                    if xs.windows(2).any(|w| w[0] >= w[1]) {
                        return Err(Error::Invalid("set order"));
                    }
                    for b in xs {
                        let v = crate::codec::decode_sexpr(b, 256 * 1024)?;
                        if native(&v) != v {
                            return Err(Error::Invalid("set value"));
                        }
                    }
                }
                RowData::Events(xs) => {
                    if xs.windows(2).any(|w| w[0].id >= w[1].id) {
                        return Err(Error::Invalid("events order"));
                    }
                    for e in xs {
                        if !wire_id(&e.id) || native(&e.selected_value) != e.selected_value {
                            return Err(Error::Invalid("event projection"));
                        }
                    }
                }
                RowData::Resource(s) => {
                    let Rule::BoundedCounter(rule) = r else {
                        return Err(Error::Invalid("resource row"));
                    };
                    s.validate(rule)?;
                }
                RowData::Progress(s) => {
                    let Rule::Progress { verb } = r else {
                        return Err(Error::Invalid("progress row"));
                    };
                    if s.verb() != verb
                        || s.protocol() != self.protocol.as_ref()
                        || crate::progress_resume::ProgressResume::decode(
                            &s.encode(),
                            self.protocol.as_ref(),
                        )? != *s
                    {
                        return Err(Error::Invalid("progress row binding"));
                    }
                }
                _ => {}
            }
        }
        let known: BTreeSet<&str> = self
            .rows
            .iter()
            .flat_map(|d| match d {
                RowData::Initial(xs) => xs.as_slice(),
                RowData::Scoped(r) => r.live.as_slice(),
                RowData::LwwRegister(c) => c.as_ref().map(core::slice::from_ref).unwrap_or(&[]),
                _ => &[],
            })
            .map(|c| c.id.as_str())
            .chain(
                self.rows
                    .iter()
                    .flat_map(|d| match d {
                        RowData::Events(xs) => xs.as_slice(),
                        _ => &[],
                    })
                    .map(|e| e.id.as_str()),
            )
            .collect();
        if self.rows.iter().any(|r|matches!(r,RowData::Scoped(r)if r.pending.iter().any(|p|known.contains(p.target.as_str())))){return Err(Error::Invalid("resolved pending target"))}
        Ok(())
    }
    /// Full recognition and arithmetic/helper staging precede any row mutation.
    pub fn apply<F: Fn(&str) -> bool>(&mut self, act: &Act, covered: F) -> Result<()> {
        record_work(1, 0, 0, 0);
        check_act(act)?;
        let covered = |id: &str| {
            record_work(0, 0, 0, 1);
            covered(id)
        };
        for (_, r) in self.clause.fields() {
            check_references(r, act)?;
            for (verb, key) in r.data_fields() {
                if verb == act.verb {
                    if let Some(v) = field(act, key) {
                        let bytes = canonical_encode(&v);
                        crate::codec::decode_sexpr(&bytes, 256 * 1024)?;
                    }
                }
            }
        }
        if covered(&act.address) {
            return Ok(());
        }
        let mut global = self.global_progress.clone();
        if let Some(resume) = &mut global {
            resume.apply(act)?;
        }
        let mut staged = Vec::new();
        for ((_, r), data) in self.clause.fields().zip(&self.rows) {
            staged.push(match data {
                RowData::Count(n) => {
                    n.checked_add(u64::try_from(integer_delta(r, act)).map_err(|_| Error::Budget)?)
                        .ok_or(Error::Budget)?;
                    None
                }
                RowData::Counter(n) => {
                    n.checked_add(integer_delta(r, act)).ok_or(Error::Budget)?;
                    None
                }
                RowData::Resource(s) => {
                    let Rule::BoundedCounter(rule) = r else {
                        return Err(Error::Invalid("resource rule"));
                    };
                    let mut s = s.clone();
                    s.apply(rule, act, covered)?;
                    Some(RowData::Resource(s))
                }
                RowData::Progress(s) => {
                    let mut s = s.clone();
                    s.apply(act)?;
                    Some(RowData::Progress(s))
                }
                _ => None,
            });
        }
        for (((_, r), data), prepared) in self.clause.fields().zip(&mut self.rows).zip(staged) {
            if let Some(prepared) = prepared {
                *data = prepared;
                continue;
            }
            match data {
                RowData::Initial(xs) if writer(r, act) => {
                    xs.push(project(r, act));
                    xs.sort_by(|a, b| a.id.cmp(&b.id));
                    xs.dedup_by(|a, b| a.id == b.id);
                    xs.truncate(2);
                }
                RowData::LwwRegister(winner) if writer(r, act) => {
                    let c = project(r, act);
                    if stamp(&c).is_some() && winner.as_ref().map_or(true, |w| stamp(&c) > stamp(w))
                    {
                        *winner = Some(c)
                    }
                }
                RowData::Scoped(row) => {
                    let c = project(r, act);
                    let k = scope(r, &c);
                    let suppressed = row.pending.contains(&Pending {
                        scope: k.clone(),
                        target: act.address.clone(),
                    });
                    row.pending.retain(|p| {
                        record_work(0, 0, 1, 0);
                        p.target != act.address
                    });
                    if writer(r, act) && !suppressed {
                        match row.live.binary_search_by(|w| {
                            record_work(0, 1, 0, 0);
                            w.id.cmp(&c.id)
                        }) {
                            Ok(_) => {}
                            Err(i) => row.live.insert(i, c),
                        }
                    }
                    if replacing(r, act) {
                        for id in references(act) {
                            row.live.retain(|w| {
                                record_work(0, 1, 0, 0);
                                w.id != *id || scope(r, w) != k
                            });
                            if id != &act.address && !covered(id) {
                                row.pending.insert(Pending {
                                    scope: k.clone(),
                                    target: id.clone(),
                                });
                            }
                        }
                    }
                }
                RowData::Exists(flag) if writer(r, act) => *flag = true,
                RowData::Count(n) => *n += integer_delta(r, act) as u64,
                RowData::Counter(n) => *n += integer_delta(r, act),
                RowData::SetUnion(xs) => {
                    if let Rule::SetUnion { verb, key } = r {
                        if act.verb == *verb {
                            if let Some(v) = field(act, key) {
                                let bytes = canonical_encode(&v);
                                if let Err(i) = xs.binary_search(&bytes) {
                                    xs.insert(i, bytes)
                                }
                            }
                        }
                    }
                }
                RowData::Events(xs) => {
                    if let Rule::Events { verb, key } = r {
                        if act.verb == *verb {
                            if let Some(value) = field(act, key) {
                                let e = Event {
                                    id: act.address.clone(),
                                    signer: act.signer.clone(),
                                    selected_value: value,
                                };
                                if let Err(i) = xs.binary_search_by(|x| x.id.cmp(&e.id)) {
                                    xs.insert(i, e)
                                }
                            }
                        }
                    }
                }
                _ => {}
            }
        }
        self.global_progress = global;
        Ok(())
    }
    pub fn render(&self) -> Vec<(String, Value)> {
        let mut done: Vec<(String, Value)> = Vec::new();
        for ((name, r), data) in self.clause.fields().zip(&self.rows) {
            let value = match data {
                RowData::Initial(xs) => fold_live(name, r, xs),
                RowData::Scoped(row) => fold_live(name, r, &row.live),
                RowData::LwwRegister(c) => fold_live(
                    name,
                    r,
                    c.as_ref().map(core::slice::from_ref).unwrap_or(&[]),
                ),
                RowData::Exists(v) => Value::Bool(*v),
                RowData::Count(n) => Value::Int(i128::from(*n)),
                RowData::Counter(n) => Value::Int(*n),
                RowData::SetUnion(xs) => Value::Set(sorted_values(xs.iter().map(|b| {
                    Value::from_sexpr(
                        &crate::codec::decode_sexpr(b, 256 * 1024).expect("validated native value"),
                    )
                }))),
                RowData::Events(xs) => Value::Map(
                    xs.iter()
                        .map(|e| {
                            (
                                Value::Str(e.id.clone()),
                                Value::Pair {
                                    by: e.signer.clone(),
                                    value: Box::new(Value::from_sexpr(&e.selected_value)),
                                },
                            )
                        })
                        .collect(),
                ),
                RowData::Derived => derive(r, &done),
                RowData::Progress(s) => Value::Int(s.progress() as i128),
                RowData::Resource(s) => {
                    let Rule::BoundedCounter(rule) = r else {
                        unreachable!("validated resource")
                    };
                    s.render(rule)
                }
            };
            done.push((name.to_string(), value));
        }
        done
    }
    pub fn render_json(&self) -> String {
        state::render_json(&self.render())
    }
    pub fn hash(&self) -> Hash {
        crate::hash(b"cbcl/checkpoint/summary/v2", &self.encode())
    }
    pub fn live_acts(&self) -> usize {
        self.rows
            .iter()
            .map(|r| match r {
                RowData::Initial(xs) => xs.len(),
                RowData::Scoped(r) => r.live.len(),
                RowData::LwwRegister(c) => usize::from(c.is_some()),
                RowData::Events(xs) => xs.len(),
                _ => 0,
            })
            .sum()
    }
    pub fn pending_references(&self) -> usize {
        self.rows
            .iter()
            .map(|r| match r {
                RowData::Scoped(r) => r.pending.len(),
                _ => 0,
            })
            .sum()
    }
}
fn fold_live(name: &str, r: &Rule, xs: &[Contribution]) -> Value {
    let clause = StateClause {
        entries: vec![Entry::Field {
            name: name.to_string(),
            rule: r.clone(),
        }],
    };
    state::fold(
        &clause,
        None,
        &xs.iter().map(|c| synthetic(r, c)).collect::<Vec<_>>(),
    )
    .remove(0)
    .1
}
fn derive(r: &Rule, done: &[(String, Value)]) -> Value {
    let (Rule::Histogram { field } | Rule::Sum { field }) = r else {
        return Value::Absent;
    };
    let entries = match done.iter().find(|(n, _)| n == field) {
        Some((_, Value::Map(xs))) => xs.as_slice(),
        _ => &[],
    };
    if matches!(r, Rule::Sum { .. }) {
        return Value::Int(entries.iter().filter_map(|(_, v)| int_value(v)).sum());
    }
    let mut counts: BTreeMap<String, (Value, i128)> = BTreeMap::new();
    for (_, v) in entries {
        let v = match v {
            Value::Pair { value, .. } => value.as_ref(),
            v => v,
        };
        if *v != Value::Absent {
            counts.entry(v.render()).or_insert((v.clone(), 0)).1 += 1
        }
    }
    Value::Map(
        counts
            .into_values()
            .map(|(v, n)| (v, Value::Int(n)))
            .collect(),
    )
}

impl Summary {
    /// Closed v2 record: version, schema hash, row count, then typed row tags.
    /// Projected values use the native canonical AST codec; no JSON or Message
    /// transport is embedded. Live IDs and map/set keys are strictly ordered.
    pub fn encode(&self) -> Vec<u8> {
        use crate::codec::{put_bytes, put_string, put_u32};
        let mut out = Vec::new();
        put_u32(&mut out, 2);
        out.extend_from_slice(&self.schema_hash());
        match &self.global_progress {
            None => put_u32(&mut out, 0),
            Some(resume) => {
                put_u32(&mut out, 1);
                put_bytes(&mut out, &resume.encode());
            }
        }
        put_u32(&mut out, self.rows.len());
        for row in &self.rows {
            match row {
                RowData::Initial(xs) => {
                    put_u32(&mut out, 0);
                    put_contributions(&mut out, xs)
                }
                RowData::Scoped(row) => {
                    put_u32(&mut out, 1);
                    put_contributions(&mut out, &row.live);
                    put_u32(&mut out, row.pending.len());
                    let mut ps: Vec<Vec<u8>> = row
                        .pending
                        .iter()
                        .map(|p| {
                            let mut b = Vec::new();
                            put_bytes(&mut b, &p.scope);
                            put_string(&mut b, &p.target);
                            b
                        })
                        .collect();
                    ps.sort();
                    for p in ps {
                        out.extend(p)
                    }
                }
                RowData::LwwRegister(c) => {
                    put_u32(&mut out, 2);
                    put_contributions(
                        &mut out,
                        c.as_ref().map(core::slice::from_ref).unwrap_or(&[]),
                    )
                }
                RowData::Exists(v) => {
                    put_u32(&mut out, 3);
                    put_u32(&mut out, usize::from(*v))
                }
                RowData::Count(n) => {
                    put_u32(&mut out, 4);
                    out.extend_from_slice(&n.to_be_bytes())
                }
                RowData::Counter(n) => {
                    put_u32(&mut out, 5);
                    out.extend_from_slice(&n.to_be_bytes())
                }
                RowData::SetUnion(xs) => {
                    put_u32(&mut out, 6);
                    put_u32(&mut out, xs.len());
                    for v in xs {
                        put_bytes(&mut out, v)
                    }
                }
                RowData::Events(xs) => {
                    put_u32(&mut out, 7);
                    put_u32(&mut out, xs.len());
                    for e in xs {
                        put_string(&mut out, &e.id);
                        put_string(&mut out, &e.signer);
                        put_bytes(&mut out, &canonical_encode(&e.selected_value))
                    }
                }
                RowData::Derived => put_u32(&mut out, 8),
                RowData::Progress(s) => {
                    put_u32(&mut out, 9);
                    put_bytes(&mut out, &s.encode())
                }
                RowData::Resource(s) => {
                    put_u32(&mut out, 10);
                    put_bytes(&mut out, &s.encode())
                }
            }
        }
        out
    }
    /// Non-progress compatibility entry point; Progress requires a pinned protocol.
    pub fn decode(bytes: &[u8], clause: &StateClause) -> Result<Self> {
        if clause
            .fields()
            .any(|(_, r)| matches!(r, Rule::Progress { .. }))
        {
            return Err(Error::Unsupported);
        }
        Self::decode_for(bytes, clause, None)
    }
    /// Fully recognize a bounded v2 snapshot under independently pinned schema and
    /// protocol. Serde is useful for local persistence, never snapshot authority.
    pub fn decode_for(
        bytes: &[u8],
        clause: &StateClause,
        protocol: Option<&CausalProtocol>,
    ) -> Result<Self> {
        use crate::codec::{put_bytes, put_string, Reader};
        const MAX: usize = 16 * 1024 * 1024;
        let mut r = Reader::new(bytes, MAX)?;
        let mut result = Self::new(clause, protocol)?;
        if r.u32()? != 2 {
            return Err(Error::Invalid("summary version"));
        }
        if r.hash()? != result.schema_hash() {
            return Err(Error::Invalid("summary schema"));
        }
        result.global_progress = match r.u32()? {
            0 => None,
            1 => Some(crate::progress_resume::ProgressResume::decode(
                r.bytes(MAX)?,
                protocol,
            )?),
            _ => return Err(Error::Invalid("global resume tag")),
        };
        let n = r.count(1024)?;
        if n != result.rows.len() {
            return Err(Error::Invalid("row count"));
        }
        for ((_, rule), row) in result.clause.fields().zip(&mut result.rows) {
            let tag = r.u32()?;
            *row = match (tag, &*row) {
                (0, RowData::Initial(_)) => RowData::Initial(read_contributions(&mut r, 2)?),
                (1, RowData::Scoped(_)) => {
                    let live = read_contributions(&mut r, 65536)?;
                    let n = r.count(65536)?;
                    let mut pending = BTreeSet::new();
                    let mut last: Option<Vec<u8>> = None;
                    for _ in 0..n {
                        let scope = r.bytes(256 * 1024)?.to_vec();
                        let target = r.string(71)?;
                        let mut key = Vec::new();
                        put_bytes(&mut key, &scope);
                        put_string(&mut key, &target);
                        if last.as_ref().is_some_and(|p| p >= &key) {
                            return Err(Error::Invalid("pending order"));
                        }
                        last = Some(key);
                        pending.insert(Pending { scope, target });
                    }
                    RowData::Scoped(ScopedRow { live, pending })
                }
                (2, RowData::LwwRegister(_)) => {
                    RowData::LwwRegister(read_contributions(&mut r, 1)?.pop())
                }
                (3, RowData::Exists(_)) => RowData::Exists(match r.u32()? {
                    0 => false,
                    1 => true,
                    _ => return Err(Error::Invalid("bool tag")),
                }),
                (4, RowData::Count(_)) => RowData::Count(u64::from_be_bytes(
                    r.take(8)?.try_into().map_err(|_| Error::Invalid("count"))?,
                )),
                (5, RowData::Counter(_)) => RowData::Counter(i128::from_be_bytes(
                    r.take(16)?
                        .try_into()
                        .map_err(|_| Error::Invalid("counter"))?,
                )),
                (6, RowData::SetUnion(_)) => {
                    let n = r.count(65536)?;
                    let mut xs = Vec::new();
                    for _ in 0..n {
                        xs.push(r.bytes(256 * 1024)?.to_vec())
                    }
                    RowData::SetUnion(xs)
                }
                (7, RowData::Events(_)) => {
                    let n = r.count(65536)?;
                    let mut xs = Vec::new();
                    for _ in 0..n {
                        xs.push(Event {
                            id: r.string(71)?,
                            signer: r.string(4096)?,
                            selected_value: crate::codec::decode_sexpr(
                                r.bytes(256 * 1024)?,
                                256 * 1024,
                            )?,
                        })
                    }
                    RowData::Events(xs)
                }
                (8, RowData::Derived) => RowData::Derived,
                (9, RowData::Progress(_)) => RowData::Progress(
                    crate::progress_resume::ProgressResume::decode(r.bytes(MAX)?, protocol)?,
                ),
                (10, RowData::Resource(_)) => {
                    let Rule::BoundedCounter(rule) = rule else {
                        return Err(Error::Invalid("resource rule"));
                    };
                    RowData::Resource(crate::resource_resume::Summary::decode(
                        r.bytes(MAX)?,
                        rule,
                    )?)
                }
                _ => return Err(Error::Invalid("row tag")),
            };
        }
        r.finish()?;
        result.validate()?;
        if result.encode() != bytes {
            return Err(Error::Invalid("noncanonical summary"));
        }
        Ok(result)
    }
}
fn put_value(out: &mut Vec<u8>, v: &Option<SExpr>) {
    use crate::codec::{put_bytes, put_u32};
    match v {
        None => put_u32(out, 0),
        Some(v) => {
            put_u32(out, 1);
            put_bytes(out, &canonical_encode(v))
        }
    }
}
fn read_value(r: &mut crate::codec::Reader<'_>) -> Result<Option<SExpr>> {
    match r.u32()? {
        0 => Ok(None),
        1 => Ok(Some(crate::codec::decode_sexpr(
            r.bytes(256 * 1024)?,
            256 * 1024,
        )?)),
        _ => Err(Error::Invalid("option tag")),
    }
}
fn put_contributions(out: &mut Vec<u8>, xs: &[Contribution]) {
    use crate::codec::{put_string, put_u32};
    put_u32(out, xs.len());
    for c in xs {
        put_string(out, &c.id);
        put_string(out, &c.signer);
        put_value(out, &c.key);
        put_value(out, &c.value);
        put_value(
            out,
            &c.clock.as_ref().map(|s| SExpr::Atom(Atom::Str(s.clone()))),
        );
    }
}
fn read_contributions(r: &mut crate::codec::Reader<'_>, max: usize) -> Result<Vec<Contribution>> {
    let n = r.count(max)?;
    let mut xs: Vec<Contribution> = Vec::new();
    for _ in 0..n {
        let c = Contribution {
            id: r.string(71)?,
            signer: r.string(4096)?,
            key: read_value(r)?,
            value: read_value(r)?,
            clock: match read_value(r)? {
                None => None,
                Some(SExpr::Atom(Atom::Str(s))) => Some(s),
                _ => return Err(Error::Invalid("clock tag")),
            },
        };
        if xs.last().is_some_and(|p| p.id >= c.id) {
            return Err(Error::Invalid("live order"));
        }
        xs.push(c);
    }
    Ok(xs)
}

#[cfg(test)]
#[path = "summary_tests.rs"]
mod tests;
