//! Bounded-counter observation continuation, NOT ResourceEvidence authority.
//!
//! Stores projected resource/cast facts and presence of referenced non-resource
//! identities. It never stores complete Acts or Messages. Apply/decode rerun the
//! native escrow verifier: CPU grows with resource evidence; this is not a
//! constant-size account/certificate runtime. Render only copies cached output.
use crate::{codec, hash, Error, Hash, Result};
use alloc::{
    boxed::Box,
    collections::{BTreeMap, BTreeSet},
    string::String,
    vec::Vec,
};
use cbcl_core::{
    canonical::canonical_encode,
    escrow::{self, CounterRule, Outcome, ResourceFact},
    sexpr::{Atom, SExpr},
    state::{Act, Value},
};
use serde::{Deserialize, Deserializer, Serialize, Serializer};
const MAX: usize = 16 * 1024 * 1024;
const RECORDS: usize = 65_536;
const FACT_BYTES: usize = 256 * 1024;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Summary {
    rule: Option<Box<CounterRule>>,
    facts: BTreeMap<String, ResourceFact>,
    known: BTreeSet<String>,
    outcome: Box<Outcome>,
}
impl Default for Summary {
    fn default() -> Self {
        Self {
            rule: None,
            facts: BTreeMap::new(),
            known: BTreeSet::new(),
            outcome: Box::new(Outcome::Pending(Vec::new())),
        }
    }
}
fn rule_hash(c: &CounterRule) -> Hash {
    hash(
        b"cbcl/checkpoint/resource-rule/v1",
        &canonical_encode(&SExpr::List(c.canonical_options())),
    )
}
fn text(x: &SExpr) -> Option<&str> {
    match x {
        SExpr::Atom(Atom::Str(s) | Atom::Symbol(s)) => Some(s),
        _ => None,
    }
}
fn needed(c: &CounterRule, facts: &BTreeMap<String, ResourceFact>) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    for f in facts.values() {
        if f.verb == c.initial_verb {
            out.extend(
                f.predecessors
                    .iter()
                    .filter(|id| cbcl_core::r7::is_address(id))
                    .cloned(),
            );
        }
        if c.operation_verbs().contains(&f.verb.as_str()) {
            if let Some(id) = f
                .fields
                .get(escrow::PREV)
                .and_then(text)
                .filter(|id| cbcl_core::r7::is_address(id))
            {
                out.insert(id.into());
            }
            if let Some(SExpr::List(xs)) = f.fields.get(escrow::DEPS) {
                out.extend(
                    xs.iter()
                        .filter_map(text)
                        .filter(|id| cbcl_core::r7::is_address(id))
                        .map(String::from),
                );
            }
        }
    }
    out
}
fn recompute(
    c: &CounterRule,
    facts: &BTreeMap<String, ResourceFact>,
    known: &BTreeSet<String>,
) -> Outcome {
    escrow::observe_facts(c, facts, |id| known.contains(id))
}
impl Summary {
    pub fn new() -> Self {
        Self::default()
    }
    /// Deterministic sparse-proof footprint for this row and incoming act.
    /// Previously classified references need no historical membership re-query:
    /// a one-act extension can change absence only for the arriving identity.
    pub fn query_ids(&self, rule: &CounterRule, act: &Act) -> Result<Vec<String>> {
        if self.rule.as_deref().is_some_and(|old| old != rule) {
            return Err(Error::Invalid("resource rule mismatch"));
        }
        let incoming = escrow::project_resource_fact(rule, act)
            .map_err(|_| Error::Invalid("resource act identity"))?;
        let mut out = BTreeSet::from([act.address.clone()]);
        if rule.ownership != escrow::Ownership::Collective && !rule.certification.is_quorum() {
            let old_refs = needed(rule, &self.facts);
            if let Some(fact) = incoming {
                let one = BTreeMap::from([(fact.address.clone(), fact)]);
                for id in needed(rule, &one) {
                    if !old_refs.contains(&id) && !self.facts.contains_key(&id) {
                        out.insert(id);
                    }
                }
            }
        }
        Ok(out.into_iter().collect())
    }
    pub fn apply<F: Fn(&str) -> bool>(
        &mut self,
        rule: &CounterRule,
        act: &Act,
        precovered: F,
    ) -> Result<()> {
        if self.rule.as_deref().is_some_and(|old| old != rule) {
            return Err(Error::Invalid("resource rule mismatch"));
        }
        let incoming = escrow::project_resource_fact(rule, act)
            .map_err(|_| Error::Invalid("resource act identity"))?;
        if precovered(&act.address) {
            if incoming
                .as_ref()
                .zip(self.facts.get(&act.address))
                .is_some_and(|(a, b)| a != b)
            {
                return Err(Error::Invalid("conflicting resource identity"));
            }
            return Ok(());
        }
        let old_refs = needed(rule, &self.facts);
        let mut next = self.clone();
        next.rule = Some(Box::new(rule.clone()));
        // These legacy modes intentionally cannot certify resource finality.
        if rule.ownership != escrow::Ownership::Collective && !rule.certification.is_quorum() {
            if let Some(f) = incoming {
                if next.facts.get(&f.address).is_some_and(|old| old != &f) {
                    return Err(Error::Invalid("conflicting resource identity"));
                }
                next.facts.insert(f.address.clone(), f);
            }
            let refs = needed(rule, &next.facts);
            next.known
                .retain(|id| refs.contains(id) && !next.facts.contains_key(id));
            for id in refs {
                if !next.facts.contains_key(&id)
                    && (id == act.address || (!old_refs.contains(&id) && precovered(&id)))
                {
                    next.known.insert(id);
                }
            }
        }
        next.outcome = Box::new(recompute(rule, &next.facts, &next.known));
        next.validate(rule)?;
        *self = next;
        Ok(())
    }
    /// No verification or history traversal; copying the finite rendered result
    /// costs its output size (accounts/evidence), not accepted-history size.
    pub fn render(&self, rule: &CounterRule) -> Value {
        match self.rule.as_deref() {
            None => recompute(rule, &self.facts, &self.known).value(),
            Some(old) if old != rule => Outcome::Fault {
                reason: "resource rule mismatch".into(),
                evidence: Vec::new(),
            }
            .value(),
            _ => self.outcome.value(),
        }
    }
    pub fn validate(&self, rule: &CounterRule) -> Result<()> {
        if self.rule.as_deref().is_some_and(|old| old != rule) {
            return Err(Error::Invalid("resource rule mismatch"));
        }
        if self.facts.len() > RECORDS || self.known.len() > RECORDS {
            return Err(Error::Budget);
        }
        if self.rule.is_none() && (!self.facts.is_empty() || !self.known.is_empty()) {
            return Err(Error::Invalid("unbound resource facts"));
        }
        let refs = needed(rule, &self.facts);
        if self.known.iter().any(|id| {
            !refs.contains(id) || self.facts.contains_key(id) || !cbcl_core::r7::is_address(id)
        }) {
            return Err(Error::Invalid("resource reference presence"));
        }
        let mut size = 0usize;
        for (id, f) in &self.facts {
            if id != &f.address
                || !cbcl_core::r7::is_address(id)
                || f.address.len() > 128
                || f.signer.len() > 2048
                || f.verb.len() > 2048
                || f.predecessors.len() > 64
                || f.fields.len() > 1024
            {
                return Err(Error::Invalid("resource fact metadata"));
            }
            let links = f
                .predecessors
                .iter()
                .map(String::as_str)
                .chain(f.fields.get(escrow::PREV).and_then(text))
                .chain(
                    f.fields
                        .get(escrow::DEPS)
                        .into_iter()
                        .flat_map(|x| match x {
                            SExpr::List(xs) => xs.as_slice(),
                            _ => &[],
                        })
                        .filter_map(text),
                );
            if links
                .into_iter()
                .any(|id| escrow::resource_state_id(id) != id)
            {
                return Err(Error::Invalid("noncanonical resource link"));
            }
            let allowed: BTreeSet<&str> = rule
                .data_fields()
                .into_iter()
                .filter(|(v, _)| *v == f.verb)
                .map(|(_, k)| k)
                .chain([escrow::PREV, escrow::DEPS])
                .collect();
            if f.fields.keys().any(|k| !allowed.contains(k.as_str()))
                || (!rule.verbs().contains(&f.verb.as_str()) && f.bindings.is_none())
            {
                return Err(Error::Invalid("resource fact projection"));
            }
            let encoded = canonical_encode(&fact_expr(f));
            if encoded.len() > FACT_BYTES {
                return Err(Error::Budget);
            }
            codec::decode_sexpr(&encoded, FACT_BYTES)?;
            size = size.checked_add(encoded.len() + 4).ok_or(Error::Budget)?;
        }
        size = size
            .checked_add(self.known.iter().map(|s| s.len() + 4).sum::<usize>())
            .ok_or(Error::Budget)?;
        if size + 64 > MAX {
            return Err(Error::Budget);
        }
        if self.rule.is_some() && *self.outcome != recompute(rule, &self.facts, &self.known) {
            return Err(Error::Invalid("resource outcome cache"));
        }
        Ok(())
    }
    /// v1: version, bound flag, pinned rule hash, sorted projected facts and
    /// sorted known referenced IDs. Cached observations are never accepted as input.
    pub fn encode(&self) -> Vec<u8> {
        let mut out = Vec::new();
        codec::put_u32(&mut out, 1);
        out.push(u8::from(self.rule.is_some()));
        if let Some(c) = &self.rule {
            out.extend_from_slice(&rule_hash(c));
        }
        codec::put_u32(&mut out, self.facts.len());
        for f in self.facts.values() {
            codec::put_bytes(&mut out, &canonical_encode(&fact_expr(f)));
        }
        codec::put_u32(&mut out, self.known.len());
        for id in &self.known {
            codec::put_string(&mut out, id);
        }
        out
    }
    pub fn decode(bytes: &[u8], rule: &CounterRule) -> Result<Self> {
        let mut r = codec::Reader::new(bytes, MAX)?;
        if r.u32()? != 1 {
            return Err(Error::Invalid("resource resume version"));
        }
        let bound = match r.take(1)?[0] {
            0 => false,
            1 => true,
            _ => return Err(Error::Invalid("resource rule flag")),
        };
        if bound && r.hash()? != rule_hash(rule) {
            return Err(Error::Invalid("resource rule hash"));
        }
        let count = r.count(RECORDS)?;
        let mut facts = BTreeMap::new();
        for _ in 0..count {
            let fact = parse_fact(codec::decode_sexpr(r.bytes(FACT_BYTES)?, FACT_BYTES)?)?;
            if facts.insert(fact.address.clone(), fact).is_some() {
                return Err(Error::Invalid("duplicate resource fact"));
            }
        }
        let count = r.count(RECORDS)?;
        let mut known = BTreeSet::new();
        for _ in 0..count {
            if !known.insert(r.string(128)?) {
                return Err(Error::Invalid("duplicate resource presence"));
            }
        }
        r.finish()?;
        let outcome = if bound {
            recompute(rule, &facts, &known)
        } else {
            Outcome::Pending(Vec::new())
        };
        let result = Self {
            rule: bound.then(|| Box::new(rule.clone())),
            facts,
            known,
            outcome: Box::new(outcome),
        };
        result.validate(rule)?;
        if result.encode() != bytes {
            return Err(Error::Invalid("noncanonical resource resume"));
        }
        Ok(result)
    }
}
fn string(s: &str) -> SExpr {
    SExpr::Atom(Atom::Str(s.into()))
}
fn optional(x: Option<SExpr>) -> SExpr {
    SExpr::List(x.into_iter().collect())
}
fn fact_expr(f: &ResourceFact) -> SExpr {
    SExpr::List(alloc::vec![
        string(&f.address),
        string(&f.verb),
        string(&f.signer),
        string(&crate::hex(&f.identity)),
        SExpr::List(f.predecessors.iter().map(|s| string(s)).collect()),
        optional(f.language.as_deref().map(string)),
        optional(f.thread.as_deref().map(string)),
        optional(f.from.clone()),
        optional(f.bindings.clone().map(SExpr::List)),
        SExpr::List(
            f.fields
                .iter()
                .map(|(k, v)| SExpr::List(alloc::vec![string(k), v.clone()]))
                .collect()
        )
    ])
}
fn parse_fact(x: SExpr) -> Result<ResourceFact> {
    fn txt(x: SExpr) -> Result<String> {
        if let SExpr::Atom(Atom::Str(s)) = x {
            Ok(s)
        } else {
            Err(Error::Invalid("resource string"))
        }
    }
    fn list(x: SExpr) -> Result<Vec<SExpr>> {
        if let SExpr::List(xs) = x {
            Ok(xs)
        } else {
            Err(Error::Invalid("resource list"))
        }
    }
    fn opt(x: SExpr) -> Result<Option<SExpr>> {
        let mut xs = list(x)?;
        match xs.len() {
            0 => Ok(None),
            1 => Ok(xs.pop()),
            _ => Err(Error::Invalid("resource optional")),
        }
    }
    let xs = list(x)?;
    if xs.len() != 10 {
        return Err(Error::Invalid("resource fact arity"));
    }
    let mut xs = xs.into_iter();
    let mut take = || xs.next().ok_or(Error::Invalid("resource fact arity"));
    let address = txt(take()?)?;
    let verb = txt(take()?)?;
    let signer = txt(take()?)?;
    let digest = txt(take()?)?;
    if digest.len() != 64
        || !digest
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
    {
        return Err(Error::Invalid("resource identity digest"));
    }
    let mut identity = [0u8; 32];
    for (i, b) in identity.iter_mut().enumerate() {
        *b = u8::from_str_radix(&digest[i * 2..i * 2 + 2], 16)
            .map_err(|_| Error::Invalid("resource digest"))?;
    }
    let predecessors = list(take()?)?
        .into_iter()
        .map(txt)
        .collect::<Result<Vec<_>>>()?;
    let language = opt(take()?)?.map(txt).transpose()?;
    let thread = opt(take()?)?.map(txt).transpose()?;
    let from = opt(take()?)?;
    let bindings = opt(take()?)?.map(list).transpose()?;
    let mut fields = BTreeMap::new();
    for pair in list(take()?)? {
        let mut pair = list(pair)?.into_iter();
        let k = txt(pair.next().ok_or(Error::Invalid("resource field"))?)?;
        let v = pair.next().ok_or(Error::Invalid("resource field"))?;
        if pair.next().is_some() || fields.insert(k, v).is_some() {
            return Err(Error::Invalid("resource field"));
        }
    }
    Ok(ResourceFact {
        address,
        verb,
        signer,
        predecessors,
        fields,
        language,
        thread,
        from,
        bindings,
        identity,
    })
}
#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Wire {
    rule: Option<CounterRule>,
    facts: Vec<ResourceFact>,
    known: Vec<String>,
}
impl Serialize for Summary {
    fn serialize<S: Serializer>(&self, s: S) -> core::result::Result<S::Ok, S::Error> {
        Wire {
            rule: self.rule.as_deref().cloned(),
            facts: self.facts.values().cloned().collect(),
            known: self.known.iter().cloned().collect(),
        }
        .serialize(s)
    }
}
impl<'de> Deserialize<'de> for Summary {
    fn deserialize<D: Deserializer<'de>>(d: D) -> core::result::Result<Self, D::Error> {
        let w = Wire::deserialize(d)?;
        if w.facts.len() > RECORDS || w.known.len() > RECORDS {
            return Err(serde::de::Error::custom("resource budget"));
        }
        let fact_count = w.facts.len();
        let known_count = w.known.len();
        let facts: BTreeMap<_, _> = w
            .facts
            .into_iter()
            .map(|f| (f.address.clone(), f))
            .collect();
        let known: BTreeSet<_> = w.known.into_iter().collect();
        if facts.len() != fact_count || known.len() != known_count {
            return Err(serde::de::Error::custom("duplicate resource record"));
        }
        let outcome = w.rule.as_ref().map_or(Outcome::Pending(Vec::new()), |c| {
            recompute(c, &facts, &known)
        });
        let result = Self {
            rule: w.rule.map(Box::new),
            facts,
            known,
            outcome: Box::new(outcome),
        };
        if let Some(c) = result.rule.as_deref() {
            result.validate(c).map_err(serde::de::Error::custom)?;
        } else if !result.facts.is_empty() || !result.known.is_empty() {
            return Err(serde::de::Error::custom("unbound resource projection"));
        }
        Ok(result)
    }
}
#[cfg(test)]
#[path = "resource_resume_tests.rs"]
mod tests;
