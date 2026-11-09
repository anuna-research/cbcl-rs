//! Independently derived member cuts and authenticated, finite-query continuation.
//!
//! [[SPEC-035-cached-state-checkpoints#CON-3502]]: coverage authenticates prior
//! acceptance, never an unsigned payload or a new causal verdict. Repeat positions resume from scoped native metadata; all-occupant fan-in
//! remains outside this profile.
use crate::{
    certificate::{
        check_scope, native, native_id, Certificate, Context, KeySigner, KeyVerifier, Manifest,
        SignedMessage,
    },
    coverage::{Coverage, Proof},
    hash,
    summary::Summary,
    Error, Hash, Result,
};
use alloc::{
    collections::BTreeSet,
    string::{String, ToString},
    vec,
    vec::Vec,
};
use cbcl_core::{
    admission::{AdmissionGate, AdmissionMonitor, AdmissionState},
    canonical::dialect_hash,
    message::{CausedBy, Message, WrapperType},
    projection::verify_causal_for_role,
    protocol::{NodeRef, VerificationResult},
    role::{parse_wrapper_cast, Endpoint},
    sexpr::{Atom, SExpr},
    state::Act,
    store::{ContentHash, MessageStore, ThreadId, ThreadedMessageStore},
};
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Step {
    pub message: SignedMessage,
    pub ancestry: Vec<(SignedMessage, Proof)>,
    pub identity: Proof,
    /// Sorted unique state addresses (`f1220`); all proofs use the PRE-root.
    pub replacements: Vec<(String, Proof)>,
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Floor {
    pub context: Hash,
    pub root: Hash,
    pub frontier: Vec<String>,
}

/// Evidence is keyed by native identity AND actual signed wire hash. Signatures
/// are not part of native identity; distinct ratifications must not overwrite.
pub type Evidence = crate::evidence::Evidence;
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Client {
    pub context: Hash,
    pub coverage: Hash,
    pub summary: Summary,
    pub frontier: Vec<String>,
    #[serde(with = "evidence_serde")]
    pub evidence: Evidence,
}
mod evidence_serde {
    use super::*;
    pub fn serialize<S: serde::Serializer>(
        e: &Evidence,
        s: S,
    ) -> core::result::Result<S::Ok, S::Error> {
        e.iter().collect::<Vec<_>>().serialize(s)
    }
    pub fn deserialize<'de, D: serde::Deserializer<'de>>(
        d: D,
    ) -> core::result::Result<Evidence, D::Error> {
        let rows = Vec::<((String, Hash), SignedMessage)>::deserialize(d)?;
        let mut out = Evidence::new();
        for (key, m) in rows {
            if evidence_key(&m).map_err(serde::de::Error::custom)? != key
                || out.insert(key, m).is_some()
            {
                return Err(serde::de::Error::custom("invalid evidence identity"));
            }
        }
        Ok(out)
    }
}
fn evidence_key(m: &SignedMessage) -> Result<(String, Hash)> {
    Ok((m.id()?, hash(b"cbcl/checkpoint/evidence/v1", &m.encode())))
}
fn parents(m: &Message) -> Vec<String> {
    match m.innermost_simple().and_then(Message::caused_by) {
        Some(CausedBy::Single(id)) => vec![id.clone()],
        Some(CausedBy::Multiple(ids)) => ids.clone(),
        _ => vec![],
    }
}
fn thread(c: &Context) -> Result<ThreadId> {
    Ok(ThreadId(
        c.target_root
            .message()
            .innermost_simple()
            .and_then(Message::thread)
            .ok_or(Error::Invalid("target thread"))?
            .to_string(),
    ))
}
fn endpoint(c: &Context) -> Result<Endpoint> {
    let Message::Wrapped {
        wrapper: WrapperType::WithRoles,
        params,
        ..
    } = c.target_root.message()
    else {
        return Err(Error::Invalid("target cast"));
    };
    let cast =
        parse_wrapper_cast(params, &c.target.roles).map_err(|_| Error::Invalid("target cast"))?;
    if let Some((role, _)) = cast.singleton.iter().next() {
        return Ok(Endpoint {
            role: role.clone(),
            occupant: None,
        });
    }
    let (role, key) = cast
        .singleton
        .iter()
        .next()
        .or_else(|| {
            cast.indexed
                .iter()
                .find_map(|(r, ks)| ks.first().map(|k| (r, k)))
        })
        .ok_or(Error::Invalid("empty target cast"))?;
    Ok(Endpoint {
        role: role.clone(),
        occupant: Some(key.clone()),
    })
}
/// Explicit capability gate: scoped native position lookups, no global fan-in.
/// Unsupported profiles must use ordinary replay, not guessed completeness.
pub fn validate_profile(c: &Context) -> Result<()> {
    if let Some(p) = &c.target.causal_protocol {
        for step in p.steps.values() {
            if step
                .predecessors
                .iter()
                .chain(&step.successors)
                .any(|n| matches!(n, NodeRef::All(_)))
            {
                return Err(Error::Unsupported);
            }
        }
    } else {
        return Err(Error::Unsupported);
    }
    let summary = Summary::new(
        c.target.state.as_ref().ok_or(Error::Unsupported)?,
        c.target.causal_protocol.as_ref(),
    )?;
    if summary.profile_hash() != c.profile {
        return Err(Error::Unsupported);
    }
    Ok(())
}
/// Check every native shape, not just state-bearing verbs. Reject duplicate or
/// dangling keywords before any map-based projection can hide one spelling.
fn shape(message: &Message, c: &Context, root: bool) -> Result<()> {
    let mut inner = message;
    if root {
        let Message::Wrapped {
            wrapper: WrapperType::WithRoles,
            content,
            ..
        } = inner
        else {
            return Err(Error::Invalid("target cast wrapper"));
        };
        inner = content;
    }
    let Message::Wrapped {
        wrapper: WrapperType::Signed,
        content,
        ..
    } = inner
    else {
        return Err(Error::Invalid("target signature wrapper"));
    };
    let inner = match content.as_ref() {
        Message::Dialect {
            dialect_name,
            inner,
        } => {
            // Context construction validates the immutable installed code pin.
            if dialect_name != &c.target.name {
                return Err(Error::Invalid("target language pin"));
            }
            inner.as_ref()
        }
        m @ Message::Simple { .. } if root => m,
        _ => return Err(Error::Invalid("target language wrapper")),
    };
    let Message::Simple { params, .. } = inner else {
        return Err(Error::Invalid("target simple"));
    };
    let mut seen = BTreeSet::new();
    if params.len() % 2 != 0 {
        return Err(Error::Invalid("keyword grammar"));
    }
    for pair in params.chunks_exact(2) {
        let SExpr::Atom(Atom::Keyword(k)) = &pair[0] else {
            return Err(Error::Invalid("keyword grammar"));
        };
        if !seen.insert(k) || ["thread", "sender", "caused-by"].contains(&k.as_str()) {
            // These three fields have dedicated native Message slots. A second
            // spelling in params would serialize to duplicate routing fields.
            return Err(Error::Invalid("duplicate keyword"));
        }
        let verb = inner
            .performative()
            .ok_or(Error::Invalid("performative"))?
            .name();
        if !cbcl_core::state::ROUTING_KEYWORDS.contains(&k.as_str())
            && !cbcl_core::r7::declared_keywords(&c.target.shapes, verb).contains(k)
        {
            return Err(Error::Invalid("closed target fields"));
        }
    }
    let perf = inner
        .performative()
        .ok_or(Error::Invalid("performative"))?
        .name();
    if root {
        if perf != "hello" || inner.caused_by() != Some(&CausedBy::Begin) {
            return Err(Error::Invalid("target root hello"));
        }
    } else if c
        .target
        .find_performative(perf)
        .and_then(|p| p.role.as_ref())
        .is_none()
        || !c.target.causal_protocol.as_ref().is_some_and(|p| {
            p.steps
                .keys()
                .any(|name| cbcl_core::protocol::repeat_base_name(name) == perf)
        })
    {
        return Err(Error::Invalid("undeclared protocol performative"));
    }
    if !root {
        match inner.caused_by() {
            Some(CausedBy::Single(id)) => native_id(id)?,
            Some(CausedBy::Multiple(ids))
                if !ids.is_empty() && !ids.windows(2).any(|w| w[0] >= w[1]) =>
            {
                for id in ids {
                    native_id(id)?;
                }
            }
            _ => return Err(Error::Invalid("target predecessor grammar")),
        }
    }
    let sx = SExpr::from(inner.clone());
    for s in c.target.shapes.iter().filter(|s| s.performative == perf) {
        s.check(&sx).map_err(|_| Error::Invalid("target shape"))?;
    }
    cbcl_core::r7::verify_state_shape(&c.target, message)
        .map_err(|_| Error::Invalid("state shape"))?;
    Ok(())
}
struct Gate<'a> {
    c: &'a Context,
    keys: &'a dyn KeyVerifier,
}
#[cfg(feature = "std")]
pub(crate) fn authenticate_target(
    message: &SignedMessage,
    c: &Context,
    keys: &dyn KeyVerifier,
) -> Result<Act> {
    let act = message.authenticate(keys)?;
    shape(
        message.message(),
        c,
        message.message() == c.target_root.message(),
    )?;
    if message
        .message()
        .innermost_simple()
        .and_then(Message::thread)
        != Some(thread(c)?.0.as_str())
    {
        return Err(Error::Invalid("foreign target thread"));
    }
    Ok(act)
}
impl AdmissionGate for Gate<'_> {
    fn authenticate(&self, m: &Message) -> core::result::Result<ContentHash, String> {
        let signed = SignedMessage::from_message(m.clone());
        signed.authenticate(self.keys).map_err(|e| e.to_string())?;
        shape(m, self.c, m == self.c.target_root.message()).map_err(|e| e.to_string())?;
        signed.id().map(ContentHash).map_err(|e| e.to_string())
    }
}
fn validate_context(c: &Context, keys: &dyn KeyVerifier) -> Result<()> {
    c.validate_runtime(keys)?;
    validate_profile(c)?;
    Ok(())
}
pub(crate) fn validate_root_uncached(c: &Context, keys: &dyn KeyVerifier) -> Result<()> {
    if c.target.hash.as_deref() != Some(dialect_hash(&c.target).as_str()) {
        return Err(Error::Invalid("installed target hash"));
    }
    let Message::Wrapped {
        wrapper: WrapperType::WithRoles,
        params,
        ..
    } = c.target_root.message()
    else {
        return Err(Error::Invalid("target cast"));
    };
    let cast =
        parse_wrapper_cast(params, &c.target.roles).map_err(|_| Error::Invalid("target cast"))?;
    if cast.dialect_pin != c.target.hash {
        return Err(Error::Invalid("target cast pin"));
    }
    let mut monitor = AdmissionMonitor::new(
        c.target.clone(),
        endpoint(c)?,
        c.target_root.message().clone(),
        Gate { c, keys },
    )
    .map_err(|_| Error::Invalid("target admission context"))?;
    monitor.drain_ready();
    if monitor.state(&ContentHash(c.target_root.id()?)) != Some(&AdmissionState::Accepted) {
        return Err(Error::Invalid("unaccepted target root"));
    }
    Ok(())
}
impl Client {
    pub fn from_certificate(
        c: &Context,
        cert: &Certificate,
        keys: &dyn KeyVerifier,
    ) -> Result<Self> {
        validate_context(c, keys)?;
        cert.verify(c, keys)?;
        let summary = Summary::decode_for(
            &cert.summary,
            c.target.state.as_ref().ok_or(Error::Unsupported)?,
            c.target.causal_protocol.as_ref(),
        )?;
        if summary.clause() != c.target.state.as_ref().ok_or(Error::Unsupported)?
            || summary.hash() != cert.manifest.summary
        {
            return Err(Error::Invalid("summary profile"));
        }
        let mut evidence = Evidence::new();
        evidence.insert(evidence_key(&c.target_root)?, c.target_root.clone());
        Ok(Self {
            context: c.hash(),
            coverage: cert.manifest.coverage,
            summary,
            frontier: cert.manifest.frontier.clone(),
            evidence,
        })
    }
    /// All validation and summary work is staged. Neither failed proofs nor
    /// missing dependencies mutate state, frontier, roots or retained evidence.
    pub fn apply(&mut self, step: &Step, c: &Context, keys: &dyn KeyVerifier) -> Result<()> {
        if self.context != c.hash() {
            return Err(Error::Invalid("client context"));
        }
        let a = step.message.authenticate(keys)?;
        let id = step.message.id()?;
        native_id(&id)?;
        let root_id = c.target_root.id()?;
        shape(step.message.message(), c, id == root_id)?;
        if step
            .message
            .message()
            .innermost_simple()
            .and_then(Message::thread)
            != Some(thread(c)?.0.as_str())
        {
            return Err(Error::Invalid("foreign target thread"));
        }
        if id == root_id && step.message.message() != c.target_root.message() {
            return Err(Error::Invalid("root substitution"));
        }
        step.identity.verify(self.coverage, &id)?;
        let refs = self.summary.query_ids(&a)?;
        let mut missing = Vec::new();
        let provided: Vec<_> = step.replacements.iter().map(|(id, _)| id.clone()).collect();
        if provided.windows(2).any(|w| w[0] >= w[1]) || provided.iter().any(|id| !refs.contains(id))
        {
            return Err(Error::Invalid("replacement footprint"));
        }
        for (id, p) in &step.replacements {
            p.verify(self.coverage, &native(id))?;
        }
        missing.extend(
            refs.iter()
                .filter(|id| !provided.contains(id))
                .map(|s| native(s)),
        );
        let needed: BTreeSet<_> = if step.identity.present {
            BTreeSet::new()
        } else {
            parents(step.message.message())
                .into_iter()
                .filter(|id| id != &root_id)
                .collect()
        };
        let mut store = ThreadedMessageStore::new();
        store.append(
            ContentHash(root_id.clone()),
            thread(c)?,
            c.target_root.message().clone(),
        );
        let mut got = BTreeSet::new();
        let mut last = None;
        for (m, p) in &step.ancestry {
            m.authenticate(keys)?;
            let dep = m.id()?;
            if last.as_ref().is_some_and(|s| s >= &dep) || !needed.contains(&dep) {
                return Err(Error::Invalid("ancestry footprint"));
            }
            last = Some(dep.clone());
            shape(m.message(), c, false)?;
            if m.message().innermost_simple().and_then(Message::thread)
                != Some(thread(c)?.0.as_str())
            {
                return Err(Error::Invalid("foreign ancestry thread"));
            }
            p.verify(self.coverage, &dep)?;
            if !p.present {
                return Err(Error::Invalid("unaccepted ancestry"));
            }
            got.insert(dep.clone());
            store.append(ContentHash(dep), thread(c)?, m.message().clone());
        }
        missing.extend(needed.difference(&got).cloned());
        let next_root = step.identity.updated_root(self.coverage, &id)?;
        let mut summary = self.summary.clone();
        if !step.identity.present {
            let Message::Wrapped { params, .. } = c.target_root.message() else {
                return Err(Error::Invalid("target cast"));
            };
            let cast = parse_wrapper_cast(params, &c.target.roles)
                .map_err(|_| Error::Invalid("target cast"))?;
            // Prior admission and scoped position metadata resume R5 without
            // retrieving old ancestor bodies. Native verification decides this act.
            let resumed = crate::progress_resume::CertifiedProgressPort::from_summary(
                &store,
                &self.summary,
                c,
            )?;
            let verdict = verify_causal_for_role(
                step.message.message(),
                &endpoint(c)?,
                &c.target,
                &cast,
                &resumed,
                &thread(c)?,
                &ContentHash(root_id),
            );
            if matches!(verdict, VerificationResult::Violation(_)) {
                return Err(Error::Invalid("target causal/role admission"));
            }
            if missing.is_empty() && verdict != VerificationResult::Valid {
                return Err(Error::Invalid("unresolved admission footprint"));
            }
            if !missing.is_empty() {
                missing.sort();
                missing.dedup();
                return Err(Error::Missing(missing));
            }
            // Rootless new chains are excluded even when the raw protocol allows begin.
            let ps = parents(step.message.message());
            if ps.is_empty() {
                return Err(Error::Invalid("unrooted target continuation"));
            }
            summary.apply(&a, |address| {
                if address == a.address {
                    return step.identity.present;
                }
                step.replacements
                    .iter()
                    .find(|(id, _)| id == address)
                    .is_some_and(|(_, p)| p.present)
            })?;
        } else if !missing.is_empty() {
            missing.sort();
            missing.dedup();
            return Err(Error::Missing(missing));
        }
        let mut frontier: BTreeSet<_> = self.frontier.iter().cloned().collect();
        if !step.identity.present {
            for p in parents(step.message.message()) {
                frontier.remove(&p);
            }
            frontier.insert(id);
        }
        // No fallible operation remains after the first evidence mutation.
        let mut supplied = Vec::new();
        for m in core::iter::once(&step.message).chain(step.ancestry.iter().map(|(m, _)| m)) {
            supplied.push((evidence_key(m)?, m.clone()));
        }
        for (k, m) in supplied {
            self.evidence.insert(k, m);
        }
        self.summary = summary;
        self.coverage = next_root;
        self.frontier = frontier.into_iter().collect();
        Ok(())
    }
    pub fn floor(&self) -> Floor {
        Floor {
            context: self.context,
            root: self.coverage,
            frontier: self.frontier.clone(),
        }
    }
    pub fn check_floor(&self, floor: &Floor, proofs: &[(String, Proof)]) -> Result<()> {
        if floor.context != self.context {
            return Err(Error::Invalid("floor context"));
        }
        if floor.frontier.is_empty() || floor.frontier.windows(2).any(|w| w[0] >= w[1]) {
            return Err(Error::Invalid("floor frontier"));
        }
        let mut missing = Vec::new();
        if proofs.windows(2).any(|w| w[0].0 >= w[1].0)
            || proofs.iter().any(|(id, _)| !floor.frontier.contains(id))
        {
            return Err(Error::Invalid("floor footprint"));
        }
        for (id, p) in proofs {
            native_id(id)?;
            p.verify(self.coverage, id)?;
            if !p.present {
                return Err(Error::Invalid("local rollback"));
            }
        }
        for id in &floor.frontier {
            native_id(id)?;
            if !proofs.iter().any(|(s, _)| s == id) {
                missing.push(id.clone());
            }
        }
        if !missing.is_empty() {
            return Err(Error::Missing(missing));
        }
        Ok(())
    }
    pub fn retain_from(&mut self, previous: &Client) -> Result<()> {
        if self.context != previous.context {
            return Err(Error::Invalid("evidence context"));
        }
        self.evidence = self.evidence.retaining(&previous.evidence);
        Ok(())
    }
}

/// Durable reconstruction record. `independent` is descriptive, never authority:
/// restoration re-authenticates and re-admits every archived accepted message.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct MemberArchive {
    pub context: Hash,
    pub signer: String,
    pub independent: bool,
    pub accepted: Vec<SignedMessage>,
    pub evidence: Vec<SignedMessage>,
    pub opener: Option<SignedMessage>,
}
/// Physical target-body work on this member's own retained archive. Metadata
/// key checks and maintained roots are not body reads. Replay-created temporary
/// members have their own counters; these counters measure the source archive.
/// Snapshot records count each accepted/evidence body actually copied, including
/// the target genesis; the separately pinned companion opener is excluded.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct MemberWork {
    pub dependency_body_lookups: usize,
    pub prefix_reconstruction_body_reads: usize,
    pub snapshot_body_records: usize,
}

// Keep body storage private to this submodule: Member cannot accidentally bypass
// counters by indexing or iterating a raw map/vector. Acceptance order is ID-only
// metadata, so a selected older cut need not scan all other retained bodies.
mod counted_archive {
    use super::{MemberWork, SignedMessage};
    use alloc::{collections::BTreeMap, string::String, vec::Vec};
    use core::cell::Cell;

    struct Record {
        sequence: usize,
        message: SignedMessage,
    }
    pub(super) struct CountedArchive {
        records: BTreeMap<String, Record>,
        order: Vec<String>,
        work: Cell<MemberWork>,
    }
    impl CountedArchive {
        pub(super) fn new(id: String, message: SignedMessage) -> Self {
            let mut out = Self {
                records: BTreeMap::new(),
                order: Vec::new(),
                work: Cell::new(MemberWork::default()),
            };
            out.insert(id, message);
            out
        }
        pub(super) fn root_id(&self) -> Option<&str> {
            self.order.first().map(String::as_str)
        }
        pub(super) fn contains_key(&self, id: &str) -> bool {
            self.records.contains_key(id)
        }
        pub(super) fn insert(&mut self, id: String, message: SignedMessage) {
            if self.records.contains_key(&id) {
                return;
            }
            let sequence = self.order.len();
            self.order.push(id.clone());
            self.records.insert(id, Record { sequence, message });
        }
        /// Count each attempted body lookup; the normal provider first checks
        /// metadata for missing IDs and reads each named accepted parent once.
        pub(super) fn get(&self, id: &str) -> Option<&SignedMessage> {
            let mut work = self.work.get();
            work.dependency_body_lookups = work.dependency_body_lookups.saturating_add(1);
            self.work.set(work);
            self.records.get(id).map(|r| &r.message)
        }
        pub(super) fn reconstruction(&self, id: &str) -> Option<(usize, &SignedMessage)> {
            let record = self.records.get(id)?;
            let mut work = self.work.get();
            work.prefix_reconstruction_body_reads =
                work.prefix_reconstruction_body_reads.saturating_add(1);
            self.work.set(work);
            Some((record.sequence, &record.message))
        }
        /// Every yielded body is counted, even if a consumer only counts or
        /// filters it rather than cloning it. There is no uncounted body iterator.
        pub(super) fn iter(&self) -> impl Iterator<Item = &SignedMessage> {
            self.order
                .iter()
                .map(move |id| self.reconstruction(id).expect("archive acceptance order").1)
        }
        pub(super) fn snapshot(&self) -> Vec<SignedMessage> {
            self.order
                .iter()
                .map(|id| {
                    let record = self.records.get(id).expect("archive acceptance order");
                    self.snapshot_record();
                    record.message.clone()
                })
                .collect()
        }
        pub(super) fn snapshot_record(&self) {
            let mut work = self.work.get();
            work.snapshot_body_records = work.snapshot_body_records.saturating_add(1);
            self.work.set(work);
        }
        pub(super) fn work(&self) -> MemberWork {
            self.work.get()
        }
        pub(super) fn reset_work(&mut self) {
            self.work.set(MemberWork::default());
        }
    }
}
use counted_archive::CountedArchive;

pub struct Member {
    signer: String,
    client: Client,
    index: Coverage,
    archive: CountedArchive,
    independent: bool,
    opener: Option<SignedMessage>,
}
impl Member {
    pub fn new(c: &Context, signer: &str, keys: &dyn KeyVerifier) -> Result<Self> {
        validate_context(c, keys)?;
        if !c.policy.roster.iter().any(|k| k == signer) {
            return Err(Error::Invalid("member signer"));
        }
        let mut index = Coverage::default();
        let id = c.target_root.id()?;
        let a = c.target_root.authenticate(keys)?;
        let mut summary = Summary::new(
            c.target.state.as_ref().ok_or(Error::Unsupported)?,
            c.target.causal_protocol.as_ref(),
        )?;
        summary.apply(&a, |_| false)?;
        index.insert(&id);
        let evidence = [(evidence_key(&c.target_root)?, c.target_root.clone())]
            .into_iter()
            .collect();
        Ok(Self {
            signer: signer.into(),
            client: Client {
                context: c.hash(),
                coverage: index.root(),
                summary,
                frontier: vec![id.clone()],
                evidence,
            },
            index,
            archive: CountedArchive::new(id, c.target_root.clone()),
            independent: true,
            opener: None,
        })
    }
    pub fn work(&self) -> MemberWork {
        self.archive.work()
    }
    pub fn reset_work(&mut self) {
        self.archive.reset_work();
    }
    pub fn client(&self) -> &Client {
        &self.client
    }
    pub fn coverage(&self) -> &Coverage {
        &self.index
    }
    pub fn signer(&self) -> &str {
        &self.signer
    }
    pub fn signing_eligible(&self) -> bool {
        self.independent
    }
    pub fn manifest(&self, c: &Context) -> Result<Manifest> {
        if self.client.context != c.hash() || !self.independent {
            return Err(Error::Invalid("independent member context"));
        }
        c.manifest(
            self.client.coverage,
            self.client.summary.hash(),
            self.client.frontier.clone(),
        )
    }
    pub fn step(&self, message: &SignedMessage) -> Result<Step> {
        let id = message.id()?;
        let identity = self.index.proof(&id);
        let root = self
            .archive
            .root_id()
            .ok_or(Error::Invalid("member genesis"))?;
        let mut ancestry = Vec::new();
        if !identity.present {
            let needed: BTreeSet<_> = parents(message.message())
                .into_iter()
                .filter(|id| id.as_str() != root)
                .collect();
            let missing: Vec<_> = needed
                .iter()
                .filter(|id| !self.archive.contains_key(id))
                .cloned()
                .collect();
            if !missing.is_empty() {
                return Err(Error::Missing(missing));
            }
            for id in needed {
                let message = self
                    .archive
                    .get(&id)
                    .ok_or_else(|| Error::Missing(vec![id.clone()]))?;
                ancestry.push((message.clone(), self.index.proof(&id)));
            }
        }
        // Footprint construction does not establish authenticity. Client::apply
        // authenticates and recomputes these exact queries against its own cut.
        let simple = message
            .message()
            .innermost_simple()
            .ok_or(Error::Invalid("simple"))?;
        let signer = simple.sender().unwrap_or("");
        let act = Act::from_message(message.message().clone(), signer)
            .map_err(|_| Error::Invalid("act"))?;
        let refs = self.client.summary.query_ids(&act)?;
        let replacements = refs
            .into_iter()
            .map(|id| {
                let p = self.index.proof(&native(&id));
                (id, p)
            })
            .collect();
        Ok(Step {
            message: message.clone(),
            ancestry,
            identity,
            replacements,
        })
    }
    pub fn accept(
        &mut self,
        message: &SignedMessage,
        c: &Context,
        keys: &dyn KeyVerifier,
    ) -> Result<()> {
        if self.client.context != c.hash() {
            return Err(Error::Invalid("member context"));
        }
        message.authenticate(keys)?;
        let step = self.step(message)?;
        self.client.apply(&step, c, keys)?;
        let id = message.id()?;
        if !self.index.contains(&id) {
            self.index.insert(&id);
            self.archive.insert(id, message.clone());
        }
        debug_assert_eq!(self.client.coverage, self.index.root());
        Ok(())
    }
    /// Exact independently maintained current cut: O(frontier + summary), no
    /// historical body scan. An older known cut is explicitly reconstructed.
    pub fn derive(
        &self,
        frontier: &[String],
        c: &Context,
        keys: &dyn KeyVerifier,
    ) -> Result<Manifest> {
        if frontier == self.client.frontier {
            return self.manifest(c);
        }
        if !self.independent || self.client.context != c.hash() {
            return Err(Error::Invalid("member provenance"));
        }
        c.manifest(
            self.client.coverage,
            self.client.summary.hash(),
            frontier.to_vec(),
        )?;
        let mut selected = BTreeSet::new();
        let mut selected_bodies = Vec::new();
        let mut todo = frontier.to_vec();
        while let Some(id) = todo.pop() {
            if !selected.insert(id.clone()) {
                continue;
            }
            let (sequence, m) = self
                .archive
                .reconstruction(&id)
                .ok_or_else(|| Error::Missing(vec![id.clone()]))?;
            todo.extend(parents(m.message()));
            selected_bodies.push((sequence, id, m.clone()));
        }
        let root = c.target_root.id()?;
        if !selected.contains(&root) {
            return Err(Error::Invalid("unrooted proposed cut"));
        }
        selected_bodies.sort_by_key(|(sequence, _, _)| *sequence);
        let mut fresh = Self::new(c, &self.signer, keys)?;
        for (_, id, m) in selected_bodies {
            if id != root {
                fresh.accept(&m, c, keys)?;
            }
        }
        if fresh.client.frontier != frontier {
            return Err(Error::Invalid("redundant cut frontier"));
        }
        fresh.manifest(c)
    }
    /// Explicit whole-prefix negative control and independent audit. Unlike
    /// current-cut publication this intentionally reads every archived target
    /// body, re-authenticates it, and recomputes the maintained cut from genesis.
    /// Work is observable on this source member even when replay returns an error.
    pub fn audit_replay(&self, c: &Context, keys: &dyn KeyVerifier) -> Result<Manifest> {
        if !self.independent || self.client.context != c.hash() {
            return Err(Error::Invalid("member provenance"));
        }
        let mut fresh = Self::new(c, &self.signer, keys)?;
        let root = c.target_root.id()?;
        for message in self.archive.iter() {
            if message.id()? != root {
                fresh.accept(message, c, keys)?;
            }
        }
        fresh.manifest(c)
    }
    pub fn snapshot(&self) -> MemberArchive {
        MemberArchive {
            context: self.client.context,
            signer: self.signer.clone(),
            independent: self.independent,
            accepted: self.archive.snapshot(),
            evidence: self
                .client
                .evidence
                .iter()
                .map(|(_, m)| {
                    self.archive.snapshot_record();
                    m.clone()
                })
                .collect(),
            opener: self.opener.clone(),
        }
    }
    pub fn restore(record: &MemberArchive, c: &Context, keys: &dyn KeyVerifier) -> Result<Self> {
        if record.context != c.hash()
            || !record.independent
            || record.accepted.first() != Some(&c.target_root)
        {
            return Err(Error::Invalid("independent archive genesis"));
        }
        let mut member = Self::new(c, &record.signer, keys)?;
        for m in record.accepted.iter().skip(1) {
            member.accept(m, c, keys)?;
        }
        for m in &record.evidence {
            // Evidence can only be imported for independently reconstructed IDs.
            if !member.index.contains(&m.id()?) {
                return Err(Error::Invalid("archive evidence acceptance"));
            }
            member.accept(m, c, keys)?;
        }
        if let Some(opener) = &record.opener {
            member.pin_opener(opener, c, keys)?;
        }
        Ok(member)
    }
    fn authorize_payload(
        &self,
        manifest: &Manifest,
        unsigned: Message,
        c: &Context,
        keys: &dyn KeyVerifier,
    ) -> Result<EndorsementCapability> {
        if self.derive(&manifest.frontier, c, keys)? != *manifest {
            return Err(Error::Invalid("independent proposal mismatch"));
        }
        // Existing native machinery recognizes the exact prospective message;
        // this verifier never produces a real signature while authorizing.
        let preview = SignedMessage::sign(unsigned.clone(), &self.signer, &Preview)?;
        let act = preview.authenticate(&Preview)?;
        let d = cbcl_parser::checkpoint_dialect::builtin()
            .map_err(|_| Error::Invalid("checkpoint dialect"))?;
        let Message::Wrapped {
            wrapper: WrapperType::Signed,
            content,
            ..
        } = preview.message()
        else {
            return Err(Error::Invalid("endorsement wrapper"));
        };
        let Message::Dialect {
            dialect_name,
            inner,
        } = content.as_ref()
        else {
            return Err(Error::Invalid("endorsement language"));
        };
        if dialect_name != &d.name {
            return Err(Error::Invalid("endorsement language pin"));
        }
        let Message::Simple { params, .. } = inner.as_ref() else {
            return Err(Error::Invalid("endorsement simple"));
        };
        let declared = cbcl_core::r7::declared_keywords(&d.shapes, "endorse");
        let mut seen = BTreeSet::new();
        if params.len() % 2 != 0 {
            return Err(Error::Invalid("endorsement keyword grammar"));
        }
        for p in params.chunks_exact(2) {
            let SExpr::Atom(Atom::Keyword(k)) = &p[0] else {
                return Err(Error::Invalid("endorsement keyword grammar"));
            };
            if !seen.insert(k)
                || ["thread", "sender", "caused-by"].contains(&k.as_str())
                || (!declared.contains(k)
                    && !cbcl_core::state::ROUTING_KEYWORDS.contains(&k.as_str()))
            {
                return Err(Error::Invalid("endorsement closed fields"));
            }
        }
        if act.verb != "endorse" || act.signer != self.signer {
            return Err(Error::Invalid("endorsement verb/signer"));
        }
        check_scope(&act, c, Some(manifest.hash()))?;
        cbcl_core::r7::verify_state_shape(&d, preview.message())
            .map_err(|_| Error::Invalid("endorsement shape"))?;
        for s in d.shapes.iter().filter(|s| s.performative == "endorse") {
            s.check(&SExpr::from(
                preview
                    .message()
                    .innermost_simple()
                    .ok_or(Error::Invalid("endorsement simple"))?
                    .clone(),
            ))
            .map_err(|_| Error::Invalid("endorsement shape"))?;
        }
        if act.predecessors.len() != 1 {
            return Err(Error::Invalid("endorsement parent"));
        }
        native_id(&act.predecessors[0])?;
        Ok(EndorsementCapability {
            unsigned,
            signer: self.signer.clone(),
        })
    }

    /// Pin the authenticated companion opener for the argument-free managed
    /// signing path. Changing this pin requires a new member/context lifecycle.
    pub fn pin_opener(
        &mut self,
        opener: &SignedMessage,
        c: &Context,
        keys: &dyn KeyVerifier,
    ) -> Result<()> {
        if self.client.context != c.hash() {
            return Err(Error::Invalid("member context"));
        }
        validate_opener(opener, c, keys)?;
        if self.opener.as_ref().is_some_and(|old| old != opener) {
            return Err(Error::Invalid("companion opener already pinned"));
        }
        self.opener = Some(opener.clone());
        Ok(())
    }
    pub fn authorize_endorse(
        &self,
        manifest: &Manifest,
        unsigned: Message,
        c: &Context,
        keys: &dyn KeyVerifier,
    ) -> Result<EndorsementCapability> {
        let opener = self
            .opener
            .as_ref()
            .ok_or(Error::Invalid("companion opener not pinned"))?;
        self.authorize_endorse_with_opener(manifest, unsigned, opener, c, keys)
    }
    /// Bind signing to the independently authenticated native companion bootstrap.
    pub fn authorize_endorse_with_opener(
        &self,
        manifest: &Manifest,
        unsigned: Message,
        opener: &SignedMessage,
        c: &Context,
        keys: &dyn KeyVerifier,
    ) -> Result<EndorsementCapability> {
        let capability = self.authorize_payload(manifest, unsigned, c, keys)?;
        let d = cbcl_parser::checkpoint_dialect::builtin()
            .map_err(|_| Error::Invalid("checkpoint dialect"))?;
        if self.opener.as_ref().is_some_and(|old| old != opener) {
            return Err(Error::Invalid("companion opener pin"));
        }
        validate_opener(opener, c, keys)?;
        let preview =
            SignedMessage::sign(capability.unsigned.clone(), &capability.signer, &Preview)?;
        if parents(preview.message()) != vec![opener.id()?] {
            return Err(Error::Invalid("endorsement opener pin"));
        }
        let Message::Wrapped { params, .. } = c.companion_root.message() else {
            return Err(Error::Invalid("companion cast"));
        };
        let cast =
            parse_wrapper_cast(params, &d.roles).map_err(|_| Error::Invalid("companion cast"))?;
        let thread = ThreadId(
            c.companion_root
                .message()
                .innermost_simple()
                .and_then(Message::thread)
                .ok_or(Error::Invalid("companion thread"))?
                .into(),
        );
        if preview
            .message()
            .innermost_simple()
            .and_then(Message::thread)
            != Some(thread.0.as_str())
        {
            return Err(Error::Invalid("endorsement thread"));
        }
        let mut store = ThreadedMessageStore::new();
        for m in [&c.companion_root, opener] {
            store.append(ContentHash(m.id()?), thread.clone(), m.message().clone());
        }
        let endpoint = Endpoint {
            role: "member".into(),
            occupant: Some(cbcl_core::role::AgentKey(self.signer.clone())),
        };
        if verify_causal_for_role(
            preview.message(),
            &endpoint,
            &d,
            &cast,
            &store,
            &thread,
            &ContentHash(c.companion_root.id()?),
        ) != VerificationResult::Valid
        {
            return Err(Error::Invalid("endorsement native admission"));
        }
        Ok(capability)
    }
}
fn validate_opener(opener: &SignedMessage, c: &Context, keys: &dyn KeyVerifier) -> Result<()> {
    let d = cbcl_parser::checkpoint_dialect::builtin()
        .map_err(|_| Error::Invalid("checkpoint dialect"))?;
    let a = opener.authenticate(keys)?;
    crate::certificate::verify_coordination(
        opener,
        c,
        &d,
        core::slice::from_ref(&c.companion_root),
        keys,
    )?;
    check_scope(&a, c, None)?;
    if a.verb != "open"
        || a.predecessors != vec![c.companion_root.id()?]
        || a.fields.get("version") != Some(&SExpr::Atom(Atom::Num(1)))
    {
        return Err(Error::Invalid("companion opener"));
    }
    Ok(())
}
/// Opaque, non-deserializable authority for exactly one unsigned native message
/// and signer. Arbitrary serialized flags cannot manufacture signing authority.
pub struct EndorsementCapability {
    unsigned: Message,
    signer: String,
}
impl EndorsementCapability {
    pub fn sign(self, keys: &dyn KeySigner) -> Result<SignedMessage> {
        SignedMessage::sign(self.unsigned, &self.signer, keys)
    }
    pub fn signer(&self) -> &str {
        &self.signer
    }
    pub fn unsigned(&self) -> &Message {
        &self.unsigned
    }
}
struct Preview;
impl KeyVerifier for Preview {
    fn verify(&self, _: &str, _: &[u8], _: &[u8]) -> bool {
        true
    }
}
impl KeySigner for Preview {
    fn sign(&self, _: &str, _: &[u8]) -> Result<Vec<u8>> {
        Ok(vec![0; 64])
    }
}

#[cfg(test)]
#[path = "member_tests.rs"]
mod tests;
