//! Admission experiment. No production monitor seeding or weakened core checks.
//! Cached accepted-set roots are an explicit trust boundary, not validity proofs.
use super::{digest, encoded, Coverage, Hash, Op, Proof, Result, Summary};
use crate::drawing_fixture::{self as fixture, Fixture, Gate, Wire};
use cbcl_core::{
    admission::{AdmissionMonitor, AdmissionState},
    canonical::dialect_hash,
    dialect::Dialect,
    envelope::{OpenedEnvelope, HEADER_FIELDS},
    keyid::{KeyId, SignatureSuite},
    message::{CausedBy, Message},
    projection::verify_causal_for_role,
    protocol::VerificationResult,
    sexpr::{Atom, SExpr},
    state::{self, Act},
    store::{ContentHash, MessageStore, ThreadId, ThreadedMessageStore},
    typed_addr::{self, FieldId},
};
use ed25519_dalek::{Signature, Signer, SigningKey, VerifyingKey};
use serde::{Deserialize, Serialize};
use std::{
    cell::Cell,
    collections::{BTreeMap, BTreeSet},
    time::Instant,
};

pub(super) mod cached;

fn address(native: &str) -> String {
    native.replacen("sha256:", "sha256-", 1)
}
fn render_state(summary: &Summary, dialect: &Dialect) -> String {
    let acts: Vec<_> = summary
        .live
        .iter()
        .map(|(id, w)| {
            let mut act = super::operation(&w.key, &w.value, false, &[], 0).act();
            act.address = id.clone();
            act
        })
        .collect();
    state::render_json(&state::fold(
        dialect.state.as_ref().unwrap(),
        dialect.causal_protocol.as_ref(),
        &acts,
    ))
}
fn projection(wire: &Wire) -> Result<Option<Op>> {
    let act = wire.act();
    if act.verb == "open" {
        return Ok(None);
    }
    if act.verb != "paint" && act.verb != "erase" {
        return Err("not a drawing operation".into());
    }
    let field = |key: &str| match act.fields.get(key) {
        Some(SExpr::Atom(Atom::Str(s))) => Ok(s.clone()),
        _ => Err(format!("missing string {key}")),
    };
    let replaces = match act.fields.get("replaces") {
        Some(SExpr::List(items)) => items
            .iter()
            .map(|x| match x {
                SExpr::Atom(Atom::Symbol(s) | Atom::Str(s)) => Ok(s.clone()),
                _ => Err("bad replacement address".to_string()),
            })
            .collect::<Result<Vec<_>>>()?,
        _ => return Err("missing replacements".into()),
    };
    Ok(Some(Op {
        id: act.address,
        key: field("shape")?,
        value: if act.verb == "paint" {
            field("value")?
        } else {
            String::new()
        },
        delete: act.verb == "erase",
        replaces,
        nonce: 0,
    }))
}

struct Config<'a> {
    fixture: &'a Fixture,
    roster: Vec<VerifyingKey>,
    context: Hash,
}
impl<'a> Config<'a> {
    fn new(f: &'a Fixture) -> Self {
        let roster = fixture::roster(&f.keys);
        let context = digest(
            b"drawing-admission-context-v1",
            &encoded(&(
                dialect_hash(&f.dialect),
                &f.root.message,
                roster
                    .iter()
                    .map(VerifyingKey::to_bytes)
                    .collect::<Vec<_>>(),
            )),
        );
        Self {
            fixture: f,
            roster,
            context,
        }
    }
    fn empty_store(&self) -> Result<ThreadedMessageStore> {
        let monitor = replay(self.fixture, &[])?;
        Ok(monitor.accepted().clone())
    }
    fn thread(&self) -> ThreadId {
        ThreadId(
            self.fixture
                .root
                .message
                .innermost_simple()
                .unwrap()
                .thread()
                .unwrap()
                .into(),
        )
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Cut {
    context: Hash,
    coverage: Hash,
    summary: Hash,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Vote {
    member: usize,
    signature: Vec<u8>,
}
fn vote(cut: &Cut, member: usize, key: &SigningKey) -> Vote {
    Vote {
        member,
        signature: key.sign(&encoded(cut)).to_bytes().to_vec(),
    }
}
fn check_vote(cut: &Cut, vote: &Vote, config: &Config<'_>) -> Result<()> {
    if cut.context != config.context {
        return Err("wrong drawing context".into());
    }
    let key = config.roster.get(vote.member).ok_or("untrusted member")?;
    let sig = Signature::from_slice(&vote.signature).map_err(|_| "bad signature encoding")?;
    key.verify_strict(&encoded(cut), &sig)
        .map_err(|_| "invalid checkpoint endorsement".into())
}
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Certified {
    cut: Cut,
    state: Summary,
    votes: Vec<Vote>,
}
impl Certified {
    fn open(&self, config: &Config<'_>) -> Result<Client> {
        if config.roster.len() != 4 || self.votes.len() < 3 || self.votes.len() > 4 {
            return Err("three of four endorsements required".into());
        }
        let mut seen = BTreeSet::new();
        for v in &self.votes {
            if !seen.insert(v.member) {
                return Err("duplicate endorsement".into());
            }
            check_vote(&self.cut, v, config)?;
        }
        Client::new(self.state.clone(), &self.cut, config)
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct HeaderRecord {
    envelope: OpenedEnvelope,
    cause: Option<CausedBy>,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct EnvelopeEvidence {
    header: HeaderRecord,
    coverage: Proof,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Step {
    wire: Wire,
    identity: Proof,
    replacements: Vec<Proof>,
    ancestry: Vec<EnvelopeEvidence>,
}
struct KeyVerifier(VerifyingKey);
impl cbcl_core::r4::Signer for KeyVerifier {
    fn sign(&self, _: &[u8]) -> Vec<u8> {
        panic!("verification-only key")
    }
    fn verify(&self, data: &[u8], sig: &[u8]) -> bool {
        Signature::from_slice(sig).is_ok_and(|sig| self.0.verify_strict(data, &sig).is_ok())
    }
}
fn opened(wire: &Wire) -> HeaderRecord {
    let simple = wire.message.innermost_simple().unwrap();
    HeaderRecord {
        envelope: OpenedEnvelope {
            root: wire.id(),
            suite: SignatureSuite::Ed25519,
            signature: wire.root_signature.clone(),
            openings: HEADER_FIELDS
                .iter()
                .map(|&field| typed_addr::open(simple, field))
                .collect(),
        },
        cause: simple.caused_by().cloned(),
    }
}
fn cause_field(config: &Config<'_>, cause: &Option<CausedBy>) -> SExpr {
    let mut simple = config
        .fixture
        .root
        .message
        .innermost_simple()
        .unwrap()
        .clone();
    if let Message::Simple { caused_by, .. } = &mut simple {
        *caused_by = cause.clone();
    }
    typed_addr::field_sexpr(&simple, FieldId::CausedBy)
}

struct Client {
    context: Hash,
    state: Summary,
    coverage: Hash,
    store: ThreadedMessageStore,
    // The core store retains Message, while these fixtures carry real detached
    // signatures separately. Keep both so evidence remains independently checkable.
    signed_bodies: BTreeMap<String, Wire>,
}
/// Read-only verifier view; staging a few openings must not clone retained history.
struct Layered<'a> {
    base: &'a ThreadedMessageStore,
    staged: &'a ThreadedMessageStore,
}
impl MessageStore for Layered<'_> {
    fn lookup(&self, h: &ContentHash) -> Option<&Message> {
        self.base.lookup(h).or_else(|| self.staged.lookup(h))
    }
    fn lookup_in_thread(&self, h: &ContentHash, t: &ThreadId) -> Option<&Message> {
        self.base
            .lookup_in_thread(h, t)
            .or_else(|| self.staged.lookup_in_thread(h, t))
    }
    fn contains(&self, h: &ContentHash, t: &ThreadId) -> bool {
        self.staged.contains(h, t) || self.base.contains(h, t)
    }
    fn append(&mut self, _: ContentHash, _: ThreadId, _: Message) -> bool {
        panic!("read-only verifier view")
    }
    fn opened_in_thread(&self, h: &ContentHash, t: &ThreadId) -> Option<&OpenedEnvelope> {
        self.staged
            .opened_in_thread(h, t)
            .or_else(|| self.base.opened_in_thread(h, t))
    }
    fn frontier(&self, t: &ThreadId) -> Vec<&ContentHash> {
        let candidates: Vec<_> = self
            .base
            .frontier(t)
            .into_iter()
            .chain(self.staged.frontier(t))
            .collect();
        let mut seen = BTreeSet::new();
        candidates
            .iter()
            .copied()
            .filter(|h| {
                seen.insert((*h).clone())
                    && !candidates
                        .iter()
                        .any(|other| other != h && self.causal_closure(other, t).contains(h))
            })
            .collect()
    }
    fn causal_closure(&self, h: &ContentHash, t: &ThreadId) -> Vec<ContentHash> {
        if !self.contains(h, t) {
            return vec![];
        }
        let mut todo = vec![h.clone()];
        let mut seen = BTreeSet::new();
        let mut out = Vec::new();
        while let Some(h) = todo.pop() {
            if !seen.insert(h.clone()) {
                continue;
            }
            if let Some(m) = self.lookup_in_thread(&h, t) {
                match m.caused_by() {
                    Some(CausedBy::Single(p)) => todo.push(ContentHash(p.clone())),
                    Some(CausedBy::Multiple(ps)) => {
                        todo.extend(ps.iter().cloned().map(ContentHash))
                    }
                    _ => {}
                }
            }
            out.push(h);
        }
        out
    }
}
fn member_key(env: &OpenedEnvelope, config: &Config<'_>) -> Result<VerifyingKey> {
    let from = env
        .from_spelling()
        .and_then(|s| KeyId::parse(s).ok())
        .ok_or("missing envelope signer")?;
    let member = (0..config.roster.len())
        .find(|i| KeyId::parse(&format!("@m{i}")).ok().as_ref() == Some(&from))
        .ok_or("unknown dependency signer")?;
    Ok(config.roster[member])
}
impl Client {
    fn new(state: Summary, cut: &Cut, config: &Config<'_>) -> Result<Self> {
        if cut.context != config.context || state.hash() != cut.summary {
            return Err("checkpoint state/context mismatch".into());
        }
        Ok(Self {
            context: config.context,
            state,
            coverage: cut.coverage,
            store: config.empty_store()?,
            signed_bodies: [(config.fixture.root.id(), config.fixture.root.clone())]
                .into_iter()
                .collect(),
        })
    }
    fn admit(&mut self, step: &Step, config: &Config<'_>) -> Result<VerificationResult> {
        if self.context != config.context {
            return Err("client belongs to another pinned context".into());
        }
        let act = step
            .wire
            .authenticate(&config.fixture.dialect, &config.roster)?;
        step.identity.check(self.coverage, &act.address)?;
        let op = projection(&step.wire)?;
        let refs = op.as_ref().map_or(&[][..], |o| o.replaces.as_slice());
        if step.replacements.len() != refs.len() {
            return Err("replacement witness arity".into());
        }
        let next_root = if step.identity.present {
            self.coverage
        } else {
            step.identity.root(&act.address, true)?
        };
        for (r, p) in refs.iter().zip(&step.replacements) {
            p.check(next_root, r)?;
        }
        // Stage both shelves and state. Invalid/unknown input cannot consume budget.
        let mut staged = ThreadedMessageStore::new();
        for e in &step.ancestry {
            let env = &e.header.envelope;
            if !e.coverage.present || env.thread() != Some(config.thread().0.as_str()) {
                return Err("uncovered or foreign dependency".into());
            }
            e.coverage
                .check(self.coverage, &address(env.content_hash()))?;
            if env.openings.iter().map(|o| o.field).collect::<Vec<_>>() != HEADER_FIELDS {
                return Err("exact header fields required".into());
            }
            if env.opening(FieldId::CausedBy).map(|o| &o.value)
                != Some(&cause_field(config, &e.header.cause))
            {
                return Err("causal field mismatch".into());
            }
            staged
                .append_opened(env.clone(), &KeyVerifier(member_key(env, config)?))
                .map_err(|e| format!("invalid dependency envelope: {e:?}"))?;
        }
        if step.identity.present {
            // Existing acceptance comes from the authenticated cut. Do not refold.
            self.retain_evidence(step, config)?;
            return Ok(VerificationResult::Valid);
        }
        let store = Layered {
            base: &self.store,
            staged: &staged,
        };
        let simple = step
            .wire
            .message
            .innermost_simple()
            .ok_or("missing simple message")?;
        let parents = predecessors(simple);
        if parents.is_empty() {
            return Err("non-root requires explicit predecessors".into());
        }
        if parents.iter().any(|p| {
            store
                .lookup_in_thread(&ContentHash(p.clone()), &config.thread())
                .is_none()
                && store
                    .opened_in_thread(&ContentHash(p.clone()), &config.thread())
                    .is_none()
        }) {
            return Ok(VerificationResult::Unknown);
        }
        let Message::Wrapped { params, .. } = &config.fixture.root.message else {
            return Err("missing cast".into());
        };
        let cast = cbcl_core::role::parse_wrapper_cast(params, &config.fixture.dialect.roles)
            .map_err(|e| format!("{e}"))?;
        let verdict = verify_causal_for_role(
            &step.wire.message,
            &fixture::endpoint(),
            &config.fixture.dialect,
            &cast,
            &store,
            &config.thread(),
            &ContentHash(config.fixture.root.id()),
        );
        if verdict != VerificationResult::Valid {
            return Ok(verdict);
        }
        let mut state = self.state.clone();
        if let Some(op) = op {
            state.apply(&op, &step.replacements, next_root)?;
        }
        self.retain_evidence(step, config)?;
        self.state = state;
        self.coverage = next_root;
        Ok(verdict)
    }
    fn retain_evidence(&mut self, step: &Step, config: &Config<'_>) -> Result<()> {
        // All checks have succeeded. Preserve supplied bodies for accountability.
        for e in &step.ancestry {
            let env = &e.header.envelope;
            self.store
                .append_opened(env.clone(), &KeyVerifier(member_key(env, config)?))
                .map_err(|e| format!("retention failed: {e:?}"))?;
        }
        self.store.append(
            ContentHash(step.wire.id()),
            config.thread(),
            step.wire.message.clone(),
        );
        self.signed_bodies.insert(step.wire.id(), step.wire.clone());
        Ok(())
    }
    fn retained_body_stats(&self) -> (usize, usize) {
        (
            self.signed_bodies.len(),
            encoded(&self.signed_bodies.values().collect::<Vec<_>>()).len(),
        )
    }
}
fn predecessors(message: &Message) -> Vec<String> {
    match message.innermost_simple().and_then(Message::caused_by) {
        Some(CausedBy::Single(s)) => vec![s.clone()],
        Some(CausedBy::Multiple(s)) => s.clone(),
        _ => vec![],
    }
}

/// Provider retains all metadata and payloads; counters distinguish actual reads.
struct Archive {
    headers: BTreeMap<String, HeaderRecord>,
    bodies: BTreeMap<String, Wire>,
    header_reads: Cell<usize>,
    body_reads: Cell<usize>,
    header_bytes: Cell<usize>,
}
impl Archive {
    fn new(f: &Fixture) -> Self {
        Self {
            headers: f.edits.iter().map(|w| (w.id(), opened(w))).collect(),
            bodies: f.edits.iter().map(|w| (w.id(), w.clone())).collect(),
            header_reads: Cell::new(0),
            body_reads: Cell::new(0),
            header_bytes: Cell::new(0),
        }
    }
    fn header(&self, id: &str) -> Result<HeaderRecord> {
        let h = self
            .headers
            .get(id)
            .ok_or("missing archive header")?
            .clone();
        self.header_reads.set(self.header_reads.get() + 1);
        self.header_bytes
            .set(self.header_bytes.get() + encoded(&h).len());
        Ok(h)
    }
    fn body(&self, id: &str) -> Result<Wire> {
        self.body_reads.set(self.body_reads.get() + 1);
        self.bodies
            .get(id)
            .cloned()
            .ok_or("missing archive payload".into())
    }
    fn reset(&self) {
        self.header_reads.set(0);
        self.body_reads.set(0);
        self.header_bytes.set(0);
    }
    fn evidence(
        &self,
        wire: &Wire,
        coverage: &Coverage,
        known: &mut BTreeSet<String>,
        root: &str,
    ) -> Result<Vec<EnvelopeEvidence>> {
        let mut todo = predecessors(&wire.message);
        let mut result = Vec::new();
        while let Some(id) = todo.pop() {
            if id == root || !known.insert(id.clone()) {
                continue;
            }
            let header = self.header(&id)?;
            let proof = coverage.proof(&address(&id));
            if !proof.present {
                return Err("dependency was not accepted at this cut".into());
            }
            match &header.cause {
                Some(CausedBy::Single(s)) => todo.push(s.clone()),
                Some(CausedBy::Multiple(s)) => todo.extend(s.iter().cloned()),
                _ => {}
            }
            result.push(EnvelopeEvidence {
                header,
                coverage: proof,
            });
        }
        Ok(result)
    }
}

#[derive(Clone)]
struct Producer {
    state: Summary,
    coverage: Coverage,
}
impl Producer {
    fn new(f: &Fixture) -> Self {
        let mut coverage = Coverage::new();
        coverage.insert(&address(&f.root.id()));
        Self {
            state: Summary::default(),
            coverage,
        }
    }
    fn cut(&self, config: &Config<'_>) -> Cut {
        Cut {
            context: config.context,
            coverage: self.coverage.root(),
            summary: self.state.hash(),
        }
    }
    fn step(
        &mut self,
        wire: &Wire,
        archive: &Archive,
        known: &mut BTreeSet<String>,
        root: &str,
    ) -> Result<Step> {
        let id = address(&wire.id());
        let identity = self.coverage.proof(&id);
        let ancestry = if identity.present {
            vec![]
        } else {
            archive.evidence(wire, &self.coverage, known, root)?
        };
        if !identity.present {
            self.coverage.insert(&id);
        }
        let op = projection(wire)?;
        let replacements = op.as_ref().map_or(vec![], |o| {
            o.replaces.iter().map(|r| self.coverage.proof(r)).collect()
        });
        if !identity.present {
            if let Some(op) = op {
                self.state.apply(&op, &replacements, self.coverage.root())?;
            }
        }
        known.insert(wire.id());
        Ok(Step {
            wire: wire.clone(),
            identity,
            replacements,
            ancestry,
        })
    }
}
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Anchor {
    cut: Cut,
    vote: Vote,
    state: Summary,
    bridge: Vec<Step>,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Reconstructed {
    target: Cut,
    anchors: Vec<Anchor>,
}
impl Reconstructed {
    fn open(&self, config: &Config<'_>) -> Result<Client> {
        if self.anchors.len() != config.roster.len() || config.roster.len() != 4 {
            return Err("all pinned member views required".into());
        }
        let mut seen = BTreeSet::new();
        let mut result = Client::new(self.anchors[0].state.clone(), &self.anchors[0].cut, config)?;
        for a in &self.anchors {
            if !seen.insert(a.vote.member) {
                return Err("duplicate member view".into());
            }
            check_vote(&a.cut, &a.vote, config)?;
            let mut client = Client::new(a.state.clone(), &a.cut, config)?;
            for step in &a.bridge {
                if client.admit(step, config)? != VerificationResult::Valid {
                    return Err("bridge admission failed".into());
                }
            }
            if client.coverage != self.target.coverage
                || client.state.hash() != self.target.summary
                || self.target.context != config.context
            {
                return Err("reconstruction differs from target".into());
            }
            // Retain evidence encountered in every bridge, independently of order.
            for step in &a.bridge {
                result.retain_evidence(step, config)?;
            }
            result.state = client.state;
            result.coverage = client.coverage;
        }
        Ok(result)
    }
}

fn replay(f: &Fixture, edits: &[Wire]) -> Result<AdmissionMonitor<Gate>> {
    let roster = fixture::roster(&f.keys);
    let wires: Vec<_> = std::iter::once(f.root.clone())
        .chain(edits.iter().cloned())
        .collect();
    let gate = Gate::new(&f.dialect, &roster, &wires);
    for wire in &wires {
        gate.check_attempt(wire)?;
    }
    let mut m = AdmissionMonitor::new(
        f.dialect.clone(),
        fixture::endpoint(),
        f.root.message.clone(),
        gate,
    )
    .map_err(|e| format!("root: {e:?}"))?;
    m.drain_ready();
    for w in edits {
        m.receive(w.message.clone())
            .map_err(|e| format!("receive: {e:?}"))?;
        m.drain_ready();
    }
    Ok(m)
}
fn folded(f: &Fixture, monitor: &AdmissionMonitor<Gate>, edits: &[Wire]) -> String {
    let acts: Vec<Act> = edits
        .iter()
        .filter(|w| monitor.state(&ContentHash(w.id())) == Some(&AdmissionState::Accepted))
        .map(Wire::act)
        .collect();
    state::render_json(&state::fold(
        f.dialect.state.as_ref().unwrap(),
        f.dialect.causal_protocol.as_ref(),
        &acts,
    ))
}

fn packages(
    f: &Fixture,
    lag: usize,
    archive: &Archive,
) -> Result<(Certified, Reconstructed, Producer)> {
    let config = Config::new(f);
    let full = replay(f, &f.edits)?;
    for w in &f.edits {
        if full.state(&ContentHash(w.id())) != Some(&AdmissionState::Accepted) {
            return Err(format!(
                "fixture not admitted: {:?}",
                full.state(&ContentHash(w.id()))
            ));
        }
    }
    let target = f.edits.len();
    let old = target - lag;
    let mut p = Producer::new(f);
    let mut stale = None;
    let mut common_known = BTreeSet::new();
    for (i, w) in f.edits.iter().enumerate() {
        if i == old {
            stale = Some(p.clone());
        }
        p.step(w, archive, &mut common_known, &f.root.id())?;
    }
    if old == target {
        stale = Some(p.clone());
    }
    let cut = p.cut(&config);
    let certified = Certified {
        cut: cut.clone(),
        state: p.state.clone(),
        votes: (0..3).map(|i| vote(&cut, i, &f.keys[i])).collect(),
    };
    let mut anchors: Vec<_> = (0..3)
        .map(|i| Anchor {
            cut: cut.clone(),
            vote: vote(&cut, i, &f.keys[i]),
            state: p.state.clone(),
            bridge: vec![],
        })
        .collect();
    let mut s = stale.ok_or("invalid lag")?;
    let old_cut = s.cut(&config);
    let mut a = Anchor {
        cut: old_cut.clone(),
        vote: vote(&old_cut, 3, &f.keys[3]),
        state: s.state.clone(),
        bridge: vec![],
    };
    let mut known = BTreeSet::new();
    for w in &f.edits[old..] {
        a.bridge.push(s.step(w, archive, &mut known, &f.root.id())?);
    }
    anchors.push(a);
    assert_eq!(
        render_state(&p.state, &f.dialect),
        folded(f, &full, &f.edits)
    );
    Ok((
        certified,
        Reconstructed {
            target: cut,
            anchors,
        },
        p,
    ))
}

fn tail(f: &Fixture, lag: usize) -> Vec<Wire> {
    let offline = f.edits.len() - lag;
    let depth = (f.dialect.causal_protocol.as_ref().unwrap().steps.len() - 2) / 2;
    let valid_parent = |end: usize| (0..end).rev().find(|i| *i == 0 || i % depth != 0).unwrap();
    let old = &f.edits[valid_parent(offline)];
    let recent = &f.edits[valid_parent(f.edits.len())];
    let old_act = old.act();
    let key = old_act
        .fields
        .get("shape")
        .and_then(|v| {
            if let SExpr::Atom(Atom::Str(s)) = v {
                Some(s.as_str())
            } else {
                None
            }
        })
        .unwrap_or("shape-0");
    vec![
        fixture::edit(
            key,
            "{\"colour\":\"offline-red\",\"x\":42,\"y\":18}",
            false,
            &[old.act().address],
            &old.id(),
            90001,
            3,
            &f.keys,
        ),
        fixture::edit(
            "shape-0",
            "{\"colour\":\"online-blue\",\"x\":5,\"y\":7}",
            false,
            &[recent.act().address],
            &recent.id(),
            90002,
            0,
            &f.keys,
        ),
    ]
}

pub(super) fn run() {
    let mut rows = Vec::new();
    for (n, depth, lag) in [(120, 8, 2), (1000, 8, 2), (1000, 8, 800), (1000, 32, 800)] {
        let f = Fixture::new(n, depth, lag);
        let config = Config::new(&f);
        let archive = Archive::new(&f);
        let (cert, recon, p) = packages(&f, lag, &archive).unwrap();
        let mut provider = p.clone();
        let mut known = BTreeSet::new();
        archive.reset();
        let tails = tail(&f, lag);
        let steps: Vec<_> = tails
            .iter()
            .map(|w| {
                provider
                    .step(w, &archive, &mut known, &f.root.id())
                    .unwrap()
            })
            .collect();
        let tail_headers = archive.header_reads.get();
        let tail_header_bytes = archive.header_bytes.get();
        let tail_bodies = archive.body_reads.get();
        let mut all = f.edits.clone();
        all.extend(tails.clone());
        let expected_monitor = replay(&f, &all).unwrap();
        let expected = folded(&f, &expected_monitor, &all);
        let cert_bytes = encoded(&(&cert, &steps));
        let recon_bytes = encoded(&(&recon, &steps));
        let mut timings = [Vec::new(), Vec::new(), Vec::new()];
        let mut retained_bodies = [(0, 0), (0, 0)];
        archive.reset();
        let mut replay_input: Vec<_> = f
            .edits
            .iter()
            .map(|w| archive.body(&w.id()).unwrap())
            .collect();
        replay_input.extend(tails.clone());
        let replay_body_reads = archive.body_reads.get();
        let replay_bytes = encoded(&replay_input);
        for _ in 0..3 {
            let start = Instant::now();
            let (s, t): (Certified, Vec<Step>) = serde_json::from_slice(&cert_bytes).unwrap();
            let mut c = s.open(&config).unwrap();
            for x in &t {
                assert_eq!(c.admit(x, &config).unwrap(), VerificationResult::Valid);
            }
            assert_eq!(render_state(&c.state, &f.dialect), expected);
            timings[0].push(start.elapsed().as_micros());
            retained_bodies[0] = c.retained_body_stats();
            let start = Instant::now();
            let (s, t): (Reconstructed, Vec<Step>) = serde_json::from_slice(&recon_bytes).unwrap();
            let mut c = s.open(&config).unwrap();
            for x in &t {
                assert_eq!(c.admit(x, &config).unwrap(), VerificationResult::Valid);
            }
            assert_eq!(render_state(&c.state, &f.dialect), expected);
            timings[1].push(start.elapsed().as_micros());
            retained_bodies[1] = c.retained_body_stats();
            let start = Instant::now();
            let wires: Vec<Wire> = serde_json::from_slice(&replay_bytes).unwrap();
            let m = replay(&f, &wires).unwrap();
            assert_eq!(folded(&f, &m, &wires), expected);
            timings[2].push(start.elapsed().as_micros());
        }
        for t in &mut timings {
            t.sort();
        }
        rows.push(serde_json::json!({"history_edits":n,"repeat_depth":depth,"offline_member_lag":lag,"tail_messages":steps.len(),"certified_json_bytes":cert_bytes.len(),"reconstruction_json_bytes":recon_bytes.len(),"history_and_tail_json_bytes":replay_bytes.len(),"certified_open_tail_median_us":timings[0][1],"reconstruction_open_tail_median_us":timings[1][1],"full_admission_fold_median_us":timings[2][1],"tail_covered_payload_fetches":tail_bodies,"tail_covered_envelope_fetches":tail_headers,"tail_covered_envelope_json_bytes":tail_header_bytes,"full_replay_archive_payload_fetches":replay_body_reads,"stale_bridge_messages":recon.anchors[3].bridge.len(),"provider_sparse_index_nodes":p.coverage.nodes.len(),"certified_retained_signed_bodies":retained_bodies[0].0,"certified_retained_signed_body_json_bytes":retained_bodies[0].1,"reconstruction_retained_signed_bodies":retained_bodies[1].0,"reconstruction_retained_signed_body_json_bytes":retained_bodies[1].1}));
    }
    println!("{}",serde_json::to_string_pretty(&serde_json::json!({"status":"experimental; cached roots attest prior accepted sets; adapter checked against full AdmissionMonitor", "policy":"fixed 4-member roster f=1; cached 3-of-4 certificate vs all-four signed member views", "timing":"median of 3 local JSON decode, signature, causal admission and render runs; no network; fixture and package creation excluded", "rows":rows})).unwrap());
}

#[cfg(test)]
mod tests;
