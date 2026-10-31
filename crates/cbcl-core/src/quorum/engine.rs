use super::types::{digest, text, Operation};
use super::*;
use crate::{
    escrow::{DEPS, NONCE, PREV},
    intend::{Instance, Reject},
    message::Message,
    role::AgentKey,
    sexpr::{Atom, SExpr},
    state::{Act, Value},
};
use alloc::{
    borrow::Cow,
    collections::{BTreeMap, BTreeSet},
    string::{String, ToString},
    vec::Vec,
};

#[derive(Debug, Default)]
struct State {
    operations: BTreeMap<String, Operation>,
    certificates: BTreeMap<(VoteKind, String), Certificate>,
    versions: BTreeMap<String, DagVersion>,
    visited: BTreeSet<String>,
    signed: BTreeSet<String>,
    effects: BTreeSet<String>,
    fences: BTreeSet<String>,
    released: BTreeSet<String>,
    active: BTreeMap<String, String>,
    // Derived from immutable signed/released history; never loaded from a snapshot.
    charges: BTreeMap<String, Resources>,
}
/// Owned, already-validated changes. No protocol checks may fail during application.
/// This is transient preparation, never serialized or accepted as journal input.
enum Update {
    Candidate(String, Operation),
    Certificate((VoteKind, String), Certificate),
    Version(String, DagVersion),
    Adopt {
        account: String,
        id: String,
    },
    Sign {
        id: String,
        epoch: String,
        charge: Resources,
    },
    Effect(String),
    Fence(String),
    Release {
        id: String,
        epoch: String,
        charge: Resources,
    },
}
/// One validator's independent state machine. Each mutation is journaled before
/// exposing a decision to the signer. There is no shared reservation authority.
pub struct Replica {
    context: Context,
    validator: String,
    limits: Limits,
    sequence: u64,
    state: State,
}
impl Replica {
    /// Creates a log exactly once. An existing identity must use `recover`.
    pub fn initialize<J: Journal>(
        context: Context,
        validator: &str,
        limits: Limits,
        journal: &mut J,
    ) -> Result<Self> {
        if !context.committee.contains(validator) {
            return Err("validator outside committee".into());
        }
        if journal.load(&context.id, validator)?.is_some() {
            return Err("journal exists: recover it".into());
        }
        if limits.events == 0 {
            return Err("event limit is zero".into());
        }
        journal.append(&context.id, validator, None, &Event::Initialize)?;
        let mut state = State::default();
        for a in context.initial.keys() {
            let root = context.root_epoch(a)?;
            state.visited.insert(root.clone());
            state.active.insert(a.clone(), root);
        }
        Ok(Self {
            context,
            validator: validator.into(),
            limits,
            sequence: 1,
            state,
        })
    }
    pub fn recover<J: Journal, A: Authentication>(
        context: Context,
        validator: &str,
        limits: Limits,
        journal: &J,
        auth: &A,
    ) -> Result<Self> {
        if !context.committee.contains(validator) {
            return Err("validator outside committee".into());
        }
        let events = journal
            .load(&context.id, validator)?
            .ok_or("missing journal; initialize explicitly")?;
        if events.first() != Some(&Event::Initialize) || events.len() as u64 > limits.events {
            return Err("invalid or oversized journal".into());
        }
        let mut state = State::default();
        for a in context.initial.keys() {
            let root = context.root_epoch(a)?;
            state.visited.insert(root.clone());
            state.active.insert(a.clone(), root);
        }
        let mut r = Self {
            context,
            validator: validator.into(),
            limits,
            sequence: 1,
            state,
        };
        for e in events.into_iter().skip(1) {
            r.apply(&e, auth)?;
            r.sequence += 1;
        }
        Ok(r)
    }
    pub fn context(&self) -> &Context {
        &self.context
    }
    pub fn validator(&self) -> &str {
        &self.validator
    }
    /// Fetch retained evidence for relay. These getters never synthesize proofs.
    pub fn operation_act(&self, id: &str) -> Option<&Act> {
        self.state.operations.get(id).map(|op| &op.act)
    }
    pub fn certificate(&self, kind: VoteKind, id: &str) -> Option<&Certificate> {
        self.state.certificates.get(&(kind, id.into()))
    }

    pub fn journal_sequence(&self) -> u64 {
        self.sequence
    }
    fn commit<J: Journal, A: Authentication>(
        &mut self,
        event: Event,
        journal: &mut J,
        auth: &A,
    ) -> Result<()> {
        let Some(update) = self.prepare(&event, auth)? else {
            return Ok(());
        };
        if self.sequence >= self.limits.events {
            return Err("journal limit reached; evidence retained".into());
        }
        // All fallible protocol validation is complete. Failure/CAS rejection
        // leaves state (including derived charges) untouched; no vote is exposed.
        journal.append(
            &self.context.id,
            &self.validator,
            Some(self.sequence),
            &event,
        )?;
        self.apply_update(update);
        self.sequence += 1;
        Ok(())
    }
    fn op(&self, id: &str) -> Result<&Operation> {
        self.state
            .operations
            .get(id)
            .ok_or_else(|| alloc::format!("missing operation {id}"))
    }
    fn has(&self, kind: VoteKind, id: &str) -> bool {
        self.state.certificates.contains_key(&(kind, id.into()))
    }
    fn epoch(&self, id: &str) -> Result<Cow<'_, VersionManifest>> {
        if let Some(v) = self.state.versions.get(id) {
            return Ok(Cow::Borrowed(&v.manifest));
        }

        for (a, b) in &self.context.initial {
            if self.context.root_epoch(a)? == id {
                return Ok(Cow::Owned(VersionManifest {
                    account: a.clone(),
                    parents: BTreeSet::new(),
                    rank: 0,
                    held: BTreeSet::new(),
                    refunded: BTreeSet::new(),
                    credited: BTreeSet::new(),
                    allocation: *b,
                }));
            }
        }
        Err(alloc::format!("missing certified epoch {id}"))
    }
    fn verify_vote<A: Authentication>(
        &self,
        v: &Vote,
        kind: VoteKind,
        payload: &str,
        key: &str,
        auth: &A,
    ) -> Result<()> {
        if v.context != self.context.id
            || v.kind != kind
            || v.payload != payload
            || v.signer != key
            || v.signature.len() > self.limits.signature_bytes
            || v.signature.is_empty()
            || !auth.verify(key, &v.preimage(), &v.signature)
        {
            return Err("invalid signature, domain, signer or payload".into());
        }
        Ok(())
    }
    fn verify_certificate<A: Authentication>(
        &self,
        c: &Certificate,
        kind: VoteKind,
        payload: &str,
        auth: &A,
    ) -> Result<()> {
        let committee = &self.context.committee;
        if c.kind != kind
            || c.payload != payload
            || c.votes.len() < committee.quorum
            || c.votes.len() > committee.validators.len()
        {
            return Err("invalid certificate kind, payload or quorum".into());
        }
        let mut keys = BTreeSet::new();
        for v in &c.votes {
            if !committee.contains(&v.signer) || !keys.insert(v.signer.clone()) {
                return Err("nonmember or duplicate validator".into());
            }
            self.verify_vote(v, kind, payload, &v.signer, auth)?;
        }
        Ok(())
    }
    fn operation(&self, a: &Act) -> Result<Operation> {
        bounded_message(&a.message, self.limits.object_bytes)?;
        self.context.structural(a)?;
        if crate::canonical::canonical_encode(&SExpr::from(&a.message)).len()
            > self.limits.object_bytes
        {
            return Err("operation too large".into());
        }
        let epoch = match a.fields.get(PREV) {
            Some(SExpr::Atom(Atom::Symbol(s))) => s.clone(),
            _ => return Err("missing source epoch".into()),
        };
        let m = self.epoch(&epoch)?;
        let account = self.context.account(&a.signer)?.to_string();
        if m.account != account {
            return Err("epoch belongs to another account".into());
        }
        let dependencies = SExpr::List(
            m.credited
                .iter()
                .map(|s| SExpr::Atom(Atom::Symbol(s.clone())))
                .collect(),
        );
        if a.fields.get(DEPS) != Some(&dependencies) {
            return Err("epoch finalized dependencies mismatch".into());
        }
        if !matches!(a.fields.get(NONCE),Some(SExpr::Atom(Atom::Str(s))) if !s.is_empty() && s.len()<=256)
        {
            return Err("missing or invalid transaction nonce".into());
        }
        let rule = &self.context.rule;
        let (key, recipient, kind) = if a.verb == rule.increment.0 {
            (&rule.increment.1, None, 0)
        } else if a.verb == rule.decrement.0 {
            (&rule.decrement.1, None, 1)
        } else if let Some((_, r, k)) = rule.transfer.as_ref().filter(|(v, _, _)| a.verb == *v) {
            (k, Some(r), 2)
        } else if let Some((v, r, k)) = &rule.transfer_headroom {
            if &a.verb == v {
                (k, Some(r), 3)
            } else {
                return Err("not a counter operation".into());
            }
        } else {
            return Err("not a counter operation".into());
        };
        let n = match a.fields.get(key) {
            Some(SExpr::Atom(Atom::Num(n))) if *n > 0 => i128::from(*n),
            _ => return Err("amount must be a positive integer".into()),
        };
        let to = match recipient {
            None => account.clone(),
            Some(k) => match a.fields.get(k) {
                Some(SExpr::Atom(Atom::Symbol(s) | Atom::Str(s)))
                    if self.context.initial.contains_key(s) =>
                {
                    s.clone()
                }
                _ => return Err("unknown recipient".into()),
            },
        };
        if kind >= 2 && to == a.signer {
            return Err("self transfer is not a resource operation".into());
        }
        if kind == 0 && !self.context.issuers.contains(&a.signer) {
            return Err("mint requires issuer authority".into());
        }
        let bounded = rule.ceiling.is_some();
        let (cost, credit) = match kind {
            0 => (
                Resources {
                    rights: 0,
                    headroom: if bounded { n } else { 0 },
                },
                Resources {
                    rights: n,
                    headroom: 0,
                },
            ),
            1 => (
                Resources {
                    rights: n,
                    headroom: 0,
                },
                Resources {
                    rights: 0,
                    headroom: if bounded { n } else { 0 },
                },
            ),
            2 => (
                Resources {
                    rights: n,
                    headroom: 0,
                },
                Resources {
                    rights: n,
                    headroom: 0,
                },
            ),
            _ => {
                if !bounded {
                    return Err("headroom requires a ceiling".into());
                }
                (
                    Resources {
                        rights: 0,
                        headroom: n,
                    },
                    Resources {
                        rights: 0,
                        headroom: n,
                    },
                )
            }
        };
        Ok(Operation {
            act: a.clone(),
            account,
            epoch,
            cost,
            credits: [(to, credit)].into_iter().collect(),
        })
    }
    fn charge(&self, epoch: &str, extra: &str) -> Result<Resources> {
        self.state
            .charges
            .get(epoch)
            .copied()
            .unwrap_or_default()
            .add(self.op(extra)?.cost)
    }
    fn budget(&self, id: &str) -> Result<Resources> {
        let op = self.op(id)?;
        let epoch = self.epoch(&op.epoch)?;
        if self.state.active.get(&op.account) != Some(&op.epoch) || self.state.released.contains(id)
        {
            return Err("version inactive or operation released".into());
        }
        let used = self.charge(&op.epoch, id)?;
        let q = self.context.committee.quorum as i128;
        let k = i128::from(self.context.committee.faults) + 1;
        if used.rights.checked_mul(q).ok_or("budget overflow")?
            > epoch
                .allocation
                .rights
                .checked_mul(k)
                .ok_or("budget overflow")?
            || used.headroom.checked_mul(q).ok_or("budget overflow")?
                > epoch
                    .allocation
                    .headroom
                    .checked_mul(k)
                    .ok_or("budget overflow")?
        {
            return Err("local validator budget exceeded".into());
        }
        Ok(used)
    }

    fn allocation(&self, m: &VersionManifest) -> Result<Resources> {
        let mut b = *self
            .context
            .initial
            .get(&m.account)
            .ok_or("unknown resource scope")?;
        for id in &m.credited {
            if !self.has(VoteKind::Effects, id) {
                return Err("missing final credit certificate".into());
            }
            b = b.add(
                *self
                    .op(id)?
                    .credits
                    .get(&m.account)
                    .ok_or("credit belongs to another account")?,
            )?;
        }
        for id in &m.held {
            let op = self.op(id)?;
            if op.account != m.account {
                return Err("held operation belongs to another account".into());
            }
            b = b.sub(op.cost)?;
        }
        for id in &m.refunded {
            if !m.held.contains(id) || !self.has(VoteKind::Cancel, id) {
                return Err("refund needs held operation and cancellation quorum".into());
            }
            b = b.add(self.op(id)?.cost)?;
        }
        if !b.nonnegative() {
            return Err("negative version allocation".into());
        }
        Ok(b)
    }
    fn check_version_manifest(&self, m: &VersionManifest) -> Result<()> {
        if !self.context.initial.contains_key(&m.account)
            || m.parents.is_empty()
            || m.parents.len() > self.limits.versions.saturating_add(1)
            || m.held.len() > self.limits.operations
            || m.refunded.len() > self.limits.operations
            || m.credited.len() > self.limits.operations
        {
            return Err("invalid DAG pool, parent set or size limit".into());
        }
        for id in &m.parents {
            let parent = self.epoch(id)?;
            if parent.account != m.account
                || parent.rank >= m.rank
                || !parent.held.is_subset(&m.held)
                || !parent.refunded.is_subset(&m.refunded)
                || !parent.credited.is_subset(&m.credited)
            {
                return Err("DAG parent rank or inherited sets mismatch".into());
            }
        }
        for id in &m.held {
            if self.epoch(&self.op(id)?.epoch)?.rank >= m.rank {
                return Err("held transaction must precede DAG version rank".into());
            }
        }
        if self.allocation(m)? != m.allocation {
            return Err("DAG version allocation mismatch".into());
        }
        Ok(())
    }
    fn check_version<A: Authentication>(&self, v: &DagVersion, auth: &A) -> Result<()> {
        self.check_version_manifest(&v.manifest)?;
        if !self
            .context
            .version_actor(&v.manifest.account, &v.authorization.signer)
        {
            return Err("unauthorized DAG version actor".into());
        }
        self.verify_vote(
            &v.authorization,
            VoteKind::VersionRequest,
            &v.manifest.id(&self.context.id),
            &v.authorization.signer,
            auth,
        )
    }
    /// Validated metadata for relay; no synthetic certificates or winner selection.
    pub fn version(&self, id: &str) -> Option<&DagVersion> {
        self.state.versions.get(id)
    }
    /// Complete immutable local history, including released and zero-cost IDs.
    pub fn version_snapshot(&self, account: &str) -> Result<VersionSnapshot> {
        let account = self.context.account(account)?;
        let root = self.context.root_epoch(account)?;
        let mut known: BTreeSet<_> = self
            .state
            .versions
            .iter()
            .filter(|(_, v)| v.manifest.account == account)
            .map(|(id, _)| id.clone())
            .collect();
        known.insert(root);
        let project = |ids: &BTreeSet<String>| {
            ids.iter()
                .filter(|id| {
                    self.state
                        .operations
                        .get(*id)
                        .is_some_and(|op| op.account == account)
                })
                .cloned()
                .collect()
        };
        let visited = self
            .state
            .visited
            .iter()
            .filter(|id| self.epoch(id).is_ok_and(|m| m.account == account))
            .cloned()
            .collect();
        Ok(VersionSnapshot {
            active: self.active_epoch(account)?.into(),
            known,
            visited,
            signed: project(&self.state.signed),
            released: project(&self.state.released),
            effects: project(&self.state.effects),
            fences: project(&self.state.fences),
        })
    }
    /// Compute unique cumulative books. The caller externally authorizes the
    /// result; receipt verifies all prerequisites independently.
    pub fn draft_version(
        &self,
        parents: &BTreeSet<String>,
        held: &BTreeSet<String>,
        refunds: &BTreeSet<String>,
        credits: &BTreeSet<String>,
    ) -> Result<VersionManifest> {
        if parents.is_empty()
            || parents.len() > self.limits.versions.saturating_add(1)
            || held.len() > self.limits.operations
            || refunds.len() > self.limits.operations
            || credits.len() > self.limits.operations
        {
            return Err("invalid DAG draft context or limits".into());
        }
        let mut m = VersionManifest {
            account: self
                .epoch(parents.first().ok_or("empty parent set")?)?
                .account
                .clone(),
            parents: parents.clone(),
            rank: 0,
            held: held.clone(),
            refunded: refunds.clone(),
            credited: credits.clone(),
            allocation: Resources::default(),
        };
        for id in parents {
            let p = self.epoch(id)?;
            m.rank = m.rank.max(p.rank);
            m.held.extend(p.held.iter().cloned());
            m.refunded.extend(p.refunded.iter().cloned());
            m.credited.extend(p.credited.iter().cloned());
        }
        if m.held.len() > self.limits.operations
            || m.refunded.len() > self.limits.operations
            || m.credited.len() > self.limits.operations
        {
            return Err("cumulative DAG sets exceed limits".into());
        }
        for id in &m.held {
            m.rank = m.rank.max(self.epoch(&self.op(id)?.epoch)?.rank);
        }
        m.rank = m.rank.checked_add(1).ok_or("DAG rank overflow")?;
        m.allocation = self.allocation(&m)?;
        self.check_version_manifest(&m)?;
        Ok(m)
    }
    pub fn receive_version<J: Journal, A: Authentication>(
        &mut self,
        version: DagVersion,
        journal: &mut J,
        auth: &A,
    ) -> Result<()> {
        self.commit(Event::Version(version), journal, auth)
    }
    pub fn adopt_version<J: Journal, A: Authentication>(
        &mut self,
        id: &str,
        journal: &mut J,
        auth: &A,
    ) -> Result<()> {
        self.commit(Event::AdoptVersion(id.into()), journal, auth)
    }
    // Replay shares exactly the same validation/update functions as live commit.
    fn apply<A: Authentication>(&mut self, event: &Event, auth: &A) -> Result<()> {
        if let Some(update) = self.prepare(event, auth)? {
            self.apply_update(update);
        }
        Ok(())
    }
    fn prepare<A: Authentication>(&self, event: &Event, auth: &A) -> Result<Option<Update>> {
        let update = match event {
            Event::Initialize => return Err("duplicate initialization".into()),
            Event::Version(v) => {
                self.check_version(v, auth)?;
                let id = v.manifest.id(&self.context.id);
                if self.state.versions.contains_key(&id) {
                    return Ok(None);
                }
                if self.state.versions.len() >= self.limits.versions {
                    return Err("version limit reached; evidence retained".into());
                }
                Update::Version(id, v.clone())
            }
            Event::AdoptVersion(id) => {
                let v = self.state.versions.get(id).ok_or("unknown DAG version")?;
                let m = &v.manifest;
                let current = self.state.active.get(&m.account).ok_or("unknown pool")?;
                if current == id {
                    return Ok(None);
                }
                if !m.parents.contains(current) {
                    return Err("adoption must follow a direct active parent".into());
                }
                // Includes every old version, released reservation and zero-cost ID.
                for signed in &self.state.signed {
                    if self.op(signed)?.account == m.account && !m.held.contains(signed) {
                        return Err("DAG version omits historical signature".into());
                    }
                }
                Update::Adopt {
                    account: m.account.clone(),
                    id: id.clone(),
                }
            }
            Event::Candidate(a) => {
                let op = self.operation(a)?;
                if !auth.authenticate_act(a) {
                    return Err("owner signature or protocol admission failed".into());
                }
                if let Some(old) = self.state.operations.get(&a.address) {
                    if *old != op {
                        return Err("conflicting act identity".into());
                    }
                    return Ok(None);
                }
                if self.state.operations.len() >= self.limits.operations {
                    return Err("operation limit reached; evidence retained".into());
                }
                Update::Candidate(a.address.clone(), op)
            }
            Event::Certificate(c) => {
                if !matches!(
                    c.kind,
                    VoteKind::Operation | VoteKind::Effects | VoteKind::Cancel
                ) {
                    return Err("unexpected certificate type".into());
                }
                self.op(&c.payload)?;
                self.verify_certificate(c, c.kind, &c.payload, auth)?;
                if c.kind == VoteKind::Effects {
                    if !self.has(VoteKind::Operation, &c.payload) {
                        return Err("effects require operation certificate".into());
                    }
                    if self.has(VoteKind::Cancel, &c.payload) {
                        return Err(
                            "conflicting genuine effects and cancellation certificates".into()
                        );
                    }
                }
                if c.kind == VoteKind::Cancel && self.has(VoteKind::Effects, &c.payload) {
                    return Err("conflicting genuine cancellation and effects certificates".into());
                }
                if self.has(c.kind, &c.payload) {
                    return Ok(None);
                }
                Update::Certificate((c.kind, c.payload.clone()), c.clone())
            }
            Event::Sign(id) => {
                if self.state.signed.contains(id) {
                    return Ok(None);
                }
                let charge = self.budget(id)?;
                Update::Sign {
                    id: id.clone(),
                    epoch: self.op(id)?.epoch.clone(),
                    charge,
                }
            }
            Event::Effect(id) => {
                if self.state.effects.contains(id) {
                    return Ok(None);
                }
                self.op(id)?;
                if self.state.fences.contains(id) || !self.has(VoteKind::Operation, id) {
                    return Err("effects fenced or missing operation certificate".into());
                }
                Update::Effect(id.clone())
            }
            Event::Fence(v) => {
                let op = self.op(&v.payload)?;
                self.verify_vote(v, VoteKind::CancelRequest, &v.payload, &op.act.signer, auth)?;
                if self.state.effects.contains(&v.payload) {
                    return Err("validator already signed effects".into());
                }
                if self.state.fences.contains(&v.payload) {
                    return Ok(None);
                }
                Update::Fence(v.payload.clone())
            }
            Event::Release(id) => {
                if !self.state.signed.contains(id) || !self.has(VoteKind::Cancel, id) {
                    return Err("release requires own charge and cancellation quorum".into());
                }
                if self.state.released.contains(id) {
                    return Ok(None);
                }
                let op = self.op(id)?;
                let charge = self
                    .state
                    .charges
                    .get(&op.epoch)
                    .copied()
                    .unwrap_or_default()
                    .sub(op.cost)?;
                if !charge.nonnegative() {
                    return Err("inconsistent derived charge".into());
                }
                Update::Release {
                    id: id.clone(),
                    epoch: op.epoch.clone(),
                    charge,
                }
            }
        };
        Ok(Some(update))
    }
    fn apply_update(&mut self, update: Update) {
        match update {
            Update::Candidate(id, op) => {
                self.state.operations.insert(id, op);
            }
            Update::Certificate(key, certificate) => {
                self.state.certificates.insert(key, certificate);
            }
            Update::Version(id, version) => {
                self.state.versions.insert(id, version);
            }
            Update::Adopt { account, id } => {
                self.state.active.insert(account, id.clone());
                self.state.visited.insert(id);
            }
            Update::Sign { id, epoch, charge } => {
                self.state.signed.insert(id);
                self.state.charges.insert(epoch, charge);
            }
            Update::Effect(id) => {
                self.state.effects.insert(id);
            }
            Update::Fence(id) => {
                self.state.fences.insert(id);
            }
            Update::Release { id, epoch, charge } => {
                self.state.released.insert(id);
                self.state.charges.insert(epoch, charge);
            }
        }
        #[cfg(debug_assertions)]
        self.assert_charge_cache();
    }
    /// Independent reference expression: the original history-based budget sum.
    /// Kept out of optimized builds; exercised at every debug execution/replay step.
    #[cfg(debug_assertions)]
    fn assert_charge_cache(&self) {
        let mut expected: BTreeMap<String, Resources> = BTreeMap::new();
        for id in &self.state.signed {
            let op = self
                .state
                .operations
                .get(id)
                .expect("signed candidate retained");
            let total = expected.entry(op.epoch.clone()).or_default();
            if !self.state.released.contains(id) {
                *total = total
                    .add(op.cost)
                    .expect("reachable historical charge fits");
            }
        }
        debug_assert_eq!(
            self.state.charges, expected,
            "derived charge differs from signed history"
        );
    }
    pub fn register<J: Journal, A: Authentication>(
        &mut self,
        act: Act,
        j: &mut J,
        a: &A,
    ) -> Result<()> {
        self.commit(Event::Candidate(act), j, a)
    }
    pub fn receive<J: Journal, A: Authentication>(
        &mut self,
        c: Certificate,
        j: &mut J,
        a: &A,
    ) -> Result<()> {
        self.commit(Event::Certificate(c), j, a)
    }
    pub fn prepare_operation<J: Journal, A: Authentication>(
        &mut self,
        id: &str,
        j: &mut J,
        a: &A,
    ) -> Result<SigningRequest> {
        self.commit(Event::Sign(id.into()), j, a)?;
        Ok(self
            .context
            .request(VoteKind::Operation, id, &self.validator))
    }
    pub fn prepare_effects<J: Journal, A: Authentication>(
        &mut self,
        id: &str,
        j: &mut J,
        a: &A,
    ) -> Result<SigningRequest> {
        self.commit(Event::Effect(id.into()), j, a)?;
        Ok(self.context.request(VoteKind::Effects, id, &self.validator))
    }
    pub fn prepare_cancel<J: Journal, A: Authentication>(
        &mut self,
        request: Vote,
        j: &mut J,
        a: &A,
    ) -> Result<SigningRequest> {
        let id = request.payload.clone();
        self.commit(Event::Fence(request), j, a)?;
        Ok(self.context.request(VoteKind::Cancel, &id, &self.validator))
    }
    pub fn release<J: Journal, A: Authentication>(
        &mut self,
        id: &str,
        j: &mut J,
        a: &A,
    ) -> Result<()> {
        self.commit(Event::Release(id.into()), j, a)
    }

    pub fn active_epoch(&self, account: &str) -> Result<&str> {
        let account = self.context.account(account)?;
        self.state
            .active
            .get(account)
            .map(String::as_str)
            .ok_or_else(|| "unknown account".into())
    }
    pub fn finalized_view(&self) -> Result<FinalizedView> {
        let mut balances = self.context.initial.clone();
        let mut finalized = BTreeSet::new();
        let mut pending = BTreeSet::new();
        for (kind, id) in self.state.certificates.keys() {
            if *kind == VoteKind::Effects {
                finalized.insert(id.clone());
            } else if *kind == VoteKind::Operation
                && !self.has(VoteKind::Cancel, id)
                && !self.has(VoteKind::Effects, id)
            {
                pending.insert(id.clone());
            }
        }
        for id in &finalized {
            let op = self.op(id)?;
            let owner = balances.get_mut(&op.account).ok_or("unknown owner")?;
            *owner = owner.sub(op.cost)?;
            for (a, credit) in &op.credits {
                let b = balances.get_mut(a).ok_or("unknown recipient")?;
                *b = b.add(*credit)?;
            }
        }
        if balances.values().any(|b| !b.nonnegative()) {
            return Err("inconsistent final evidence violates resource bounds".into());
        }
        let rights: BTreeMap<_, _> = balances
            .iter()
            .map(|(a, b)| (a.clone(), b.rights))
            .collect();
        let value = rights
            .values()
            .try_fold(i128::from(self.context.rule.floor), |s, n| {
                s.checked_add(*n).ok_or("balance overflow")
            })?;
        if self
            .context
            .rule
            .ceiling
            .is_some_and(|cap| value > i128::from(cap))
        {
            return Err("final evidence exceeds ceiling".into());
        }
        Ok(FinalizedView {
            ownership: self.context.rule.ownership,
            context: self.context.id.clone(),
            evidence_digest: digest(alloc::vec![
                text("cbcl/final-view/v1"),
                text(&self.context.id),
                super::types::strings(&finalized)
            ]),
            rights,
            headroom: self.context.rule.ceiling.map(|_| {
                balances
                    .iter()
                    .map(|(a, b)| (a.clone(), b.headroom))
                    .collect()
            }),
            value,
            finalized,
            pending,
        })
    }
    pub fn intend(
        &self,
        inst: &Instance,
        owner: &AgentKey,
        verb: &str,
        fields: BTreeMap<String, SExpr>,
        nonce: &str,
    ) -> core::result::Result<Message, Reject> {
        let bound = Instance::new(inst.dialect, inst.thread.clone(), inst.acts)
            .map_err(Reject::Resource)?;
        crate::intend::intend_certified(&bound, owner, verb, fields, self, nonce)
    }
    pub(crate) fn bind_authoring<'a, 'd>(
        &'a self,
        instance: &'a Instance<'d>,
    ) -> Result<BoundAuthoring<'a, 'd>> {
        if !self.context.matches(instance) {
            return Err("runtime does not match instance or counter verb".into());
        }
        Ok(BoundAuthoring {
            replica: self,
            instance,
        })
    }

    pub fn fold_instance(&self, inst: &Instance) -> Result<Vec<(String, Value)>> {
        if !self.context.matches(inst) {
            return Err("runtime instance mismatch".into());
        }
        let mut folded = crate::escrow::fold_instance(inst.dialect, &inst.thread.0, inst.acts);
        let field = folded
            .iter_mut()
            .find(|(name, _)| *name == self.context.field)
            .ok_or("missing resource field")?;
        field.1 = self.finalized_view()?.value();
        Ok(folded)
    }
}

/// Bound the typed tree before recursive cloning/canonicalization/authentication.
/// Wire decoders must ALSO enforce their own allocation limits before constructing
/// these values. Depth 64 is the runtime ceiling, independent of host limits.
fn bounded_message(message: &Message, limit: usize) -> Result<()> {
    use crate::message::{CausedBy, Recipients};
    let mut total = 0usize;
    let mut charge = |n: usize| -> Result<()> {
        total = total.checked_add(n).ok_or("object size overflow")?;
        if total > limit {
            return Err("operation object limit exceeded".into());
        }
        Ok(())
    };
    let mut msg = message;
    let mut expressions = Vec::new();
    for depth in 0..=64 {
        charge(16)?;
        match msg {
            Message::Dialect {
                dialect_name,
                inner,
            } => {
                charge(dialect_name.len())?;
                msg = inner;
            }
            Message::Wrapped {
                params, content, ..
            } => {
                if params.len() > limit {
                    return Err("wrapper size limit exceeded".into());
                }
                expressions.extend(params.iter().map(|s| (s, depth + 1)));
                msg = content;
            }
            Message::Simple {
                performative,
                recipient,
                content,
                params,
                thread,
                sender,
                caused_by,
            } => {
                charge(performative.name().len())?;
                if let Some(r) = recipient {
                    match r {
                        Recipients::One(k) => charge(k.len())?,
                        Recipients::Set(ks) => {
                            if ks.len() > limit {
                                return Err("recipient limit exceeded".into());
                            }
                            for k in ks {
                                charge(k.len() + 1)?;
                            }
                        }
                    }
                }
                if let Some(t) = thread {
                    charge(t.len())?;
                }
                if let Some(s) = sender {
                    charge(s.len())?;
                }
                match caused_by {
                    Some(CausedBy::Single(s)) => charge(s.len())?,
                    Some(CausedBy::Multiple(xs)) => {
                        if xs.len() > limit {
                            return Err("cause limit exceeded".into());
                        }
                        for x in xs {
                            charge(x.len() + 1)?;
                        }
                    }
                    _ => {}
                }
                if params.len() > limit {
                    return Err("parameter limit exceeded".into());
                }
                expressions.push((content, depth + 1));
                expressions.extend(params.iter().map(|s| (s, depth + 1)));
                break;
            }
            Message::Meta { .. } => {
                return Err("resource candidate cannot be a meta message".into())
            }
        }
        if depth == 64 {
            return Err("message nesting limit exceeded".into());
        }
    }
    while let Some((s, depth)) = expressions.pop() {
        if depth > 64 {
            return Err("S-expression nesting limit exceeded".into());
        }
        charge(16)?;
        match s {
            SExpr::Atom(Atom::Symbol(s) | Atom::Keyword(s) | Atom::Str(s)) => charge(s.len())?,
            SExpr::Atom(_) => {}
            SExpr::List(xs) => {
                if xs.len() > limit {
                    return Err("list limit exceeded".into());
                }
                expressions.extend(xs.iter().map(|s| (s, depth + 1)));
            }
        }
    }
    Ok(())
}

/// Immutable authoring inputs whose instance identity was checked together.
/// Only this module can construct the binding; it cannot be retargeted to a
/// different instance. Bookkeeping and candidate checks share that validation.
pub(crate) struct BoundAuthoring<'a, 'd> {
    replica: &'a Replica,
    instance: &'a Instance<'d>,
}
impl<'d> BoundAuthoring<'_, 'd> {
    pub(crate) fn instance(&self) -> &Instance<'d> {
        self.instance
    }
    pub(crate) fn bookkeeping(
        &self,
        owner: &str,
        verb: &str,
        nonce: &str,
    ) -> Result<Vec<(String, SExpr)>> {
        if !self.replica.context.rule.operation_verbs().contains(&verb) {
            return Err("runtime does not match instance or counter verb".into());
        }
        if nonce.is_empty() || nonce.len() > 256 {
            return Err("nonce must contain 1..256 bytes".into());
        }
        let epoch = self.replica.active_epoch(owner)?;
        let m = self.replica.epoch(epoch)?;
        Ok(alloc::vec![
            (PREV.into(), SExpr::Atom(Atom::Symbol(epoch.into()))),
            (
                DEPS.into(),
                SExpr::List(
                    m.credited
                        .iter()
                        .map(|s| SExpr::Atom(Atom::Symbol(s.clone())))
                        .collect()
                )
            ),
            (NONCE.into(), SExpr::Atom(Atom::Str(nonce.into())))
        ])
    }
    pub(crate) fn check_candidate(&self, candidate: &Act) -> Result<()> {
        self.replica.operation(candidate)?;
        Ok(())
    }
}
