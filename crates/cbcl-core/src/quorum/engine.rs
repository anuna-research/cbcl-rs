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
    collections::{BTreeMap, BTreeSet},
    string::{String, ToString},
    vec::Vec,
};

#[derive(Debug, Clone, PartialEq, Eq, Default)]
struct State {
    operations: BTreeMap<String, Operation>,
    certificates: BTreeMap<(VoteKind, String), Certificate>,
    proposals: BTreeMap<String, Proposal>,
    checkpoints: BTreeMap<String, Checkpoint>,
    versions: BTreeMap<String, DagVersion>,
    visited: BTreeSet<String>,
    signed: BTreeSet<String>,
    effects: BTreeSet<String>,
    fences: BTreeSet<String>,
    released: BTreeSet<String>,
    sealed: BTreeMap<String, BTreeSet<String>>,
    choices: BTreeMap<String, String>,
    active: BTreeMap<String, String>,
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
    pub fn checkpoint(&self, id: &str) -> Option<&Checkpoint> {
        self.state.checkpoints.get(id)
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
        let old = self.state.clone();
        if let Err(e) = self.apply(&event, auth) {
            self.state = old;
            return Err(e);
        }
        if self.state == old {
            return Ok(());
        }
        if self.sequence >= self.limits.events {
            self.state = old;
            return Err("journal limit reached; evidence retained".into());
        }
        if let Err(e) = journal.append(
            &self.context.id,
            &self.validator,
            Some(self.sequence),
            &event,
        ) {
            self.state = old;
            return Err(e);
        }
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
    fn epoch(&self, id: &str) -> Result<Manifest> {
        if let Some(v) = self.state.versions.get(id) {
            return Ok(v.manifest.books());
        }
        if let Some(c) = self.state.checkpoints.get(id) {
            return Ok(c.proposal.manifest.clone());
        }
        for (a, b) in &self.context.initial {
            if self.context.root_epoch(a)? == id {
                return Ok(Manifest {
                    account: a.clone(),
                    parent: String::new(),
                    depth: 0,
                    held: BTreeSet::new(),
                    refunded: BTreeSet::new(),
                    credited: BTreeSet::new(),
                    allocation: *b,
                });
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
        let mut total = Resources::default();
        let extra = extra.to_string();
        for id in self.state.signed.iter().chain(core::iter::once(&extra)) {
            if self.state.released.contains(id) {
                continue;
            }
            let op = self.op(id)?;
            if op.epoch == epoch {
                total = total.add(op.cost)?;
            }
        }
        Ok(total)
    }
    fn budget(&self, id: &str) -> Result<()> {
        let op = self.op(id)?;
        let epoch = self.epoch(&op.epoch)?;
        if self.state.active.get(&op.account) != Some(&op.epoch)
            || self.state.sealed.contains_key(&op.epoch)
            || self.state.released.contains(id)
        {
            return Err("epoch inactive, sealed or operation released".into());
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
        Ok(())
    }
    fn signed_in(&self, epoch: &str) -> BTreeSet<String> {
        self.state
            .signed
            .iter()
            .filter(|id| {
                self.state
                    .operations
                    .get(*id)
                    .is_some_and(|op| op.epoch == epoch)
            })
            .cloned()
            .collect()
    }
    fn allocation(&self, m: &Manifest) -> Result<Resources> {
        let mut b = *self
            .context
            .initial
            .get(&m.account)
            .ok_or("unknown checkpoint account")?;
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
            return Err("negative checkpoint allocation".into());
        }
        Ok(b)
    }
    fn check_manifest(&self, m: &Manifest) -> Result<()> {
        let p = self.epoch(&m.parent)?;
        if m.account != p.account
            || m.depth != p.depth.checked_add(1).ok_or("epoch depth overflow")?
            || !p.held.is_subset(&m.held)
            || !p.refunded.is_subset(&m.refunded)
            || !p.credited.is_subset(&m.credited)
        {
            return Err("checkpoint parent, depth or monotonicity mismatch".into());
        }
        if m.held.len() > self.limits.operations
            || m.refunded.len() > self.limits.operations
            || m.credited.len() > self.limits.operations
        {
            return Err("checkpoint too large".into());
        }
        for id in m.held.difference(&p.held) {
            if self.op(id)?.epoch != m.parent {
                return Err("new held operation outside parent epoch".into());
            }
        }
        if self.allocation(m)? != m.allocation {
            return Err("checkpoint allocation mismatch".into());
        }
        Ok(())
    }
    fn check_proposal<A: Authentication>(&self, p: &Proposal, auth: &A) -> Result<()> {
        let m = &p.manifest;
        self.check_manifest(m)?;
        let id = m.id(&self.context.id);
        if !self
            .context
            .checkpoint_actor(&m.account, &p.authorization.signer)
        {
            return Err("unauthorized checkpoint actor".into());
        }
        self.verify_vote(
            &p.authorization,
            VoteKind::CheckpointRequest,
            &id,
            &p.authorization.signer,
            auth,
        )?;
        if p.reports.len() < self.context.committee.quorum
            || p.reports.len() > self.context.committee.validators.len()
        {
            return Err("checkpoint requires a seal quorum".into());
        }
        let mut keys = BTreeSet::new();
        for report in &p.reports {
            if report.epoch != m.parent
                || report.signed.len() > self.limits.operations
                || !self.context.committee.contains(&report.vote.signer)
                || !keys.insert(report.vote.signer.clone())
            {
                return Err("invalid seal report quorum".into());
            }
            for id in &report.signed {
                if self.op(id)?.epoch != m.parent || !m.held.contains(id) {
                    return Err("checkpoint omits sealed journal candidate".into());
                }
            }
            self.verify_vote(
                &report.vote,
                VoteKind::Seal,
                &SealReport::payload(&self.context.id, &report.epoch, &report.signed),
                &report.vote.signer,
                auth,
            )?;
        }
        Ok(())
    }
    fn check_version_manifest(&self, m: &VersionManifest) -> Result<()> {
        if m.account != COLLECTIVE_POOL
            || m.parents.is_empty()
            || m.parents.len() > self.limits.checkpoints.saturating_add(1)
            || m.held.len() > self.limits.operations
            || m.refunded.len() > self.limits.operations
            || m.credited.len() > self.limits.operations
        {
            return Err("invalid DAG pool, parent set or size limit".into());
        }
        for id in &m.parents {
            let parent = self.epoch(id)?;
            if parent.account != m.account
                || parent.depth >= m.rank
                || !parent.held.is_subset(&m.held)
                || !parent.refunded.is_subset(&m.refunded)
                || !parent.credited.is_subset(&m.credited)
            {
                return Err("DAG parent rank or inherited sets mismatch".into());
            }
        }
        for id in &m.held {
            if self.epoch(&self.op(id)?.epoch)?.depth >= m.rank {
                return Err("held transaction must precede DAG version rank".into());
            }
        }
        if self.allocation(&m.books())? != m.allocation {
            return Err("DAG version allocation mismatch".into());
        }
        Ok(())
    }
    fn check_version<A: Authentication>(&self, v: &DagVersion, auth: &A) -> Result<()> {
        self.check_version_manifest(&v.manifest)?;
        if !self
            .context
            .checkpoint_actor(&v.manifest.account, &v.authorization.signer)
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
    pub fn version_snapshot(&self) -> Result<VersionSnapshot> {
        if self.context.handoff != Handoff::MultiParent {
            return Err("not a multi-parent context".into());
        }
        let root = self.context.root_epoch(COLLECTIVE_POOL)?;
        let mut known: BTreeSet<_> = self.state.versions.keys().cloned().collect();
        known.insert(root);
        Ok(VersionSnapshot {
            active: self.active_epoch(COLLECTIVE_POOL)?.into(),
            known,
            visited: self.state.visited.clone(),
            signed: self.state.signed.clone(),
            released: self.state.released.clone(),
            effects: self.state.effects.clone(),
            fences: self.state.fences.clone(),
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
        if self.context.handoff != Handoff::MultiParent
            || parents.is_empty()
            || parents.len() > self.limits.checkpoints.saturating_add(1)
            || held.len() > self.limits.operations
            || refunds.len() > self.limits.operations
            || credits.len() > self.limits.operations
        {
            return Err("invalid DAG draft context or limits".into());
        }
        let mut m = VersionManifest {
            account: COLLECTIVE_POOL.into(),
            parents: parents.clone(),
            rank: 0,
            held: held.clone(),
            refunded: refunds.clone(),
            credited: credits.clone(),
            allocation: Resources::default(),
        };
        for id in parents {
            let p = self.epoch(id)?;
            m.rank = m.rank.max(p.depth);
            m.held.extend(p.held);
            m.refunded.extend(p.refunded);
            m.credited.extend(p.credited);
        }
        if m.held.len() > self.limits.operations
            || m.refunded.len() > self.limits.operations
            || m.credited.len() > self.limits.operations
        {
            return Err("cumulative DAG sets exceed limits".into());
        }
        for id in &m.held {
            m.rank = m.rank.max(self.epoch(&self.op(id)?.epoch)?.depth);
        }
        m.rank = m.rank.checked_add(1).ok_or("DAG rank overflow")?;
        m.allocation = self.allocation(&m.books())?;
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
    fn apply<A: Authentication>(&mut self, event: &Event, auth: &A) -> Result<()> {
        let legacy = matches!(
            event,
            Event::Seal(_)
                | Event::Proposal(_)
                | Event::Endorse(_)
                | Event::Checkpoint(_)
                | Event::Install(_)
        );
        let dag = matches!(event, Event::Version(_) | Event::AdoptVersion(_));
        if (legacy && self.context.handoff != Handoff::SingleParent)
            || (dag && self.context.handoff != Handoff::MultiParent)
        {
            return Err("handoff protocol/context mismatch".into());
        }
        match event {
            Event::Initialize => return Err("duplicate initialization".into()),
            Event::Version(v) => {
                self.check_version(v, auth)?;
                let id = v.manifest.id(&self.context.id);
                if !self.state.versions.contains_key(&id)
                    && self.state.versions.len() >= self.limits.checkpoints
                {
                    return Err("version limit reached; evidence retained".into());
                }
                self.state.versions.entry(id).or_insert_with(|| v.clone());
            }
            Event::AdoptVersion(id) => {
                let v = self.state.versions.get(id).ok_or("unknown DAG version")?;
                let m = &v.manifest;
                let current = self.state.active.get(&m.account).ok_or("unknown pool")?;
                if current == id {
                    return Ok(());
                }
                if !m.parents.contains(current) {
                    return Err("adoption must follow a direct active parent".into());
                }
                // Includes every old version, released reservation and zero-cost ID.
                if !self.state.signed.is_subset(&m.held) {
                    return Err("DAG version omits historical signature".into());
                }
                self.state.active.insert(m.account.clone(), id.clone());
                self.state.visited.insert(id.clone());
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
                    return Ok(());
                }
                if self.state.operations.len() >= self.limits.operations {
                    return Err("operation limit reached; evidence retained".into());
                }
                self.state.operations.insert(a.address.clone(), op);
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
                self.state
                    .certificates
                    .entry((c.kind, c.payload.clone()))
                    .or_insert_with(|| c.clone());
            }
            Event::Sign(id) => {
                if self.state.signed.contains(id) {
                    return Ok(());
                }
                self.budget(id)?;
                self.state.signed.insert(id.clone());
            }
            Event::Effect(id) => {
                if self.state.effects.contains(id) {
                    return Ok(());
                }
                self.op(id)?;
                if self.state.fences.contains(id) || !self.has(VoteKind::Operation, id) {
                    return Err("effects fenced or missing operation certificate".into());
                }
                self.state.effects.insert(id.clone());
            }
            Event::Fence(v) => {
                let op = self.op(&v.payload)?;
                self.verify_vote(v, VoteKind::CancelRequest, &v.payload, &op.act.signer, auth)?;
                if self.state.effects.contains(&v.payload) {
                    return Err("validator already signed effects".into());
                }
                self.state.fences.insert(v.payload.clone());
            }
            Event::Seal(epoch) => {
                self.epoch(epoch)?;
                let ids = self.signed_in(epoch);
                self.state.sealed.entry(epoch.clone()).or_insert(ids);
            }
            Event::Proposal(p) => {
                self.check_proposal(p, auth)?;
                let id = p.manifest.id(&self.context.id);
                if !self.state.proposals.contains_key(&id)
                    && self.state.proposals.len() >= self.limits.checkpoints
                {
                    return Err("proposal limit reached".into());
                }
                self.state.proposals.entry(id).or_insert_with(|| p.clone());
            }
            Event::Endorse(id) => {
                let p = self.state.proposals.get(id).ok_or("missing proposal")?;
                let m = &p.manifest;
                let own = self
                    .state
                    .sealed
                    .get(&m.parent)
                    .ok_or("endorsement requires own sealed journal")?;
                if !own.is_subset(&m.held) {
                    return Err("checkpoint omits own sealed candidate".into());
                }
                if let Some(chosen) = self.state.choices.get(&m.parent) {
                    if chosen != id {
                        return Err("successor vote already cast".into());
                    }
                }
                self.state.choices.insert(m.parent.clone(), id.clone());
            }
            Event::Checkpoint(c) => {
                self.check_proposal(&c.proposal, auth)?;
                let m = &c.proposal.manifest;
                let id = m.id(&self.context.id);
                self.verify_certificate(&c.certificate, VoteKind::Checkpoint, &id, auth)?;
                if self.state.checkpoints.values().any(|old| {
                    old.proposal.manifest.parent == m.parent && old.proposal.manifest != *m
                }) {
                    return Err("conflicting genuine successor certificates".into());
                }
                if !self.state.checkpoints.contains_key(&id)
                    && self.state.checkpoints.len() >= self.limits.checkpoints
                {
                    return Err("checkpoint limit reached".into());
                }
                self.state
                    .checkpoints
                    .entry(id)
                    .or_insert_with(|| c.clone());
            }
            Event::Release(id) => {
                if !self.state.signed.contains(id) || !self.has(VoteKind::Cancel, id) {
                    return Err("release requires own charge and cancellation quorum".into());
                }
                self.state.released.insert(id.clone());
            }
            Event::Install(id) => {
                let cp = self
                    .state
                    .checkpoints
                    .get(id)
                    .ok_or("missing checkpoint certificate")?;
                let m = &cp.proposal.manifest;
                let current = self.state.active.get(&m.account).ok_or("unknown account")?;
                if current == id {
                    return Ok(());
                }
                if current != &m.parent {
                    return Err("install must follow local active parent".into());
                }
                self.state.active.insert(m.account.clone(), id.clone());
            }
        }
        Ok(())
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
    pub fn seal<J: Journal, A: Authentication>(
        &mut self,
        epoch: &str,
        j: &mut J,
        a: &A,
    ) -> Result<(BTreeSet<String>, SigningRequest)> {
        self.commit(Event::Seal(epoch.into()), j, a)?;
        let ids = self
            .state
            .sealed
            .get(epoch)
            .ok_or("missing sealed journal")?
            .clone();
        Ok((
            ids.clone(),
            self.context.request(
                VoteKind::Seal,
                &SealReport::payload(&self.context.id, epoch, &ids),
                &self.validator,
            ),
        ))
    }
    /// Construct semantic checkpoint contents; the owner subsequently signs the
    /// returned manifest ID. Reports and authorization are validated at admission.
    pub fn draft_checkpoint(
        &self,
        epoch: &str,
        reports: &[SealReport],
        refunds: &BTreeSet<String>,
        credits: &BTreeSet<String>,
    ) -> Result<Manifest> {
        if self.context.handoff != Handoff::SingleParent {
            return Err("legacy checkpoint draft in multi-parent context".into());
        }
        if reports.len() > self.context.committee.validators.len()
            || refunds.len() > self.limits.operations
            || credits.len() > self.limits.operations
        {
            return Err("checkpoint draft input limit exceeded".into());
        }
        let parent = self.epoch(epoch)?;
        let mut m = Manifest {
            account: parent.account.clone(),
            parent: epoch.into(),
            depth: parent.depth.checked_add(1).ok_or("depth overflow")?,
            held: parent.held,
            refunded: parent.refunded,
            credited: parent.credited,
            allocation: Resources::default(),
        };
        for r in reports {
            if r.epoch != epoch || r.signed.len() > self.limits.operations {
                return Err("invalid report epoch or size".into());
            }
            m.held.extend(r.signed.clone());
        }
        m.refunded.extend(refunds.clone());
        m.credited.extend(credits.clone());
        m.allocation = self.allocation(&m)?;
        self.check_manifest(&m)?;
        Ok(m)
    }
    pub fn register_proposal<J: Journal, A: Authentication>(
        &mut self,
        p: Proposal,
        j: &mut J,
        a: &A,
    ) -> Result<String> {
        self.check_proposal(&p, a)?;
        let id = p.manifest.id(&self.context.id);
        self.commit(Event::Proposal(p), j, a)?;
        Ok(id)
    }
    pub fn prepare_checkpoint<J: Journal, A: Authentication>(
        &mut self,
        id: &str,
        j: &mut J,
        a: &A,
    ) -> Result<SigningRequest> {
        self.commit(Event::Endorse(id.into()), j, a)?;
        Ok(self
            .context
            .request(VoteKind::Checkpoint, id, &self.validator))
    }
    pub fn receive_checkpoint<J: Journal, A: Authentication>(
        &mut self,
        c: Checkpoint,
        j: &mut J,
        a: &A,
    ) -> Result<String> {
        self.check_proposal(&c.proposal, a)?;
        let id = c.proposal.manifest.id(&self.context.id);
        self.commit(Event::Checkpoint(c), j, a)?;
        Ok(id)
    }
    pub fn release<J: Journal, A: Authentication>(
        &mut self,
        id: &str,
        j: &mut J,
        a: &A,
    ) -> Result<()> {
        self.commit(Event::Release(id.into()), j, a)
    }
    pub fn install<J: Journal, A: Authentication>(
        &mut self,
        id: &str,
        j: &mut J,
        a: &A,
    ) -> Result<()> {
        self.commit(Event::Install(id.into()), j, a)
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
    pub(crate) fn bookkeeping(
        &self,
        inst: &Instance,
        owner: &str,
        verb: &str,
        nonce: &str,
    ) -> Result<Vec<(String, SExpr)>> {
        if !self.context.matches(inst) || !self.context.rule.operation_verbs().contains(&verb) {
            return Err("runtime does not match instance or counter verb".into());
        }
        if nonce.is_empty() || nonce.len() > 256 {
            return Err("nonce must contain 1..256 bytes".into());
        }
        let epoch = self.active_epoch(owner)?;
        let m = self.epoch(epoch)?;
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
    pub(crate) fn check_candidate(&self, inst: &Instance, candidate: &Act) -> Result<()> {
        if !self.context.matches(inst) {
            return Err("runtime instance mismatch".into());
        }
        self.operation(candidate)?;
        Ok(())
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
