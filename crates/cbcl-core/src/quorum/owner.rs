//! Durable FIFO issuance for one coherent logical account owner (SPEC-033).
use super::*;
use crate::{
    escrow::{NONCE, PREV},
    sexpr::{Atom, SExpr},
    state::Act,
};
use alloc::{collections::BTreeSet, string::String, vec::Vec};

/// Same nonforking durability/CAS contract as the validator journal. Separate
/// namespace: validator and owner logs must never share an identity accidentally.
pub trait OwnerJournal {
    fn load_owner(&self, context: &str, owner: &str) -> Result<Option<Vec<OwnerEvent>>>;
    fn append_owner(
        &mut self,
        context: &str,
        owner: &str,
        expected: Option<u64>,
        event: &OwnerEvent,
    ) -> Result<()>;
}
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(deny_unknown_fields))]
pub enum OwnerEvent {
    Initialize,
    Enqueue(Act),
    Issue {
        request: String,
        act: Act,
    },
    Freeze,
    Manifest {
        manifest: VersionManifest,
        seal: bool,
    },
    Activated(String),
    Complete(String),
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OwnerAction {
    Idle,
    /// Exact durable act plus retained prerequisites. Host supplies real act
    /// authentication envelopes and retries receiver processing until completion.
    Publish(Publication),
    /// Host obtains both VersionRequest and distinct OwnedSealRequest signatures.
    AuthorizeSeal {
        manifest: VersionManifest,
        evidence: Vec<RelayItem>,
    },
    AuthorizeVersion(VersionManifest),
    Adopt(String),
}
#[derive(Clone)]
struct Entry {
    draft: Act,
    issued: Option<Act>,
    complete: bool,
}
/// Use the same owner driver after restart. Independent devices sharing a key
/// require a single nonforking owner journal; no distributed lock is provided.
pub struct OwnerDriver {
    context: String,
    owner: String,
    sequence: u64,
    entries: Vec<Entry>,
    frozen: bool,
    manifest: Option<(VersionManifest, bool)>,
    limits: Limits,
}
impl OwnerDriver {
    fn empty(replica: &Replica, owner: &str, limits: Limits) -> Result<Self> {
        if replica.context().ownership() != crate::escrow::Ownership::Account {
            return Err("owner driver requires account ownership".into());
        }
        replica.active_epoch(owner)?;
        Ok(Self {
            context: replica.context().id().into(),
            owner: owner.into(),
            sequence: 1,
            entries: Vec::new(),
            frozen: false,
            manifest: None,
            limits,
        })
    }
    pub fn initialize<J: OwnerJournal>(
        replica: &Replica,
        owner: &str,
        limits: Limits,
        j: &mut J,
    ) -> Result<Self> {
        let driver = Self::empty(replica, owner, limits)?;
        if !replica.owner_pristine(owner) {
            return Err(
                "initialize owner journal before first issuance; existing owners must recover"
                    .into(),
            );
        }
        if limits.events == 0 || j.load_owner(&driver.context, owner)?.is_some() {
            return Err("owner journal exists or has no capacity".into());
        }
        j.append_owner(&driver.context, owner, None, &OwnerEvent::Initialize)?;
        Ok(driver)
    }
    /// Requires retained validator metadata/evidence. Re-derives every cost from
    /// immutable acts; no serialized balance/reservation cache is accepted.
    pub fn recover<J: OwnerJournal>(
        replica: &Replica,
        owner: &str,
        limits: Limits,
        j: &J,
    ) -> Result<Self> {
        let mut driver = Self::empty(replica, owner, limits)?;
        let events = j
            .load_owner(&driver.context, owner)?
            .ok_or("missing owner journal")?;
        if events.first() != Some(&OwnerEvent::Initialize) || events.len() as u64 > limits.events {
            return Err("invalid owner journal".into());
        }
        for event in events.into_iter().skip(1) {
            driver.validate(&event, replica)?;
            driver.apply(event);
            driver.sequence += 1;
        }
        driver.available(replica)?;
        Ok(driver)
    }
    fn nonce(act: &Act) -> Result<&str> {
        match act.fields.get(NONCE) {
            Some(SExpr::Atom(Atom::Str(s))) => Ok(s),
            _ => Err("missing immutable owner nonce".into()),
        }
    }
    fn check(&self, replica: &Replica) -> Result<()> {
        if replica.context().id() != self.context {
            return Err("owner context mismatch".into());
        }
        Ok(())
    }
    fn validate(&self, event: &OwnerEvent, r: &Replica) -> Result<()> {
        self.check(r)?;
        match event {
            OwnerEvent::Initialize => return Err("duplicate owner initialization".into()),
            OwnerEvent::Enqueue(a) => {
                if a.signer != self.owner || self.entries.len() >= self.limits.operations {
                    return Err("owner or queue limit mismatch".into());
                }
                r.owner_cost(a)?;
                let nonce = Self::nonce(a)?;
                if self
                    .entries
                    .iter()
                    .any(|e| Self::nonce(&e.draft).ok() == Some(nonce))
                {
                    return Err("owner nonce already reserved".into());
                }
            }
            OwnerEvent::Issue { request, act } => {
                let head = self
                    .entries
                    .iter()
                    .find(|e| !e.complete && e.issued.is_none())
                    .ok_or("no unissued request")?;
                if head.draft.address != *request || head.draft.signer != act.signer {
                    return Err("issuance is not FIFO".into());
                }
                let epoch = match act.fields.get(PREV) {
                    Some(SExpr::Atom(Atom::Symbol(s))) => s,
                    _ => return Err("missing issued epoch".into()),
                };
                if r.owner_rebase(&head.draft, epoch)? != *act {
                    return Err("issued request changed business content".into());
                }
                if self.manifest.is_some() {
                    return Err("issuance during handoff".into());
                }
                if self.frozen && !r.owner_epoch_is_owned(&self.owner, epoch)? {
                    return Err("concurrent issuance after permanent freeze".into());
                }
                if r.owner_epoch_is_owned(&self.owner, epoch)?
                    && self.entries.iter().any(|e| {
                        e.issued
                            .as_ref()
                            .is_some_and(|a| a.fields.get(PREV) == act.fields.get(PREV))
                    })
                {
                    return Err("duplicate owned slot in owner journal".into());
                }
                r.owner_batch_fits(
                    act,
                    &self
                        .entries
                        .iter()
                        .filter_map(|e| e.issued.clone())
                        .collect::<Vec<_>>(),
                )?;
                // Recovery checks immutable issuance and exact content. Current
                // active state may be later than this historical event.
            }
            OwnerEvent::Freeze => {
                if self.frozen {
                    return Err("duplicate freeze".into());
                }
            }
            OwnerEvent::Manifest { manifest, seal } => {
                if self.manifest.is_some()
                    || manifest.account != self.owner
                    || (*seal && !self.frozen)
                {
                    return Err("invalid owner manifest decision".into());
                }
                let held: BTreeSet<_> = self
                    .entries
                    .iter()
                    .filter_map(|e| e.issued.as_ref().map(|a| a.address.clone()))
                    .collect();
                if !held.is_subset(&manifest.held) {
                    return Err("owner manifest omits issued operation".into());
                }
                // Independently recompute books from the retained pinned parents.
                let mut rebuilt = r.draft_version(
                    &manifest.parents,
                    &manifest.held,
                    &manifest.refunded,
                    &manifest.credited,
                )?;
                if *seal {
                    rebuilt.phase = VersionPhase::Owned;
                }
                if rebuilt != *manifest {
                    return Err("owner manifest books mismatch".into());
                }
                for id in &manifest.held {
                    if r.certificate(VoteKind::Effects, id).is_none()
                        && r.certificate(VoteKind::Cancel, id).is_none()
                    {
                        return Err("owner manifest is not drained".into());
                    }
                }
            }
            OwnerEvent::Activated(id) => {
                let (m, seal) = self.manifest.as_ref().ok_or("no pending owner manifest")?;
                if m.id(&self.context) != *id
                    || r.version(id).is_none()
                    || (*seal && r.certificate(VoteKind::OwnedSeal, id).is_none())
                {
                    return Err("owner activation lacks certificate/metadata".into());
                }
            }
            OwnerEvent::Complete(id) => {
                if !self
                    .entries
                    .iter()
                    .any(|e| !e.complete && e.issued.as_ref().is_some_and(|a| a.address == *id))
                    || r.certificate(VoteKind::Effects, id).is_none()
                {
                    return Err("completion needs observed effects certificate".into());
                }
            }
        }
        Ok(())
    }
    fn apply(&mut self, event: OwnerEvent) {
        match event {
            OwnerEvent::Enqueue(draft) => self.entries.push(Entry {
                draft,
                issued: None,
                complete: false,
            }),
            OwnerEvent::Issue { request, act } => {
                self.entries
                    .iter_mut()
                    .find(|e| e.draft.address == request)
                    .unwrap()
                    .issued = Some(act)
            }
            OwnerEvent::Freeze => self.frozen = true,
            OwnerEvent::Manifest { manifest, seal } => self.manifest = Some((manifest, seal)),
            OwnerEvent::Activated(_) => self.manifest = None,
            OwnerEvent::Complete(id) => {
                self.entries
                    .iter_mut()
                    .find(|e| e.issued.as_ref().is_some_and(|a| a.address == id))
                    .unwrap()
                    .complete = true
            }
            OwnerEvent::Initialize => unreachable!(),
        }
    }
    fn commit<J: OwnerJournal>(&mut self, event: OwnerEvent, r: &Replica, j: &mut J) -> Result<()> {
        self.validate(&event, r)?;
        if self.sequence >= self.limits.events {
            return Err("owner journal full; reservations retained".into());
        }
        j.append_owner(&self.context, &self.owner, Some(self.sequence), &event)?;
        self.apply(event);
        self.sequence += 1;
        Ok(())
    }
    fn available(&self, r: &Replica) -> Result<Resources> {
        self.check(r)?;
        let view = r.finalized_view()?;
        let mut available = Resources {
            rights: view.rights[&self.owner],
            headroom: view.headroom.as_ref().map_or(0, |m| m[&self.owner]),
        };
        for e in &self.entries {
            if !e.complete
                && !e
                    .issued
                    .as_ref()
                    .is_some_and(|a| r.certificate(VoteKind::Effects, &a.address).is_some())
            {
                available = available.sub(r.owner_cost(&e.draft)?)?;
            }
        }
        if !available.nonnegative() {
            return Err("owner reservations exceed certified funds".into());
        }
        Ok(available)
    }
    /// A draft is built with Replica::intend; it is not published or signed yet.
    pub fn enqueue<J: OwnerJournal>(&mut self, draft: Act, r: &Replica, j: &mut J) -> Result<()> {
        if let Some(old) = self
            .entries
            .iter()
            .find(|e| Self::nonce(&e.draft).ok() == Self::nonce(&draft).ok())
        {
            if old.draft == draft {
                return Ok(());
            }
            return Err("nonce reused with changed request".into());
        }
        if !self.available(r)?.sub(r.owner_cost(&draft)?)?.nonnegative() {
            return Err("unfunded owner request".into());
        }
        self.commit(OwnerEvent::Enqueue(draft), r, j)
    }
    /// Advance deterministic local work. Every externally visible decision is
    /// durable first. Poll after importing authentic metadata/certificates.
    pub fn poll<J: OwnerJournal>(&mut self, r: &Replica, j: &mut J) -> Result<OwnerAction> {
        self.check(r)?;
        'progress: loop {
            for e in &self.entries {
                if let Some(a) = &e.issued {
                    if !e.complete && r.certificate(VoteKind::Effects, &a.address).is_some() {
                        self.commit(OwnerEvent::Complete(a.address.clone()), r, j)?;
                        continue 'progress;
                    }
                }
            }
            if let Some((m, seal)) = &self.manifest {
                let id = m.id(&self.context);
                if *seal && r.certificate(VoteKind::OwnedSeal, &id).is_none() {
                    return Ok(OwnerAction::AuthorizeSeal {
                        manifest: m.clone(),
                        evidence: r.seal_evidence(m)?,
                    });
                }
                if r.version(&id).is_none() {
                    return Ok(OwnerAction::AuthorizeVersion(m.clone()));
                }
                if r.active_epoch(&self.owner)? != id {
                    return Ok(OwnerAction::Adopt(id));
                }
                self.commit(OwnerEvent::Activated(id), r, j)?;
                continue;
            }
            let outstanding = self
                .entries
                .iter()
                .find(|e| !e.complete && e.issued.is_some());
            let head = self
                .entries
                .iter()
                .find(|e| !e.complete && e.issued.is_none());
            let Some(head) = head else {
                return match outstanding {
                    Some(e) => Ok(OwnerAction::Publish(
                        r.publication(e.issued.as_ref().unwrap())?,
                    )),
                    None => Ok(OwnerAction::Idle),
                };
            };
            let act = r.owner_rebase(&head.draft, r.active_epoch(&self.owner)?)?;
            let owned = r.owned_root(&self.owner).is_some();
            if let (true, Some(e)) = (owned, outstanding) {
                return Ok(OwnerAction::Publish(
                    r.publication(e.issued.as_ref().unwrap())?,
                ));
            }
            if (!self.frozen || owned)
                && r.owner_can_issue(
                    &act,
                    &self
                        .entries
                        .iter()
                        .filter_map(|e| e.issued.clone())
                        .collect::<Vec<_>>(),
                )
                .is_ok()
            {
                self.available(r)?;
                self.commit(
                    OwnerEvent::Issue {
                        request: head.draft.address.clone(),
                        act: act.clone(),
                    },
                    r,
                    j,
                )?;
                return Ok(OwnerAction::Publish(r.publication(&act)?));
            }
            if !self.frozen {
                self.commit(OwnerEvent::Freeze, r, j)?;
            }
            if let Some(e) = self
                .entries
                .iter()
                .find(|e| !e.complete && e.issued.is_some())
            {
                return Ok(OwnerAction::Publish(
                    r.publication(e.issued.as_ref().unwrap())?,
                ));
            }
            let issued = self
                .entries
                .iter()
                .filter_map(|e| e.issued.as_ref().map(|a| a.address.clone()))
                .collect();
            let manifest = r.owner_manifest(&self.owner, &issued)?;
            self.commit(
                OwnerEvent::Manifest {
                    manifest: manifest.clone(),
                    seal: !owned,
                },
                r,
                j,
            )?;
            return Ok(if owned {
                OwnerAction::AuthorizeVersion(manifest)
            } else {
                OwnerAction::AuthorizeSeal {
                    evidence: r.seal_evidence(&manifest)?,
                    manifest,
                }
            });
        }
    }
}
