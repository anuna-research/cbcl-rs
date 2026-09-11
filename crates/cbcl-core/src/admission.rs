//! Accepted-history admission corresponding to the paper's `Execution.Trace`.
//!
//! This is an opt-in full-message monitor. Receipt never grants acceptance.
//! Only accepted predecessors are visible to the verifier; pending candidates
//! are retained and scheduled round-robin. Hosts must drive `step` (or
//! `drain_ready`) and deliver application messages only on `Accepted` events.
//! This aligns the execution discipline; it is not a proof of Rust/Lean
//! verifier equivalence or of the host's authentication implementation.

#![forbid(unsafe_code)]

use crate::canonical::dialect_hash;
use crate::dialect::Dialect;
use crate::message::{CausedBy, Message, WrapperType};
use crate::projection::verify_causal_for_role;
use crate::protocol::{CausalViolation, VerificationResult, BEGIN_KEYWORD};
use crate::r6::{r6_instantiated_violations, r6_violations};
use crate::role::{parse_wrapper_cast, AgentKey, Cast, CausalLocality, Endpoint};
use crate::sexpr::{Atom, SExpr};
use crate::store::{ContentHash, MessageStore, ThreadId, ThreadedMessageStore};
use alloc::collections::{BTreeMap, BTreeSet, VecDeque};
use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;

/// Required immutable gate, supplied by the authenticated transport/application.
/// There is intentionally no default accepting implementation.
///
/// Implementations must authenticate the signer used by role verification AND
/// the complete semantic envelope (including cast, thread, and dialect wrappers),
/// check any required immutable syntax/shape constraints, and return its verified
/// content address. A self-asserted `signed` wrapper is not authentication.
/// Decisions must be stable for this monitor's fixed context. Revocation or
/// time-dependent policy belongs to a separate execution model.
pub trait AdmissionGate {
    fn authenticate(&self, message: &Message) -> Result<ContentHash, String>;
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AdmissionError {
    Authentication(String),
    Context(String),
    Message(String),
    ConflictingIdentity(ContentHash),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AdmissionState {
    Pending,
    Accepted,
    Rejected(CausalViolation),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AdmissionEvent {
    pub hash: ContentHash,
    pub state: AdmissionState,
}

struct Candidate {
    message: Message,
    state: AdmissionState,
}

/// One pinned thread and one concrete endpoint. All state is private; no API
/// allows arbitrary insertion into, removal from, or mutation of accepted history.
/// Pending candidates have no TTL/eviction. Hosts needing memory bounds should
/// apply backpressure before receipt; discarded input needs a retry assumption.
pub struct AdmissionMonitor<G> {
    dialect: Dialect,
    cast: Cast,
    endpoint: Endpoint,
    endpoint_key: AgentKey,
    thread: ThreadId,
    root: ContentHash,
    gate: G,
    received: BTreeMap<ContentHash, Candidate>,
    pending: VecDeque<ContentHash>,
    accepted: ThreadedMessageStore,
}

impl<G: AdmissionGate> AdmissionMonitor<G> {
    /// Freeze a fully annotated dialect and the authenticated cast-bearing root.
    /// The root is received, but acceptance still requires a scheduling step.
    /// Requires strict causal locality, an exact dialect content pin, consistent
    /// unique annotations, and R5/R6 checks. No envelope-derived routes are used.
    pub fn new(
        dialect: Dialect,
        endpoint: Endpoint,
        root: Message,
        gate: G,
    ) -> Result<Self, AdmissionError> {
        let context = |s: &str| AdmissionError::Context(String::from(s));
        if !matches!(dialect.causal_locality, CausalLocality::Reject) {
            return Err(context("admission requires full-message causal locality"));
        }
        let mut names = BTreeSet::new();
        if dialect
            .performatives
            .iter()
            .any(|p| !names.insert(p.name.as_str()))
        {
            return Err(context("duplicate performative annotations"));
        }
        let mut roles = BTreeSet::new();
        if dialect.roles.iter().any(|r| !roles.insert(r.name.as_str())) {
            return Err(context("duplicate roles"));
        }
        let protocol = dialect
            .causal_protocol
            .as_ref()
            .ok_or_else(|| context("a causal protocol is required"))?;
        if !protocol
            .steps
            .get(BEGIN_KEYWORD)
            .is_some_and(|s| s.predecessors.is_empty())
        {
            return Err(context("protocol requires a predecessor-free begin step"));
        }
        let defined: Vec<&str> = dialect
            .performatives
            .iter()
            .map(|p| p.name.as_str())
            .collect();
        if !protocol.verify_r5_protocol(&defined).is_empty()
            || protocol
                .steps
                .iter()
                .any(|(name, step)| name != &step.performative)
            || !r6_violations(&dialect).is_empty()
        {
            return Err(context("dialect fails R5/R6 or step-name consistency"));
        }
        // Require direct annotations for every runtime step (including unrolled
        // steps); do not rely on differing duplicate/base-name lookup policies.
        if protocol.steps.keys().any(|name| {
            name != BEGIN_KEYWORD
                && dialect
                    .find_performative(name)
                    .and_then(|p| p.role.as_ref())
                    .is_none()
        }) {
            return Err(context(
                "every protocol step needs a direct role annotation",
            ));
        }
        let Message::Wrapped {
            wrapper: WrapperType::WithRoles,
            params,
            ..
        } = &root
        else {
            return Err(context("root must be the outer with-roles wrapper"));
        };
        let cast = parse_wrapper_cast(params, &dialect.roles)
            .map_err(|e| AdmissionError::Context(format!("{e}")))?;
        let pin = dialect_hash(&dialect);
        if dialect.hash.as_deref() != Some(pin.as_str())
            || cast.dialect_pin.as_deref() != Some(pin.as_str())
        {
            return Err(context(
                "root and installed dialect must pin the computed dialect hash",
            ));
        }
        if !r6_instantiated_violations(&dialect, &cast).is_empty() {
            return Err(context("cast fails per-occupant causal locality"));
        }
        let endpoint_key = match (&endpoint.occupant, cast.singleton.get(&endpoint.role)) {
            (None, Some(key)) => key.clone(),
            (Some(key), None)
                if cast
                    .indexed
                    .get(&endpoint.role)
                    .is_some_and(|keys| keys.contains(key)) =>
            {
                key.clone()
            }
            _ => return Err(context("endpoint must name a sealed cast occupant")),
        };
        let thread = ThreadId(
            root.innermost_simple()
                .and_then(Message::thread)
                .ok_or_else(|| context("root requires an explicit thread"))?
                .into(),
        );
        let root_hash = gate
            .authenticate(&root)
            .map_err(AdmissionError::Authentication)?;
        let mut monitor = Self {
            dialect,
            cast,
            endpoint,
            endpoint_key,
            thread,
            root: root_hash.clone(),
            gate,
            received: BTreeMap::new(),
            pending: VecDeque::new(),
            accepted: ThreadedMessageStore::new(),
        };
        monitor.check_message(&root_hash, &root)?;
        if !matches!(monitor.verify(&root), VerificationResult::Valid) {
            return Err(context("invalid root nomination"));
        }
        monitor.received.insert(
            root_hash.clone(),
            Candidate {
                message: root,
                state: AdmissionState::Pending,
            },
        );
        monitor.pending.push_back(root_hash);
        Ok(monitor)
    }

    pub fn root(&self) -> &ContentHash {
        &self.root
    }
    pub fn thread(&self) -> &ThreadId {
        &self.thread
    }
    pub fn accepted(&self) -> &ThreadedMessageStore {
        &self.accepted
    }
    pub fn pending_len(&self) -> usize {
        self.pending.len()
    }
    pub fn state(&self, hash: &ContentHash) -> Option<&AdmissionState> {
        self.received.get(hash).map(|c| &c.state)
    }
    pub fn received_message(&self, hash: &ContentHash) -> Option<&Message> {
        self.received.get(hash).map(|c| &c.message)
    }

    /// Authenticate and retain a candidate. Duplicates do not reset queue order,
    /// repeat acceptance events, or replace either pending or accepted messages.
    pub fn receive(&mut self, message: Message) -> Result<ContentHash, AdmissionError> {
        let hash = self
            .gate
            .authenticate(&message)
            .map_err(AdmissionError::Authentication)?;
        if let Some(existing) = self.received.get(&hash) {
            return if existing.message == message {
                Ok(hash)
            } else {
                Err(AdmissionError::ConflictingIdentity(hash))
            };
        }
        self.check_message(&hash, &message)?;
        self.received.insert(
            hash.clone(),
            Candidate {
                message,
                state: AdmissionState::Pending,
            },
        );
        self.pending.push_back(hash.clone());
        Ok(hash)
    }

    /// Perform one bounded queue visit. Missing ACCEPTED predecessors yield
    /// Pending before calling the eager verifier, including a missing root.
    /// With repeated calls, tail insertion prevents new arrivals starving an
    /// existing candidate. This bounds visits, not verifier cost or memory.
    pub fn step(&mut self) -> Option<AdmissionEvent> {
        let hash = self.pending.pop_front()?;
        let candidate = self.received.get(&hash).expect("queued candidate exists");
        let state = if !self.resolved(&hash, &candidate.message) {
            AdmissionState::Pending
        } else {
            match self.verify(&candidate.message) {
                VerificationResult::Valid => AdmissionState::Accepted,
                VerificationResult::Unknown => AdmissionState::Pending,
                VerificationResult::Violation(e) => AdmissionState::Rejected(e),
            }
        };
        if matches!(state, AdmissionState::Accepted) {
            // Verification used the pre-insertion accepted store. No candidate
            // can satisfy its own predecessor reference by being stored early.
            self.accepted
                .append(hash.clone(), self.thread.clone(), candidate.message.clone());
        } else if matches!(state, AdmissionState::Pending) {
            self.pending.push_back(hash.clone());
        }
        self.received
            .get_mut(&hash)
            .expect("candidate exists")
            .state = state.clone();
        Some(AdmissionEvent { hash, state })
    }

    /// Drain finite queued input to a fixed point; retain unresolved candidates.
    /// Returns only new acceptance/rejection events, in admission order. Calling
    /// after each receipt discharges reconsideration for finite input; hosts
    /// under continuous input can interleave receive and step instead.
    pub fn drain_ready(&mut self) -> Vec<AdmissionEvent> {
        let mut events = Vec::new();
        loop {
            let mut progress = false;
            for _ in 0..self.pending.len() {
                let event = self.step().expect("round started with queued candidate");
                if !matches!(event.state, AdmissionState::Pending) {
                    progress = true;
                    events.push(event);
                }
            }
            if !progress {
                return events;
            }
        }
    }

    fn verify(&self, message: &Message) -> VerificationResult {
        verify_causal_for_role(
            message,
            &self.endpoint,
            &self.dialect,
            &self.cast,
            &self.accepted,
            &self.thread,
            &self.root,
        )
    }

    fn resolved(&self, hash: &ContentHash, message: &Message) -> bool {
        if hash == &self.root {
            return true;
        }
        if !self.accepted.contains(&self.root, &self.thread) {
            return false;
        }
        match message.innermost_simple().and_then(Message::caused_by) {
            Some(CausedBy::Single(h)) => self
                .accepted
                .contains(&ContentHash(h.clone()), &self.thread),
            Some(CausedBy::Multiple(hs)) => hs.iter().all(|h| {
                self.accepted
                    .contains(&ContentHash(h.clone()), &self.thread)
            }),
            _ => false, // rejected at receive; never interpreted as a second root
        }
    }

    fn check_message(&self, hash: &ContentHash, message: &Message) -> Result<(), AdmissionError> {
        let error = |s: &str| AdmissionError::Message(String::from(s));
        let simple = message
            .innermost_simple()
            .ok_or_else(|| error("simple payload required"))?;
        if simple.thread() != Some(self.thread.0.as_str()) {
            return Err(error("message must explicitly name the pinned thread"));
        }
        let is_root = hash == &self.root;
        let mut cur = message;
        let mut signer = None;
        loop {
            match cur {
                Message::Wrapped {
                    wrapper,
                    params,
                    content,
                } => {
                    if *wrapper == WrapperType::WithRoles
                        && !(is_root && core::ptr::eq(cur, message))
                    {
                        return Err(error("only the pinned outer root may carry a cast"));
                    }
                    if *wrapper == WrapperType::Signed {
                        if signer.is_some() {
                            return Err(error("ambiguous nested signatures"));
                        }
                        signer = match params.first() {
                            Some(SExpr::Atom(Atom::Symbol(key))) => Some(key.as_str()),
                            _ => return Err(error("signed wrapper requires a signer key")),
                        };
                    }
                    cur = content;
                }
                Message::Dialect {
                    dialect_name,
                    inner,
                } => {
                    if dialect_name != &self.dialect.name {
                        return Err(error("wrong dialect wrapper"));
                    }
                    cur = inner;
                }
                _ => break,
            }
        }
        let signer = signer.ok_or_else(|| error("authenticated signed wrapper required"))?;
        if is_root {
            if message.wrapper_type() != Some(WrapperType::WithRoles)
                || !matches!(simple.caused_by(), Some(CausedBy::Begin))
            {
                return Err(error("root must be predecessor-free with-roles nomination"));
            }
            return Ok(());
        }
        if !matches!(simple.caused_by(), Some(CausedBy::Single(_)))
            && !matches!(simple.caused_by(), Some(CausedBy::Multiple(hs)) if !hs.is_empty())
        {
            return Err(error(
                "non-root messages require explicit predecessor hashes",
            ));
        }
        let perf = simple
            .performative()
            .expect("simple has performative")
            .name();
        if !self
            .dialect
            .causal_protocol
            .as_ref()
            .expect("protocol checked")
            .steps
            .contains_key(perf)
            || perf == BEGIN_KEYWORD
        {
            return Err(error("performative is not a protocol step"));
        }
        let ann = self
            .dialect
            .find_performative(perf)
            .and_then(|p| p.role.as_ref())
            .ok_or_else(|| error("missing role annotation"))?;
        // Both role and concrete key matter for indexed sender roles: another
        // occupant's send is not this endpoint's send unless it is also a receive.
        let sends = ann.from == self.endpoint.role && signer == self.endpoint_key.0;
        let receives = ann.to.contains(&self.endpoint.role)
            && simple
                .recipient_set()
                .contains(self.endpoint_key.0.as_str());
        if !sends && !receives {
            return Err(error("message is not relevant to this endpoint"));
        }
        Ok(())
    }
}
