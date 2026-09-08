//! Agent: a CBCL participant with beliefs, dialects, and message queues.
//!
//! Mirrors `Agent.lean` from the Lean 4 proof library (lines 16–39).
//! The Agent struct holds mutable state for dialect installation, belief
//! management, and conversation threading.

#![forbid(unsafe_code)]

use alloc::collections::{BTreeMap, BTreeSet, VecDeque};
use alloc::string::String;
use alloc::sync::Arc;
use alloc::vec::Vec;

use crate::clock::{Clock, NoClock};
use crate::dialect::{Dialect, DialectInstallError, DialectRegistry};
use crate::evaluator::{Effect, EvalError, EvalResult};
use crate::message::{CausedBy, Message};
use crate::policy::{
    apply_policy, DropReason, PendingEntry, PendingQueue, PendingReason, PolicyOutcome,
    UnknownPredecessorPolicy,
};
use crate::protocol::{verify_causal, CausalViolation, VerificationResult};
use crate::sexpr::SExpr;
use crate::store::{ContentHash, MessageStore, ThreadId, ThreadedMessageStore};

/// A CBCL agent (REQ-030).
///
/// An agent is a participant in the CBCL protocol with:
/// - a unique identifier
/// - a set of beliefs (S-expressions)
/// - a dialect registry (always containing the base dialect at index 0)
/// - a message queue for incoming messages
/// - conversation threads indexed by thread id
///
/// # Well-formedness Invariant
///
/// An agent is well-formed iff `self.dialect_registry.is_well_formed()`,
/// i.e. the base dialect is always installed at index 0. `Agent::new()`
/// guarantees this invariant, and no method on `Agent` can violate it.
#[derive(Debug, Clone)]
pub struct Agent {
    id: String,
    beliefs: BTreeSet<SExpr>,
    dialect_registry: DialectRegistry,
    message_queue: VecDeque<Message>,
    conversation_threads: BTreeMap<String, Vec<Message>>,
    /// Per-thread message store consulted during causal verification (REQ-300).
    message_store: ThreadedMessageStore,
    /// Policy for handling `VerificationResult::Unknown` (REQ-305).
    policy: UnknownPredecessorPolicy,
    /// Buffered messages awaiting predecessor arrival under the Buffer policy.
    pending_queue: PendingQueue,
    /// How outcomes from multiple matching protocols are combined.
    merge_policy: MergePolicy,
    /// Time source for buffered-entry timestamps and TTL expiry. Defaults to
    /// [`NoClock`], which yields `u64::MAX` so entries never expire — opt
    /// into TTL by injecting a real clock via [`Agent::with_clock`].
    clock: Arc<dyn Clock>,
}

/// How the agent combines verdicts when several installed protocols declare a
/// step for the same performative.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum MergePolicy {
    /// Strictest verdict wins: any `Reject` rejects, any `Pending`/`Buffered`
    /// short-circuits before `Accept`. This is the fail-closed default and
    /// matches the live verification path the parser pipeline uses.
    #[default]
    Conjunction,
    /// A single `Accept` is enough to apply the message. `Reject` only fires
    /// when *every* matching protocol rejects; otherwise `Pending`/`Buffered`
    /// is preserved if no protocol accepted. Useful when multiple protocols
    /// represent alternative permitted behaviours rather than a stack of
    /// constraints to satisfy together.
    ///
    /// **Security surface.** Disjunction widens trust: with mixed-trust
    /// dialects, an attacker who can install one permissive protocol can
    /// override another protocol's rejection. Only opt in when every
    /// installable dialect is trusted to the same level — typically when
    /// they originated from the same authority or were verified by R4.
    /// The pipeline (`run_pipeline_full`) is conjunction-only and remains
    /// the right entry point for receive-side fail-closed enforcement.
    Disjunction,
}

/// Combine two `PolicyOutcome` values under [`MergePolicy::Conjunction`]:
/// `Reject` > `Pending` > `Buffered` > `Accept`. The strictest outcome wins
/// so any single protocol can fail-close regardless of what other protocols
/// say.
///
/// When both inputs are `Pending`, the left-hand reason is preserved. Today
/// `PendingReason` has only one variant, so the choice is moot, but the arm
/// is explicit so that adding new reasons doesn't silently drop one of them.
fn merge_policy_outcomes(a: PolicyOutcome, b: PolicyOutcome) -> PolicyOutcome {
    use PolicyOutcome::*;
    match (a, b) {
        (Reject(v), _) | (_, Reject(v)) => Reject(v),
        (Pending(left), Pending(_right)) => Pending(left),
        (Pending(r), _) | (_, Pending(r)) => Pending(r),
        (Buffered, _) | (_, Buffered) => Buffered,
        (Accept, Accept) => Accept,
    }
}

/// Combine two `PolicyOutcome` values under [`MergePolicy::Disjunction`]:
/// any `Accept` accepts. Otherwise `Pending` > `Buffered` > `Reject`, with
/// the left-hand `Reject` preserved when both inputs reject (the disjunction
/// only collapses to a rejection when no matching protocol accepted *and* no
/// matching protocol left the message pending).
fn merge_policy_outcomes_disjunctive(a: PolicyOutcome, b: PolicyOutcome) -> PolicyOutcome {
    use PolicyOutcome::*;
    match (a, b) {
        (Accept, _) | (_, Accept) => Accept,
        (Pending(r), _) | (_, Pending(r)) => Pending(r),
        (Buffered, _) | (_, Buffered) => Buffered,
        (Reject(v), _) => Reject(v),
    }
}

/// Combine two `VerificationResult`s under "any-accept" disjunction
/// semantics, in lock-step with [`merge_policy_outcomes_disjunctive`].
///
/// This is *not* the same as [`VerificationResult::join`]: `join` is the
/// information-theoretic LUB used for `(any ...)` fan-in inside a single
/// protocol, where a definitive `Violation` outranks an undecided
/// `Unknown`. Across multiple matching protocols under disjunction, an
/// `Unknown` from one protocol must be preserved over a `Violation` from
/// another — the Unknown protocol might still resolve to `Valid` once its
/// predecessor arrives, and a single `Valid` is enough to accept the
/// message. Collapsing to `Violation` would prematurely flush such entries
/// from the pending queue.
///
/// Truth table (commutative):
/// - `Valid ⊔ _ = Valid`           (any accept wins)
/// - `Unknown ⊔ Violation = Unknown` (preserve hope)
/// - `Unknown ⊔ Unknown = Unknown`
/// - `Violation ⊔ Violation = Violation`  (only when no protocol could accept)
fn merge_disjunctive_result(a: VerificationResult, b: VerificationResult) -> VerificationResult {
    use VerificationResult::*;
    match (a, b) {
        (Valid, _) | (_, Valid) => Valid,
        (Unknown, _) | (_, Unknown) => Unknown,
        (Violation(v), _) => Violation(v),
    }
}

/// Whether a `:caused-by` reference is *resolved* — every hash it names
/// present in `thread`'s store (SPEC-003 REQ-315). `Begin` (and an absent
/// `:caused-by`) name no hashes and count as resolved; `Single`/`Multiple`
/// check each hash's presence via the store's hash index.
fn caused_by_resolved(
    caused_by: Option<&CausedBy>,
    store: &ThreadedMessageStore,
    thread: &ThreadId,
) -> bool {
    match caused_by {
        None | Some(CausedBy::Begin) => true,
        Some(CausedBy::Single(h)) => store.contains(&ContentHash(h.clone()), thread),
        Some(CausedBy::Multiple(hs)) => hs
            .iter()
            .all(|h| store.contains(&ContentHash(h.clone()), thread)),
    }
}

/// Resolution gate (SPEC-003 REQ-315): a `Violation` reached while some
/// named `:caused-by` hash is still absent from the store is *provisional*
/// — under an `(any …)` clause the eager clause algebra can supersede it
/// with `Valid` at resolution (the lattice's monotonicity is
/// valid-is-sticky, not violation-is-sticky, before resolution) — so
/// action must wait: the verdict is downgraded to `Unknown`, making the
/// Reject policy answer `CausalPending` and the Buffer policy enqueue,
/// exactly as for any `Unknown`. A *resolved* `Violation` (every named
/// hash present) is permanent under store growth and still maps to
/// `Reject`.
fn gate_unresolved_violation(result: VerificationResult, resolved: bool) -> VerificationResult {
    if !resolved && matches!(result, VerificationResult::Violation(_)) {
        VerificationResult::Unknown
    } else {
        result
    }
}

/// Outcome of [`Agent::evaluate_and_apply`] (REQ-231 fail-closed contract).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AgentOutcome {
    /// Causal verification succeeded (or was not applicable) and the message
    /// was evaluated, with effects applied to the agent.
    Applied(EvalResult),
    /// Causal protocol violation; message was not evaluated.
    CausalReject(CausalViolation),
    /// Predecessor not yet in the local store under [`UnknownPredecessorPolicy::Reject`];
    /// senders should retry once the predecessor arrives.
    Pending(PendingReason),
    /// Predecessor not yet in the local store under [`UnknownPredecessorPolicy::Buffer`];
    /// the agent has enqueued the message for later re-evaluation.
    Buffered,
    /// Evaluator failure (template expansion, unknown performative, etc.).
    EvalError(EvalError),
}

impl Agent {
    /// Create a new agent with the given id, bootstrapped with the base dialect (REQ-031).
    ///
    /// The returned agent is always well-formed: the dialect registry
    /// contains exactly the base dialect.
    pub fn new(id: impl Into<String>) -> Self {
        Self::with_policy(id, UnknownPredecessorPolicy::default())
    }

    /// Create a new agent with the given id and unknown-predecessor policy.
    pub fn with_policy(id: impl Into<String>, policy: UnknownPredecessorPolicy) -> Self {
        let pending_queue = match &policy {
            UnknownPredecessorPolicy::Buffer { max_pending, ttl } => {
                PendingQueue::new(*max_pending, *ttl)
            }
            UnknownPredecessorPolicy::Reject => PendingQueue::new(0, 0),
        };
        Self {
            id: id.into(),
            beliefs: BTreeSet::new(),
            dialect_registry: DialectRegistry::new(),
            message_queue: VecDeque::new(),
            conversation_threads: BTreeMap::new(),
            message_store: ThreadedMessageStore::new(),
            policy,
            pending_queue,
            merge_policy: MergePolicy::default(),
            clock: Arc::new(NoClock),
        }
    }

    /// Set how outcomes from multiple matching protocols are combined.
    /// Defaults to [`MergePolicy::Conjunction`] (fail-closed).
    pub fn with_merge_policy(mut self, merge_policy: MergePolicy) -> Self {
        self.merge_policy = merge_policy;
        self
    }

    /// Returns the configured merge policy.
    pub fn merge_policy(&self) -> MergePolicy {
        self.merge_policy
    }

    /// Inject a [`Clock`] for buffered-entry timestamps and TTL expiry.
    ///
    /// Without this, the agent uses [`NoClock`] which stamps every buffered
    /// entry with `u64::MAX`, so TTL never fires. Pass [`crate::clock::SystemClock`]
    /// (with the `std` feature) to use real time, or any custom `Clock`
    /// implementation — useful for deterministic tests.
    pub fn with_clock<C: Clock + 'static>(mut self, clock: C) -> Self {
        self.clock = Arc::new(clock);
        self
    }

    /// Returns a reference to the agent's message store.
    pub fn message_store(&self) -> &ThreadedMessageStore {
        &self.message_store
    }

    /// Mutable access to the agent's message store. Callers manage content
    /// hashing — the agent itself does not synthesize hashes.
    pub fn message_store_mut(&mut self) -> &mut ThreadedMessageStore {
        &mut self.message_store
    }

    /// Returns the configured unknown-predecessor policy.
    pub fn policy(&self) -> &UnknownPredecessorPolicy {
        &self.policy
    }

    /// Number of buffered (pending) messages awaiting predecessor arrival.
    pub fn pending_len(&self) -> usize {
        self.pending_queue.len()
    }

    /// Returns the agent's identifier.
    pub fn id(&self) -> &str {
        &self.id
    }

    // -- Well-formedness --

    /// Check whether this agent is well-formed (REQ-032).
    ///
    /// An agent is well-formed iff the base dialect is installed at index 0
    /// of the dialect registry. Mirrors `Agent.isWellFormed` in `Agent.lean`.
    pub fn is_well_formed(&self) -> bool {
        self.dialect_registry.is_well_formed()
    }

    // -- Dialect management --

    /// Returns a reference to the dialect registry.
    pub fn dialect_registry(&self) -> &DialectRegistry {
        &self.dialect_registry
    }

    /// Every installed dialect defining `name`, in installation order
    /// (REQ-033).
    ///
    /// Introspection only. Dispatch never uses it: a custom performative is
    /// resolved against the dialect named by its `(lang …)` wrapper, so more
    /// than one result here is normal rather than a conflict.
    pub fn dialects_defining<'a>(&'a self, name: &'a str) -> impl Iterator<Item = &'a Dialect> {
        self.dialect_registry.dialects_defining(name)
    }

    /// Install a dialect after verifying R1, R2, and R3 (REQ-034).
    ///
    /// Delegates to `DialectRegistry::install`. The well-formedness
    /// invariant is preserved because install only appends.
    pub fn install_dialect(&mut self, d: Dialect) -> Result<(), DialectInstallError> {
        self.dialect_registry.install(d)
    }

    // -- Beliefs --

    /// Returns a reference to the agent's belief set.
    pub fn beliefs(&self) -> &BTreeSet<SExpr> {
        &self.beliefs
    }

    /// Add a belief to the agent's belief set.
    /// Returns `true` if the belief was newly inserted.
    pub fn add_belief(&mut self, belief: SExpr) -> bool {
        self.beliefs.insert(belief)
    }

    /// Remove a belief from the agent's belief set.
    /// Returns `true` if the belief was present.
    pub fn remove_belief(&mut self, belief: &SExpr) -> bool {
        self.beliefs.remove(belief)
    }

    /// Check whether the agent holds a given belief.
    pub fn has_belief(&self, belief: &SExpr) -> bool {
        self.beliefs.contains(belief)
    }

    // -- Message queue --

    /// Returns a reference to the message queue.
    pub fn message_queue(&self) -> &VecDeque<Message> {
        &self.message_queue
    }

    /// Enqueue a message at the back of the message queue.
    pub fn enqueue_message(&mut self, msg: Message) {
        self.message_queue.push_back(msg);
    }

    /// Dequeue a message from the front of the message queue.
    pub fn dequeue_message(&mut self) -> Option<Message> {
        self.message_queue.pop_front()
    }

    /// Returns the number of messages in the queue.
    pub fn message_queue_len(&self) -> usize {
        self.message_queue.len()
    }

    // -- Conversation threads --

    /// Returns a reference to all conversation threads.
    pub fn conversation_threads(&self) -> &BTreeMap<String, Vec<Message>> {
        &self.conversation_threads
    }

    /// Get the messages in a specific conversation thread.
    pub fn thread(&self, thread_id: &str) -> Option<&[Message]> {
        self.conversation_threads
            .get(thread_id)
            .map(|v| v.as_slice())
    }

    /// Append a message to a conversation thread, creating the thread if needed.
    pub fn append_to_thread(&mut self, thread_id: impl Into<String>, msg: Message) {
        self.conversation_threads
            .entry(thread_id.into())
            .or_default()
            .push(msg);
    }

    // -- Evaluation --

    /// Evaluate a message and apply its effects to this agent.
    ///
    /// Pipeline (REQ-231 fail-closed):
    /// 1. Causal verification against the agent's dialect registry, message
    ///    store, and configured [`UnknownPredecessorPolicy`].
    /// 2. On `Accept`: evaluate the message and apply its effects.
    /// 3. On a *resolved* `Violation`: return [`AgentOutcome::CausalReject`]
    ///    without applying. A provisional `Violation` — some named
    ///    `:caused-by` hash still absent from the store — is downgraded to
    ///    `Unknown` first (SPEC-003 REQ-315), so it follows 4/5 instead.
    /// 4. On `Unknown` + `Reject` policy: return [`AgentOutcome::Pending`].
    /// 5. On `Unknown` + `Buffer` policy: enqueue in the pending queue and
    ///    return [`AgentOutcome::Buffered`]; the message is *not* applied.
    ///
    /// Buffered entries are timestamped via the injected [`Clock`]. With the
    /// default [`NoClock`] this is `u64::MAX`, so [`Self::expire`] will never
    /// drain them. Inject a real clock via [`Self::with_clock`] (or call
    /// [`Self::evaluate_and_apply_at`] for an explicit one-off override) to
    /// enable TTL-based eviction.
    pub fn evaluate_and_apply(&mut self, msg: &Message) -> AgentOutcome {
        let now = self.clock.now();
        self.evaluate_and_apply_at(msg, now)
    }

    /// Like [`Self::evaluate_and_apply`] but stamps any newly-buffered entry
    /// with the supplied `now` (seconds since epoch), bypassing the injected
    /// clock. Useful for tests or when the caller wants per-message control
    /// over the timestamp.
    pub fn evaluate_and_apply_at(&mut self, msg: &Message, now: u64) -> AgentOutcome {
        // Step 1: causal verification (only meaningful for Simple messages with a
        // performative whose owning dialect declares a causal protocol).
        if let Some(verdict) = self.causal_verdict(msg) {
            match verdict {
                PolicyOutcome::Accept => {}
                PolicyOutcome::Reject(cv) => return AgentOutcome::CausalReject(cv),
                PolicyOutcome::Pending(reason) => return AgentOutcome::Pending(reason),
                PolicyOutcome::Buffered => {
                    self.buffer_pending(msg, now);
                    return AgentOutcome::Buffered;
                }
            }
        }

        // Step 2: evaluate and apply.
        let result = match crate::evaluator::evaluate(msg, &self.dialect_registry) {
            Ok(r) => r,
            Err(e) => return AgentOutcome::EvalError(e),
        };

        for effect in &result.effects {
            match effect {
                Effect::StoreBelief(belief) => {
                    self.add_belief(belief.clone());
                }
                Effect::RemoveBelief(belief) => {
                    self.remove_belief(belief);
                }
                _ => {
                    // Other effects (send, announce, etc.) are returned to the
                    // caller for external handling — the agent cannot perform
                    // I/O itself.
                }
            }
        }

        if let Some(ref thread_id) = result.thread {
            self.append_to_thread(thread_id.clone(), msg.clone());
        }

        AgentOutcome::Applied(result)
    }

    /// Run causal verification + policy mapping for a message.
    ///
    /// Returns `None` when no installed protocol constrains the message —
    /// the innermost payload is not Simple, or no installed dialect declares
    /// a protocol step for its performative.
    ///
    /// Multiple installed dialects may declare protocols for the same
    /// performative (notably child dialects constraining a base/inherited
    /// performative such as `ok`); constraints compose by conjunction so any
    /// rejection short-circuits, with `Pending`/`Buffered` outranking
    /// `Accept`. This mirrors the full pipeline's step 6a.
    ///
    /// Each per-protocol verdict passes through the REQ-315 resolution gate
    /// ([`gate_unresolved_violation`]) before [`apply_policy`], so only
    /// resolved `Violation`s can become `Reject`.
    fn causal_verdict(&self, msg: &Message) -> Option<PolicyOutcome> {
        let inner = msg.innermost_simple()?;
        let (caused_by, thread, perf_name) = match inner {
            Message::Simple {
                caused_by,
                thread,
                performative,
                ..
            } => (caused_by.as_ref(), thread.as_ref(), performative.name()),
            _ => return None,
        };

        let thread_id = ThreadId(thread.cloned().unwrap_or_else(|| String::from("default")));

        // SPEC-003 REQ-315: resolvedness is a property of the message and
        // store alone, shared by every matching protocol's verdict.
        let resolved = caused_by_resolved(caused_by, &self.message_store, &thread_id);

        let mut decision: Option<PolicyOutcome> = None;
        for d in self.dialect_registry.iter() {
            let Some(ref proto) = d.causal_protocol else {
                continue;
            };
            if !proto.steps.contains_key(perf_name) {
                continue;
            }
            let result =
                verify_causal(perf_name, caused_by, &self.message_store, proto, &thread_id);
            let result = gate_unresolved_violation(result, resolved);
            let outcome = apply_policy(&result, &self.policy);
            decision = Some(match decision {
                None => outcome,
                Some(prev) => match self.merge_policy {
                    MergePolicy::Conjunction => merge_policy_outcomes(prev, outcome),
                    MergePolicy::Disjunction => merge_policy_outcomes_disjunctive(prev, outcome),
                },
            });
            // Conjunction can short-circuit on Reject (any rejection wins);
            // Disjunction can short-circuit on Accept (any accept wins).
            match (self.merge_policy, &decision) {
                (MergePolicy::Conjunction, Some(PolicyOutcome::Reject(_))) => break,
                (MergePolicy::Disjunction, Some(PolicyOutcome::Accept)) => break,
                _ => {}
            }
        }
        decision
    }

    /// Enqueue a message in the pending queue under the Buffer policy.
    ///
    /// Buffers the original (possibly wrapped) message, but uses the
    /// innermost Simple's caused_by/thread/performative for re-evaluation
    /// keys so wrapped pending messages are handled identically to bare ones.
    /// `now` (seconds since epoch) is stamped onto the entry for use by
    /// [`Self::expire`]; callers that don't need TTL semantics can pass
    /// `u64::MAX` to opt out.
    fn buffer_pending(&mut self, msg: &Message, now: u64) {
        let Some(inner) = msg.innermost_simple() else {
            return;
        };
        let Message::Simple {
            caused_by,
            thread,
            performative,
            ..
        } = inner
        else {
            return;
        };
        let thread_id = ThreadId(thread.clone().unwrap_or_else(|| String::from("default")));

        // The agent does not synthesize content hashes; store an empty hash for
        // the buffered entry. Callers that re-evaluate will look up by
        // :caused-by, which is what verify_causal needs.
        let entry = PendingEntry {
            hash: ContentHash(String::new()),
            message: msg.clone(),
            thread: thread_id,
            performative: String::from(performative.name()),
            caused_by: caused_by.clone(),
            inserted_at: now,
        };
        self.pending_queue.enqueue(entry);
    }

    /// Drop buffered entries whose TTL has elapsed at `now` (seconds since
    /// epoch). Returns the dropped entries with [`DropReason::CausalTimeout`].
    ///
    /// Entries stamped with `u64::MAX` (the default when the agent is
    /// constructed without a clock and [`Self::evaluate_and_apply`] is used)
    /// never expire. To get TTL behaviour, either inject a real clock via
    /// [`Self::with_clock`] or pass an explicit timestamp via
    /// [`Self::evaluate_and_apply_at`] / [`Self::step_at`].
    ///
    /// **Eviction is pull-based.** The agent does not call `expire` on its
    /// own — the embedder is responsible for invoking it on a schedule that
    /// matches the configured TTL (e.g. once per second, once per minute).
    /// Without that, expired entries linger in the queue until the next
    /// caller-driven invocation, holding memory but not causing
    /// correctness issues. A future revision could opt-in to expire-on-each
    /// `evaluate_and_apply` if it becomes a footgun in practice.
    pub fn expire(&mut self, now: u64) -> Vec<(PendingEntry, DropReason)> {
        self.pending_queue.expire(now)
    }

    /// Re-evaluate buffered messages against the (possibly grown) message store.
    ///
    /// Returns the entries that now resolve to either `Accept` or `Reject`.
    /// Entries whose performative isn't constrained by any installed
    /// protocol stay buffered (rather than being spuriously accepted by an
    /// unrelated protocol — `verify_causal` returns `Valid` for performatives
    /// outside a protocol's step set, so iterating naively over every
    /// installed protocol would flush entries that are still waiting on
    /// their real predecessor).
    ///
    /// When multiple protocols constrain the same performative, results
    /// compose by conjunction (any rejection rejects, any `Unknown` keeps
    /// pending) — the same semantics as the live verification path.
    ///
    /// The caller is responsible for re-applying accepted messages; the
    /// agent does not auto-apply them, since [`Agent::evaluate_and_apply`]
    /// mutates state and the caller may want explicit control over re-entry.
    pub fn reevaluate_pending(&mut self) -> Vec<(PendingEntry, PolicyOutcome)> {
        let registry = &self.dialect_registry;
        let store = &self.message_store;
        let merge = self.merge_policy;
        self.pending_queue.re_evaluate_with(|entry, thread_id| {
            // SPEC-003 REQ-315: same resolution gate as the live path — a
            // still-provisional Violation keeps the entry pending rather
            // than flushing it as Reject.
            let resolved = caused_by_resolved(entry.caused_by.as_ref(), store, thread_id);
            let mut combined: Option<VerificationResult> = None;
            for d in registry.iter() {
                let Some(ref proto) = d.causal_protocol else {
                    continue;
                };
                if !proto.steps.contains_key(entry.performative.as_str()) {
                    continue;
                }
                let r = verify_causal(
                    &entry.performative,
                    entry.caused_by.as_ref(),
                    store,
                    proto,
                    thread_id,
                );
                let r = gate_unresolved_violation(r, resolved);
                combined = Some(match combined {
                    None => r,
                    Some(prev) => match merge {
                        // Conjunction = lattice meet (Unknown < Valid; Valid ⊓ Violation = Violation).
                        MergePolicy::Conjunction => prev.meet(r),
                        // Disjunction = "any-accept" merge (Valid wins; Unknown
                        // outranks Violation so a still-pending protocol can
                        // resolve later — see `merge_disjunctive_result`).
                        MergePolicy::Disjunction => merge_disjunctive_result(prev, r),
                    },
                });
            }
            combined
        })
    }

    /// Dequeue the next message, evaluate it, and apply effects.
    ///
    /// Returns `None` if the queue is empty. Buffered entries inherit the
    /// `u64::MAX` timestamp from [`Self::evaluate_and_apply`]; use
    /// [`Self::step_at`] when TTL semantics are required.
    pub fn step(&mut self) -> Option<AgentOutcome> {
        let msg = self.dequeue_message()?;
        Some(self.evaluate_and_apply(&msg))
    }

    /// Like [`Self::step`] but stamps any newly-buffered entry with `now`.
    pub fn step_at(&mut self, now: u64) -> Option<AgentOutcome> {
        let msg = self.dequeue_message()?;
        Some(self.evaluate_and_apply_at(&msg, now))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dialect::{PerformativeDef, ResourceBounds};
    use crate::message::{CorePerformative, Performative};
    use crate::sexpr::Atom;

    fn valid_custom_dialect(name: &str) -> Dialect {
        Dialect {
            roles: Vec::new(),
            causal_locality: Default::default(),
            name: String::from(name),
            extends: Vec::new(),
            author: None,
            performatives: vec![PerformativeDef {
                role: None,
                name: String::from("custom-action"),
                params: Vec::new(),
                template: SExpr::List(alloc::vec![
                    SExpr::Atom(Atom::Symbol(String::from("effect"))),
                    SExpr::Atom(Atom::Symbol(String::from("custom"))),
                ]),
            }],
            resources: ResourceBounds {
                max_depth: 8,
                max_expansion_size: 512,
                verification_time_ms: 10,
            },
            examples: Vec::new(),
            signature: None,
            hash: None,
            protocol: None,
            causal_protocol: None,
            shapes: Vec::new(),
        }
    }

    fn simple_tell(content: &str) -> Message {
        Message::Simple {
            performative: Performative::Core(CorePerformative::Tell),
            recipient: None,
            content: SExpr::Atom(Atom::Str(String::from(content))),
            params: Vec::new(),
            thread: None,
            sender: None,
            caused_by: None,
        }
    }

    // -- Construction and well-formedness --

    #[test]
    fn new_agent_is_well_formed() {
        let agent = Agent::new("agent-1");
        assert!(agent.is_well_formed());
        assert_eq!(agent.id(), "agent-1");
    }

    #[test]
    fn new_agent_has_base_dialect() {
        let agent = Agent::new("a");
        assert_eq!(agent.dialect_registry().len(), 1);
        assert_eq!(agent.dialect_registry().get(0).unwrap().name, "cbcl-base");
    }

    #[test]
    fn new_agent_has_empty_beliefs() {
        let agent = Agent::new("a");
        assert!(agent.beliefs().is_empty());
    }

    #[test]
    fn new_agent_has_empty_message_queue() {
        let agent = Agent::new("a");
        assert_eq!(agent.message_queue_len(), 0);
        assert!(agent.message_queue().is_empty());
    }

    #[test]
    fn new_agent_has_empty_threads() {
        let agent = Agent::new("a");
        assert!(agent.conversation_threads().is_empty());
    }

    // -- Dialect management --

    #[test]
    fn install_dialect_preserves_well_formedness() {
        let mut agent = Agent::new("a");
        agent.install_dialect(valid_custom_dialect("ext")).unwrap();
        assert!(agent.is_well_formed());
        assert_eq!(agent.dialect_registry().len(), 2);
    }

    #[test]
    fn dialects_defining_finds_custom() {
        let mut agent = Agent::new("a");
        agent.install_dialect(valid_custom_dialect("ext")).unwrap();
        let names: Vec<&str> = agent
            .dialects_defining("custom-action")
            .map(|d| d.name.as_str())
            .collect();
        assert_eq!(names, vec!["ext"]);
    }

    /// REQ-033: two dialects defining one performative name is legitimate —
    /// the `(lang …)` wrapper says which is meant — so introspection reports
    /// both rather than treating the second as a conflict.
    #[test]
    fn dialects_defining_reports_every_definer() {
        let mut agent = Agent::new("a");
        agent.install_dialect(valid_custom_dialect("ext")).unwrap();
        agent.install_dialect(valid_custom_dialect("ext2")).unwrap();
        let names: Vec<&str> = agent
            .dialects_defining("custom-action")
            .map(|d| d.name.as_str())
            .collect();
        assert_eq!(names, vec!["ext", "ext2"]);
    }

    #[test]
    fn install_bad_dialect_rejected() {
        let mut agent = Agent::new("a");
        let bad = Dialect {
            roles: Vec::new(),
            causal_locality: Default::default(),
            name: String::from("bad"),
            extends: Vec::new(),
            author: None,
            performatives: vec![PerformativeDef {
                role: None,
                name: String::from("tell"), // R3 violation: redefines core
                params: Vec::new(),
                template: SExpr::Atom(Atom::Symbol(String::from("x"))),
            }],
            resources: ResourceBounds {
                max_depth: 8,
                max_expansion_size: 512,
                verification_time_ms: 10,
            },
            examples: Vec::new(),
            signature: None,
            hash: None,
            protocol: None,
            causal_protocol: None,
            shapes: Vec::new(),
        };
        assert!(agent.install_dialect(bad).is_err());
        // Still well-formed, still only base dialect
        assert!(agent.is_well_formed());
        assert_eq!(agent.dialect_registry().len(), 1);
    }

    // -- Beliefs --

    #[test]
    fn add_and_check_belief() {
        let mut agent = Agent::new("a");
        let belief = SExpr::Atom(Atom::Symbol(String::from("sky-is-blue")));
        assert!(!agent.has_belief(&belief));
        assert!(agent.add_belief(belief.clone()));
        assert!(agent.has_belief(&belief));
        assert_eq!(agent.beliefs().len(), 1);
    }

    #[test]
    fn add_duplicate_belief() {
        let mut agent = Agent::new("a");
        let belief = SExpr::Atom(Atom::Num(42));
        assert!(agent.add_belief(belief.clone()));
        assert!(!agent.add_belief(belief)); // duplicate
        assert_eq!(agent.beliefs().len(), 1);
    }

    #[test]
    fn remove_belief() {
        let mut agent = Agent::new("a");
        let belief = SExpr::Atom(Atom::Bool(true));
        agent.add_belief(belief.clone());
        assert!(agent.remove_belief(&belief));
        assert!(!agent.has_belief(&belief));
        assert!(agent.beliefs().is_empty());
    }

    #[test]
    fn remove_absent_belief() {
        let mut agent = Agent::new("a");
        let belief = SExpr::Atom(Atom::Num(1));
        assert!(!agent.remove_belief(&belief));
    }

    // -- Message queue --

    #[test]
    fn enqueue_dequeue_fifo() {
        let mut agent = Agent::new("a");
        agent.enqueue_message(simple_tell("first"));
        agent.enqueue_message(simple_tell("second"));
        assert_eq!(agent.message_queue_len(), 2);

        let first = agent.dequeue_message().unwrap();
        assert_eq!(
            first.content(),
            Some(&SExpr::Atom(Atom::Str(String::from("first"))))
        );

        let second = agent.dequeue_message().unwrap();
        assert_eq!(
            second.content(),
            Some(&SExpr::Atom(Atom::Str(String::from("second"))))
        );

        assert!(agent.dequeue_message().is_none());
    }

    // -- Conversation threads --

    #[test]
    fn append_to_thread_creates_thread() {
        let mut agent = Agent::new("a");
        agent.append_to_thread("t1", simple_tell("hello"));
        assert_eq!(agent.thread("t1").unwrap().len(), 1);
    }

    #[test]
    fn append_to_thread_accumulates() {
        let mut agent = Agent::new("a");
        agent.append_to_thread("t1", simple_tell("msg1"));
        agent.append_to_thread("t1", simple_tell("msg2"));
        assert_eq!(agent.thread("t1").unwrap().len(), 2);
    }

    #[test]
    fn absent_thread_returns_none() {
        let agent = Agent::new("a");
        assert!(agent.thread("nonexistent").is_none());
    }

    #[test]
    fn multiple_threads() {
        let mut agent = Agent::new("a");
        agent.append_to_thread("t1", simple_tell("a"));
        agent.append_to_thread("t2", simple_tell("b"));
        assert_eq!(agent.conversation_threads().len(), 2);
        assert_eq!(agent.thread("t1").unwrap().len(), 1);
        assert_eq!(agent.thread("t2").unwrap().len(), 1);
    }

    // -- Evaluation --

    fn expect_applied(outcome: AgentOutcome) -> EvalResult {
        match outcome {
            AgentOutcome::Applied(r) => r,
            other => panic!("expected Applied, got {other:?}"),
        }
    }

    #[test]
    fn evaluate_and_apply_stores_belief_on_tell() {
        let mut agent = Agent::new("@alice");
        let msg = simple_tell("the sky is blue");
        let result = expect_applied(agent.evaluate_and_apply(&msg));
        // tell produces StoreBelief effect → agent should hold the belief
        assert!(agent.has_belief(&SExpr::Atom(Atom::Str(String::from("the sky is blue")))));
        assert!(!result.effects.is_empty());
    }

    #[test]
    fn evaluate_and_apply_tracks_thread() {
        let mut agent = Agent::new("@alice");
        let msg = Message::Simple {
            performative: Performative::Core(CorePerformative::Tell),
            recipient: Some("@bob".into()),
            content: SExpr::Atom(Atom::Str(String::from("hello"))),
            params: Vec::new(),
            thread: Some(String::from("conv-1")),
            sender: Some(String::from("@alice")),
            caused_by: None,
        };
        let _ = expect_applied(agent.evaluate_and_apply(&msg));
        assert_eq!(agent.thread("conv-1").unwrap().len(), 1);
    }

    #[test]
    fn step_processes_queued_message() {
        let mut agent = Agent::new("@alice");
        agent.enqueue_message(simple_tell("fact-1"));
        agent.enqueue_message(simple_tell("fact-2"));

        let _r1 = expect_applied(agent.step().unwrap());
        assert!(agent.has_belief(&SExpr::Atom(Atom::Str(String::from("fact-1")))));
        assert_eq!(agent.message_queue_len(), 1);

        let _r2 = expect_applied(agent.step().unwrap());
        assert!(agent.has_belief(&SExpr::Atom(Atom::Str(String::from("fact-2")))));
        assert_eq!(agent.message_queue_len(), 0);
    }

    #[test]
    fn step_returns_none_on_empty_queue() {
        let mut agent = Agent::new("@alice");
        assert!(agent.step().is_none());
    }

    #[test]
    fn evaluate_and_apply_no_thread_no_tracking() {
        let mut agent = Agent::new("@alice");
        let msg = simple_tell("hi");
        let _ = expect_applied(agent.evaluate_and_apply(&msg));
        assert!(agent.conversation_threads().is_empty());
    }

    // -- REQ-231 / REQ-305: agent enforces causal verification --

    fn ack_dialect_with_protocol() -> Dialect {
        use crate::protocol::{CausalProtocol, NodeRef, StepDecl};
        let mut steps = alloc::collections::BTreeMap::new();
        steps.insert(
            "begin".into(),
            StepDecl {
                performative: "begin".into(),
                predecessors: alloc::vec![],
                successors: alloc::vec![NodeRef::Single("ack".into())],
            },
        );
        steps.insert(
            "ack".into(),
            StepDecl {
                performative: "ack".into(),
                predecessors: alloc::vec![NodeRef::Single("begin".into())],
                successors: alloc::vec![],
            },
        );
        let proto = CausalProtocol { steps };

        Dialect {
            roles: Vec::new(),
            causal_locality: Default::default(),
            name: String::from("ack-dialect"),
            extends: alloc::vec![String::from("cbcl")],
            author: None,
            performatives: vec![PerformativeDef {
                role: None,
                name: String::from("ack"),
                params: Vec::new(),
                template: SExpr::List(alloc::vec![
                    SExpr::Atom(Atom::Symbol(String::from("effect"))),
                    SExpr::Atom(Atom::Symbol(String::from("ack-action"))),
                ]),
            }],
            resources: ResourceBounds {
                max_depth: 8,
                max_expansion_size: 512,
                verification_time_ms: 10,
            },
            examples: Vec::new(),
            signature: None,
            hash: None,
            protocol: None,
            causal_protocol: Some(proto),
            shapes: Vec::new(),
        }
    }

    fn ack_with_caused_by(hash: &str) -> Message {
        Message::Dialect {
            dialect_name: String::from("ack-dialect"),
            inner: alloc::boxed::Box::new(Message::Simple {
                performative: Performative::Custom(String::from("ack")),
                recipient: None,
                content: SExpr::Atom(Atom::Str(String::from("done"))),
                params: Vec::new(),
                thread: None,
                sender: None,
                caused_by: Some(crate::message::CausedBy::Single(String::from(hash))),
            }),
        }
    }

    #[test]
    fn agent_rejects_unknown_predecessor_under_default_policy() {
        let mut agent = Agent::new("@alice");
        agent.install_dialect(ack_dialect_with_protocol()).unwrap();
        let msg = ack_with_caused_by("missing-hash");
        match agent.evaluate_and_apply(&msg) {
            AgentOutcome::Pending(_) => {}
            other => panic!("expected Pending under default Reject policy, got {other:?}"),
        }
        // No belief stored, no thread tracked — message was not applied.
        assert!(agent.beliefs().is_empty());
    }

    #[test]
    fn agent_buffers_unknown_predecessor_under_buffer_policy() {
        let mut agent = Agent::with_policy("@alice", UnknownPredecessorPolicy::buffer(60));
        agent.install_dialect(ack_dialect_with_protocol()).unwrap();
        let msg = ack_with_caused_by("missing-hash");
        match agent.evaluate_and_apply(&msg) {
            AgentOutcome::Buffered => {}
            other => panic!("expected Buffered under Buffer policy, got {other:?}"),
        }
        assert_eq!(agent.pending_len(), 1);
    }

    #[test]
    fn agent_rejects_missing_caused_by_when_protocol_requires_predecessor() {
        let mut agent = Agent::new("@alice");
        agent.install_dialect(ack_dialect_with_protocol()).unwrap();
        // ack with no :caused-by; protocol requires "begin" as predecessor.
        let msg = Message::Simple {
            performative: Performative::Custom(String::from("ack")),
            recipient: None,
            content: SExpr::Atom(Atom::Str(String::from("done"))),
            params: Vec::new(),
            thread: None,
            sender: None,
            caused_by: None,
        };
        match agent.evaluate_and_apply(&msg) {
            AgentOutcome::CausalReject(crate::protocol::CausalViolation::MissingCausedBy) => {}
            other => panic!("expected CausalReject(MissingCausedBy), got {other:?}"),
        }
    }

    #[test]
    fn agent_accepts_when_predecessor_is_present() {
        use crate::store::ContentHash as Hash;
        let mut agent = Agent::new("@alice");
        agent.install_dialect(ack_dialect_with_protocol()).unwrap();

        // Insert a "begin" message into the agent's store.
        let begin = Message::Simple {
            performative: Performative::Custom(String::from("begin")),
            recipient: None,
            content: SExpr::Atom(Atom::Str(String::from("start"))),
            params: Vec::new(),
            thread: None,
            sender: None,
            caused_by: Some(crate::message::CausedBy::Begin),
        };
        agent.message_store_mut().append(
            Hash(String::from("begin-hash")),
            ThreadId(String::from("default")),
            begin,
        );

        let msg = ack_with_caused_by("begin-hash");
        let outcome = agent.evaluate_and_apply(&msg);
        match outcome {
            AgentOutcome::Applied(_) => {}
            other => panic!("expected Applied, got {other:?}"),
        }
    }

    // -- SPEC-003 REQ-315 / TEST-355: resolution-gated rejection --

    /// Dialect whose protocol gives `z` the disjunctive clause `(any x y)`.
    fn any_xy_dialect() -> Dialect {
        use crate::protocol::{CausalProtocol, NodeRef, StepDecl};
        let mut any_set = alloc::collections::BTreeSet::new();
        any_set.insert(String::from("x"));
        any_set.insert(String::from("y"));
        let mut steps = alloc::collections::BTreeMap::new();
        steps.insert(
            "begin".into(),
            StepDecl {
                performative: "begin".into(),
                predecessors: alloc::vec![],
                successors: alloc::vec![NodeRef::Single("x".into()), NodeRef::Single("y".into()),],
            },
        );
        steps.insert(
            "x".into(),
            StepDecl {
                performative: "x".into(),
                predecessors: alloc::vec![NodeRef::Single("begin".into())],
                successors: alloc::vec![NodeRef::Single("z".into())],
            },
        );
        steps.insert(
            "y".into(),
            StepDecl {
                performative: "y".into(),
                predecessors: alloc::vec![NodeRef::Single("begin".into())],
                successors: alloc::vec![NodeRef::Single("z".into())],
            },
        );
        steps.insert(
            "z".into(),
            StepDecl {
                performative: "z".into(),
                predecessors: alloc::vec![NodeRef::Any(any_set)],
                successors: alloc::vec![],
            },
        );
        let def = |name: &str| PerformativeDef {
            role: None,
            name: String::from(name),
            params: Vec::new(),
            template: SExpr::List(alloc::vec![
                SExpr::Atom(Atom::Symbol(String::from("effect"))),
                SExpr::Atom(Atom::Symbol(alloc::format!("{name}-action"))),
            ]),
        };
        Dialect {
            roles: Vec::new(),
            causal_locality: Default::default(),
            name: String::from("any-xy"),
            extends: alloc::vec![String::from("cbcl")],
            author: None,
            performatives: vec![def("x"), def("y"), def("z")],
            resources: ResourceBounds {
                max_depth: 8,
                max_expansion_size: 512,
                verification_time_ms: 10,
            },
            examples: Vec::new(),
            signature: None,
            hash: None,
            protocol: None,
            causal_protocol: Some(CausalProtocol { steps }),
            shapes: Vec::new(),
        }
    }

    fn z_with_caused_by_hashes(hashes: &[&str]) -> Message {
        Message::Simple {
            performative: Performative::Custom(String::from("z")),
            recipient: None,
            content: SExpr::Atom(Atom::Str(String::from("zed"))),
            params: Vec::new(),
            thread: None,
            sender: None,
            caused_by: Some(crate::message::CausedBy::Multiple(
                hashes.iter().map(|h| String::from(*h)).collect(),
            )),
        }
    }

    /// Append a predecessor of the given performative type at `hash` in the
    /// default thread.
    fn append_pred(agent: &mut Agent, hash: &str, perf: &str) {
        use crate::store::ContentHash as Hash;
        let msg = Message::Simple {
            performative: Performative::Custom(String::from(perf)),
            recipient: None,
            content: SExpr::Atom(Atom::Str(String::from("p"))),
            params: Vec::new(),
            thread: None,
            sender: None,
            caused_by: Some(crate::message::CausedBy::Begin),
        };
        agent.message_store_mut().append(
            Hash(String::from(hash)),
            ThreadId(String::from("default")),
            msg,
        );
    }

    #[test]
    fn agent_gates_provisional_violation_as_pending_until_resolution() {
        // TEST-355: m names two hashes under z's `(any x y)` clause — one
        // resolving to a stored wrong-typed predecessor, one absent. The
        // verifier's verdict is an eager Violation, but the message is
        // unresolved, so the agent must answer Pending(CausalPending), NOT
        // CausalReject (which the ungated Violation → Reject mapping gave).
        let mut agent = Agent::new("@alice");
        agent.install_dialect(any_xy_dialect()).unwrap();
        append_pred(&mut agent, "h-wrong", "w"); // not x or y
        let m = z_with_caused_by_hashes(&["h-absent", "h-wrong"]);
        match agent.evaluate_and_apply(&m) {
            AgentOutcome::Pending(PendingReason::CausalPending) => {}
            other => panic!("expected Pending for a provisional violation, got {other:?}"),
        }

        // The absent hash arrives wrong-typed too: m is now resolved, the
        // Violation is permanent under store growth, and the gate no
        // longer applies — a resolved Violation still maps to Reject.
        append_pred(&mut agent, "h-absent", "w2");
        match agent.evaluate_and_apply(&m) {
            AgentOutcome::CausalReject(_) => {}
            other => panic!("expected CausalReject once resolved, got {other:?}"),
        }
    }

    #[test]
    fn agent_buffers_provisional_violation_until_resolution() {
        // TEST-355 under the Buffer policy: a provisional Violation is
        // enqueued exactly as an Unknown, and re-evaluation while the
        // named hash is still absent keeps it buffered rather than
        // flushing it as Reject.
        let mut agent = Agent::with_policy("@alice", UnknownPredecessorPolicy::buffer(60));
        agent.install_dialect(any_xy_dialect()).unwrap();
        append_pred(&mut agent, "h-wrong", "w");
        let m = z_with_caused_by_hashes(&["h-absent", "h-wrong"]);
        match agent.evaluate_and_apply(&m) {
            AgentOutcome::Buffered => {}
            other => panic!("expected Buffered, got {other:?}"),
        }
        assert_eq!(agent.pending_len(), 1);

        // Still unresolved: the re-evaluation gate keeps it pending.
        let resolved = agent.reevaluate_pending();
        assert!(
            resolved.is_empty(),
            "provisional violation must stay buffered, got {resolved:?}"
        );
        assert_eq!(agent.pending_len(), 1);

        // Resolution with a second wrong-typed predecessor: flushed as
        // Reject.
        append_pred(&mut agent, "h-absent", "w2");
        let resolved = agent.reevaluate_pending();
        assert_eq!(resolved.len(), 1);
        match &resolved[0].1 {
            PolicyOutcome::Reject(_) => {}
            other => panic!("expected Reject after resolution, got {other:?}"),
        }
        assert_eq!(agent.pending_len(), 0);
    }

    #[test]
    fn agent_still_rejects_resolved_violation_immediately() {
        // REQ-315's other half: when every named hash is present, a
        // Violation is permanent under store growth and maps straight to
        // Reject — the gate must not delay it.
        let mut agent = Agent::new("@alice");
        agent.install_dialect(any_xy_dialect()).unwrap();
        append_pred(&mut agent, "h-wrong", "w");
        let m = Message::Simple {
            performative: Performative::Custom(String::from("z")),
            recipient: None,
            content: SExpr::Atom(Atom::Str(String::from("zed"))),
            params: Vec::new(),
            thread: None,
            sender: None,
            caused_by: Some(crate::message::CausedBy::Single(String::from("h-wrong"))),
        };
        match agent.evaluate_and_apply(&m) {
            AgentOutcome::CausalReject(crate::protocol::CausalViolation::InvalidPredecessor {
                ..
            }) => {}
            other => panic!("expected CausalReject(InvalidPredecessor), got {other:?}"),
        }
    }

    #[test]
    fn resolution_with_legal_type_still_rejects_multi_hash_any_reference() {
        // TEST-355's remaining branch expects that once the absent hash
        // arrives with a *legal* type (x or y), m verifies Valid and is
        // accepted. The deployed `verify_causal` has no multi-hash
        // evaluation for `(any …)` clauses — a `Multiple` reference
        // without an `(all …)` declaration is FanInWithoutAllDecl
        // regardless of the store — so at resolution the verdict is a
        // (resolved) Violation and the gate correctly stands aside. This
        // test pins that gap: delivering the Accept branch of TEST-355
        // needs `(any …)` clause evaluation over multi-hash references in
        // the verifier, which REQ-315 scopes out of this change.
        let mut agent = Agent::new("@alice");
        agent.install_dialect(any_xy_dialect()).unwrap();
        append_pred(&mut agent, "h-wrong", "w");
        let m = z_with_caused_by_hashes(&["h-absent", "h-wrong"]);
        match agent.evaluate_and_apply(&m) {
            AgentOutcome::Pending(PendingReason::CausalPending) => {}
            other => panic!("expected Pending pre-resolution, got {other:?}"),
        }
        append_pred(&mut agent, "h-absent", "x"); // legal type
        match agent.evaluate_and_apply(&m) {
            AgentOutcome::CausalReject(crate::protocol::CausalViolation::FanInWithoutAllDecl {
                ..
            }) => {}
            other => panic!("expected CausalReject(FanInWithoutAllDecl), got {other:?}"),
        }
    }

    // -- PR feedback P1: wrappers must not bypass agent causal verification. --

    fn ack_simple_with_missing_predecessor() -> Message {
        Message::Simple {
            performative: Performative::Custom(String::from("ack")),
            recipient: None,
            content: SExpr::Atom(Atom::Str(String::from("done"))),
            params: Vec::new(),
            thread: None,
            sender: None,
            caused_by: Some(crate::message::CausedBy::Single(String::from("missing"))),
        }
    }

    #[test]
    fn agent_wrapped_message_does_not_bypass_causal() {
        let mut agent = Agent::new("@alice");
        agent.install_dialect(ack_dialect_with_protocol()).unwrap();
        // Wrap the violating ack in an envelope.
        let wrapped = Message::Wrapped {
            wrapper: crate::message::WrapperType::Envelope,
            params: vec![
                SExpr::Atom(Atom::Keyword(String::from("from"))),
                SExpr::Atom(Atom::Symbol(String::from("@alice"))),
            ],
            content: alloc::boxed::Box::new(ack_simple_with_missing_predecessor()),
        };
        match agent.evaluate_and_apply(&wrapped) {
            AgentOutcome::Pending(_) => {}
            other => panic!("expected wrapper to surface inner Pending, got {other:?}"),
        }
        assert!(
            agent.beliefs().is_empty(),
            "wrapped reject should not apply effects"
        );
    }

    #[test]
    fn agent_lang_scoped_message_does_not_bypass_causal() {
        let mut agent = Agent::new("@alice");
        agent.install_dialect(ack_dialect_with_protocol()).unwrap();
        let scoped = Message::Dialect {
            dialect_name: String::from("ack-dialect"),
            inner: alloc::boxed::Box::new(ack_simple_with_missing_predecessor()),
        };
        match agent.evaluate_and_apply(&scoped) {
            AgentOutcome::Pending(_) => {}
            other => panic!("expected lang-scoped wrapper to surface inner Pending, got {other:?}"),
        }
    }

    // -- PR feedback P1: child protocols on inherited (core) performatives. --

    fn ok_protocol_dialect() -> Dialect {
        use crate::protocol::{CausalProtocol, NodeRef, StepDecl};
        let mut steps = alloc::collections::BTreeMap::new();
        steps.insert(
            "begin".into(),
            StepDecl {
                performative: "begin".into(),
                predecessors: alloc::vec![],
                successors: alloc::vec![NodeRef::Single("ok".into())],
            },
        );
        steps.insert(
            "ok".into(),
            StepDecl {
                performative: "ok".into(),
                predecessors: alloc::vec![NodeRef::Single("begin".into())],
                successors: alloc::vec![],
            },
        );
        Dialect {
            roles: Vec::new(),
            causal_locality: Default::default(),
            name: String::from("ok-protocol"),
            extends: alloc::vec![String::from("cbcl")],
            author: None,
            performatives: alloc::vec![],
            resources: ResourceBounds {
                max_depth: 8,
                max_expansion_size: 512,
                verification_time_ms: 10,
            },
            examples: alloc::vec![],
            signature: None,
            hash: None,
            protocol: None,
            causal_protocol: Some(CausalProtocol { steps }),
            shapes: alloc::vec![],
        }
    }

    #[test]
    fn agent_enforces_child_protocol_on_core_performative() {
        let mut agent = Agent::new("@alice");
        agent.install_dialect(ok_protocol_dialect()).unwrap();
        // (ok) with no :caused-by — child protocol requires "begin".
        let msg = Message::Simple {
            performative: Performative::Core(CorePerformative::Ok),
            recipient: None,
            content: SExpr::List(Vec::new()),
            params: Vec::new(),
            thread: None,
            sender: None,
            caused_by: None,
        };
        match agent.evaluate_and_apply(&msg) {
            AgentOutcome::CausalReject(crate::protocol::CausalViolation::MissingCausedBy) => {}
            other => panic!(
                "expected child protocol on core `ok` to reject MissingCausedBy, got {other:?}"
            ),
        }
    }

    // -- PR feedback P2: reevaluate_pending must not flush via unrelated protocol. --

    #[test]
    fn agent_reevaluate_does_not_accept_via_unrelated_protocol() {
        use crate::protocol::{CausalProtocol, NodeRef, StepDecl};

        let mut agent = Agent::with_policy("@alice", UnknownPredecessorPolicy::buffer(60));
        // Protocol A constrains "ack" (caller will buffer an "ack").
        agent.install_dialect(ack_dialect_with_protocol()).unwrap();
        // Protocol B constrains an unrelated performative "ping" — its mere
        // presence used to flush every pending entry as Accept because
        // verify_causal returned Valid for performatives outside its steps.
        let mut steps = alloc::collections::BTreeMap::new();
        steps.insert(
            "begin".into(),
            StepDecl {
                performative: "begin".into(),
                predecessors: alloc::vec![],
                successors: alloc::vec![NodeRef::Single("ping".into())],
            },
        );
        steps.insert(
            "ping".into(),
            StepDecl {
                performative: "ping".into(),
                predecessors: alloc::vec![NodeRef::Single("begin".into())],
                successors: alloc::vec![],
            },
        );
        agent
            .install_dialect(Dialect {
                roles: Vec::new(),
                causal_locality: Default::default(),
                name: String::from("ping-dialect"),
                extends: alloc::vec![String::from("cbcl")],
                author: None,
                performatives: alloc::vec![PerformativeDef {
                    role: None,
                    name: String::from("ping"),
                    params: Vec::new(),
                    template: SExpr::List(alloc::vec![
                        SExpr::Atom(Atom::Symbol(String::from("effect"))),
                        SExpr::Atom(Atom::Symbol(String::from("ping-action"))),
                    ]),
                }],
                resources: ResourceBounds {
                    max_depth: 8,
                    max_expansion_size: 512,
                    verification_time_ms: 10,
                },
                examples: Vec::new(),
                signature: None,
                hash: None,
                protocol: None,
                causal_protocol: Some(CausalProtocol { steps }),
                shapes: Vec::new(),
            })
            .unwrap();

        // Buffer an ack with a missing predecessor.
        let msg = ack_with_caused_by("missing");
        match agent.evaluate_and_apply(&msg) {
            AgentOutcome::Buffered => {}
            other => panic!("expected Buffered, got {other:?}"),
        }
        assert_eq!(agent.pending_len(), 1);

        // Re-evaluate without adding the predecessor. Only the ack-dialect's
        // protocol matches the entry; its verdict is Unknown so the entry
        // stays buffered. The unrelated ping-dialect protocol must not flush
        // it as Accept.
        let resolved = agent.reevaluate_pending();
        assert!(
            resolved.is_empty(),
            "unrelated protocol should not flush pending entry, got {resolved:?}"
        );
        assert_eq!(agent.pending_len(), 1);
    }

    // -- PR feedback (low): default-buffered entries don't insta-expire --

    #[test]
    fn agent_default_buffered_entries_never_expire() {
        let mut agent = Agent::with_policy("@alice", UnknownPredecessorPolicy::buffer(60));
        agent.install_dialect(ack_dialect_with_protocol()).unwrap();

        // Buffer via the no-clock entry point; entry should be stamped with
        // u64::MAX so even the largest reasonable `now` does not expire it.
        match agent.evaluate_and_apply(&ack_with_caused_by("missing")) {
            AgentOutcome::Buffered => {}
            other => panic!("expected Buffered, got {other:?}"),
        }
        assert_eq!(agent.pending_len(), 1);

        let dropped = agent.expire(u64::MAX / 2);
        assert!(
            dropped.is_empty(),
            "default-buffered entry must not expire, got {dropped:?}"
        );
        assert_eq!(agent.pending_len(), 1);
    }

    #[test]
    fn agent_evaluate_and_apply_at_respects_ttl() {
        let mut agent = Agent::with_policy("@alice", UnknownPredecessorPolicy::buffer(10));
        agent.install_dialect(ack_dialect_with_protocol()).unwrap();

        // Buffer at t=100; TTL=10s so it expires at t=110.
        match agent.evaluate_and_apply_at(&ack_with_caused_by("missing"), 100) {
            AgentOutcome::Buffered => {}
            other => panic!("expected Buffered, got {other:?}"),
        }
        assert_eq!(agent.pending_len(), 1);

        // At t=109, nothing has expired yet.
        let dropped = agent.expire(109);
        assert!(dropped.is_empty(), "TTL not yet elapsed, got {dropped:?}");
        assert_eq!(agent.pending_len(), 1);

        // At t=110 the entry expires.
        let dropped = agent.expire(110);
        assert_eq!(dropped.len(), 1);
        assert_eq!(dropped[0].1, DropReason::CausalTimeout);
        assert_eq!(agent.pending_len(), 0);
    }

    // -- MergePolicy: any-protocol-accepts (disjunction) mode --
    //
    // Two installed dialects both declare protocol steps for the inherited
    // core performative `ok` — neither *defines* `ok` (R3 forbids that) but
    // each constrains it differently. This is the canonical "two protocols
    // matching the same perf" shape we proved supported in earlier review
    // rounds; it's what makes a discriminating disjunction test possible.

    /// Single-predecessor protocol on `ok`: accepts `(ok :caused-by begin)`.
    fn single_pred_ok_dialect(name: &str) -> Dialect {
        use crate::protocol::{CausalProtocol, NodeRef, StepDecl};
        let mut steps = alloc::collections::BTreeMap::new();
        steps.insert(
            "begin".into(),
            StepDecl {
                performative: "begin".into(),
                predecessors: alloc::vec![],
                successors: alloc::vec![NodeRef::Single("ok".into())],
            },
        );
        steps.insert(
            "ok".into(),
            StepDecl {
                performative: "ok".into(),
                predecessors: alloc::vec![NodeRef::Single("begin".into())],
                successors: alloc::vec![],
            },
        );
        Dialect {
            roles: Vec::new(),
            causal_locality: Default::default(),
            name: String::from(name),
            extends: alloc::vec![String::from("cbcl")],
            author: None,
            performatives: alloc::vec![],
            resources: ResourceBounds {
                max_depth: 8,
                max_expansion_size: 512,
                verification_time_ms: 10,
            },
            examples: Vec::new(),
            signature: None,
            hash: None,
            protocol: None,
            causal_protocol: Some(CausalProtocol { steps }),
            shapes: Vec::new(),
        }
    }

    /// Strict protocol on `ok`: rejects any `:caused-by` (no predecessors).
    fn strict_no_pred_ok_dialect(name: &str) -> Dialect {
        use crate::protocol::{CausalProtocol, NodeRef, StepDecl};
        let mut steps = alloc::collections::BTreeMap::new();
        // begin step needed for reachability (R5).
        steps.insert(
            "begin".into(),
            StepDecl {
                performative: "begin".into(),
                predecessors: alloc::vec![],
                successors: alloc::vec![NodeRef::Single("ok".into())],
            },
        );
        steps.insert(
            "ok".into(),
            StepDecl {
                performative: "ok".into(),
                predecessors: alloc::vec![], // no predecessors permitted
                successors: alloc::vec![],
            },
        );
        Dialect {
            roles: Vec::new(),
            causal_locality: Default::default(),
            name: String::from(name),
            extends: alloc::vec![String::from("cbcl")],
            author: None,
            performatives: alloc::vec![],
            resources: ResourceBounds {
                max_depth: 8,
                max_expansion_size: 512,
                verification_time_ms: 10,
            },
            examples: Vec::new(),
            signature: None,
            hash: None,
            protocol: None,
            causal_protocol: Some(CausalProtocol { steps }),
            shapes: Vec::new(),
        }
    }

    /// Fan-in protocol on `ok`: requires `(all p1 p2)` — two custom perfs.
    fn fan_in_ok_dialect(name: &str) -> Dialect {
        use crate::protocol::{CausalProtocol, NodeRef, StepDecl};
        let mut all_set = alloc::collections::BTreeSet::new();
        all_set.insert(String::from("p1"));
        all_set.insert(String::from("p2"));

        let mut steps = alloc::collections::BTreeMap::new();
        steps.insert("begin".into(), StepDecl {
            performative: "begin".into(),
            predecessors: alloc::vec![],
            successors: alloc::vec![
                NodeRef::Single("p1".into()),
                NodeRef::Single("p2".into()),
            ],
        });
        steps.insert(
            "p1".into(),
            StepDecl {
                performative: "p1".into(),
                predecessors: alloc::vec![NodeRef::Single("begin".into())],
                successors: alloc::vec![NodeRef::Single("ok".into())],
            },
        );
        steps.insert(
            "p2".into(),
            StepDecl {
                performative: "p2".into(),
                predecessors: alloc::vec![NodeRef::Single("begin".into())],
                successors: alloc::vec![NodeRef::Single("ok".into())],
            },
        );
        steps.insert(
            "ok".into(),
            StepDecl {
                performative: "ok".into(),
                predecessors: alloc::vec![NodeRef::All(all_set)],
                successors: alloc::vec![],
            },
        );
        Dialect {
            roles: Vec::new(),
            causal_locality: Default::default(),
            name: String::from(name),
            extends: alloc::vec![String::from("cbcl")],
            author: None,
            performatives: vec![
                PerformativeDef {
                    role: None,
                    name: String::from("p1"),
                    params: Vec::new(),
                    template: SExpr::List(alloc::vec![
                        SExpr::Atom(Atom::Symbol(String::from("effect"))),
                        SExpr::Atom(Atom::Symbol(String::from("p1-action"))),
                    ]),
                },
                PerformativeDef {
                    role: None,
                    name: String::from("p2"),
                    params: Vec::new(),
                    template: SExpr::List(alloc::vec![
                        SExpr::Atom(Atom::Symbol(String::from("effect"))),
                        SExpr::Atom(Atom::Symbol(String::from("p2-action"))),
                    ]),
                },
            ],
            resources: ResourceBounds {
                max_depth: 8,
                max_expansion_size: 512,
                verification_time_ms: 10,
            },
            examples: Vec::new(),
            signature: None,
            hash: None,
            protocol: None,
            causal_protocol: Some(CausalProtocol { steps }),
            shapes: Vec::new(),
        }
    }

    fn core_ok_with_caused_by(caused_by: crate::message::CausedBy) -> Message {
        Message::Simple {
            performative: Performative::Core(CorePerformative::Ok),
            recipient: None,
            content: SExpr::List(Vec::new()),
            params: Vec::new(),
            thread: None,
            sender: None,
            caused_by: Some(caused_by),
        }
    }

    #[test]
    fn agent_disjunction_accepts_when_one_protocol_accepts_other_rejects() {
        use crate::store::{ContentHash as Hash, MessageStore as _};

        // Two protocols both fire on `ok`:
        //   single_pred: requires `begin` predecessor → Valid given begin in store
        //   strict:      requires no predecessor      → Violation (extraneous)
        let mut agent = Agent::new("@alice").with_merge_policy(MergePolicy::Disjunction);
        agent
            .install_dialect(single_pred_ok_dialect("accept-after-begin"))
            .expect("single_pred dialect must install");
        agent
            .install_dialect(strict_no_pred_ok_dialect("strict-no-pred"))
            .expect("strict dialect must install");

        // Insert a `begin` (any non-ok core performative is fine — its
        // performative name just needs to match what single_pred allows as
        // the predecessor type for `ok`).
        let begin_msg = Message::Simple {
            performative: Performative::Custom(String::from("begin")),
            recipient: None,
            content: SExpr::List(Vec::new()),
            params: Vec::new(),
            thread: None,
            sender: None,
            caused_by: Some(crate::message::CausedBy::Begin),
        };
        agent.message_store_mut().append(
            Hash(String::from("begin-hash")),
            ThreadId(String::from("default")),
            begin_msg,
        );

        let msg =
            core_ok_with_caused_by(crate::message::CausedBy::Single(String::from("begin-hash")));
        match agent.evaluate_and_apply(&msg) {
            AgentOutcome::Applied(_) => {}
            other => panic!(
                "expected disjunction Accept (one protocol accepts, one rejects), got {other:?}"
            ),
        }
    }

    #[test]
    fn agent_conjunction_rejects_same_setup_disjunction_accepts() {
        use crate::store::{ContentHash as Hash, MessageStore as _};

        // Same fixture as above but with conjunction: the strict protocol's
        // Violation is enough to reject.
        let mut agent = Agent::new("@alice"); // default Conjunction
        agent
            .install_dialect(single_pred_ok_dialect("accept-after-begin"))
            .unwrap();
        agent
            .install_dialect(strict_no_pred_ok_dialect("strict-no-pred"))
            .unwrap();

        let begin_msg = Message::Simple {
            performative: Performative::Custom(String::from("begin")),
            recipient: None,
            content: SExpr::List(Vec::new()),
            params: Vec::new(),
            thread: None,
            sender: None,
            caused_by: Some(crate::message::CausedBy::Begin),
        };
        agent.message_store_mut().append(
            Hash(String::from("begin-hash")),
            ThreadId(String::from("default")),
            begin_msg,
        );

        let msg =
            core_ok_with_caused_by(crate::message::CausedBy::Single(String::from("begin-hash")));
        match agent.evaluate_and_apply(&msg) {
            AgentOutcome::CausalReject(_) => {}
            other => panic!("expected conjunction CausalReject, got {other:?}"),
        }
    }

    #[test]
    fn agent_disjunction_reevaluate_keeps_buffered_when_one_protocol_unknown() {
        // Reproduces the (Unknown, Violation) inconsistency that
        // `merge_disjunctive_result` fixes.
        //
        // fan_in protocol: ok requires `(all p1 p2)` — Multiple-friendly.
        // single_pred  : ok requires single `begin` — *not* Multiple-friendly,
        //                so a Multiple `:caused-by` triggers
        //                Violation(FanInWithoutAllDecl) without any store
        //                lookup, regardless of whether the hashes are known.
        //
        // Send `(ok :caused-by (h1 h2))` with store empty:
        //   fan_in     → Unknown (h1, h2 missing from store)
        //   single_pred → Violation (FanInWithoutAllDecl)
        //
        // Live disjunction path: merge_policy_outcomes_disjunctive
        //   (Buffered, Reject) = Buffered ✓
        //
        // Re-evaluate path BEFORE fix: prev.join(r) used
        //   Unknown.join(Violation) = Violation → Reject — flushed entry.
        // Re-evaluate path AFTER  fix: merge_disjunctive_result
        //   (Unknown, Violation) = Unknown → still Unknown → kept buffered.
        let mut agent = Agent::with_policy("@alice", UnknownPredecessorPolicy::buffer(60))
            .with_merge_policy(MergePolicy::Disjunction);
        agent.install_dialect(fan_in_ok_dialect("fan-in")).unwrap();
        agent
            .install_dialect(single_pred_ok_dialect("single-pred"))
            .unwrap();

        let msg = core_ok_with_caused_by(crate::message::CausedBy::Multiple(alloc::vec![
            String::from("h1"),
            String::from("h2"),
        ]));
        match agent.evaluate_and_apply(&msg) {
            AgentOutcome::Buffered => {}
            other => panic!("expected Buffered live, got {other:?}"),
        }
        assert_eq!(agent.pending_len(), 1);

        let resolved = agent.reevaluate_pending();
        assert!(
            resolved.is_empty(),
            "disjunction must not flush still-pending entry across an \
             unrelated Violation, got {resolved:?}"
        );
        assert_eq!(agent.pending_len(), 1);
    }

    #[test]
    fn merge_policy_default_is_conjunction() {
        let agent = Agent::new("@alice");
        assert_eq!(agent.merge_policy(), MergePolicy::Conjunction);
    }

    #[test]
    fn with_merge_policy_sets_disjunction() {
        let agent = Agent::new("@alice").with_merge_policy(MergePolicy::Disjunction);
        assert_eq!(agent.merge_policy(), MergePolicy::Disjunction);
    }

    // Direct truth-table tests of the disjunction VerificationResult merge.
    // These pin the (Unknown, Violation) → Unknown semantic that
    // `merge_disjunctive_result` introduces vs. the existing `join`
    // (Unknown.join(Violation) = Violation).

    fn vr_violation() -> VerificationResult {
        VerificationResult::Violation(crate::protocol::CausalViolation::MissingCausedBy)
    }

    #[test]
    fn merge_disjunctive_result_valid_absorbs() {
        assert!(matches!(
            merge_disjunctive_result(VerificationResult::Valid, VerificationResult::Unknown),
            VerificationResult::Valid
        ));
        assert!(matches!(
            merge_disjunctive_result(VerificationResult::Unknown, VerificationResult::Valid),
            VerificationResult::Valid
        ));
        assert!(matches!(
            merge_disjunctive_result(VerificationResult::Valid, vr_violation()),
            VerificationResult::Valid
        ));
        assert!(matches!(
            merge_disjunctive_result(vr_violation(), VerificationResult::Valid),
            VerificationResult::Valid
        ));
    }

    #[test]
    fn merge_disjunctive_result_unknown_outranks_violation() {
        assert!(matches!(
            merge_disjunctive_result(VerificationResult::Unknown, vr_violation()),
            VerificationResult::Unknown
        ));
        assert!(matches!(
            merge_disjunctive_result(vr_violation(), VerificationResult::Unknown),
            VerificationResult::Unknown
        ));
    }

    #[test]
    fn merge_disjunctive_result_violation_only_when_no_hope() {
        assert!(matches!(
            merge_disjunctive_result(vr_violation(), vr_violation()),
            VerificationResult::Violation(_)
        ));
    }

    // -- Clock injection --

    #[derive(Debug)]
    struct FixedClock(u64);
    impl crate::clock::Clock for FixedClock {
        fn now(&self) -> u64 {
            self.0
        }
    }

    /// A clock that increments on each `now()` call, useful for tests that
    /// want to observe Arc-shared mutability across cloned agents.
    #[derive(Debug)]
    struct TickingClock(core::sync::atomic::AtomicU64);
    impl crate::clock::Clock for TickingClock {
        fn now(&self) -> u64 {
            self.0.fetch_add(1, core::sync::atomic::Ordering::Relaxed)
        }
    }

    #[test]
    fn agent_uses_injected_clock_for_buffer_timestamps() {
        let mut agent = Agent::with_policy("@alice", UnknownPredecessorPolicy::buffer(10))
            .with_clock(FixedClock(100));
        agent.install_dialect(ack_dialect_with_protocol()).unwrap();

        // The agent now consults FixedClock(100) automatically — no _at
        // call needed. Buffer at clock=100; TTL=10 → expires at 110.
        match agent.evaluate_and_apply(&ack_with_caused_by("missing")) {
            AgentOutcome::Buffered => {}
            other => panic!("expected Buffered, got {other:?}"),
        }

        let dropped = agent.expire(109);
        assert!(dropped.is_empty(), "TTL not yet elapsed: {dropped:?}");

        let dropped = agent.expire(110);
        assert_eq!(dropped.len(), 1);
        assert_eq!(dropped[0].1, DropReason::CausalTimeout);
    }

    #[test]
    fn agent_clone_shares_clock_via_arc() {
        // Cloning an agent shares the Arc<dyn Clock> rather than duplicating
        // it. A clock with interior mutability (here an AtomicU64) advances
        // for both clones — proving they share state, not that the clone
        // captured a snapshot.
        let agent_a =
            Agent::new("@alice").with_clock(TickingClock(core::sync::atomic::AtomicU64::new(0)));
        let agent_b = agent_a.clone();
        // Each call to either agent's clock increments the shared counter.
        let t0 = agent_a.clock.now();
        let t1 = agent_b.clock.now();
        let t2 = agent_a.clock.now();
        assert_eq!(t0, 0);
        assert_eq!(t1, 1);
        assert_eq!(t2, 2);
    }
}
