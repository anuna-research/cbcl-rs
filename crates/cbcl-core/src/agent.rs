//! Agent: a CBCL participant with beliefs, dialects, and message queues.
//!
//! Mirrors `Agent.lean` from the Lean 4 proof library (lines 16–39).
//! The Agent struct holds mutable state for dialect installation, belief
//! management, and conversation threading.

#![forbid(unsafe_code)]

use alloc::collections::{BTreeMap, BTreeSet, VecDeque};
use alloc::string::String;
use alloc::vec::Vec;

use crate::dialect::{Dialect, DialectInstallError, DialectRegistry};
use crate::evaluator::{Effect, EvalError, EvalResult};
use crate::message::{Message, Performative};
use crate::policy::{
    apply_policy, PendingEntry, PendingQueue, PendingReason, PolicyOutcome,
    UnknownPredecessorPolicy,
};
use crate::protocol::{verify_causal, CausalViolation};
use crate::sexpr::SExpr;
use crate::store::{ContentHash, ThreadId, ThreadedMessageStore};

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
        }
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

    /// Search dialects in reverse order for one that defines the given
    /// performative (REQ-033).
    ///
    /// Delegates to `DialectRegistry::find_performative_dialect`.
    pub fn find_performative_dialect(&self, name: &str) -> Option<&Dialect> {
        self.dialect_registry.find_performative_dialect(name)
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
    /// 3. On `Violation`: return [`AgentOutcome::CausalReject`] without applying.
    /// 4. On `Unknown` + `Reject` policy: return [`AgentOutcome::Pending`].
    /// 5. On `Unknown` + `Buffer` policy: enqueue in the pending queue and
    ///    return [`AgentOutcome::Buffered`]; the message is *not* applied.
    pub fn evaluate_and_apply(&mut self, msg: &Message) -> AgentOutcome {
        // Step 1: causal verification (only meaningful for Simple messages with a
        // performative whose owning dialect declares a causal protocol).
        if let Some(verdict) = self.causal_verdict(msg) {
            match verdict {
                PolicyOutcome::Accept => {}
                PolicyOutcome::Reject(cv) => return AgentOutcome::CausalReject(cv),
                PolicyOutcome::Pending(reason) => return AgentOutcome::Pending(reason),
                PolicyOutcome::Buffered => {
                    self.buffer_pending(msg);
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
    /// Returns `None` if causal verification doesn't apply (non-simple message,
    /// no performative, no protocol owning the performative).
    fn causal_verdict(&self, msg: &Message) -> Option<PolicyOutcome> {
        let (caused_by, thread) = match msg {
            Message::Simple {
                caused_by, thread, ..
            } => (caused_by.as_ref(), thread.as_ref()),
            _ => return None,
        };

        let perf = msg.performative()?;
        let perf_name = match perf {
            Performative::Core(_) | Performative::Custom(_) => perf.name(),
        };

        let dialect = self.dialect_registry.find_performative_dialect(perf_name)?;
        let proto = dialect.causal_protocol.as_ref()?;

        let thread_id =
            ThreadId(thread.cloned().unwrap_or_else(|| String::from("default")));
        let result = verify_causal(perf_name, caused_by, &self.message_store, proto, &thread_id);
        Some(apply_policy(&result, &self.policy))
    }

    /// Enqueue a message in the pending queue under the Buffer policy.
    fn buffer_pending(&mut self, msg: &Message) {
        let (caused_by, thread) = match msg {
            Message::Simple {
                caused_by, thread, ..
            } => (caused_by.clone(), thread.clone()),
            _ => return,
        };
        let Some(perf) = msg.performative() else {
            return;
        };
        let thread_id = ThreadId(thread.unwrap_or_else(|| String::from("default")));

        // The agent does not synthesize content hashes; store an empty hash for
        // the buffered entry. Callers that re-evaluate will look up by
        // :caused-by, which is what verify_causal needs.
        let entry = PendingEntry {
            hash: ContentHash(String::new()),
            message: msg.clone(),
            thread: thread_id,
            performative: String::from(perf.name()),
            caused_by,
            inserted_at: 0,
        };
        self.pending_queue.enqueue(entry);
    }

    /// Re-evaluate buffered messages against the (possibly grown) message store.
    ///
    /// Returns the entries that now resolve to either `Accept` or `Reject`. The
    /// caller is responsible for re-applying accepted messages — the agent does
    /// not auto-apply them, since [`Agent::evaluate_and_apply`] mutates state
    /// and the caller may want explicit control over re-entry.
    pub fn reevaluate_pending(&mut self) -> Vec<(PendingEntry, PolicyOutcome)> {
        // Collect all installed dialects' protocols and re-evaluate each entry
        // against the protocol owning its performative. We can't pre-compute a
        // single protocol since different entries may target different dialects.
        let mut resolved = Vec::new();
        for dialect in self.dialect_registry.iter() {
            let Some(ref proto) = dialect.causal_protocol else {
                continue;
            };
            let mut more = self.pending_queue.re_evaluate(&self.message_store, proto);
            resolved.append(&mut more);
        }
        resolved
    }

    /// Dequeue the next message, evaluate it, and apply effects.
    ///
    /// Returns `None` if the queue is empty.
    pub fn step(&mut self) -> Option<AgentOutcome> {
        let msg = self.dequeue_message()?;
        Some(self.evaluate_and_apply(&msg))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dialect::{PerformativeDef, ResourceBounds};
    use crate::message::{CorePerformative, Performative};
    use crate::sexpr::Atom;
    use crate::store::MessageStore as _;

    fn valid_custom_dialect(name: &str) -> Dialect {
        Dialect {
            name: String::from(name),
            extends: Vec::new(),
            author: None,
            performatives: vec![PerformativeDef {
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
            protocol: None, causal_protocol: None, shapes: Vec::new(),
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
    fn find_performative_dialect_finds_core() {
        let agent = Agent::new("a");
        let d = agent.find_performative_dialect("tell").unwrap();
        assert_eq!(d.name, "cbcl-base");
    }

    #[test]
    fn find_performative_dialect_finds_custom() {
        let mut agent = Agent::new("a");
        agent.install_dialect(valid_custom_dialect("ext")).unwrap();
        let d = agent.find_performative_dialect("custom-action").unwrap();
        assert_eq!(d.name, "ext");
    }

    #[test]
    fn install_bad_dialect_rejected() {
        let mut agent = Agent::new("a");
        let bad = Dialect {
            name: String::from("bad"),
            extends: Vec::new(),
            author: None,
            performatives: vec![PerformativeDef {
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
            protocol: None, causal_protocol: None, shapes: Vec::new(),
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
            recipient: Some(String::from("@bob")),
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
            name: String::from("ack-dialect"),
            extends: alloc::vec![String::from("cbcl")],
            author: None,
            performatives: vec![PerformativeDef {
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
        Message::Simple {
            performative: Performative::Custom(String::from("ack")),
            recipient: None,
            content: SExpr::Atom(Atom::Str(String::from("done"))),
            params: Vec::new(),
            thread: None,
            sender: None,
            caused_by: Some(crate::message::CausedBy::Single(String::from(hash))),
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
        agent
            .message_store_mut()
            .append(Hash(String::from("begin-hash")), ThreadId(String::from("default")), begin);

        let msg = ack_with_caused_by("begin-hash");
        let outcome = agent.evaluate_and_apply(&msg);
        match outcome {
            AgentOutcome::Applied(_) => {}
            other => panic!("expected Applied, got {other:?}"),
        }
    }
}
