//! Unknown predecessor policy: maps verification results to policy outcomes (REQ-305).
//!
//! Two policies govern how `VerificationResult::Unknown` is handled:
//!
//! - **Reject** — returns `Pending` with retry-after hint; zero mutable state (NFR-204, NFR-302).
//! - **Buffer** — enqueues the message in a bounded, per-thread [`PendingQueue`] with TTL expiry
//!   and re-evaluation on store growth (NFR-301, max_pending default 64).
//!
//! `Violation` results are *never* buffered regardless of policy.

#![forbid(unsafe_code)]

use alloc::collections::VecDeque;
use alloc::vec::Vec;
use hashbrown::HashMap;

use crate::message::{CausedBy, Message};
use crate::protocol::{CausalProtocol, CausalViolation, VerificationResult, verify_causal};
use crate::store::{ContentHash, MessageStore, ThreadId};

// ---------------------------------------------------------------------------
// Policy enum
// ---------------------------------------------------------------------------

/// Policy for handling `VerificationResult::Unknown` (predecessor not yet in store).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UnknownPredecessorPolicy {
    /// Reject unknown predecessors immediately. Returns `Pending` with retry hint.
    /// Preserves zero mutable state (NFR-204, NFR-302).
    Reject,
    /// Buffer messages with unknown predecessors for later re-evaluation.
    Buffer {
        /// Maximum number of pending messages per thread (NFR-301, default 64).
        max_pending: usize,
        /// Time-to-live in seconds for buffered entries. Expired entries yield `CausalTimeout`.
        ttl: u64,
    },
}

impl Default for UnknownPredecessorPolicy {
    fn default() -> Self {
        UnknownPredecessorPolicy::Reject
    }
}

impl UnknownPredecessorPolicy {
    /// Create a `Buffer` policy with default settings (max_pending=64).
    pub fn buffer(ttl: u64) -> Self {
        UnknownPredecessorPolicy::Buffer {
            max_pending: 64,
            ttl,
        }
    }
}

// ---------------------------------------------------------------------------
// Policy outcome
// ---------------------------------------------------------------------------

/// Reason a message is pending under the Reject policy.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PendingReason {
    /// Causal predecessor not yet in the local store.
    CausalPending,
}

/// Reason a buffered message was dropped.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DropReason {
    /// TTL expired while waiting for predecessor.
    CausalTimeout,
    /// Buffer was full; this entry was the oldest and got evicted.
    Evicted,
}

/// Result of applying a policy to a verification result.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PolicyOutcome {
    /// Message passed causal verification.
    Accept,
    /// Message violated causal constraints — never buffered.
    Reject(CausalViolation),
    /// Under Reject policy: predecessor unknown, sender should retry.
    Pending(PendingReason),
    /// Under Buffer policy: message enqueued for later re-evaluation.
    Buffered,
}

// ---------------------------------------------------------------------------
// apply_policy — stateless mapping  (CON-302)
// ---------------------------------------------------------------------------

/// Map a `VerificationResult` + `UnknownPredecessorPolicy` to a `PolicyOutcome`.
///
/// This function is pure: it does not mutate any state. Under the `Buffer` policy
/// the caller is responsible for actually inserting the message into a [`PendingQueue`].
pub fn apply_policy(
    result: &VerificationResult,
    policy: &UnknownPredecessorPolicy,
) -> PolicyOutcome {
    match result {
        VerificationResult::Valid => PolicyOutcome::Accept,
        VerificationResult::Violation(v) => PolicyOutcome::Reject(v.clone()),
        VerificationResult::Unknown => match policy {
            UnknownPredecessorPolicy::Reject => {
                PolicyOutcome::Pending(PendingReason::CausalPending)
            }
            UnknownPredecessorPolicy::Buffer { .. } => PolicyOutcome::Buffered,
        },
    }
}

// ---------------------------------------------------------------------------
// PendingQueue — per-thread bounded buffer (NFR-301)
// ---------------------------------------------------------------------------

/// A buffered entry awaiting re-evaluation.
#[derive(Debug, Clone)]
pub struct PendingEntry {
    /// Content hash of the buffered message.
    pub hash: ContentHash,
    /// The buffered message.
    pub message: Message,
    /// Thread the message belongs to.
    pub thread: ThreadId,
    /// Performative type string for re-verification.
    pub performative: alloc::string::String,
    /// Caused-by reference for re-verification.
    pub caused_by: Option<CausedBy>,
    /// Timestamp (seconds since epoch) when the entry was inserted.
    pub inserted_at: u64,
}

/// Per-thread bounded queue for messages with unknown predecessors.
///
/// Each thread has an independent bounded queue with `max_pending` capacity (NFR-301).
/// Entries expire after `ttl` seconds. When a thread's queue is full the oldest entry
/// is evicted. Re-evaluation happens when the caller signals store growth.
#[derive(Debug)]
pub struct PendingQueue {
    /// Maximum entries per thread.
    max_pending: usize,
    /// TTL in seconds.
    ttl: u64,
    /// Per-thread queues.
    queues: HashMap<ThreadId, VecDeque<PendingEntry>>,
}

impl PendingQueue {
    /// Create a new `PendingQueue` with the given bounds.
    pub fn new(max_pending: usize, ttl: u64) -> Self {
        PendingQueue {
            max_pending,
            ttl,
            queues: HashMap::new(),
        }
    }

    /// Create from a `Buffer` policy. Panics if given `Reject`.
    pub fn from_policy(policy: &UnknownPredecessorPolicy) -> Self {
        match policy {
            UnknownPredecessorPolicy::Buffer { max_pending, ttl } => {
                PendingQueue::new(*max_pending, *ttl)
            }
            UnknownPredecessorPolicy::Reject => {
                panic!("PendingQueue::from_policy called with Reject policy")
            }
        }
    }

    /// Enqueue a pending message. If the thread's queue is at capacity,
    /// the oldest entry is evicted and returned as `DropReason::Evicted`.
    pub fn enqueue(&mut self, entry: PendingEntry) -> Option<(PendingEntry, DropReason)> {
        let queue = self.queues.entry(entry.thread.clone()).or_default();
        let evicted = if queue.len() >= self.max_pending {
            queue.pop_front().map(|e| (e, DropReason::Evicted))
        } else {
            None
        };
        queue.push_back(entry);
        evicted
    }

    /// Remove and return all entries whose TTL has expired at the given `now` timestamp.
    pub fn expire(&mut self, now: u64) -> Vec<(PendingEntry, DropReason)> {
        let mut expired = Vec::new();
        for queue in self.queues.values_mut() {
            // Entries are insertion-ordered, so drain from front while expired.
            while let Some(front) = queue.front() {
                if now.saturating_sub(front.inserted_at) >= self.ttl {
                    let entry = queue.pop_front().unwrap();
                    expired.push((entry, DropReason::CausalTimeout));
                } else {
                    break;
                }
            }
        }
        expired
    }

    /// Re-evaluate all pending entries against the (grown) store.
    ///
    /// Returns entries that now resolve to `Accept` or `Reject`. Entries still
    /// `Unknown` remain in the queue.
    pub fn re_evaluate<S: MessageStore>(
        &mut self,
        store: &S,
        protocol: &CausalProtocol,
    ) -> Vec<(PendingEntry, PolicyOutcome)> {
        let mut resolved = Vec::new();

        for (thread_id, queue) in self.queues.iter_mut() {
            let mut i = 0;
            while i < queue.len() {
                let entry = &queue[i];
                let result = verify_causal(
                    &entry.performative,
                    entry.caused_by.as_ref(),
                    store,
                    protocol,
                    thread_id,
                );
                match result {
                    VerificationResult::Unknown => {
                        i += 1; // still pending
                    }
                    VerificationResult::Valid => {
                        let entry = queue.remove(i).unwrap();
                        resolved.push((entry, PolicyOutcome::Accept));
                    }
                    VerificationResult::Violation(v) => {
                        let entry = queue.remove(i).unwrap();
                        resolved.push((entry, PolicyOutcome::Reject(v)));
                    }
                }
            }
        }

        resolved
    }

    /// Total number of buffered entries across all threads.
    pub fn len(&self) -> usize {
        self.queues.values().map(|q| q.len()).sum()
    }

    /// Whether the queue is empty.
    pub fn is_empty(&self) -> bool {
        self.queues.values().all(|q| q.is_empty())
    }

    /// Number of buffered entries for a specific thread.
    pub fn thread_len(&self, thread: &ThreadId) -> usize {
        self.queues.get(thread).map_or(0, |q| q.len())
    }

    /// Maximum entries per thread.
    pub fn max_pending(&self) -> usize {
        self.max_pending
    }

    /// TTL in seconds.
    pub fn ttl(&self) -> u64 {
        self.ttl
    }
}

// ---------------------------------------------------------------------------
// Tests (TEST-305)
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::message::{CausedBy, Message, Performative};
    use crate::protocol::{CausalProtocol, CausalViolation, NodeRef, StepDecl, VerificationResult};
    use crate::sexpr::{Atom, SExpr};
    use crate::store::{ContentHash, ThreadId, ThreadedMessageStore, MessageStore};
    use alloc::collections::BTreeMap;
    use alloc::string::ToString;
    use alloc::vec;

    fn make_message(performative: &str) -> Message {
        Message::Simple {
            performative: Performative::Custom(performative.to_string()),
            recipient: None,
            content: SExpr::Atom(Atom::Str("x".into())),
            params: vec![],
            thread: None,
            sender: None,
            caused_by: None,
        }
    }

    fn make_thread() -> ThreadId {
        ThreadId("t1".to_string())
    }

    fn make_hash(s: &str) -> ContentHash {
        ContentHash(s.to_string())
    }

    // ---- apply_policy tests ----

    #[test]
    fn test_apply_policy_valid_accept() {
        let result = VerificationResult::Valid;
        let outcome = apply_policy(&result, &UnknownPredecessorPolicy::Reject);
        assert_eq!(outcome, PolicyOutcome::Accept);

        let outcome = apply_policy(&result, &UnknownPredecessorPolicy::buffer(60));
        assert_eq!(outcome, PolicyOutcome::Accept);
    }

    #[test]
    fn test_apply_policy_violation_reject() {
        let v = CausalViolation::MissingCausedBy;
        let result = VerificationResult::Violation(v.clone());

        // Violation -> Reject regardless of policy
        let outcome = apply_policy(&result, &UnknownPredecessorPolicy::Reject);
        assert_eq!(outcome, PolicyOutcome::Reject(v.clone()));

        let outcome = apply_policy(&result, &UnknownPredecessorPolicy::buffer(60));
        assert_eq!(outcome, PolicyOutcome::Reject(v));
    }

    #[test]
    fn test_apply_policy_unknown_reject_pending() {
        let result = VerificationResult::Unknown;
        let outcome = apply_policy(&result, &UnknownPredecessorPolicy::Reject);
        assert_eq!(
            outcome,
            PolicyOutcome::Pending(PendingReason::CausalPending)
        );
    }

    #[test]
    fn test_apply_policy_unknown_buffer_buffered() {
        let result = VerificationResult::Unknown;
        let outcome = apply_policy(&result, &UnknownPredecessorPolicy::buffer(60));
        assert_eq!(outcome, PolicyOutcome::Buffered);
    }

    // ---- Reject policy: zero mutable state (NFR-204, NFR-302) ----

    #[test]
    fn test_reject_policy_no_mutable_state() {
        // Reject policy is a simple enum variant with no fields.
        // apply_policy with Reject never allocates or mutates.
        let policy = UnknownPredecessorPolicy::Reject;
        let results = [
            VerificationResult::Valid,
            VerificationResult::Unknown,
            VerificationResult::Violation(CausalViolation::MissingCausedBy),
        ];
        for r in &results {
            let _ = apply_policy(r, &policy);
        }
        // If this compiles and runs, Reject preserves zero mutable state.
        assert_eq!(policy, UnknownPredecessorPolicy::Reject);
    }

    // ---- PendingQueue tests ----

    fn make_entry(hash: &str, perf: &str, thread: &ThreadId, ts: u64) -> PendingEntry {
        PendingEntry {
            hash: make_hash(hash),
            message: make_message(perf),
            thread: thread.clone(),
            performative: perf.to_string(),
            caused_by: Some(CausedBy::Single(hash.to_string())),
            inserted_at: ts,
        }
    }

    #[test]
    fn test_pending_queue_enqueue_within_capacity() {
        let mut pq = PendingQueue::new(64, 300);
        let tid = make_thread();
        let evicted = pq.enqueue(make_entry("h1", "ask", &tid, 100));
        assert!(evicted.is_none());
        assert_eq!(pq.len(), 1);
        assert_eq!(pq.thread_len(&tid), 1);
    }

    #[test]
    fn test_pending_queue_evicts_oldest_at_capacity() {
        let mut pq = PendingQueue::new(2, 300);
        let tid = make_thread();

        pq.enqueue(make_entry("h1", "ask", &tid, 100));
        pq.enqueue(make_entry("h2", "ask", &tid, 101));

        // Third enqueue should evict h1
        let evicted = pq.enqueue(make_entry("h3", "ask", &tid, 102));
        assert!(evicted.is_some());
        let (entry, reason) = evicted.unwrap();
        assert_eq!(entry.hash, make_hash("h1"));
        assert_eq!(reason, DropReason::Evicted);
        assert_eq!(pq.thread_len(&tid), 2);
    }

    #[test]
    fn test_pending_queue_per_thread_isolation() {
        let mut pq = PendingQueue::new(2, 300);
        let t1 = ThreadId("t1".to_string());
        let t2 = ThreadId("t2".to_string());

        pq.enqueue(make_entry("h1", "ask", &t1, 100));
        pq.enqueue(make_entry("h2", "ask", &t1, 101));
        pq.enqueue(make_entry("h3", "ask", &t2, 100));

        assert_eq!(pq.thread_len(&t1), 2);
        assert_eq!(pq.thread_len(&t2), 1);
        assert_eq!(pq.len(), 3);
    }

    #[test]
    fn test_pending_queue_ttl_expiry() {
        let mut pq = PendingQueue::new(64, 10); // 10-second TTL
        let tid = make_thread();

        pq.enqueue(make_entry("h1", "ask", &tid, 100));
        pq.enqueue(make_entry("h2", "ask", &tid, 105));

        // At t=109, nothing expired (TTL=10)
        let expired = pq.expire(109);
        assert!(expired.is_empty());

        // At t=110, h1 expires (100 + 10 = 110)
        let expired = pq.expire(110);
        assert_eq!(expired.len(), 1);
        assert_eq!(expired[0].0.hash, make_hash("h1"));
        assert_eq!(expired[0].1, DropReason::CausalTimeout);

        // h2 still pending
        assert_eq!(pq.len(), 1);

        // At t=115, h2 expires
        let expired = pq.expire(115);
        assert_eq!(expired.len(), 1);
        assert_eq!(expired[0].0.hash, make_hash("h2"));
    }

    #[test]
    fn test_pending_queue_re_evaluate_on_store_growth() {
        // Set up a protocol: ask -> reply
        let mut steps = BTreeMap::new();
        steps.insert(
            "ask".to_string(),
            StepDecl {
                performative: "ask".to_string(),
                predecessors: vec![],
                successors: vec![NodeRef::Single("reply".to_string())],
            },
        );
        steps.insert(
            "reply".to_string(),
            StepDecl {
                performative: "reply".to_string(),
                predecessors: vec![NodeRef::Single("ask".to_string())],
                successors: vec![],
            },
        );
        let protocol = CausalProtocol { steps };

        let tid = make_thread();
        let mut store = ThreadedMessageStore::new();
        let mut pq = PendingQueue::new(64, 300);

        // Buffer a "reply" that references a missing "ask" predecessor
        let entry = PendingEntry {
            hash: make_hash("reply1"),
            message: make_message("reply"),
            thread: tid.clone(),
            performative: "reply".to_string(),
            caused_by: Some(CausedBy::Single("ask1".to_string())),
            inserted_at: 100,
        };
        pq.enqueue(entry);

        // Re-evaluate with empty store: still Unknown
        let resolved = pq.re_evaluate(&store, &protocol);
        assert!(resolved.is_empty());
        assert_eq!(pq.len(), 1);

        // Now add the predecessor "ask" to the store
        let ask_msg = make_message("ask");
        store.append(make_hash("ask1"), tid.clone(), ask_msg);

        // Re-evaluate: should now resolve to Accept
        let resolved = pq.re_evaluate(&store, &protocol);
        assert_eq!(resolved.len(), 1);
        assert_eq!(resolved[0].1, PolicyOutcome::Accept);
        assert_eq!(pq.len(), 0);
    }

    #[test]
    fn test_pending_queue_violation_on_re_evaluate() {
        // Protocol where "reply" expects predecessor "ask"
        let mut steps = BTreeMap::new();
        steps.insert(
            "ask".to_string(),
            StepDecl {
                performative: "ask".to_string(),
                predecessors: vec![],
                successors: vec![NodeRef::Single("reply".to_string())],
            },
        );
        steps.insert(
            "reply".to_string(),
            StepDecl {
                performative: "reply".to_string(),
                predecessors: vec![NodeRef::Single("ask".to_string())],
                successors: vec![],
            },
        );
        let protocol = CausalProtocol { steps };

        let tid = make_thread();
        let mut store = ThreadedMessageStore::new();
        let mut pq = PendingQueue::new(64, 300);

        // Buffer a "reply" referencing "wrong_hash"
        let entry = PendingEntry {
            hash: make_hash("reply1"),
            message: make_message("reply"),
            thread: tid.clone(),
            performative: "reply".to_string(),
            caused_by: Some(CausedBy::Single("wrong_hash".to_string())),
            inserted_at: 100,
        };
        pq.enqueue(entry);

        // Add a message with the referenced hash but wrong performative type
        let wrong_msg = make_message("notify"); // not "ask"
        store.append(make_hash("wrong_hash"), tid.clone(), wrong_msg);

        // Re-evaluate: should resolve to Reject (InvalidPredecessor)
        let resolved = pq.re_evaluate(&store, &protocol);
        assert_eq!(resolved.len(), 1);
        match &resolved[0].1 {
            PolicyOutcome::Reject(_) => {} // expected
            other => panic!("expected Reject, got {:?}", other),
        }
        assert_eq!(pq.len(), 0);
    }

    #[test]
    fn test_default_policy_is_reject() {
        assert_eq!(
            UnknownPredecessorPolicy::default(),
            UnknownPredecessorPolicy::Reject
        );
    }

    #[test]
    fn test_buffer_convenience_constructor() {
        let policy = UnknownPredecessorPolicy::buffer(120);
        assert_eq!(
            policy,
            UnknownPredecessorPolicy::Buffer {
                max_pending: 64,
                ttl: 120,
            }
        );
    }

    #[test]
    fn test_from_policy_buffer() {
        let policy = UnknownPredecessorPolicy::buffer(60);
        let pq = PendingQueue::from_policy(&policy);
        assert_eq!(pq.max_pending(), 64);
        assert_eq!(pq.ttl(), 60);
    }

    #[test]
    #[should_panic(expected = "Reject policy")]
    fn test_from_policy_reject_panics() {
        PendingQueue::from_policy(&UnknownPredecessorPolicy::Reject);
    }
}
