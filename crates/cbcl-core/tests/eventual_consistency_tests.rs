//! Integration tests: eventual consistency under Buffer policy (TEST-307).
//!
//! Three properties:
//! 1. Random-order delivery to Buffer-policy agent — all messages eventually Valid.
//! 2. Property-based: for random permutations, all verify as Valid after full delivery.
//! 3. Convergence: two agents receiving same messages in different order reach same results.

use cbcl_core::message::{CausedBy, Message, Performative};
use cbcl_core::policy::{
    apply_policy, PendingEntry, PendingQueue, PolicyOutcome, UnknownPredecessorPolicy,
};
use cbcl_core::protocol::{verify_causal, CausalProtocol, NodeRef, StepDecl, VerificationResult};
use cbcl_core::sexpr::{Atom, SExpr};
use cbcl_core::store::{ContentHash, MessageStore, ThreadId, ThreadedMessageStore};

use std::collections::BTreeMap;

use proptest::prelude::*;

// ===========================================================================
// Test helpers
// ===========================================================================

fn hash(s: &str) -> ContentHash {
    ContentHash(s.to_string())
}

fn thread_id() -> ThreadId {
    ThreadId("test-thread".to_string())
}

fn simple_msg(perf: &str, caused_by: Option<CausedBy>) -> Message {
    Message::Simple {
        performative: Performative::Custom(perf.to_string()),
        recipient: None,
        content: SExpr::Atom(Atom::Str(format!("{}-content", perf))),
        params: Vec::new(),
        thread: None,
        sender: None,
        caused_by,
    }
}

fn make_entry(
    hash_str: &str,
    perf: &str,
    thread: &ThreadId,
    caused_by: Option<CausedBy>,
    ts: u64,
) -> PendingEntry {
    PendingEntry {
        hash: hash(hash_str),
        message: simple_msg(perf, caused_by.clone()),
        thread: thread.clone(),
        performative: perf.to_string(),
        caused_by,
        inserted_at: ts,
    }
}

/// A linear protocol: begin -> ask -> reply -> confirm
fn linear_protocol() -> CausalProtocol {
    let mut steps = BTreeMap::new();
    steps.insert(
        "ask".to_string(),
        StepDecl {
            performative: "ask".to_string(),
            predecessors: vec![NodeRef::Single("begin".to_string())],
            successors: vec![NodeRef::Single("reply".to_string())],
        },
    );
    steps.insert(
        "reply".to_string(),
        StepDecl {
            performative: "reply".to_string(),
            predecessors: vec![NodeRef::Single("ask".to_string())],
            successors: vec![NodeRef::Single("confirm".to_string())],
        },
    );
    steps.insert(
        "confirm".to_string(),
        StepDecl {
            performative: "confirm".to_string(),
            predecessors: vec![NodeRef::Single("reply".to_string())],
            successors: vec![],
        },
    );
    CausalProtocol { steps }
}

/// A diamond protocol: begin -> ask, begin -> notify, (all ask notify) -> merge
fn diamond_protocol() -> CausalProtocol {
    let mut steps = BTreeMap::new();
    steps.insert(
        "ask".to_string(),
        StepDecl {
            performative: "ask".to_string(),
            predecessors: vec![NodeRef::Single("begin".to_string())],
            successors: vec![],
        },
    );
    steps.insert(
        "notify".to_string(),
        StepDecl {
            performative: "notify".to_string(),
            predecessors: vec![NodeRef::Single("begin".to_string())],
            successors: vec![],
        },
    );
    steps.insert(
        "merge".to_string(),
        StepDecl {
            performative: "merge".to_string(),
            predecessors: vec![NodeRef::All(
                ["ask".to_string(), "notify".to_string()]
                    .into_iter()
                    .collect(),
            )],
            successors: vec![],
        },
    );
    CausalProtocol { steps }
}

/// A valid linear trace: ask(begin) -> reply(ask) -> confirm(reply)
fn linear_trace() -> Vec<(String, String, Option<CausedBy>)> {
    vec![
        (
            "h-ask".to_string(),
            "ask".to_string(),
            Some(CausedBy::Begin),
        ),
        (
            "h-reply".to_string(),
            "reply".to_string(),
            Some(CausedBy::Single("h-ask".to_string())),
        ),
        (
            "h-confirm".to_string(),
            "confirm".to_string(),
            Some(CausedBy::Single("h-reply".to_string())),
        ),
    ]
}

/// A valid diamond trace: ask(begin), notify(begin), merge(all ask notify)
fn diamond_trace() -> Vec<(String, String, Option<CausedBy>)> {
    vec![
        (
            "h-ask".to_string(),
            "ask".to_string(),
            Some(CausedBy::Begin),
        ),
        (
            "h-notify".to_string(),
            "notify".to_string(),
            Some(CausedBy::Begin),
        ),
        (
            "h-merge".to_string(),
            "merge".to_string(),
            Some(CausedBy::Multiple(vec![
                "h-ask".to_string(),
                "h-notify".to_string(),
            ])),
        ),
    ]
}

/// Deliver a trace in the given order to a store+pending queue, processing
/// re-evaluations after each delivery. Returns the final verification results
/// for all messages (hash -> VerificationResult).
fn deliver_trace_with_buffer(
    trace: &[(String, String, Option<CausedBy>)],
    protocol: &CausalProtocol,
) -> (ThreadedMessageStore, Vec<(String, PolicyOutcome)>) {
    let tid = thread_id();
    let policy = UnknownPredecessorPolicy::buffer(3600);
    let mut store = ThreadedMessageStore::new();
    let mut pq = PendingQueue::from_policy(&policy);
    let mut outcomes: Vec<(String, PolicyOutcome)> = Vec::new();

    for (i, (hash_str, perf, caused_by)) in trace.iter().enumerate() {
        let msg = simple_msg(perf, caused_by.clone());

        // Verify against current store state
        let result = verify_causal(perf, caused_by.as_ref(), &store, protocol, &tid);
        let outcome = apply_policy(&result, &policy);

        match &outcome {
            PolicyOutcome::Accept => {
                store.append(hash(hash_str), tid.clone(), msg);
                outcomes.push((hash_str.clone(), PolicyOutcome::Accept));

                // Re-evaluate pending queue iteratively until stable.
                // Each accepted message may unblock further pending messages.
                loop {
                    let resolved = pq.re_evaluate(&store, protocol);
                    if resolved.is_empty() {
                        break;
                    }
                    for (entry, entry_outcome) in resolved {
                        if matches!(entry_outcome, PolicyOutcome::Accept) {
                            store.append(entry.hash.clone(), tid.clone(), entry.message);
                        }
                        outcomes.push((entry.hash.0.clone(), entry_outcome));
                    }
                }
            }
            PolicyOutcome::Buffered => {
                let entry = make_entry(hash_str, perf, &tid, caused_by.clone(), i as u64);
                pq.enqueue(entry);
            }
            _ => {
                outcomes.push((hash_str.clone(), outcome));
            }
        }
    }

    (store, outcomes)
}

// ===========================================================================
// Test 1: Random-order delivery — all messages eventually Valid
// ===========================================================================

#[test]
fn test_reverse_order_delivery_all_eventually_valid() {
    let protocol = linear_protocol();
    let mut trace = linear_trace();
    trace.reverse(); // deliver in reverse: confirm, reply, ask

    let (store, _outcomes) = deliver_trace_with_buffer(&trace, &protocol);
    let tid = thread_id();

    // After full delivery, all messages should be in the store
    assert!(
        store.contains(&hash("h-ask"), &tid),
        "h-ask should be in store after delivery"
    );
    assert!(
        store.contains(&hash("h-reply"), &tid),
        "h-reply should be in store after delivery"
    );
    assert!(
        store.contains(&hash("h-confirm"), &tid),
        "h-confirm should be in store after delivery"
    );

    // Re-verify all messages — should all be Valid now
    for (hash_str, perf, caused_by) in linear_trace() {
        let result = verify_causal(perf.as_str(), caused_by.as_ref(), &store, &protocol, &tid);
        assert_eq!(
            result,
            VerificationResult::Valid,
            "message {} should verify as Valid after full delivery",
            hash_str
        );
    }
}

#[test]
fn test_diamond_reverse_order_all_eventually_valid() {
    let protocol = diamond_protocol();
    let mut trace = diamond_trace();
    trace.reverse(); // deliver merge first, then notify, then ask

    let (store, _outcomes) = deliver_trace_with_buffer(&trace, &protocol);
    let tid = thread_id();

    // All should be in store
    assert!(store.contains(&hash("h-ask"), &tid));
    assert!(store.contains(&hash("h-notify"), &tid));
    assert!(store.contains(&hash("h-merge"), &tid));

    // Re-verify all
    for (hash_str, perf, caused_by) in diamond_trace() {
        let result = verify_causal(perf.as_str(), caused_by.as_ref(), &store, &protocol, &tid);
        assert_eq!(
            result,
            VerificationResult::Valid,
            "message {} should verify as Valid",
            hash_str
        );
    }
}

// ===========================================================================
// Test 2: Property-based — random permutations all reach Valid
// ===========================================================================

/// Generate a permutation index for a trace of given length.
fn arb_permutation(len: usize) -> impl Strategy<Value = Vec<usize>> {
    // Generate a vector of sort keys, then argsort
    prop::collection::vec(any::<u32>(), len).prop_map(move |keys| {
        let mut indices: Vec<usize> = (0..len).collect();
        indices.sort_by_key(|&i| keys[i]);
        indices
    })
}

fn permute<T: Clone>(items: &[T], perm: &[usize]) -> Vec<T> {
    perm.iter().map(|&i| items[i].clone()).collect()
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(200))]

    /// For any permutation of a valid linear trace, Buffer policy eventually
    /// accepts all messages after full delivery.
    #[test]
    fn prop_linear_trace_any_order_eventually_valid(perm in arb_permutation(3)) {
        let protocol = linear_protocol();
        let trace = linear_trace();
        let shuffled = permute(&trace, &perm);

        let (store, _outcomes) = deliver_trace_with_buffer(&shuffled, &protocol);
        let tid = thread_id();

        // All messages must be in the store
        for (hash_str, _, _) in &trace {
            prop_assert!(
                store.contains(&hash(hash_str), &tid),
                "message {} missing from store after delivery in order {:?}",
                hash_str,
                perm
            );
        }

        // All must verify as Valid
        for (hash_str, perf, caused_by) in &trace {
            let result = verify_causal(perf.as_str(), caused_by.as_ref(), &store, &protocol, &tid);
            prop_assert_eq!(
                result,
                VerificationResult::Valid,
                "message {} should be Valid after full delivery in order {:?}",
                hash_str,
                perm
            );
        }
    }

    /// For any permutation of a valid diamond trace, Buffer policy eventually
    /// accepts all messages after full delivery.
    #[test]
    fn prop_diamond_trace_any_order_eventually_valid(perm in arb_permutation(3)) {
        let protocol = diamond_protocol();
        let trace = diamond_trace();
        let shuffled = permute(&trace, &perm);

        let (store, _outcomes) = deliver_trace_with_buffer(&shuffled, &protocol);
        let tid = thread_id();

        for (hash_str, _, _) in &trace {
            prop_assert!(
                store.contains(&hash(hash_str), &tid),
                "message {} missing from store",
                hash_str
            );
        }

        for (hash_str, perf, caused_by) in &trace {
            let result = verify_causal(perf.as_str(), caused_by.as_ref(), &store, &protocol, &tid);
            prop_assert_eq!(
                result,
                VerificationResult::Valid,
                "message {} should be Valid",
                hash_str
            );
        }
    }
}

// ===========================================================================
// Test 3: Convergence — two agents, different orders, same final state
// ===========================================================================

/// Run trace through buffer delivery and return the set of accepted message hashes.
fn accepted_hashes(
    trace: &[(String, String, Option<CausedBy>)],
    protocol: &CausalProtocol,
) -> Vec<String> {
    let (store, _) = deliver_trace_with_buffer(trace, protocol);
    let tid = thread_id();
    let original_trace = linear_trace();
    let mut accepted = Vec::new();
    for (hash_str, _, _) in &original_trace {
        if store.contains(&hash(hash_str), &tid) {
            accepted.push(hash_str.clone());
        }
    }
    accepted.sort();
    accepted
}

#[test]
fn test_convergence_linear_forward_vs_reverse() {
    let protocol = linear_protocol();
    let trace = linear_trace();
    let mut reversed = trace.clone();
    reversed.reverse();

    let accepted_fwd = accepted_hashes(&trace, &protocol);
    let accepted_rev = accepted_hashes(&reversed, &protocol);

    assert_eq!(
        accepted_fwd, accepted_rev,
        "forward and reverse delivery must converge to same accepted set"
    );
    assert_eq!(accepted_fwd.len(), 3, "all 3 messages should be accepted");
}

#[test]
fn test_convergence_diamond_two_orderings() {
    let protocol = diamond_protocol();
    let trace = diamond_trace();

    // Order 1: merge, ask, notify
    let order1 = vec![trace[2].clone(), trace[0].clone(), trace[1].clone()];
    // Order 2: notify, ask, merge
    let order2 = vec![trace[1].clone(), trace[0].clone(), trace[2].clone()];

    let (store1, _) = deliver_trace_with_buffer(&order1, &protocol);
    let (store2, _) = deliver_trace_with_buffer(&order2, &protocol);
    let tid = thread_id();

    // Both stores must contain all messages
    for (hash_str, _, _) in &trace {
        assert!(
            store1.contains(&hash(hash_str), &tid),
            "store1 missing {}",
            hash_str
        );
        assert!(
            store2.contains(&hash(hash_str), &tid),
            "store2 missing {}",
            hash_str
        );
    }

    // Both must yield identical verification results
    for (hash_str, perf, caused_by) in &trace {
        let r1 = verify_causal(perf.as_str(), caused_by.as_ref(), &store1, &protocol, &tid);
        let r2 = verify_causal(perf.as_str(), caused_by.as_ref(), &store2, &protocol, &tid);
        assert_eq!(
            r1, r2,
            "convergence violated for message {}: {:?} vs {:?}",
            hash_str, r1, r2
        );
        assert_eq!(r1, VerificationResult::Valid);
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(200))]

    /// Any two permutations of the same valid trace converge to the same
    /// verification results after full delivery.
    #[test]
    fn prop_convergence_any_two_permutations(
        perm1 in arb_permutation(3),
        perm2 in arb_permutation(3),
    ) {
        let protocol = linear_protocol();
        let trace = linear_trace();
        let shuffled1 = permute(&trace, &perm1);
        let shuffled2 = permute(&trace, &perm2);

        let (store1, _) = deliver_trace_with_buffer(&shuffled1, &protocol);
        let (store2, _) = deliver_trace_with_buffer(&shuffled2, &protocol);
        let tid = thread_id();

        // Both must contain all messages
        for (hash_str, _, _) in &trace {
            prop_assert!(store1.contains(&hash(hash_str), &tid));
            prop_assert!(store2.contains(&hash(hash_str), &tid));
        }

        // Verification results must be identical
        for (hash_str, perf, caused_by) in &trace {
            let r1 = verify_causal(perf.as_str(), caused_by.as_ref(), &store1, &protocol, &tid);
            let r2 = verify_causal(perf.as_str(), caused_by.as_ref(), &store2, &protocol, &tid);
            prop_assert_eq!(
                r1.clone(), r2.clone(),
                "convergence violated for {}: {:?} vs {:?} (perm1={:?}, perm2={:?})",
                hash_str, r1, r2, perm1, perm2
            );
            prop_assert_eq!(r1, VerificationResult::Valid);
        }
    }

    /// Convergence for diamond protocol with fan-in.
    #[test]
    fn prop_convergence_diamond_any_two_permutations(
        perm1 in arb_permutation(3),
        perm2 in arb_permutation(3),
    ) {
        let protocol = diamond_protocol();
        let trace = diamond_trace();
        let shuffled1 = permute(&trace, &perm1);
        let shuffled2 = permute(&trace, &perm2);

        let (store1, _) = deliver_trace_with_buffer(&shuffled1, &protocol);
        let (store2, _) = deliver_trace_with_buffer(&shuffled2, &protocol);
        let tid = thread_id();

        for (hash_str, _, _) in &trace {
            prop_assert!(store1.contains(&hash(hash_str), &tid));
            prop_assert!(store2.contains(&hash(hash_str), &tid));
        }

        for (_hash_str, perf, caused_by) in &trace {
            let r1 = verify_causal(perf.as_str(), caused_by.as_ref(), &store1, &protocol, &tid);
            let r2 = verify_causal(perf.as_str(), caused_by.as_ref(), &store2, &protocol, &tid);
            prop_assert_eq!(r1.clone(), r2.clone());
            prop_assert_eq!(r1, VerificationResult::Valid);
        }
    }
}

// ===========================================================================
// Test 4: Monotonicity — Unknown -> Valid, never backwards
// ===========================================================================

#[test]
fn test_monotonicity_unknown_to_valid_on_store_growth() {
    let protocol = linear_protocol();
    let tid = thread_id();
    let mut store = ThreadedMessageStore::new();

    // Verify "reply" before "ask" exists — should be Unknown
    let result = verify_causal(
        "reply",
        Some(&CausedBy::Single("h-ask".to_string())),
        &store,
        &protocol,
        &tid,
    );
    assert_eq!(result, VerificationResult::Unknown);

    // Add "ask" to the store
    store.append(
        hash("h-ask"),
        tid.clone(),
        simple_msg("ask", Some(CausedBy::Begin)),
    );

    // Re-verify — should now be Valid
    let result = verify_causal(
        "reply",
        Some(&CausedBy::Single("h-ask".to_string())),
        &store,
        &protocol,
        &tid,
    );
    assert_eq!(result, VerificationResult::Valid);
}

#[test]
fn test_pending_queue_drains_completely_after_all_predecessors_arrive() {
    let protocol = linear_protocol();
    let tid = thread_id();
    let policy = UnknownPredecessorPolicy::buffer(3600);
    let mut store = ThreadedMessageStore::new();
    let mut pq = PendingQueue::from_policy(&policy);

    // Buffer confirm (needs reply) and reply (needs ask) — both Unknown
    pq.enqueue(make_entry(
        "h-confirm",
        "confirm",
        &tid,
        Some(CausedBy::Single("h-reply".to_string())),
        0,
    ));
    pq.enqueue(make_entry(
        "h-reply",
        "reply",
        &tid,
        Some(CausedBy::Single("h-ask".to_string())),
        1,
    ));
    assert_eq!(pq.len(), 2);

    // Deliver ask (root) — should unblock reply
    store.append(
        hash("h-ask"),
        tid.clone(),
        simple_msg("ask", Some(CausedBy::Begin)),
    );

    let resolved = pq.re_evaluate(&store, &protocol);
    // reply should resolve
    assert!(
        !resolved.is_empty(),
        "reply should resolve after ask arrives"
    );
    for (entry, outcome) in &resolved {
        if entry.hash == hash("h-reply") {
            assert_eq!(*outcome, PolicyOutcome::Accept);
            store.append(entry.hash.clone(), tid.clone(), entry.message.clone());
        }
    }

    // Now re-evaluate again — confirm should resolve
    let resolved2 = pq.re_evaluate(&store, &protocol);
    for (entry, outcome) in &resolved2 {
        if entry.hash == hash("h-confirm") {
            assert_eq!(*outcome, PolicyOutcome::Accept);
        }
    }

    assert_eq!(pq.len(), 0, "pending queue should be fully drained");
}

// ===========================================================================
// Test 5: Longer chain — 5-message protocol in random order
// ===========================================================================

fn five_step_protocol() -> CausalProtocol {
    let mut steps = BTreeMap::new();
    let names = ["step-a", "step-b", "step-c", "step-d", "step-e"];
    for i in 0..5 {
        let preds = if i == 0 {
            vec![NodeRef::Single("begin".to_string())]
        } else {
            vec![NodeRef::Single(names[i - 1].to_string())]
        };
        let succs = if i < 4 {
            vec![NodeRef::Single(names[i + 1].to_string())]
        } else {
            vec![]
        };
        steps.insert(
            names[i].to_string(),
            StepDecl {
                performative: names[i].to_string(),
                predecessors: preds,
                successors: succs,
            },
        );
    }
    CausalProtocol { steps }
}

fn five_step_trace() -> Vec<(String, String, Option<CausedBy>)> {
    let names = ["step-a", "step-b", "step-c", "step-d", "step-e"];
    let mut trace = Vec::new();
    for i in 0..5 {
        let caused_by = if i == 0 {
            Some(CausedBy::Begin)
        } else {
            Some(CausedBy::Single(format!("h-{}", names[i - 1])))
        };
        trace.push((format!("h-{}", names[i]), names[i].to_string(), caused_by));
    }
    trace
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(100))]

    /// 5-message chain in any permutation: all eventually Valid.
    #[test]
    fn prop_five_step_any_order_eventually_valid(perm in arb_permutation(5)) {
        let protocol = five_step_protocol();
        let trace = five_step_trace();
        let shuffled = permute(&trace, &perm);

        let (store, _) = deliver_trace_with_buffer(&shuffled, &protocol);
        let tid = thread_id();

        for (hash_str, perf, caused_by) in &trace {
            prop_assert!(
                store.contains(&hash(hash_str), &tid),
                "{} missing from store (perm={:?})",
                hash_str, perm
            );
            let result = verify_causal(perf.as_str(), caused_by.as_ref(), &store, &protocol, &tid);
            prop_assert_eq!(
                result, VerificationResult::Valid,
                "{} not Valid (perm={:?})", hash_str, perm
            );
        }
    }

    /// 5-message chain convergence: any two permutations yield same state.
    #[test]
    fn prop_five_step_convergence(
        perm1 in arb_permutation(5),
        perm2 in arb_permutation(5),
    ) {
        let protocol = five_step_protocol();
        let trace = five_step_trace();
        let shuffled1 = permute(&trace, &perm1);
        let shuffled2 = permute(&trace, &perm2);

        let (store1, _) = deliver_trace_with_buffer(&shuffled1, &protocol);
        let (store2, _) = deliver_trace_with_buffer(&shuffled2, &protocol);
        let tid = thread_id();

        for (_hash_str, perf, caused_by) in &trace {
            let r1 = verify_causal(perf.as_str(), caused_by.as_ref(), &store1, &protocol, &tid);
            let r2 = verify_causal(perf.as_str(), caused_by.as_ref(), &store2, &protocol, &tid);
            prop_assert_eq!(r1, r2);
        }
    }
}
