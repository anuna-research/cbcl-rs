//! Property-based tests for the monotonicity guarantee (TEST-304, TEST-211).
//!
//! Core property: for any message M and store S,
//!   verify(M, S) <= verify(M, S ∪ {random_msg})
//!
//! That is, adding messages to the store can only move the verification result
//! *up* the lattice (Unknown → Valid or Unknown → Violation), never backwards.
//!
//! Covers:
//! - Single predecessor chains (linear protocols)
//! - `(all ...)` fan-in (diamond protocols)
//! - `(any ...)` disjunction (choice protocols)

use cbcl_core::message::{CausedBy, Message, Performative};
use cbcl_core::protocol::{
    verify_causal, CausalProtocol, NodeRef, StepDecl, VerificationResult,
};
use cbcl_core::sexpr::{Atom, SExpr};
use cbcl_core::store::{ContentHash, MessageStore, ThreadId, ThreadedMessageStore};

use std::collections::BTreeMap;

use proptest::prelude::*;

// ===========================================================================
// Helpers
// ===========================================================================

fn hash(s: &str) -> ContentHash {
    ContentHash(s.to_string())
}

fn thread_id() -> ThreadId {
    ThreadId("mono-thread".to_string())
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

/// Assert monotonicity: result_before <= result_after in the flat lattice.
///
/// Unknown < Valid, Unknown < Violation, Valid and Violation are incomparable.
/// If result_before is resolved (Valid or Violation), result_after must stay
/// in the same lattice position (Valid stays Valid, Violation stays Violation).
/// The specific violation details may differ — only the lattice position matters.
fn assert_monotone(before: &VerificationResult, after: &VerificationResult, ctx: &str) {
    match before {
        VerificationResult::Unknown => {
            // Unknown can transition to anything — monotonicity holds trivially
        }
        VerificationResult::Valid => {
            assert_eq!(
                after,
                &VerificationResult::Valid,
                "monotonicity violated: Valid regressed to {:?} ({})",
                after,
                ctx
            );
        }
        VerificationResult::Violation(_) => {
            assert!(
                matches!(after, VerificationResult::Violation(_)),
                "monotonicity violated: Violation regressed to {:?} ({})",
                after,
                ctx
            );
        }
    }
}

/// Assert stability: once resolved, the lattice position never changes.
/// For Violation, only checks that it stays Violation (details may vary
/// depending on which predecessor the verifier examines first).
fn assert_stable(before: &VerificationResult, after: &VerificationResult, ctx: &str) {
    match before {
        VerificationResult::Unknown => {
            // Not yet resolved — no stability constraint
        }
        VerificationResult::Valid => {
            assert_eq!(
                after,
                &VerificationResult::Valid,
                "stability violated: Valid changed to {:?} ({})",
                after,
                ctx
            );
        }
        VerificationResult::Violation(_) => {
            assert!(
                matches!(after, VerificationResult::Violation(_)),
                "stability violated: Violation changed to {:?} ({})",
                after,
                ctx
            );
        }
    }
}

// ===========================================================================
// Protocol builders
// ===========================================================================

/// Linear: begin -> ask -> reply -> confirm
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

/// Diamond fan-in: begin -> ask, begin -> notify, (all ask notify) -> merge
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
                ["ask".to_string(), "notify".to_string()].into_iter().collect(),
            )],
            successors: vec![],
        },
    );
    CausalProtocol { steps }
}

/// Choice/disjunction: (any ask notify) -> response
fn choice_protocol() -> CausalProtocol {
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
        "response".to_string(),
        StepDecl {
            performative: "response".to_string(),
            predecessors: vec![NodeRef::Any(
                ["ask".to_string(), "notify".to_string()].into_iter().collect(),
            )],
            successors: vec![],
        },
    );
    CausalProtocol { steps }
}

// ===========================================================================
// Proptest strategies
// ===========================================================================

/// Strategy for a random message that could land in our store.
/// Generates (hash_string, performative_name, caused_by) tuples.
fn arb_store_message() -> impl Strategy<Value = (String, String, Option<CausedBy>)> {
    let perfs = prop_oneof![
        Just("ask".to_string()),
        Just("reply".to_string()),
        Just("confirm".to_string()),
        Just("notify".to_string()),
        Just("merge".to_string()),
        Just("response".to_string()),
        Just("unknown-perf".to_string()),
    ];

    let caused_bys = prop_oneof![
        Just(None),
        Just(Some(CausedBy::Begin)),
        Just(Some(CausedBy::Single("h-ask".to_string()))),
        Just(Some(CausedBy::Single("h-reply".to_string()))),
        Just(Some(CausedBy::Single("h-notify".to_string()))),
        Just(Some(CausedBy::Single("h-confirm".to_string()))),
        Just(Some(CausedBy::Single("h-unknown".to_string()))),
        Just(Some(CausedBy::Multiple(vec![
            "h-ask".to_string(),
            "h-notify".to_string(),
        ]))),
    ];

    let hashes = prop_oneof![
        Just("h-ask".to_string()),
        Just("h-reply".to_string()),
        Just("h-confirm".to_string()),
        Just("h-notify".to_string()),
        Just("h-merge".to_string()),
        Just("h-response".to_string()),
        Just("h-extra-1".to_string()),
        Just("h-extra-2".to_string()),
    ];

    (hashes, perfs, caused_bys)
}

/// Strategy for a random subset of messages to pre-populate a store.
fn arb_store_prefix() -> impl Strategy<Value = Vec<(String, String, Option<CausedBy>)>> {
    prop::collection::vec(arb_store_message(), 0..6)
}

// ===========================================================================
// TEST-304: Single predecessor monotonicity
// ===========================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(500))]

    /// For a linear protocol, verifying "reply" (caused-by h-ask) against store S
    /// then against S + random_msg: result never decreases.
    #[test]
    fn prop_monotonicity_single_predecessor(
        prefix in arb_store_prefix(),
        extra in arb_store_message(),
    ) {
        let protocol = linear_protocol();
        let tid = thread_id();

        // Build store S from prefix
        let mut store = ThreadedMessageStore::new();
        for (h, perf, cb) in &prefix {
            store.append(hash(h), tid.clone(), simple_msg(perf, cb.clone()));
        }

        // Verify "reply" (caused-by h-ask) against S
        let caused_by = CausedBy::Single("h-ask".to_string());
        let result_before = verify_causal(
            "reply",
            Some(&caused_by),
            &store,
            &protocol,
            &tid,
        );

        // Add random message to get S' = S ∪ {extra}
        let (eh, ep, ecb) = &extra;
        store.append(hash(eh), tid.clone(), simple_msg(ep, ecb.clone()));

        // Verify same message against S'
        let result_after = verify_causal(
            "reply",
            Some(&caused_by),
            &store,
            &protocol,
            &tid,
        );

        assert_monotone(&result_before, &result_after, "single predecessor (reply)");
    }

    /// Monotonicity for "confirm" (caused-by h-reply) under store growth.
    #[test]
    fn prop_monotonicity_single_predecessor_confirm(
        prefix in arb_store_prefix(),
        extra in arb_store_message(),
    ) {
        let protocol = linear_protocol();
        let tid = thread_id();

        let mut store = ThreadedMessageStore::new();
        for (h, perf, cb) in &prefix {
            store.append(hash(h), tid.clone(), simple_msg(perf, cb.clone()));
        }

        let caused_by = CausedBy::Single("h-reply".to_string());
        let result_before = verify_causal(
            "confirm",
            Some(&caused_by),
            &store,
            &protocol,
            &tid,
        );

        let (eh, ep, ecb) = &extra;
        store.append(hash(eh), tid.clone(), simple_msg(ep, ecb.clone()));

        let result_after = verify_causal(
            "confirm",
            Some(&caused_by),
            &store,
            &protocol,
            &tid,
        );

        assert_monotone(&result_before, &result_after, "single predecessor (confirm)");
    }

    /// Monotonicity for "ask" (caused-by begin) — already resolved, must stay Valid.
    #[test]
    fn prop_monotonicity_begin_stays_valid(
        prefix in arb_store_prefix(),
        extra in arb_store_message(),
    ) {
        let protocol = linear_protocol();
        let tid = thread_id();

        let mut store = ThreadedMessageStore::new();
        for (h, perf, cb) in &prefix {
            store.append(hash(h), tid.clone(), simple_msg(perf, cb.clone()));
        }

        let caused_by = CausedBy::Begin;
        let result_before = verify_causal(
            "ask",
            Some(&caused_by),
            &store,
            &protocol,
            &tid,
        );

        let (eh, ep, ecb) = &extra;
        store.append(hash(eh), tid.clone(), simple_msg(ep, ecb.clone()));

        let result_after = verify_causal(
            "ask",
            Some(&caused_by),
            &store,
            &protocol,
            &tid,
        );

        // Begin is always immediately resolved — must remain stable
        assert_monotone(&result_before, &result_after, "begin (ask)");
        prop_assert_eq!(result_before, VerificationResult::Valid);
        prop_assert_eq!(result_after, VerificationResult::Valid);
    }
}

// ===========================================================================
// TEST-304: (all ...) fan-in monotonicity
// ===========================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(500))]

    /// For a diamond protocol, verifying "merge" (caused-by [h-ask, h-notify])
    /// against store S then S + random_msg: result never decreases.
    #[test]
    fn prop_monotonicity_fan_in(
        prefix in arb_store_prefix(),
        extra in arb_store_message(),
    ) {
        let protocol = diamond_protocol();
        let tid = thread_id();

        let mut store = ThreadedMessageStore::new();
        for (h, perf, cb) in &prefix {
            store.append(hash(h), tid.clone(), simple_msg(perf, cb.clone()));
        }

        let caused_by = CausedBy::Multiple(vec![
            "h-ask".to_string(),
            "h-notify".to_string(),
        ]);
        let result_before = verify_causal(
            "merge",
            Some(&caused_by),
            &store,
            &protocol,
            &tid,
        );

        let (eh, ep, ecb) = &extra;
        store.append(hash(eh), tid.clone(), simple_msg(ep, ecb.clone()));

        let result_after = verify_causal(
            "merge",
            Some(&caused_by),
            &store,
            &protocol,
            &tid,
        );

        assert_monotone(&result_before, &result_after, "fan-in (merge)");
    }

    /// Fan-in with partial predecessors: adding the missing one must transition
    /// from Unknown to Valid (or stay if already resolved).
    #[test]
    fn prop_fan_in_partial_to_complete(
        has_ask in any::<bool>(),
        has_notify in any::<bool>(),
    ) {
        let protocol = diamond_protocol();
        let tid = thread_id();

        // Build store with subset of predecessors
        let mut store = ThreadedMessageStore::new();
        if has_ask {
            store.append(hash("h-ask"), tid.clone(), simple_msg("ask", Some(CausedBy::Begin)));
        }
        if has_notify {
            store.append(hash("h-notify"), tid.clone(), simple_msg("notify", Some(CausedBy::Begin)));
        }

        let caused_by = CausedBy::Multiple(vec![
            "h-ask".to_string(),
            "h-notify".to_string(),
        ]);
        let result_before = verify_causal(
            "merge",
            Some(&caused_by),
            &store,
            &protocol,
            &tid,
        );

        // Now add both (idempotent if already present)
        store.append(hash("h-ask"), tid.clone(), simple_msg("ask", Some(CausedBy::Begin)));
        store.append(hash("h-notify"), tid.clone(), simple_msg("notify", Some(CausedBy::Begin)));

        let result_after = verify_causal(
            "merge",
            Some(&caused_by),
            &store,
            &protocol,
            &tid,
        );

        assert_monotone(&result_before, &result_after, "fan-in partial→complete");
        // After both predecessors are present, must be Valid
        prop_assert_eq!(result_after, VerificationResult::Valid);
    }
}

// ===========================================================================
// TEST-211: (any ...) disjunction monotonicity
// ===========================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(500))]

    /// For a choice protocol with (any ask notify) -> response,
    /// verifying "response" against store S then S + random_msg: result never decreases.
    #[test]
    fn prop_monotonicity_disjunction(
        prefix in arb_store_prefix(),
        extra in arb_store_message(),
    ) {
        let protocol = choice_protocol();
        let tid = thread_id();

        let mut store = ThreadedMessageStore::new();
        for (h, perf, cb) in &prefix {
            store.append(hash(h), tid.clone(), simple_msg(perf, cb.clone()));
        }

        // response caused-by h-ask (single ref into an any-set)
        let caused_by = CausedBy::Single("h-ask".to_string());
        let result_before = verify_causal(
            "response",
            Some(&caused_by),
            &store,
            &protocol,
            &tid,
        );

        let (eh, ep, ecb) = &extra;
        store.append(hash(eh), tid.clone(), simple_msg(ep, ecb.clone()));

        let result_after = verify_causal(
            "response",
            Some(&caused_by),
            &store,
            &protocol,
            &tid,
        );

        assert_monotone(&result_before, &result_after, "disjunction (response via ask)");
    }

    /// Disjunction: response caused-by h-notify (the other branch).
    #[test]
    fn prop_monotonicity_disjunction_alt_branch(
        prefix in arb_store_prefix(),
        extra in arb_store_message(),
    ) {
        let protocol = choice_protocol();
        let tid = thread_id();

        let mut store = ThreadedMessageStore::new();
        for (h, perf, cb) in &prefix {
            store.append(hash(h), tid.clone(), simple_msg(perf, cb.clone()));
        }

        let caused_by = CausedBy::Single("h-notify".to_string());
        let result_before = verify_causal(
            "response",
            Some(&caused_by),
            &store,
            &protocol,
            &tid,
        );

        let (eh, ep, ecb) = &extra;
        store.append(hash(eh), tid.clone(), simple_msg(ep, ecb.clone()));

        let result_after = verify_causal(
            "response",
            Some(&caused_by),
            &store,
            &protocol,
            &tid,
        );

        assert_monotone(&result_before, &result_after, "disjunction (response via notify)");
    }

    /// Disjunction: adding the correct predecessor transitions Unknown → Valid.
    #[test]
    fn prop_disjunction_unknown_to_valid(
        use_ask in any::<bool>(),
    ) {
        let protocol = choice_protocol();
        let tid = thread_id();
        let mut store = ThreadedMessageStore::new();

        let (pred_hash, pred_perf) = if use_ask {
            ("h-ask", "ask")
        } else {
            ("h-notify", "notify")
        };

        let caused_by = CausedBy::Single(pred_hash.to_string());

        // Empty store — Unknown
        let result_before = verify_causal(
            "response",
            Some(&caused_by),
            &store,
            &protocol,
            &tid,
        );
        prop_assert_eq!(&result_before, &VerificationResult::Unknown);

        // Add the predecessor
        store.append(hash(pred_hash), tid.clone(), simple_msg(pred_perf, Some(CausedBy::Begin)));

        let result_after = verify_causal(
            "response",
            Some(&caused_by),
            &store,
            &protocol,
            &tid,
        );

        assert_monotone(&result_before, &result_after, "disjunction unknown→valid");
        prop_assert_eq!(result_after, VerificationResult::Valid);
    }
}

// ===========================================================================
// General monotonicity: multiple store growth steps
// ===========================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(300))]

    /// Monotonicity over a sequence of store additions: the verification result
    /// for a fixed message must be non-decreasing at every step.
    #[test]
    fn prop_monotonicity_incremental_growth(
        msgs in prop::collection::vec(arb_store_message(), 1..8),
    ) {
        let protocol = linear_protocol();
        let tid = thread_id();
        let mut store = ThreadedMessageStore::new();

        // Track result for "reply" (caused-by h-ask) across all additions
        let caused_by = CausedBy::Single("h-ask".to_string());
        let mut prev_result = verify_causal(
            "reply",
            Some(&caused_by),
            &store,
            &protocol,
            &tid,
        );

        for (h, perf, cb) in &msgs {
            store.append(hash(h), tid.clone(), simple_msg(perf, cb.clone()));
            let curr_result = verify_causal(
                "reply",
                Some(&caused_by),
                &store,
                &protocol,
                &tid,
            );
            assert_monotone(&prev_result, &curr_result, "incremental growth (reply)");
            prev_result = curr_result;
        }
    }

    /// Incremental monotonicity for fan-in (merge) over a sequence of additions.
    #[test]
    fn prop_monotonicity_incremental_fan_in(
        msgs in prop::collection::vec(arb_store_message(), 1..8),
    ) {
        let protocol = diamond_protocol();
        let tid = thread_id();
        let mut store = ThreadedMessageStore::new();

        let caused_by = CausedBy::Multiple(vec![
            "h-ask".to_string(),
            "h-notify".to_string(),
        ]);
        let mut prev_result = verify_causal(
            "merge",
            Some(&caused_by),
            &store,
            &protocol,
            &tid,
        );

        for (h, perf, cb) in &msgs {
            store.append(hash(h), tid.clone(), simple_msg(perf, cb.clone()));
            let curr_result = verify_causal(
                "merge",
                Some(&caused_by),
                &store,
                &protocol,
                &tid,
            );
            assert_monotone(&prev_result, &curr_result, "incremental growth (merge)");
            prev_result = curr_result;
        }
    }

    /// Incremental monotonicity for disjunction (response) over a sequence of additions.
    #[test]
    fn prop_monotonicity_incremental_disjunction(
        msgs in prop::collection::vec(arb_store_message(), 1..8),
    ) {
        let protocol = choice_protocol();
        let tid = thread_id();
        let mut store = ThreadedMessageStore::new();

        let caused_by = CausedBy::Single("h-ask".to_string());
        let mut prev_result = verify_causal(
            "response",
            Some(&caused_by),
            &store,
            &protocol,
            &tid,
        );

        for (h, perf, cb) in &msgs {
            store.append(hash(h), tid.clone(), simple_msg(perf, cb.clone()));
            let curr_result = verify_causal(
                "response",
                Some(&caused_by),
                &store,
                &protocol,
                &tid,
            );
            assert_monotone(&prev_result, &curr_result, "incremental growth (response)");
            prev_result = curr_result;
        }
    }
}

// ===========================================================================
// Stability: once resolved, result never changes
// ===========================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(300))]

    /// Once a verification result is resolved (Valid or Violation), its lattice
    /// position must remain stable under any subsequent store growth.
    #[test]
    fn prop_stability_after_resolution(
        msgs in prop::collection::vec(arb_store_message(), 2..10),
    ) {
        let protocol = linear_protocol();
        let tid = thread_id();
        let mut store = ThreadedMessageStore::new();

        let caused_by = CausedBy::Single("h-ask".to_string());
        let mut resolved_result: Option<VerificationResult> = None;

        for (h, perf, cb) in &msgs {
            store.append(hash(h), tid.clone(), simple_msg(perf, cb.clone()));
            let result = verify_causal(
                "reply",
                Some(&caused_by),
                &store,
                &protocol,
                &tid,
            );

            if let Some(ref prev) = resolved_result {
                assert_stable(prev, &result, "single predecessor (reply)");
            } else if result.is_resolved() {
                resolved_result = Some(result);
            }
        }
    }

    /// Stability for fan-in: once merge resolves, lattice position is permanent.
    #[test]
    fn prop_stability_fan_in_after_resolution(
        msgs in prop::collection::vec(arb_store_message(), 2..10),
    ) {
        let protocol = diamond_protocol();
        let tid = thread_id();
        let mut store = ThreadedMessageStore::new();

        let caused_by = CausedBy::Multiple(vec![
            "h-ask".to_string(),
            "h-notify".to_string(),
        ]);
        let mut resolved_result: Option<VerificationResult> = None;

        for (h, perf, cb) in &msgs {
            store.append(hash(h), tid.clone(), simple_msg(perf, cb.clone()));
            let result = verify_causal(
                "merge",
                Some(&caused_by),
                &store,
                &protocol,
                &tid,
            );

            if let Some(ref prev) = resolved_result {
                assert_stable(prev, &result, "fan-in (merge)");
            } else if result.is_resolved() {
                resolved_result = Some(result);
            }
        }
    }

    /// Stability for disjunction: once response resolves, lattice position is permanent.
    #[test]
    fn prop_stability_disjunction_after_resolution(
        msgs in prop::collection::vec(arb_store_message(), 2..10),
    ) {
        let protocol = choice_protocol();
        let tid = thread_id();
        let mut store = ThreadedMessageStore::new();

        let caused_by = CausedBy::Single("h-ask".to_string());
        let mut resolved_result: Option<VerificationResult> = None;

        for (h, perf, cb) in &msgs {
            store.append(hash(h), tid.clone(), simple_msg(perf, cb.clone()));
            let result = verify_causal(
                "response",
                Some(&caused_by),
                &store,
                &protocol,
                &tid,
            );

            if let Some(ref prev) = resolved_result {
                assert_stable(prev, &result, "disjunction (response)");
            } else if result.is_resolved() {
                resolved_result = Some(result);
            }
        }
    }
}

// ===========================================================================
// Deterministic unit tests for transition coverage
// ===========================================================================

#[test]
fn test_single_unknown_to_valid() {
    let protocol = linear_protocol();
    let tid = thread_id();
    let mut store = ThreadedMessageStore::new();

    let caused_by = CausedBy::Single("h-ask".to_string());

    // Empty store → Unknown
    let r1 = verify_causal("reply", Some(&caused_by), &store, &protocol, &tid);
    assert_eq!(r1, VerificationResult::Unknown);

    // Add correct predecessor → Valid
    store.append(hash("h-ask"), tid.clone(), simple_msg("ask", Some(CausedBy::Begin)));
    let r2 = verify_causal("reply", Some(&caused_by), &store, &protocol, &tid);
    assert_eq!(r2, VerificationResult::Valid);
}

#[test]
fn test_single_unknown_to_violation() {
    let protocol = linear_protocol();
    let tid = thread_id();
    let mut store = ThreadedMessageStore::new();

    let caused_by = CausedBy::Single("h-ask".to_string());

    // Empty store → Unknown
    let r1 = verify_causal("reply", Some(&caused_by), &store, &protocol, &tid);
    assert_eq!(r1, VerificationResult::Unknown);

    // Add wrong predecessor type → Violation
    store.append(hash("h-ask"), tid.clone(), simple_msg("confirm", Some(CausedBy::Begin)));
    let r2 = verify_causal("reply", Some(&caused_by), &store, &protocol, &tid);
    assert!(matches!(r2, VerificationResult::Violation(_)));
}

#[test]
fn test_fan_in_unknown_to_valid() {
    let protocol = diamond_protocol();
    let tid = thread_id();
    let mut store = ThreadedMessageStore::new();

    let caused_by = CausedBy::Multiple(vec!["h-ask".to_string(), "h-notify".to_string()]);

    // Empty store → Unknown
    let r1 = verify_causal("merge", Some(&caused_by), &store, &protocol, &tid);
    assert_eq!(r1, VerificationResult::Unknown);

    // Add first predecessor → still Unknown (incomplete)
    store.append(hash("h-ask"), tid.clone(), simple_msg("ask", Some(CausedBy::Begin)));
    let r2 = verify_causal("merge", Some(&caused_by), &store, &protocol, &tid);
    assert_eq!(r2, VerificationResult::Unknown);

    // Monotonicity: Unknown <= Unknown ✓
    assert_monotone(&r1, &r2, "fan-in step 1");

    // Add second predecessor → Valid
    store.append(hash("h-notify"), tid.clone(), simple_msg("notify", Some(CausedBy::Begin)));
    let r3 = verify_causal("merge", Some(&caused_by), &store, &protocol, &tid);
    assert_eq!(r3, VerificationResult::Valid);

    // Monotonicity: Unknown <= Valid ✓
    assert_monotone(&r2, &r3, "fan-in step 2");
}

#[test]
fn test_disjunction_unknown_to_valid_via_either_branch() {
    let protocol = choice_protocol();
    let tid = thread_id();

    // Branch 1: response caused-by h-ask
    {
        let mut store = ThreadedMessageStore::new();
        let caused_by = CausedBy::Single("h-ask".to_string());

        let r1 = verify_causal("response", Some(&caused_by), &store, &protocol, &tid);
        assert_eq!(r1, VerificationResult::Unknown);

        store.append(hash("h-ask"), tid.clone(), simple_msg("ask", Some(CausedBy::Begin)));
        let r2 = verify_causal("response", Some(&caused_by), &store, &protocol, &tid);
        assert_eq!(r2, VerificationResult::Valid);
        assert_monotone(&r1, &r2, "disjunction via ask");
    }

    // Branch 2: response caused-by h-notify
    {
        let mut store = ThreadedMessageStore::new();
        let caused_by = CausedBy::Single("h-notify".to_string());

        let r1 = verify_causal("response", Some(&caused_by), &store, &protocol, &tid);
        assert_eq!(r1, VerificationResult::Unknown);

        store.append(hash("h-notify"), tid.clone(), simple_msg("notify", Some(CausedBy::Begin)));
        let r2 = verify_causal("response", Some(&caused_by), &store, &protocol, &tid);
        assert_eq!(r2, VerificationResult::Valid);
        assert_monotone(&r1, &r2, "disjunction via notify");
    }
}

#[test]
fn test_valid_stable_under_unrelated_additions() {
    let protocol = linear_protocol();
    let tid = thread_id();
    let mut store = ThreadedMessageStore::new();

    // Set up valid state
    store.append(hash("h-ask"), tid.clone(), simple_msg("ask", Some(CausedBy::Begin)));
    let caused_by = CausedBy::Single("h-ask".to_string());
    let r1 = verify_causal("reply", Some(&caused_by), &store, &protocol, &tid);
    assert_eq!(r1, VerificationResult::Valid);

    // Add many unrelated messages — result must stay Valid
    for i in 0..10 {
        store.append(
            hash(&format!("h-unrelated-{}", i)),
            tid.clone(),
            simple_msg("notify", None),
        );
        let r = verify_causal("reply", Some(&caused_by), &store, &protocol, &tid);
        assert_eq!(r, VerificationResult::Valid, "stable after unrelated msg {}", i);
    }
}

#[test]
fn test_violation_stable_under_store_growth() {
    let protocol = linear_protocol();
    let tid = thread_id();
    let mut store = ThreadedMessageStore::new();

    // Add wrong predecessor type
    store.append(hash("h-ask"), tid.clone(), simple_msg("confirm", Some(CausedBy::Begin)));
    let caused_by = CausedBy::Single("h-ask".to_string());
    let r1 = verify_causal("reply", Some(&caused_by), &store, &protocol, &tid);
    assert!(matches!(r1, VerificationResult::Violation(_)));

    // Add more messages — Violation must persist
    store.append(hash("h-reply"), tid.clone(), simple_msg("reply", None));
    store.append(hash("h-extra"), tid.clone(), simple_msg("ask", Some(CausedBy::Begin)));

    let r2 = verify_causal("reply", Some(&caused_by), &store, &protocol, &tid);
    assert!(
        matches!(r2, VerificationResult::Violation(_)),
        "violation must be stable: got {:?}",
        r2
    );
}
