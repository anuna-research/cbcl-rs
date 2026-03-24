//! Certificate tests for Merkle DAG as lattice position certificate (TEST-306).
//!
//! Verifies REQ-306:
//! 1. Modify any message in causal closure → root hash changes
//! 2. Two agents computing same message hash independently get same result
//! 3. Canonical :caused-by sort ensures determinism
//! 4. Fan-in join commits to union of predecessor histories

use cbcl_core::canonical::canonical_encode;
use cbcl_core::message::{CausedBy, Message, Performative};
use cbcl_core::sexpr::{Atom, SExpr};
use cbcl_core::store::{
    CausalClosureBundle, ContentHash, MessageStore, ThreadId, ThreadedMessageStore,
};

use sha2::{Digest, Sha256};

// ===========================================================================
// Helpers
// ===========================================================================

fn thread_id() -> ThreadId {
    ThreadId("cert-thread".to_string())
}

fn simple_msg(perf: &str, caused_by: Option<CausedBy>) -> Message {
    Message::Simple {
        performative: Performative::Custom(perf.to_string()),
        recipient: None,
        content: SExpr::Atom(Atom::Str(format!("{perf}-content"))),
        params: Vec::new(),
        thread: None,
        sender: None,
        caused_by,
    }
}

fn simple_msg_with_content(perf: &str, content: &str, caused_by: Option<CausedBy>) -> Message {
    Message::Simple {
        performative: Performative::Custom(perf.to_string()),
        recipient: None,
        content: SExpr::Atom(Atom::Str(content.to_string())),
        params: Vec::new(),
        thread: None,
        sender: None,
        caused_by,
    }
}

/// Compute a SHA-256 content hash from a message's canonical encoding.
fn compute_hash(msg: &Message) -> ContentHash {
    let sexpr = SExpr::from(msg);
    let canonical = canonical_encode(&sexpr);
    let digest = Sha256::digest(&canonical);
    ContentHash(hex::encode(digest))
}

/// Hex-encode bytes (no external dep needed beyond sha2).
mod hex {
    pub fn encode(bytes: impl AsRef<[u8]>) -> String {
        bytes
            .as_ref()
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect()
    }
}

/// Build a linear chain: root → m1 → m2 → ... → tip, return (store, hashes).
fn build_linear_chain(n: usize) -> (ThreadedMessageStore, Vec<ContentHash>) {
    let tid = thread_id();
    let mut store = ThreadedMessageStore::new();
    let mut hashes = Vec::new();

    let root = simple_msg("step-0", Some(CausedBy::Begin));
    let root_hash = compute_hash(&root);
    store.append(root_hash.clone(), tid.clone(), root);
    hashes.push(root_hash);

    for i in 1..n {
        let prev = &hashes[i - 1];
        let msg = simple_msg(
            &format!("step-{i}"),
            Some(CausedBy::Single(prev.0.clone())),
        );
        let h = compute_hash(&msg);
        store.append(h.clone(), tid.clone(), msg);
        hashes.push(h);
    }

    (store, hashes)
}

// ===========================================================================
// TEST-306.1: Modify any message in causal closure → root hash changes
// ===========================================================================

/// Changing the content of the root message produces a different hash.
#[test]
fn modifying_root_content_changes_hash() {
    let msg_a = simple_msg_with_content("root", "original", Some(CausedBy::Begin));
    let msg_b = simple_msg_with_content("root", "modified", Some(CausedBy::Begin));

    let hash_a = compute_hash(&msg_a);
    let hash_b = compute_hash(&msg_b);

    assert_ne!(
        hash_a, hash_b,
        "changing message content must change its hash"
    );
}

/// Changing the performative produces a different hash.
#[test]
fn modifying_performative_changes_hash() {
    let msg_a = simple_msg("tell", Some(CausedBy::Begin));
    let msg_b = simple_msg("ask", Some(CausedBy::Begin));

    assert_ne!(
        compute_hash(&msg_a),
        compute_hash(&msg_b),
        "different performatives must produce different hashes"
    );
}

/// In a 3-message chain root→mid→tip, modifying root's content changes
/// root's hash, which changes mid's :caused-by, which changes mid's hash,
/// which changes tip's :caused-by. This demonstrates Merkle chain propagation.
#[test]
fn modifying_interior_message_propagates_hash_change() {
    // Original chain
    let root_a = simple_msg_with_content("root", "original", Some(CausedBy::Begin));
    let root_a_hash = compute_hash(&root_a);

    let mid_a = simple_msg_with_content(
        "mid",
        "mid-content",
        Some(CausedBy::Single(root_a_hash.0.clone())),
    );
    let mid_a_hash = compute_hash(&mid_a);

    let tip_a = simple_msg_with_content(
        "tip",
        "tip-content",
        Some(CausedBy::Single(mid_a_hash.0.clone())),
    );
    let tip_a_hash = compute_hash(&tip_a);

    // Modified chain: change root content
    let root_b = simple_msg_with_content("root", "MODIFIED", Some(CausedBy::Begin));
    let root_b_hash = compute_hash(&root_b);
    assert_ne!(root_a_hash, root_b_hash);

    // mid now points to the new root hash
    let mid_b = simple_msg_with_content(
        "mid",
        "mid-content",
        Some(CausedBy::Single(root_b_hash.0.clone())),
    );
    let mid_b_hash = compute_hash(&mid_b);
    assert_ne!(mid_a_hash, mid_b_hash, "mid hash must change when root hash changes");

    // tip now points to the new mid hash
    let tip_b = simple_msg_with_content(
        "tip",
        "tip-content",
        Some(CausedBy::Single(mid_b_hash.0.clone())),
    );
    let tip_b_hash = compute_hash(&tip_b);
    assert_ne!(
        tip_a_hash, tip_b_hash,
        "tip hash must change when interior message changes (Merkle propagation)"
    );
}

/// Modifying :caused-by reference itself (not the target) changes the hash.
#[test]
fn modifying_caused_by_reference_changes_hash() {
    let msg_a = simple_msg("step", Some(CausedBy::Single("hash-aaa".to_string())));
    let msg_b = simple_msg("step", Some(CausedBy::Single("hash-bbb".to_string())));

    assert_ne!(
        compute_hash(&msg_a),
        compute_hash(&msg_b),
        "different :caused-by references must produce different hashes"
    );
}

/// Extracting causal closure from a modified chain yields a different bundle.
#[test]
fn causal_closure_differs_after_content_modification() {
    let tid = thread_id();

    // Build original 3-message chain
    let root = simple_msg_with_content("root", "original", Some(CausedBy::Begin));
    let root_hash = compute_hash(&root);

    let mid = simple_msg(
        "mid",
        Some(CausedBy::Single(root_hash.0.clone())),
    );
    let mid_hash = compute_hash(&mid);

    let tip = simple_msg(
        "tip",
        Some(CausedBy::Single(mid_hash.0.clone())),
    );
    let tip_hash = compute_hash(&tip);

    let mut store_a = ThreadedMessageStore::new();
    store_a.append(root_hash.clone(), tid.clone(), root);
    store_a.append(mid_hash.clone(), tid.clone(), mid);
    store_a.append(tip_hash.clone(), tid.clone(), tip);

    let bundle_a = CausalClosureBundle::extract(&tip_hash, &tid, &store_a).unwrap();
    let bundle_a_hashes: Vec<&ContentHash> = bundle_a.hashes();

    // Build modified chain: different root content
    let root2 = simple_msg_with_content("root", "TAMPERED", Some(CausedBy::Begin));
    let root2_hash = compute_hash(&root2);

    let mid2 = simple_msg(
        "mid",
        Some(CausedBy::Single(root2_hash.0.clone())),
    );
    let mid2_hash = compute_hash(&mid2);

    let tip2 = simple_msg(
        "tip",
        Some(CausedBy::Single(mid2_hash.0.clone())),
    );
    let tip2_hash = compute_hash(&tip2);

    let mut store_b = ThreadedMessageStore::new();
    store_b.append(root2_hash, tid.clone(), root2);
    store_b.append(mid2_hash, tid.clone(), mid2);
    store_b.append(tip2_hash.clone(), tid.clone(), tip2);

    let bundle_b = CausalClosureBundle::extract(&tip2_hash, &tid, &store_b).unwrap();
    let bundle_b_hashes: Vec<&ContentHash> = bundle_b.hashes();

    assert_ne!(
        bundle_a_hashes, bundle_b_hashes,
        "modifying any message in causal closure must change the closure's hashes"
    );
}

// ===========================================================================
// TEST-306.2: Independent agents compute same hash for same message
// ===========================================================================

/// Two independent computations of the same message yield identical hashes.
#[test]
fn independent_hash_computation_is_identical() {
    let msg1 = simple_msg_with_content("tell", "hello world", Some(CausedBy::Begin));
    let msg2 = simple_msg_with_content("tell", "hello world", Some(CausedBy::Begin));

    let hash1 = compute_hash(&msg1);
    let hash2 = compute_hash(&msg2);

    assert_eq!(
        hash1, hash2,
        "same message content must produce same hash regardless of who computes it"
    );
}

/// Two agents building identical chains independently get the same hashes.
#[test]
fn independent_agents_same_chain_same_hashes() {
    // Agent A builds: root → reply
    let root_a = simple_msg_with_content("tell", "request", Some(CausedBy::Begin));
    let root_a_hash = compute_hash(&root_a);
    let reply_a = simple_msg_with_content(
        "reply",
        "response",
        Some(CausedBy::Single(root_a_hash.0.clone())),
    );
    let reply_a_hash = compute_hash(&reply_a);

    // Agent B builds the exact same chain independently
    let root_b = simple_msg_with_content("tell", "request", Some(CausedBy::Begin));
    let root_b_hash = compute_hash(&root_b);
    let reply_b = simple_msg_with_content(
        "reply",
        "response",
        Some(CausedBy::Single(root_b_hash.0.clone())),
    );
    let reply_b_hash = compute_hash(&reply_b);

    assert_eq!(root_a_hash, root_b_hash, "root hashes must match");
    assert_eq!(reply_a_hash, reply_b_hash, "reply hashes must match");
}

/// Canonical encoding is deterministic: same SExpr always produces same bytes.
#[test]
fn canonical_encoding_deterministic_across_invocations() {
    let msg = simple_msg_with_content("tell", "determinism-test", Some(CausedBy::Begin));
    let sexpr = SExpr::from(&msg);

    let enc1 = canonical_encode(&sexpr);
    let enc2 = canonical_encode(&sexpr);
    let enc3 = canonical_encode(&sexpr);

    assert_eq!(enc1, enc2);
    assert_eq!(enc2, enc3);
}

/// verify_hashes succeeds with a correct hasher.
#[test]
fn bundle_verify_hashes_succeeds_with_correct_hasher() {
    let (store, hashes) = build_linear_chain(4);
    let tid = thread_id();
    let tip = hashes.last().unwrap();

    let bundle = CausalClosureBundle::extract(tip, &tid, &store).unwrap();
    assert!(
        bundle.verify_hashes(|msg| compute_hash(msg)).is_ok(),
        "verify_hashes must pass when hashes are correctly computed"
    );
}

/// verify_hashes fails with a wrong hasher.
#[test]
fn bundle_verify_hashes_fails_with_wrong_hasher() {
    let (store, hashes) = build_linear_chain(3);
    let tid = thread_id();
    let tip = hashes.last().unwrap();

    let bundle = CausalClosureBundle::extract(tip, &tid, &store).unwrap();
    let result = bundle.verify_hashes(|_msg| ContentHash("bogus".to_string()));
    assert!(
        result.is_err(),
        "verify_hashes must fail when hasher returns wrong hashes"
    );
}

// ===========================================================================
// TEST-306.3: Canonical :caused-by sort ensures determinism
// ===========================================================================

/// CausedBy::Multiple with sorted hashes produces the same message regardless
/// of the order the hashes were originally encountered.
#[test]
fn caused_by_multiple_sorted_order_is_deterministic() {
    let hashes_sorted = vec!["aaa".to_string(), "bbb".to_string(), "ccc".to_string()];

    let msg_a = simple_msg(
        "join",
        Some(CausedBy::Multiple(hashes_sorted.clone())),
    );

    // Construct again independently with same sorted order
    let msg_b = simple_msg(
        "join",
        Some(CausedBy::Multiple(hashes_sorted)),
    );

    assert_eq!(
        compute_hash(&msg_a),
        compute_hash(&msg_b),
        "same sorted :caused-by must produce same hash"
    );
}

/// Different orderings of :caused-by hashes produce different hashes when
/// NOT canonically sorted. This shows why canonical sorting matters.
#[test]
fn unsorted_caused_by_produces_different_hash() {
    let msg_a = simple_msg(
        "join",
        Some(CausedBy::Multiple(vec![
            "aaa".to_string(),
            "bbb".to_string(),
        ])),
    );

    let msg_b = simple_msg(
        "join",
        Some(CausedBy::Multiple(vec![
            "bbb".to_string(),
            "aaa".to_string(),
        ])),
    );

    assert_ne!(
        compute_hash(&msg_a),
        compute_hash(&msg_b),
        "different ordering of :caused-by produces different canonical bytes"
    );
}

/// If agents canonically sort :caused-by hashes before constructing the
/// message, they get the same hash regardless of discovery order.
#[test]
fn canonical_sort_makes_discovery_order_irrelevant() {
    // Agent A discovers hashes in order: ccc, aaa, bbb
    let mut discovered_a = vec!["ccc".to_string(), "aaa".to_string(), "bbb".to_string()];
    discovered_a.sort();

    // Agent B discovers hashes in order: bbb, ccc, aaa
    let mut discovered_b = vec!["bbb".to_string(), "ccc".to_string(), "aaa".to_string()];
    discovered_b.sort();

    let msg_a = simple_msg("join", Some(CausedBy::Multiple(discovered_a)));
    let msg_b = simple_msg("join", Some(CausedBy::Multiple(discovered_b)));

    assert_eq!(
        compute_hash(&msg_a),
        compute_hash(&msg_b),
        "canonical sorting must ensure discovery-order-independent hashing"
    );
}

/// Canonical encoding of :caused-by list is order-sensitive at the byte level.
#[test]
fn canonical_encoding_reflects_caused_by_order() {
    let msg_sorted = simple_msg(
        "join",
        Some(CausedBy::Multiple(vec![
            "alpha".to_string(),
            "beta".to_string(),
        ])),
    );
    let msg_reversed = simple_msg(
        "join",
        Some(CausedBy::Multiple(vec![
            "beta".to_string(),
            "alpha".to_string(),
        ])),
    );

    let enc_sorted = canonical_encode(&SExpr::from(&msg_sorted));
    let enc_reversed = canonical_encode(&SExpr::from(&msg_reversed));

    assert_ne!(
        enc_sorted, enc_reversed,
        "canonical encoding must be sensitive to :caused-by element order"
    );
}

// ===========================================================================
// TEST-306.4: Fan-in join commits to union of predecessor histories
// ===========================================================================

/// Fan-in message's causal closure is the union of its predecessors' closures
/// plus the fan-in message itself.
#[test]
fn fan_in_closure_is_union_of_predecessor_closures() {
    let tid = thread_id();
    let mut store = ThreadedMessageStore::new();

    // Shared root
    let root = simple_msg("root", Some(CausedBy::Begin));
    let root_hash = compute_hash(&root);
    store.append(root_hash.clone(), tid.clone(), root);

    // Branch A: root → a1 → a2
    let a1 = simple_msg("branch-a1", Some(CausedBy::Single(root_hash.0.clone())));
    let a1_hash = compute_hash(&a1);
    store.append(a1_hash.clone(), tid.clone(), a1);

    let a2 = simple_msg("branch-a2", Some(CausedBy::Single(a1_hash.0.clone())));
    let a2_hash = compute_hash(&a2);
    store.append(a2_hash.clone(), tid.clone(), a2);

    // Branch B: root → b1 → b2
    let b1 = simple_msg("branch-b1", Some(CausedBy::Single(root_hash.0.clone())));
    let b1_hash = compute_hash(&b1);
    store.append(b1_hash.clone(), tid.clone(), b1);

    let b2 = simple_msg("branch-b2", Some(CausedBy::Single(b1_hash.0.clone())));
    let b2_hash = compute_hash(&b2);
    store.append(b2_hash.clone(), tid.clone(), b2);

    // Fan-in: join of a2 and b2
    let mut fan_in_causes = vec![a2_hash.0.clone(), b2_hash.0.clone()];
    fan_in_causes.sort(); // canonical sort
    let join = simple_msg("join", Some(CausedBy::Multiple(fan_in_causes)));
    let join_hash = compute_hash(&join);
    store.append(join_hash.clone(), tid.clone(), join);

    // Get the causal closure of the join
    let join_closure = store.causal_closure(&join_hash, &tid);
    let join_closure_set: std::collections::HashSet<_> = join_closure.iter().collect();

    // Get individual branch closures
    let a_closure = store.causal_closure(&a2_hash, &tid);
    let b_closure = store.causal_closure(&b2_hash, &tid);

    // The join's closure must contain all of A's closure
    for h in &a_closure {
        assert!(
            join_closure_set.contains(h),
            "fan-in closure must contain branch A message: {}",
            h.0
        );
    }

    // The join's closure must contain all of B's closure
    for h in &b_closure {
        assert!(
            join_closure_set.contains(h),
            "fan-in closure must contain branch B message: {}",
            h.0
        );
    }

    // The join's closure must contain the join itself
    assert!(
        join_closure_set.contains(&join_hash),
        "fan-in closure must contain the join message itself"
    );

    // The join's closure should be exactly: A_closure ∪ B_closure ∪ {join}
    let mut expected: std::collections::HashSet<_> = a_closure.iter().collect();
    expected.extend(b_closure.iter());
    expected.insert(&join_hash);

    assert_eq!(
        join_closure_set, expected,
        "fan-in closure must be exactly the union of predecessor closures plus the join"
    );
}

/// Fan-in bundle extracted from the store is complete and verifiable.
#[test]
fn fan_in_bundle_is_complete_and_verifiable() {
    let tid = thread_id();
    let mut store = ThreadedMessageStore::new();

    // Root
    let root = simple_msg("root", Some(CausedBy::Begin));
    let root_hash = compute_hash(&root);
    store.append(root_hash.clone(), tid.clone(), root);

    // Two branches from root
    let left = simple_msg("left", Some(CausedBy::Single(root_hash.0.clone())));
    let left_hash = compute_hash(&left);
    store.append(left_hash.clone(), tid.clone(), left);

    let right = simple_msg("right", Some(CausedBy::Single(root_hash.0.clone())));
    let right_hash = compute_hash(&right);
    store.append(right_hash.clone(), tid.clone(), right);

    // Fan-in joining both branches
    let mut causes = vec![left_hash.0.clone(), right_hash.0.clone()];
    causes.sort();
    let join = simple_msg("join", Some(CausedBy::Multiple(causes)));
    let join_hash = compute_hash(&join);
    store.append(join_hash.clone(), tid.clone(), join);

    // Extract bundle
    let bundle = CausalClosureBundle::extract(&join_hash, &tid, &store).unwrap();

    // Must contain all 4 messages
    assert_eq!(bundle.len(), 4, "fan-in bundle must contain all 4 messages");

    // Completeness verification must pass
    assert!(
        bundle.verify_completeness().is_ok(),
        "fan-in bundle must pass completeness verification"
    );

    // Hash verification must pass
    assert!(
        bundle.verify_hashes(|msg| compute_hash(msg)).is_ok(),
        "fan-in bundle must pass hash verification"
    );
}

/// Fan-in bundle is topologically sorted: predecessors appear before successors.
#[test]
fn fan_in_bundle_is_topologically_sorted() {
    let tid = thread_id();
    let mut store = ThreadedMessageStore::new();

    let root = simple_msg("root", Some(CausedBy::Begin));
    let root_hash = compute_hash(&root);
    store.append(root_hash.clone(), tid.clone(), root);

    let left = simple_msg("left", Some(CausedBy::Single(root_hash.0.clone())));
    let left_hash = compute_hash(&left);
    store.append(left_hash.clone(), tid.clone(), left);

    let right = simple_msg("right", Some(CausedBy::Single(root_hash.0.clone())));
    let right_hash = compute_hash(&right);
    store.append(right_hash.clone(), tid.clone(), right);

    let mut causes = vec![left_hash.0.clone(), right_hash.0.clone()];
    causes.sort();
    let join = simple_msg("join", Some(CausedBy::Multiple(causes)));
    let join_hash = compute_hash(&join);
    store.append(join_hash.clone(), tid.clone(), join);

    let bundle = CausalClosureBundle::extract(&join_hash, &tid, &store).unwrap();

    // Build position map
    let pos: std::collections::HashMap<&ContentHash, usize> = bundle
        .messages
        .iter()
        .enumerate()
        .map(|(i, (h, _))| (h, i))
        .collect();

    // Root must appear before left and right
    assert!(pos[&root_hash] < pos[&left_hash], "root before left");
    assert!(pos[&root_hash] < pos[&right_hash], "root before right");

    // Left and right must appear before join
    assert!(pos[&left_hash] < pos[&join_hash], "left before join");
    assert!(pos[&right_hash] < pos[&join_hash], "right before join");
}

/// Merging a fan-in bundle into another store preserves all messages.
#[test]
fn fan_in_bundle_merge_preserves_union_history() {
    let tid = thread_id();
    let mut store = ThreadedMessageStore::new();

    let root = simple_msg("root", Some(CausedBy::Begin));
    let root_hash = compute_hash(&root);
    store.append(root_hash.clone(), tid.clone(), root);

    let left = simple_msg("left", Some(CausedBy::Single(root_hash.0.clone())));
    let left_hash = compute_hash(&left);
    store.append(left_hash.clone(), tid.clone(), left);

    let right = simple_msg("right", Some(CausedBy::Single(root_hash.0.clone())));
    let right_hash = compute_hash(&right);
    store.append(right_hash.clone(), tid.clone(), right);

    let mut causes = vec![left_hash.0.clone(), right_hash.0.clone()];
    causes.sort();
    let join = simple_msg("join", Some(CausedBy::Multiple(causes)));
    let join_hash = compute_hash(&join);
    store.append(join_hash.clone(), tid.clone(), join);

    let bundle = CausalClosureBundle::extract(&join_hash, &tid, &store).unwrap();

    // Merge into a fresh store
    let mut target_store = ThreadedMessageStore::new();
    let result = bundle.merge(&mut target_store);

    assert_eq!(result.added, 4, "all 4 messages should be added");
    assert_eq!(result.deduplicated, 0, "no duplicates in fresh store");

    // Verify all messages are present
    assert!(target_store.contains(&root_hash, &tid));
    assert!(target_store.contains(&left_hash, &tid));
    assert!(target_store.contains(&right_hash, &tid));
    assert!(target_store.contains(&join_hash, &tid));

    // The target store's causal closure of join should match
    let target_closure = target_store.causal_closure(&join_hash, &tid);
    assert_eq!(target_closure.len(), 4);
}

/// Merging a bundle into a store that already has some messages deduplicates.
#[test]
fn fan_in_bundle_merge_deduplicates_shared_history() {
    let tid = thread_id();
    let mut store = ThreadedMessageStore::new();

    // Build a diamond: root → left, root → right, (left, right) → join
    let root = simple_msg("root", Some(CausedBy::Begin));
    let root_hash = compute_hash(&root);
    store.append(root_hash.clone(), tid.clone(), root.clone());

    let left = simple_msg("left", Some(CausedBy::Single(root_hash.0.clone())));
    let left_hash = compute_hash(&left);
    store.append(left_hash.clone(), tid.clone(), left);

    let right = simple_msg("right", Some(CausedBy::Single(root_hash.0.clone())));
    let right_hash = compute_hash(&right);
    store.append(right_hash.clone(), tid.clone(), right);

    let mut causes = vec![left_hash.0.clone(), right_hash.0.clone()];
    causes.sort();
    let join = simple_msg("join", Some(CausedBy::Multiple(causes)));
    let join_hash = compute_hash(&join);
    store.append(join_hash.clone(), tid.clone(), join);

    let bundle = CausalClosureBundle::extract(&join_hash, &tid, &store).unwrap();

    // Target store already has the root
    let mut target_store = ThreadedMessageStore::new();
    target_store.append(root_hash.clone(), tid.clone(), root);

    let result = bundle.merge(&mut target_store);

    assert_eq!(result.added, 3, "3 new messages added");
    assert_eq!(result.deduplicated, 1, "root was already present");
}

/// Linear chain bundle has complete causal closure.
#[test]
fn linear_chain_bundle_has_complete_closure() {
    let (store, hashes) = build_linear_chain(5);
    let tid = thread_id();
    let tip = hashes.last().unwrap();

    let bundle = CausalClosureBundle::extract(tip, &tid, &store).unwrap();

    assert_eq!(bundle.len(), 5, "5-message chain");
    assert!(bundle.verify_completeness().is_ok());
    assert!(bundle.verify_hashes(|msg| compute_hash(msg)).is_ok());

    // All hashes must be present
    let bundle_hash_set: std::collections::HashSet<_> =
        bundle.messages.iter().map(|(h, _)| h).collect();
    for h in &hashes {
        assert!(bundle_hash_set.contains(h));
    }
}
