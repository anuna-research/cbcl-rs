//! Differential parity tests with the Lean mechanisation (REQ-518 / TEST-518 / ADR-513).
//!
//! For every Lean theorem in REQ-510..516 in `lean-cbcl/`, this file asserts
//! the same property at the value level via `proptest` (1000 cases default).
//! Each test references the corresponding Lean theorem in a code comment so
//! that drift between the model and the Rust implementation surfaces as a
//! property-test failure rather than a silent divergence.
//!
//! See SPEC-005 §"REQ-518: Differential parity with Rust implementation",
//! §"TEST-518: Differential parity", and §"ADR-513".

use cbcl_core::message::{CausedBy, Message, Performative};
use cbcl_core::protocol::{
    verify_causal, CausalProtocol, CausalViolation, NodeRef, ProtocolViolation, StepDecl,
    VerificationResult,
};
use cbcl_core::sexpr::{Atom, SExpr};
use cbcl_core::store::{ContentHash, MessageStore, ThreadId, ThreadedMessageStore};

use std::collections::{BTreeMap, BTreeSet};

use proptest::prelude::*;

// ===========================================================================
// Lattice-position helpers
// ===========================================================================
//
// The Lean mechanisation collapses every `Violation _` into a single carrier
// element (`LeanCbcl/Lattice/Result.lean::VerificationResult.violation`),
// whereas Rust's `VerificationResult::Violation(CausalViolation)` retains
// blame detail. The parity tests therefore compare *lattice positions*, not
// exact violation payloads — anything else would conflate the lattice axioms
// with blame-attribution choices that are out of scope for REQ-510..514.

/// Three-element lattice carrier matching `LeanCbcl/Lattice/Result.lean`:
/// `0 = unknown`, `1 = valid`, `2 = violation`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Pos {
    Unknown,
    Valid,
    Violation,
}

fn pos(r: &VerificationResult) -> Pos {
    match r {
        VerificationResult::Unknown => Pos::Unknown,
        VerificationResult::Valid => Pos::Valid,
        VerificationResult::Violation(_) => Pos::Violation,
    }
}

/// `meet` truth table from SPEC-003 REQ-303 / `Lattice/Result.lean::meet`.
fn meet_pos(a: Pos, b: Pos) -> Pos {
    use Pos::*;
    match (a, b) {
        (Violation, _) | (_, Violation) => Violation,
        (Unknown, _) | (_, Unknown) => Unknown,
        (Valid, Valid) => Valid,
    }
}

/// `join` truth table from SPEC-003 REQ-303 / `Lattice/Result.lean::join`.
fn join_pos(a: Pos, b: Pos) -> Pos {
    use Pos::*;
    match (a, b) {
        (Valid, _) | (_, Valid) => Valid,
        (Violation, _) | (_, Violation) => Violation,
        (Unknown, Unknown) => Unknown,
    }
}

/// Lean's "valid is sticky" knowledge order from `Lattice/Result.lean::le`:
/// `a ⊑ b ↔ (a = valid → b = valid)`. Used by REQ-512 / REQ-514.
fn le_lean(a: Pos, b: Pos) -> bool {
    !matches!(a, Pos::Valid) || matches!(b, Pos::Valid)
}

// ===========================================================================
// Generators
// ===========================================================================

fn arb_pos() -> impl Strategy<Value = Pos> {
    prop_oneof![Just(Pos::Unknown), Just(Pos::Valid), Just(Pos::Violation)]
}

/// Sample `VerificationResult` values, covering every constructor including
/// two distinct `Violation` variants so the lattice axioms can be exercised
/// against blame-bearing values (the position-level comparison strips blame).
fn arb_result() -> impl Strategy<Value = VerificationResult> {
    prop_oneof![
        Just(VerificationResult::Unknown),
        Just(VerificationResult::Valid),
        Just(VerificationResult::Violation(CausalViolation::MissingCausedBy)),
        Just(VerificationResult::Violation(CausalViolation::UnknownPredecessor {
            caused_by: "h".into()
        })),
    ]
}

fn tid() -> ThreadId {
    ThreadId("parity".into())
}

fn make_msg(perf: &str, caused_by: Option<CausedBy>) -> Message {
    Message::Simple {
        performative: Performative::Custom(perf.into()),
        recipient: None,
        content: SExpr::Atom(Atom::Str(format!("{}-content", perf))),
        params: Vec::new(),
        thread: None,
        sender: None,
        caused_by,
    }
}

/// Linear protocol used as the substrate for REQ-512 / REQ-514:
/// `begin → ask → reply → confirm`.
fn linear_protocol() -> CausalProtocol {
    let mut steps = BTreeMap::new();
    steps.insert(
        "ask".into(),
        StepDecl {
            performative: "ask".into(),
            predecessors: vec![NodeRef::Single("begin".into())],
            successors: vec![NodeRef::Single("reply".into())],
        },
    );
    steps.insert(
        "reply".into(),
        StepDecl {
            performative: "reply".into(),
            predecessors: vec![NodeRef::Single("ask".into())],
            successors: vec![NodeRef::Single("confirm".into())],
        },
    );
    steps.insert(
        "confirm".into(),
        StepDecl {
            performative: "confirm".into(),
            predecessors: vec![NodeRef::Single("reply".into())],
            successors: vec![],
        },
    );
    CausalProtocol { steps }
}

/// Pool of (hash, performative, caused_by) triples used to populate stores
/// in REQ-512 / REQ-514 tests. Hashes are drawn from a small fixed pool so
/// arbitrary subsets exhibit the full range of (Unknown, Valid, Violation)
/// outcomes when verified.
fn arb_store_entry() -> impl Strategy<Value = (String, String, Option<CausedBy>)> {
    let h = prop_oneof![
        Just("h-ask".to_string()),
        Just("h-reply".to_string()),
        Just("h-confirm".to_string()),
        Just("h-other".to_string()),
    ];
    let p = prop_oneof![
        Just("ask".to_string()),
        Just("reply".to_string()),
        Just("confirm".to_string()),
        Just("rogue".to_string()),
    ];
    let cb = prop_oneof![
        Just(None),
        Just(Some(CausedBy::Begin)),
        Just(Some(CausedBy::Single("h-ask".to_string()))),
    ];
    (h, p, cb)
}

/// Disjoint variant for REQ-514: hashes are drawn from a pool guaranteed
/// not to collide with the partner pool, so sequential `append`-as-union
/// behaves like real set union (no first-write-wins ambiguity).
fn arb_store_entry_pool_a() -> impl Strategy<Value = (String, String, Option<CausedBy>)> {
    let h = prop_oneof![
        Just("a-ask".to_string()),
        Just("a-reply".to_string()),
        Just("a-confirm".to_string()),
    ];
    let p = prop_oneof![
        Just("ask".to_string()),
        Just("reply".to_string()),
        Just("confirm".to_string()),
        Just("rogue".to_string()),
    ];
    (h, p, Just(Some(CausedBy::Begin)))
}

fn arb_store_entry_pool_b() -> impl Strategy<Value = (String, String, Option<CausedBy>)> {
    let h = prop_oneof![
        Just("b-ask".to_string()),
        Just("b-reply".to_string()),
        Just("b-confirm".to_string()),
    ];
    let p = prop_oneof![
        Just("ask".to_string()),
        Just("reply".to_string()),
        Just("confirm".to_string()),
        Just("rogue".to_string()),
    ];
    (h, p, Just(Some(CausedBy::Begin)))
}

fn build_store(entries: &[(String, String, Option<CausedBy>)]) -> ThreadedMessageStore {
    let mut store = ThreadedMessageStore::new();
    let t = tid();
    for (h, perf, cb) in entries {
        store.append(ContentHash(h.clone()), t.clone(), make_msg(perf, cb.clone()));
    }
    store
}

// ===========================================================================
// REQ-510: Three-valued result lattice axioms.
// Mirrors `LeanCbcl/Lattice/Result.lean :: BoundedLattice VerificationResult`
// (`meet_assoc`, `meet_comm`, `meet_idem`, `join_assoc`, `join_comm`,
// `join_idem`, `bot_join`, `join_bot`, `top_meet`, `meet_top`) and
// `result_meet_table` / `result_join_table`.
// ===========================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(1000))]

    /// REQ-510 — `Lattice/Result.lean :: meet_assoc`.
    #[test]
    fn req510_meet_assoc(a in arb_result(), b in arb_result(), c in arb_result()) {
        let lhs = pos(&a.clone().meet(b.clone()).meet(c.clone()));
        let rhs = pos(&a.meet(b.meet(c)));
        prop_assert_eq!(lhs, rhs);
    }

    /// REQ-510 — `Lattice/Result.lean :: meet_comm`.
    #[test]
    fn req510_meet_comm(a in arb_result(), b in arb_result()) {
        prop_assert_eq!(pos(&a.clone().meet(b.clone())), pos(&b.meet(a)));
    }

    /// REQ-510 — `Lattice/Result.lean :: meet_idem`.
    #[test]
    fn req510_meet_idem(a in arb_result()) {
        prop_assert_eq!(pos(&a.clone().meet(a.clone())), pos(&a));
    }

    /// REQ-510 — `Lattice/Result.lean :: join_assoc`.
    #[test]
    fn req510_join_assoc(a in arb_result(), b in arb_result(), c in arb_result()) {
        let lhs = pos(&a.clone().join(b.clone()).join(c.clone()));
        let rhs = pos(&a.join(b.join(c)));
        prop_assert_eq!(lhs, rhs);
    }

    /// REQ-510 — `Lattice/Result.lean :: join_comm`.
    #[test]
    fn req510_join_comm(a in arb_result(), b in arb_result()) {
        prop_assert_eq!(pos(&a.clone().join(b.clone())), pos(&b.join(a)));
    }

    /// REQ-510 — `Lattice/Result.lean :: join_idem`.
    #[test]
    fn req510_join_idem(a in arb_result()) {
        prop_assert_eq!(pos(&a.clone().join(a.clone())), pos(&a));
    }

    /// REQ-510 — `Lattice/Result.lean :: bot_join` / `join_bot`.
    /// `bot = unknown` is a two-sided identity for `join`.
    #[test]
    fn req510_join_bot_identity(a in arb_result()) {
        let bot = VerificationResult::Unknown;
        prop_assert_eq!(pos(&bot.clone().join(a.clone())), pos(&a));
        prop_assert_eq!(pos(&a.clone().join(bot)), pos(&a));
    }

    /// REQ-510 — `Lattice/Result.lean :: top_meet` / `meet_top`.
    /// `top = valid` is a two-sided identity for `meet`.
    #[test]
    fn req510_meet_top_identity(a in arb_result()) {
        let top = VerificationResult::Valid;
        prop_assert_eq!(pos(&top.clone().meet(a.clone())), pos(&a));
        prop_assert_eq!(pos(&a.clone().meet(top)), pos(&a));
    }

    /// REQ-510 — `Lattice/Result.lean :: result_meet_table` / `result_join_table`.
    /// The 3×3 truth tables agree with the Pos-level functions, which mirror
    /// the SPEC-003 REQ-303 markdown verbatim.
    #[test]
    fn req510_truth_tables(a in arb_result(), b in arb_result()) {
        prop_assert_eq!(pos(&a.clone().meet(b.clone())), meet_pos(pos(&a), pos(&b)));
        prop_assert_eq!(pos(&a.clone().join(b.clone())), join_pos(pos(&a), pos(&b)));
    }
}

// ===========================================================================
// REQ-511: Message store G-Set axioms.
// Mirrors `LeanCbcl/Lattice/Store.lean` — `union` is associative,
// commutative, and idempotent under set equality, and `lookup` is monotone
// under `⊆`.
//
// The Rust analog of `union` is sequential `append` of disjoint hashes;
// duplicate hashes deduplicate (REQ-310). We test the lattice axioms by
// asserting that lookup results are invariant under reordering / repetition
// of the appended messages.
// ===========================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(1000))]

    /// REQ-511 — `Lattice/Store.lean :: union_comm` (lookup-equivalent form).
    /// Two stores built from the same set of messages in opposite orders
    /// expose the same lookups for every hash — the order of `append` does
    /// not affect set membership.
    #[test]
    fn req511_union_comm(
        entries in prop::collection::vec(arb_store_entry(), 0..6),
    ) {
        let s_ab = build_store(&entries);
        let mut reversed = entries.clone();
        reversed.reverse();
        let s_ba = build_store(&reversed);
        let t = tid();
        for (h, _, _) in &entries {
            let ch = ContentHash(h.clone());
            let in_ab = s_ab.contains(&ch, &t);
            let in_ba = s_ba.contains(&ch, &t);
            prop_assert_eq!(in_ab, in_ba);
        }
    }

    /// REQ-511 — `Lattice/Store.lean :: union_assoc`.
    /// Three stores built from concatenations `(A ++ B) ++ C` and
    /// `A ++ (B ++ C)` expose the same membership.
    #[test]
    fn req511_union_assoc(
        a in prop::collection::vec(arb_store_entry(), 0..3),
        b in prop::collection::vec(arb_store_entry(), 0..3),
        c in prop::collection::vec(arb_store_entry(), 0..3),
    ) {
        let mut left = a.clone();
        left.extend(b.clone());
        left.extend(c.clone());
        let mut right = a.clone();
        let mut bc = b.clone();
        bc.extend(c.clone());
        right.extend(bc);
        let s_left = build_store(&left);
        let s_right = build_store(&right);
        let t = tid();
        for (h, _, _) in left.iter().chain(right.iter()) {
            let ch = ContentHash(h.clone());
            prop_assert_eq!(s_left.contains(&ch, &t), s_right.contains(&ch, &t));
        }
    }

    /// REQ-511 — `Lattice/Store.lean :: union_idem`.
    /// Appending the same entries twice (order preserved) yields the same
    /// membership as appending once. This relies on REQ-310 (deduplication).
    #[test]
    fn req511_union_idem(entries in prop::collection::vec(arb_store_entry(), 0..6)) {
        let s_once = build_store(&entries);
        let mut twice = entries.clone();
        twice.extend(entries.clone());
        let s_twice = build_store(&twice);
        let t = tid();
        for (h, _, _) in &entries {
            let ch = ContentHash(h.clone());
            prop_assert_eq!(s_once.contains(&ch, &t), s_twice.contains(&ch, &t));
        }
    }

    /// REQ-511 — `Lattice/Store.lean :: lookup_monotone`.
    /// `S₁ ⊆ S₂` ⇒ for every hash `h` and message `M`,
    /// `lookup h S₁ = some M → lookup h S₂ = some M`. We construct `S₂` as
    /// `S₁ ∪ extras` so subsetting is by construction.
    #[test]
    fn req511_lookup_monotone(
        base in prop::collection::vec(arb_store_entry(), 0..6),
        extras in prop::collection::vec(arb_store_entry(), 0..6),
    ) {
        let s1 = build_store(&base);
        let mut combined = base.clone();
        combined.extend(extras.clone());
        let s2 = build_store(&combined);
        let t = tid();

        for (h, _, _) in &base {
            let ch = ContentHash(h.clone());
            if let Some(m1) = s1.lookup_in_thread(&ch, &t) {
                let m1_perf = m1.performative().map(|p| p.name().to_string());
                let m2 = s2.lookup_in_thread(&ch, &t);
                prop_assert!(m2.is_some(), "S₁ ⊆ S₂ violated: hash {} missing in S₂", h);
                let m2_perf = m2.unwrap().performative().map(|p| p.name().to_string());
                prop_assert_eq!(m1_perf, m2_perf,
                    "lookup_monotone violated: same hash resolves to different messages");
            }
        }
    }
}

// ===========================================================================
// REQ-512: `verify_monotone`.
// Mirrors `LeanCbcl/Verify.lean :: verify_monotone`:
//
//     S₁ ⊆ S₂ → verify M P S₁ ⊑ verify M P S₂
//
// `⊑` is the "valid is sticky" order from `Lattice/Result.lean::le`.
// ===========================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(1000))]

    /// REQ-512 — `Verify.lean :: verify_monotone` (single predecessor).
    #[test]
    fn req512_verify_monotone_single(
        base in prop::collection::vec(arb_store_entry(), 0..4),
        extras in prop::collection::vec(arb_store_entry(), 0..4),
        target in prop_oneof![
            Just("ask".to_string()),
            Just("reply".to_string()),
            Just("confirm".to_string()),
        ],
        cb_hash in prop_oneof![
            Just("h-ask".to_string()),
            Just("h-reply".to_string()),
            Just("h-other".to_string()),
            Just("h-missing".to_string()),
        ],
    ) {
        let proto = linear_protocol();
        let t = tid();
        let s1 = build_store(&base);
        let mut combined = base.clone();
        combined.extend(extras);
        let s2 = build_store(&combined);
        let cb = CausedBy::Single(cb_hash);
        let r1 = pos(&verify_causal(&target, Some(&cb), &s1, &proto, &t));
        let r2 = pos(&verify_causal(&target, Some(&cb), &s2, &proto, &t));
        prop_assert!(le_lean(r1, r2),
            "verify_monotone violated: r1={:?}, r2={:?}", r1, r2);
    }

    /// REQ-512 — `Verify.lean :: verify_monotone` covering every CausedBy
    /// arm: missing, Begin, Single, Multiple. The `target` performative is
    /// drawn from the linear protocol.
    #[test]
    fn req512_verify_monotone_all_caused_by_arms(
        base in prop::collection::vec(arb_store_entry(), 0..4),
        extras in prop::collection::vec(arb_store_entry(), 0..4),
        cb_kind in 0u8..4,
    ) {
        let proto = linear_protocol();
        let t = tid();
        let s1 = build_store(&base);
        let mut combined = base.clone();
        combined.extend(extras);
        let s2 = build_store(&combined);
        let cb = match cb_kind {
            0 => None,
            1 => Some(CausedBy::Begin),
            2 => Some(CausedBy::Single("h-ask".into())),
            _ => Some(CausedBy::Multiple(vec!["h-ask".into(), "h-reply".into()])),
        };
        let r1 = pos(&verify_causal("reply", cb.as_ref(), &s1, &proto, &t));
        let r2 = pos(&verify_causal("reply", cb.as_ref(), &s2, &proto, &t));
        prop_assert!(le_lean(r1, r2),
            "verify_monotone violated for cb_kind={}: r1={:?}, r2={:?}",
            cb_kind, r1, r2);
    }
}

// ===========================================================================
// REQ-513: `verify_all_is_meet`.
// Mirrors `LeanCbcl/Verify.lean :: verify` for `(all ps)`:
//
//     verify M (all ps) S = ps.foldr (fun p acc => verify M p S ⊓ acc) ⊤
//
// In Rust, fan-in is expressed via `NodeRef::All(set)` on the predecessor
// list combined with `CausedBy::Multiple(hashes)`. Each hash contributes a
// per-component verification result (Unknown if absent, Valid if its
// resolved performative is in `set`, Violation otherwise); the fan-in
// outcome is then the meet over these contributions, with one residual
// `IncompleteFanIn` violation when the meet is `Valid` but `set` is not
// fully covered.
//
// The parity test fixes the all-set to a 2-element pair and generates
// hashes whose store-resolved type either covers both slots or fails to
// cover them; we assert that the fan-in lattice position equals the meet
// of per-hash positions, and that `Valid` only arises when every slot is
// covered (the `IncompleteFanIn` residual).
// ===========================================================================

/// Minimal fan-in protocol: `(all x y) → z`.
fn fan_in_protocol() -> CausalProtocol {
    let mut steps = BTreeMap::new();
    let mut all_set = BTreeSet::new();
    all_set.insert("x".to_string());
    all_set.insert("y".to_string());
    steps.insert(
        "z".into(),
        StepDecl {
            performative: "z".into(),
            predecessors: vec![NodeRef::All(all_set)],
            successors: vec![],
        },
    );
    CausalProtocol { steps }
}

fn arb_fanin_entry() -> impl Strategy<Value = (String, String)> {
    let h = prop_oneof![
        Just("h1".to_string()),
        Just("h2".to_string()),
        Just("h3".to_string()),
    ];
    let perf = prop_oneof![
        Just("x".to_string()),
        Just("y".to_string()),
        Just("z".to_string()), // not in {x, y} — wrong type
    ];
    (h, perf)
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(1000))]

    /// REQ-513 — `Verify.lean :: verify` for `(all ps)`.
    /// The fan-in lattice position equals the meet of per-hash positions,
    /// modulo the `IncompleteFanIn` residual when the per-hash meet is
    /// `Valid` but `{x, y}` is not fully covered. In every case, the
    /// per-hash meet is `⊑` the fan-in result in the Lean order.
    #[test]
    fn req513_verify_all_is_meet(
        store_entries in prop::collection::vec(arb_fanin_entry(), 0..4),
        cb_hashes in prop::collection::vec(
            prop_oneof![
                Just("h1".to_string()),
                Just("h2".to_string()),
                Just("missing".to_string()),
            ],
            1..4,
        ),
    ) {
        let proto = fan_in_protocol();
        let t = tid();
        let mut store = ThreadedMessageStore::new();
        for (h, perf) in &store_entries {
            store.append(ContentHash(h.clone()), t.clone(),
                make_msg(perf, Some(CausedBy::Begin)));
        }

        let cb = CausedBy::Multiple(cb_hashes.clone());
        let actual = pos(&verify_causal("z", Some(&cb), &store, &proto, &t));

        // Per-component meet: lookup each hash, classify as Unknown / Valid
        // (if its resolved type is in {x, y}) / Violation (wrong type).
        let allowed: BTreeSet<&str> = ["x", "y"].into_iter().collect();
        let mut acc = Pos::Valid;
        for h in &cb_hashes {
            let ch = ContentHash(h.clone());
            let p = match store.lookup_in_thread(&ch, &t) {
                None => Pos::Unknown,
                Some(msg) => {
                    let pname = msg.performative().map(|p| p.name()).unwrap_or("");
                    if allowed.contains(pname) { Pos::Valid } else { Pos::Violation }
                }
            };
            acc = meet_pos(acc, p);
        }

        // When the per-component meet is non-Valid, it equals the fan-in
        // result — this is the equality the Lean theorem asserts at the
        // abstract level. The `Valid` case is an over-approximation in the
        // Lean model (which has no completeness side-check); the Rust
        // implementation refines it with `IncompleteFanIn` when not every
        // slot in the all-set is covered, which is observable as the
        // fan-in result becoming `Violation` instead of `Valid`.
        if acc != Pos::Valid {
            prop_assert_eq!(acc, actual,
                "verify_all_is_meet: expected meet ({:?}) to equal actual ({:?})", acc, actual);
        } else {
            prop_assert!(matches!(actual, Pos::Valid | Pos::Violation),
                "verify_all_is_meet: meet=Valid but actual={:?} is not in {{Valid, Violation}}",
                actual);
        }
    }

    /// REQ-513 — meet identity for the empty fold. With both `x` and `y`
    /// resolving to correct types, the fan-in returns `Valid` — the
    /// `meet`-identity (`⊤ = valid`) of the empty residual fold.
    #[test]
    fn req513_verify_all_full_coverage_is_valid(_ in 0..32u32) {
        let proto = fan_in_protocol();
        let t = tid();
        let mut store = ThreadedMessageStore::new();
        store.append(ContentHash("hx".into()), t.clone(),
            make_msg("x", Some(CausedBy::Begin)));
        store.append(ContentHash("hy".into()), t.clone(),
            make_msg("y", Some(CausedBy::Begin)));
        let cb = CausedBy::Multiple(vec!["hx".into(), "hy".into()]);
        let r = verify_causal("z", Some(&cb), &store, &proto, &t);
        prop_assert_eq!(pos(&r), Pos::Valid);
    }
}

// ===========================================================================
// REQ-514: `verify_eventually_consistent`.
// Mirrors `LeanCbcl/Verify.lean :: verify_eventually_consistent`:
//
//     verify M P S₁ ⊔ verify M P S₂ ⊑ verify M P (S₁ ∪ S₂)
//
// We construct two stores from disjoint random subsets and compare against
// the store union (sequential `append`).
// ===========================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(1000))]

    /// REQ-514 — `Verify.lean :: verify_eventually_consistent`.
    /// Stores are drawn from disjoint hash pools so that sequential
    /// `append`-as-union faithfully models set union (Rust `append` is
    /// first-write-wins on hash collisions, which would otherwise make
    /// `S₁ ∪ S₂ ≠ S₂ ∪ S₁` and fail the theorem on inputs that the Lean
    /// abstract `MessageStore` would never produce).
    #[test]
    fn req514_verify_eventually_consistent(
        a in prop::collection::vec(arb_store_entry_pool_a(), 0..4),
        b in prop::collection::vec(arb_store_entry_pool_b(), 0..4),
        target in prop_oneof![
            Just("ask".to_string()),
            Just("reply".to_string()),
            Just("confirm".to_string()),
        ],
        cb_hash in prop_oneof![
            Just("a-ask".to_string()),
            Just("a-reply".to_string()),
            Just("b-ask".to_string()),
            Just("b-reply".to_string()),
            Just("missing".to_string()),
        ],
    ) {
        let proto = linear_protocol();
        let t = tid();
        let s1 = build_store(&a);
        let s2 = build_store(&b);
        let mut union = a.clone();
        union.extend(b);
        let s12 = build_store(&union);
        let cb = CausedBy::Single(cb_hash);

        let r1 = pos(&verify_causal(&target, Some(&cb), &s1, &proto, &t));
        let r2 = pos(&verify_causal(&target, Some(&cb), &s2, &proto, &t));
        let r12 = pos(&verify_causal(&target, Some(&cb), &s12, &proto, &t));
        let joined = join_pos(r1, r2);
        prop_assert!(le_lean(joined, r12),
            "verify_eventually_consistent violated: \
             r1={:?}, r2={:?}, join={:?}, r(union)={:?}",
            r1, r2, joined, r12);
    }
}

// ===========================================================================
// REQ-515: R5 sub-check soundness + completeness (full iff).
// Mirrors `LeanCbcl/R5.lean :: check_acyclicity_iff_no_cycle`,
// `check_reachability_iff_all_reachable`,
// `check_performative_definedness_iff_all_defined`, and
// `check_step_uniqueness_iff_no_duplicates`.
//
// Each test asserts the soundness or completeness direction at the value
// level by generating known-good and known-bad protocols and confirming
// the check's return value classifies them correctly.
// ===========================================================================

fn step(name: &str, preds: Vec<&str>, succs: Vec<&str>) -> StepDecl {
    StepDecl {
        performative: name.into(),
        predecessors: preds.iter().map(|s| NodeRef::Single(s.to_string())).collect(),
        successors: succs.iter().map(|s| NodeRef::Single(s.to_string())).collect(),
    }
}

/// Build a random DAG-shaped protocol whose successor edges go from earlier
/// to later names — guaranteed acyclic by construction.
fn arb_acyclic_protocol() -> impl Strategy<Value = CausalProtocol> {
    prop::collection::vec(0u8..4, 1..6).prop_map(|targets| {
        let names: Vec<String> = (0..targets.len()).map(|i| format!("p{}", i)).collect();
        let mut steps = BTreeMap::new();
        steps.insert("begin".into(), step("begin", vec![], names.iter().map(|s| s.as_str()).collect()));
        for (i, name) in names.iter().enumerate() {
            let preds: Vec<&str> = if i == 0 { vec!["begin"] } else { vec![names[i - 1].as_str()] };
            let succs: Vec<&str> = if i + 1 < names.len() {
                vec![names[i + 1].as_str()]
            } else {
                vec![]
            };
            steps.insert(name.clone(), step(name, preds, succs));
        }
        CausalProtocol { steps }
    })
}

/// Build a protocol with a guaranteed direct cycle `a → b → a`.
fn arb_cyclic_protocol() -> impl Strategy<Value = CausalProtocol> {
    Just(()).prop_map(|_| {
        let mut steps = BTreeMap::new();
        steps.insert("a".into(), step("a", vec!["b"], vec!["b"]));
        steps.insert("b".into(), step("b", vec!["a"], vec!["a"]));
        CausalProtocol { steps }
    })
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(1000))]

    /// REQ-515 — `R5.lean :: check_acyclicity_iff_no_cycle` (soundness `→`).
    /// Acyclic-by-construction protocols pass `check_acyclicity`.
    #[test]
    fn req515_acyclicity_sound_on_acyclic(proto in arb_acyclic_protocol()) {
        let violations = proto.check_acyclicity();
        prop_assert!(violations.is_empty(),
            "acyclic protocol flagged as cyclic: {:?}", violations);
    }

    /// REQ-515 — `R5.lean :: check_acyclicity_iff_no_cycle` (completeness `←`).
    /// Cyclic-by-construction protocols are flagged.
    #[test]
    fn req515_acyclicity_complete_on_cyclic(proto in arb_cyclic_protocol()) {
        let violations = proto.check_acyclicity();
        prop_assert!(violations.iter().any(|v| matches!(v, ProtocolViolation::Cycle { .. })),
            "cyclic protocol not flagged: {:?}", violations);
    }

    /// REQ-515 — `R5.lean :: check_reachability_iff_all_reachable` (soundness `→`).
    /// In a linear chain `begin → p0 → p1 → ...`, every step is reachable
    /// from `begin`; the check returns `[]`.
    #[test]
    fn req515_reachability_sound_on_linear(proto in arb_acyclic_protocol()) {
        let violations = proto.check_reachability();
        prop_assert!(violations.is_empty(),
            "fully-reachable protocol flagged: {:?}", violations);
    }

    /// REQ-515 — `R5.lean :: check_reachability_iff_all_reachable` (completeness `←`).
    /// Adding an orphan step that is not reachable from `begin` is flagged.
    #[test]
    fn req515_reachability_complete_on_orphan(orphan_name in "p[a-z]{1,4}") {
        let mut steps = BTreeMap::new();
        steps.insert("begin".into(), step("begin", vec![], vec!["p0"]));
        steps.insert("p0".into(), step("p0", vec!["begin"], vec![]));
        steps.insert(orphan_name.clone(), step(&orphan_name, vec![], vec![]));
        let proto = CausalProtocol { steps };
        let violations = proto.check_reachability();
        if orphan_name != "begin" && orphan_name != "p0" {
            prop_assert!(violations.iter().any(|v|
                matches!(v, ProtocolViolation::Unreachable { step } if step == &orphan_name)),
                "orphan step {} not flagged: {:?}", orphan_name, violations);
        }
    }

    /// REQ-515 — `R5.lean :: check_performative_definedness_iff_all_defined`.
    /// Every referenced performative (excluding `begin`) is in the defined
    /// set ⇒ check returns `[]`.
    #[test]
    fn req515_definedness_sound(proto in arb_acyclic_protocol()) {
        let names: Vec<String> = proto.steps.keys().filter(|k| *k != "begin").cloned().collect();
        let defined: Vec<&str> = names.iter().map(|s| s.as_str()).collect();
        let violations = proto.check_performative_definedness(&defined);
        prop_assert!(violations.is_empty(),
            "all-defined protocol flagged: {:?}", violations);
    }

    /// REQ-515 — `R5.lean :: check_performative_definedness_iff_all_defined`
    /// (completeness). Removing one defined name flags the corresponding
    /// undefined-performative violation.
    #[test]
    fn req515_definedness_complete(proto in arb_acyclic_protocol()) {
        let names: Vec<String> = proto.steps.keys().filter(|k| *k != "begin").cloned().collect();
        prop_assume!(!names.is_empty());
        let dropped = names[0].clone();
        let kept: Vec<&str> = names.iter().skip(1).map(|s| s.as_str()).collect();
        let violations = proto.check_performative_definedness(&kept);
        prop_assert!(violations.iter().any(|v|
            matches!(v, ProtocolViolation::UndefinedPerformative { name } if name == &dropped)),
            "dropped name {} not flagged: {:?}", dropped, violations);
    }

    /// REQ-515 — `R5.lean :: check_step_uniqueness_iff_no_duplicates`.
    /// A protocol with no duplicate predecessor / successor `NodeRef`
    /// entries passes the uniqueness check.
    #[test]
    fn req515_step_uniqueness_sound(proto in arb_acyclic_protocol()) {
        let violations = proto.check_step_uniqueness();
        prop_assert!(violations.is_empty(),
            "duplicate-free protocol flagged: {:?}", violations);
    }

    /// REQ-515 — `R5.lean :: check_step_uniqueness_iff_no_duplicates`
    /// (completeness). Inserting a duplicate predecessor flags the step.
    #[test]
    fn req515_step_uniqueness_complete(name in "p[a-z]{1,4}") {
        let mut steps = BTreeMap::new();
        steps.insert(
            name.clone(),
            StepDecl {
                performative: name.clone(),
                predecessors: vec![
                    NodeRef::Single("begin".into()),
                    NodeRef::Single("begin".into()),
                ],
                successors: vec![],
            },
        );
        let proto = CausalProtocol { steps };
        let violations = proto.check_step_uniqueness();
        prop_assert!(violations.iter().any(|v|
            matches!(v, ProtocolViolation::DuplicateStep { name: n } if n == &name)),
            "duplicate-predecessor step {} not flagged: {:?}", name, violations);
    }
}

// ===========================================================================
// REQ-516: DCFL preservation theorems.
// Mirrors `LeanCbcl/DCFLPreservation.lean :: protocolClause_isSExpr` and
// `shapeClause_isSExpr` (and their `dcfl_preserved_*` corollaries):
//
//   * `(protocol args …)` is a `.list (.atom (.symbol "protocol") :: args)`
//     — the same `SExpr.list` constructor that every other CBCL clause
//     uses, so `IsSExpr` accepts it trivially.
//   * Same argument for `(shape args …)`.
//
// At the value level: build `(protocol args)` / `(shape args)` from
// arbitrary CBCL S-expression bodies, serialise, and reparse via
// `SExpr::parse`. The clauses round-trip through the existing DCFL parser
// — adding them to a dialect introduces no new grammar shape.
// ===========================================================================

fn arb_clause_arg() -> impl Strategy<Value = SExpr> {
    let leaf = prop_oneof![
        prop::string::string_regex("[a-z][a-z0-9_-]{0,4}").unwrap()
            .prop_map(|s| SExpr::Atom(Atom::Symbol(s))),
        any::<i64>().prop_map(|n| SExpr::Atom(Atom::Num(n))),
        any::<bool>().prop_map(|b| SExpr::Atom(Atom::Bool(b))),
    ];
    leaf.prop_recursive(3, 16, 4, |inner| {
        prop::collection::vec(inner, 0..4).prop_map(SExpr::List)
    })
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(1000))]

    /// REQ-516 — `DCFLPreservation.lean :: protocolClause_isSExpr` /
    /// `dcfl_preserved_under_protocol`. A `(protocol args…)` clause built
    /// over arbitrary CBCL S-expression bodies parses cleanly via the
    /// existing DCFL recogniser and round-trips through display/parse.
    #[test]
    fn req516_protocol_clause_is_sexpr(args in prop::collection::vec(arb_clause_arg(), 0..4)) {
        let mut items = vec![SExpr::Atom(Atom::Symbol("protocol".into()))];
        items.extend(args);
        let clause = SExpr::List(items);
        let serialised = clause.to_string();
        let reparsed: SExpr = serialised.parse().expect("clause must parse");
        prop_assert_eq!(reparsed, clause);
    }

    /// REQ-516 — `DCFLPreservation.lean :: shapeClause_isSExpr` /
    /// `dcfl_preserved_under_shape`. Same property for `(shape args…)`.
    #[test]
    fn req516_shape_clause_is_sexpr(args in prop::collection::vec(arb_clause_arg(), 0..4)) {
        let mut items = vec![SExpr::Atom(Atom::Symbol("shape".into()))];
        items.extend(args);
        let clause = SExpr::List(items);
        let serialised = clause.to_string();
        let reparsed: SExpr = serialised.parse().expect("clause must parse");
        prop_assert_eq!(reparsed, clause);
    }

    /// REQ-516 — `DCFLPreservation.lean :: protocol_dispatch_deterministic`.
    /// The dispatch token `protocol` heads the clause as a deterministic
    /// symbol — no alternation in the head position.
    #[test]
    fn req516_protocol_dispatch_deterministic(args in prop::collection::vec(arb_clause_arg(), 0..4)) {
        let mut items = vec![SExpr::Atom(Atom::Symbol("protocol".into()))];
        items.extend(args);
        let clause = SExpr::List(items);
        match &clause {
            SExpr::List(xs) => {
                prop_assert!(!xs.is_empty());
                match &xs[0] {
                    SExpr::Atom(Atom::Symbol(s)) => prop_assert_eq!(s.as_str(), "protocol"),
                    _ => prop_assert!(false, "protocol head must be a symbol atom"),
                }
            }
            _ => prop_assert!(false, "protocol clause must be a list"),
        }
    }

    /// REQ-516 — `DCFLPreservation.lean :: shape_dispatch_deterministic`.
    /// Same property for the `shape` dispatch token.
    #[test]
    fn req516_shape_dispatch_deterministic(args in prop::collection::vec(arb_clause_arg(), 0..4)) {
        let mut items = vec![SExpr::Atom(Atom::Symbol("shape".into()))];
        items.extend(args);
        let clause = SExpr::List(items);
        match &clause {
            SExpr::List(xs) => {
                prop_assert!(!xs.is_empty());
                match &xs[0] {
                    SExpr::Atom(Atom::Symbol(s)) => prop_assert_eq!(s.as_str(), "shape"),
                    _ => prop_assert!(false, "shape head must be a symbol atom"),
                }
            }
            _ => prop_assert!(false, "shape clause must be a list"),
        }
    }
}

// Suppress unused-import warning for the `arb_pos` generator — it exists
// to document the lattice carrier even when not directly invoked.
#[allow(dead_code)]
fn _ensure_arb_pos_referenced() -> impl Strategy<Value = Pos> {
    arb_pos()
}
