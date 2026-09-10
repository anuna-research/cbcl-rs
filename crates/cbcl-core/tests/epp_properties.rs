//! SPEC-014 TEST-630..636: property tests transcribing the mechanised EPP
//! theorems over randomly generated protocols and runs.
//!
//! | Test | Lean anchor |
//! |------|-------------|
//! | TEST-630 projection determinism | paper Prop. Determinism (paper-only) |
//! | TEST-631 EPP soundness | `soundness_safety`, EPP.lean |
//! | TEST-632 EPP completeness | `completeness_safety`, EPP.lean |
//! | TEST-633 exactness round-trip | `glue_project_eq` / `project_glue_eq`, EPP.lean |
//! | TEST-634 unknown-means-not-yet-arrived | `unknown_means_not_yet_arrived`, Projectability.lean |
//! | TEST-635 converse witness | `nonlocal_protocol_counterexample`, Projectability.lean |
//! | TEST-636 monotonicity | `valid_stable`, EPP.lean; deployed valid-is-sticky order (ADR-602) |
//!
//! Generator scope: linear (chain) protocols over 2–4 singleton roles with
//! endpoint sets shrinking along the chain — causal locality holds by
//! construction, so generated dialects are R6-clean (asserted). Choices and
//! indexed roles are covered by the example-based suites in `r6.rs`,
//! `projection.rs`, and `auction_e2e.rs`; linearisation coverage comes from
//! shuffled insertion orders (TEST-636).

use cbcl_core::dialect::{Dialect, PerformativeDef, ResourceBounds};
use cbcl_core::message::Message;
use cbcl_core::projection::{project, verify_causal_for_role, LocalProtocol};
use cbcl_core::protocol::{CausalProtocol, NodeRef, StepDecl, VerificationResult};
use cbcl_core::r6::{r6_violations, r6_violations_counted};
use cbcl_core::role::{parse_cast, parse_roles, Cast, Endpoint};
use cbcl_core::sexpr::SExpr;
use cbcl_core::store::{ContentHash, MessageStore, ThreadId, ThreadedMessageStore};
use proptest::prelude::*;
use std::collections::{BTreeMap, BTreeSet};

const ROLE_NAMES: [&str; 4] = ["r0", "r1", "r2", "r3"];
const KEYS: [&str; 4] = ["@k0", "@k1", "@k2", "@k3"];

/// A generated chain protocol: step i has sender `senders[i]`, endpoint
/// set `endpoint_sets[i]` (shrinking along the chain so causal locality
/// holds by construction), predecessor step i−1 (step 0: begin).
#[derive(Debug, Clone)]
struct ChainProtocol {
    n_roles: usize,
    senders: Vec<usize>,
    endpoint_sets: Vec<BTreeSet<usize>>,
}

impl ChainProtocol {
    fn perf_name(i: usize) -> String {
        format!("p{i}")
    }

    fn dialect(&self) -> Dialect {
        let mut perfs = Vec::new();
        let mut steps: BTreeMap<String, StepDecl> = BTreeMap::new();
        steps.insert(
            "begin".to_string(),
            StepDecl {
                performative: "begin".to_string(),
                predecessors: vec![],
                successors: vec![NodeRef::Single(Self::perf_name(0))],
            },
        );
        for (i, eps) in self.endpoint_sets.iter().enumerate() {
            let name = Self::perf_name(i);
            let from = ROLE_NAMES[self.senders[i]];
            let to: BTreeSet<String> = eps
                .iter()
                .filter(|r| **r != self.senders[i])
                .map(|r| ROLE_NAMES[*r].to_string())
                .collect();
            perfs.push(PerformativeDef {
                name: name.clone(),
                params: Vec::new(),
                template: "t".parse::<SExpr>().unwrap(),
                role: Some(cbcl_core::role::RoleAnnotation {
                    from: from.to_string(),
                    to,
                }),
            });
            let pred = if i == 0 {
                "begin".to_string()
            } else {
                Self::perf_name(i - 1)
            };
            let succs = if i + 1 < self.endpoint_sets.len() {
                vec![NodeRef::Single(Self::perf_name(i + 1))]
            } else {
                vec![]
            };
            steps.insert(
                name.clone(),
                StepDecl {
                    performative: name,
                    predecessors: vec![NodeRef::Single(pred)],
                    successors: succs,
                },
            );
        }
        Dialect {
            causal_locality: Default::default(),
            roles: parse_roles(
                &format!("({})", ROLE_NAMES[..self.n_roles].join(" "))
                    .parse::<SExpr>()
                    .unwrap(),
            )
            .unwrap(),
            name: "chain".to_string(),
            extends: Vec::new(),
            author: None,
            performatives: perfs,
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

    fn cast(&self, d: &Dialect) -> Cast {
        let bindings: Vec<String> = (0..self.n_roles)
            .map(|i| format!("({} {})", ROLE_NAMES[i], KEYS[i]))
            .collect();
        parse_cast(
            &format!("({})", bindings.join(" "))
                .parse::<SExpr>()
                .unwrap(),
            &d.roles,
        )
        .unwrap()
    }

    fn root_msg(&self) -> Message {
        let bindings: Vec<String> = (0..self.n_roles)
            .map(|i| format!("({} {})", ROLE_NAMES[i], KEYS[i]))
            .collect();
        let src = format!(
            "(with-roles ({}) (signed {} \"sig\" (hello :thread \"conv\" :caused-by begin)))",
            bindings.join(" "),
            KEYS[0]
        );
        Message::try_from(&src.parse::<SExpr>().unwrap()).unwrap()
    }

    /// The full global run: root plus one message per chain step, each
    /// signed by its sender's key and addressed to its recipients' keys.
    fn run(&self) -> Vec<(String, Message)> {
        let mut msgs = vec![("m-root".to_string(), self.root_msg())];
        for (i, eps) in self.endpoint_sets.iter().enumerate() {
            let sender_key = KEYS[self.senders[i]];
            let recipients: Vec<&str> = eps
                .iter()
                .filter(|r| **r != self.senders[i])
                .map(|r| KEYS[*r])
                .collect();
            let recipient_part = match recipients.len() {
                0 => String::new(),
                1 => format!("{} ", recipients[0]),
                _ => format!("({}) ", recipients.join(" ")),
            };
            let pred = if i == 0 {
                "m-root".to_string()
            } else {
                format!("m{}", i - 1)
            };
            let src = format!(
                "(signed {sender_key} \"sig\" (lang chain ({} {recipient_part}\"x\" :caused-by {pred})))",
                Self::perf_name(i)
            );
            msgs.push((
                format!("m{i}"),
                Message::try_from(&src.parse::<SExpr>().unwrap()).unwrap(),
            ));
        }
        msgs
    }

    /// Run-level projection for a role: the root (root convention) plus
    /// every message of a step whose endpoint set contains the role — for
    /// a chain with shrinking endpoint sets this is a causally closed
    /// prefix.
    fn local_run(&self, role_idx: usize) -> BTreeSet<String> {
        let mut set = BTreeSet::new();
        set.insert("m-root".to_string());
        for (i, eps) in self.endpoint_sets.iter().enumerate() {
            if eps.contains(&role_idx) {
                set.insert(format!("m{i}"));
            }
        }
        set
    }
}

fn arb_chain() -> impl Strategy<Value = ChainProtocol> {
    (2usize..=4, 1usize..=6).prop_flat_map(|(n_roles, len)| {
        // endpoint sets shrink along the chain; the first covers all roles
        // (which also satisfies role reachability).
        let sets = proptest::collection::vec(0u8..(n_roles as u8), len);
        (
            Just(n_roles),
            Just(len),
            sets,
            proptest::collection::vec(0usize..n_roles, len),
        )
            .prop_map(|(n_roles, len, drop_masks, sender_picks)| {
                let mut endpoint_sets: Vec<BTreeSet<usize>> = Vec::with_capacity(len);
                let mut current: BTreeSet<usize> = (0..n_roles).collect();
                let mut senders = Vec::with_capacity(len);
                for i in 0..len {
                    if i > 0 {
                        // drop at most one role per step, keeping ≥ 1
                        let candidate = (drop_masks[i] as usize) % n_roles;
                        if current.len() > 1 {
                            current.remove(&candidate);
                        }
                    }
                    endpoint_sets.push(current.clone());
                    // sender must be an endpoint of its own step
                    let members: Vec<usize> = current.iter().copied().collect();
                    senders.push(members[sender_picks[i] % members.len()]);
                }
                ChainProtocol {
                    n_roles,
                    senders,
                    endpoint_sets,
                }
            })
    })
}

fn tid() -> ThreadId {
    ThreadId("conv".to_string())
}

fn store_of(msgs: &[(String, Message)], include: &BTreeSet<String>) -> ThreadedMessageStore {
    let mut store = ThreadedMessageStore::new();
    for (h, m) in msgs {
        if include.contains(h) {
            store.append(ContentHash(h.clone()), tid(), m.clone());
        }
    }
    store
}

fn ep(role_idx: usize) -> Endpoint {
    Endpoint {
        role: ROLE_NAMES[role_idx].to_string(),
        occupant: None,
    }
}

proptest! {
    /// Generated chains are R6-clean by construction (generator sanity).
    #[test]
    fn generated_chains_pass_r6(chain in arb_chain()) {
        prop_assert_eq!(r6_violations(&chain.dialect()), Vec::new());
    }

    /// TEST-630: projection determinism (paper Prop. Determinism).
    #[test]
    fn test_630_projection_determinism(chain in arb_chain()) {
        let d = chain.dialect();
        for r in 0..chain.n_roles {
            let a: LocalProtocol = project(&d, &ep(r), None);
            let b: LocalProtocol = project(&d, &ep(r), None);
            prop_assert_eq!(a, b);
        }
    }

    /// TEST-631 (Lean `soundness_safety`): every message of a projected
    /// local run verifies non-Violation against the local store alone.
    #[test]
    fn test_631_epp_soundness(chain in arb_chain()) {
        let d = chain.dialect();
        let cast = chain.cast(&d);
        let msgs = chain.run();
        for r in 0..chain.n_roles {
            let local = chain.local_run(r);
            let store = store_of(&msgs, &local);
            for (h, m) in &msgs {
                if !local.contains(h) { continue; }
                let v = verify_causal_for_role(m, &ep(r), &d, &cast, &store, &tid(), &ContentHash("m-root".to_string()));
                prop_assert!(
                    !matches!(v, VerificationResult::Violation(_)),
                    "role {r}, message {h}: {v:?}"
                );
            }
        }
    }

    /// TEST-632 (Lean `completeness_safety`): the glue of the compatible
    /// family of local runs is safe and causally closed.
    /// TEST-633 (Lean `glue_project_eq`/`project_glue_eq`): glue ∘ project
    /// = id and project ∘ glue = id at the set level.
    #[test]
    fn test_632_633_completeness_and_exactness(chain in arb_chain()) {
        let d = chain.dialect();
        let cast = chain.cast(&d);
        let msgs = chain.run();
        let all: BTreeSet<String> = msgs.iter().map(|(h, _)| h.clone()).collect();

        // glue = union of local runs (dedup by hash)
        let mut glued: BTreeSet<String> = BTreeSet::new();
        for r in 0..chain.n_roles {
            glued.extend(chain.local_run(r));
        }
        // glue ∘ project = id: every message has its sender as an endpoint
        prop_assert_eq!(&glued, &all);

        // safety of the glued store (TEST-632)
        let store = store_of(&msgs, &glued);
        for (h, m) in &msgs {
            let v = verify_causal_for_role(m, &ep(0), &d, &cast, &store, &tid(), &ContentHash("m-root".to_string()));
            prop_assert!(
                !matches!(v, VerificationResult::Violation(_)),
                "glued store, message {h}: {v:?}"
            );
            prop_assert!(
                matches!(v, VerificationResult::Valid),
                "glued store is closed, so every verdict is decided: {h}: {v:?}"
            );
        }

        // project ∘ glue = id: re-projecting the glued set per role gives
        // back exactly the local runs (TEST-633)
        for r in 0..chain.n_roles {
            let reprojected: BTreeSet<String> = glued
                .iter()
                .filter(|h| chain.local_run(r).contains(*h))
                .cloned()
                .collect();
            prop_assert_eq!(reprojected, chain.local_run(r));
        }
    }

    /// TEST-634 (Lean `unknown_means_not_yet_arrived`): in any partial
    /// local store, an Unknown verdict on an r-relevant message names a
    /// missing predecessor that is itself r-relevant.
    #[test]
    fn test_634_unknown_means_not_yet_arrived(chain in arb_chain(), cut in 0usize..8) {
        let d = chain.dialect();
        let cast = chain.cast(&d);
        let msgs = chain.run();
        for r in 0..chain.n_roles {
            let local = chain.local_run(r);
            // partial store: drop a suffix of the local run
            let keep: BTreeSet<String> = local.iter().take(cut.max(1).min(local.len())).cloned().collect();
            let store = store_of(&msgs, &keep);
            for (h, m) in &msgs {
                if !keep.contains(h) { continue; }
                let v = verify_causal_for_role(m, &ep(r), &d, &cast, &store, &tid(), &ContentHash("m-root".to_string()));
                if matches!(v, VerificationResult::Unknown) {
                    // the missing predecessor must be r-relevant (in the
                    // full local run) — never a third-party message
                    let idx: usize = h.trim_start_matches('m').parse().unwrap_or(0);
                    let pred = if idx == 0 { "m-root".to_string() } else { format!("m{}", idx - 1) };
                    prop_assert!(
                        local.contains(&pred),
                        "Unknown at {h} names {pred}, which is not r-relevant for role {r}"
                    );
                    prop_assert!(!keep.contains(&pred), "Unknown but predecessor present");
                }
            }
        }
    }

    /// TEST-636 (Lean `valid_stable`; deployed valid-is-sticky order,
    /// ADR-602): Valid never changes under store growth, and once every
    /// referenced predecessor is present the verdict is permanent.
    #[test]
    fn test_636_monotonicity(chain in arb_chain(), order in proptest::collection::vec(0usize..64, 8)) {
        let d = chain.dialect();
        let cast = chain.cast(&d);
        let msgs = chain.run();

        // full-store verdicts = the permanent reference point
        let all: BTreeSet<String> = msgs.iter().map(|(h, _)| h.clone()).collect();
        let full = store_of(&msgs, &all);
        let final_verdicts: Vec<VerificationResult> = msgs
            .iter()
            .map(|(_, m)| verify_causal_for_role(m, &ep(0), &d, &cast, &full, &tid(), &ContentHash("m-root".to_string())))
            .collect();

        // shuffled insertion order via the random keys
        let mut sequence: Vec<usize> = (0..msgs.len()).collect();
        for (i, k) in order.iter().enumerate() {
            let j = k % msgs.len();
            let i = i % msgs.len();
            sequence.swap(i, j);
        }

        let mut store = ThreadedMessageStore::new();
        let mut seen_valid: Vec<bool> = vec![false; msgs.len()];
        for idx in sequence {
            let (h, m) = &msgs[idx];
            store.append(ContentHash(h.clone()), tid(), m.clone());
            for (j, (_, mj)) in msgs.iter().enumerate() {
                let v = verify_causal_for_role(mj, &ep(0), &d, &cast, &store, &tid(), &ContentHash("m-root".to_string()));
                if seen_valid[j] {
                    prop_assert!(
                        matches!(v, VerificationResult::Valid),
                        "valid-is-sticky violated at message {j}"
                    );
                }
                if matches!(v, VerificationResult::Valid) {
                    seen_valid[j] = true;
                    prop_assert_eq!(&v, &final_verdicts[j]);
                }
            }
        }
        // at the full store every verdict equals the reference verdict
        for (j, (_, mj)) in msgs.iter().enumerate() {
            let v = verify_causal_for_role(mj, &ep(0), &d, &cast, &store, &tid(), &ContentHash("m-root".to_string()));
            prop_assert_eq!(&v, &final_verdicts[j]);
        }
    }
}

/// TEST-637 (NFR-600 operation-count guard): the R6 checker's atomic table
/// lookups stay within `c · |P|² · |R|` over protocols of |P| ∈ {10, 100,
/// 1000}. A falsifiable structural bound — a regression to a worse
/// complexity class (e.g. the O(|P|³) reachability that a prior revision
/// shipped) blows past it — not a wall-clock timing assertion.
#[test]
fn test_637_operation_count_within_bound() {
    /// A hub protocol of `n` chained steps over two roles (`a` sends, `hub`
    /// receives), R6-clean by construction: every step shares endpoints
    /// `{a, hub}`, so causal locality and reachability both hold.
    fn hub_protocol(n: usize) -> Dialect {
        let mut perfs = Vec::new();
        let mut steps: BTreeMap<String, StepDecl> = BTreeMap::new();
        steps.insert(
            "begin".to_string(),
            StepDecl {
                performative: "begin".to_string(),
                predecessors: vec![],
                successors: vec![NodeRef::Single("p0".to_string())],
            },
        );
        for i in 0..n {
            let name = format!("p{i}");
            perfs.push(PerformativeDef {
                name: name.clone(),
                params: Vec::new(),
                template: "t".parse::<SExpr>().unwrap(),
                role: Some(cbcl_core::role::RoleAnnotation {
                    from: "a".to_string(),
                    to: ["hub".to_string()].into_iter().collect(),
                }),
            });
            let pred = if i == 0 {
                "begin".to_string()
            } else {
                format!("p{}", i - 1)
            };
            let succs = if i + 1 < n {
                vec![NodeRef::Single(format!("p{}", i + 1))]
            } else {
                vec![]
            };
            steps.insert(
                name.clone(),
                StepDecl {
                    performative: name,
                    predecessors: vec![NodeRef::Single(pred)],
                    successors: succs,
                },
            );
        }
        Dialect {
            causal_locality: Default::default(),
            roles: parse_roles(&"(a hub)".parse::<SExpr>().unwrap()).unwrap(),
            name: "hub".to_string(),
            extends: Vec::new(),
            author: None,
            performatives: perfs,
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

    // c chosen to admit the true O(|P|·|R|) cost with headroom while still
    // catching any super-quadratic regression (which exceeds it by orders
    // of magnitude at |P| = 1000).
    const C: u64 = 10;
    for n in [10usize, 100, 1000] {
        let d = hub_protocol(n);
        let mut ops = 0u64;
        let violations = r6_violations_counted(&d, &mut ops);
        assert!(violations.is_empty(), "hub protocol must be R6-clean");
        let roles = d.roles.len() as u64;
        let p = (n as u64) + 1; // + begin

        // Lower bound: the check performs a *linear* amount of work over the
        // hub protocol — exactly 3 atomic ops per step (2 causal-locality
        // membership tests + 1 forward-edge relaxation), deterministic. The
        // lower bound is what makes the counter meaningful: a mutation that
        // stops the counter incrementing (e.g. `+= 1` → `*= 1`, which pins
        // it at 0) drops below it and is caught, instead of trivially
        // satisfying an upper bound alone.
        let expected = 3 * (n as u64);
        assert!(
            ops >= expected,
            "|P|={p}: {ops} atomic ops is below the linear floor {expected} \
             — the operation counter is not tracking work"
        );

        // Upper bound (NFR-600): the count stays within c·|P|²·|R|. A
        // regression to a worse complexity class (e.g. the O(|P|³)
        // reachability a prior revision shipped) blows past it.
        let bound = C * p * p * roles;
        assert!(
            ops <= bound,
            "|P|={p}: {ops} atomic ops exceeds {C}·|P|²·|R| = {bound}"
        );
    }
}

/// TEST-635 (Lean `nonlocal_protocol_counterexample`): the straight-line converse
/// witness — x : A → B, y : C → B, protocol (then begin x y). R6 rejects
/// it; bypassing R6, y's verdict at role C is Unknown in every local store
/// C can reach (C never holds x).
#[test]
fn test_635_converse_witness() {
    use cbcl_core::role::R6Violation;

    let d = {
        let mut steps: BTreeMap<String, StepDecl> = BTreeMap::new();
        steps.insert(
            "begin".to_string(),
            StepDecl {
                performative: "begin".to_string(),
                predecessors: vec![],
                successors: vec![NodeRef::Single("x".to_string())],
            },
        );
        steps.insert(
            "x".to_string(),
            StepDecl {
                performative: "x".to_string(),
                predecessors: vec![NodeRef::Single("begin".to_string())],
                successors: vec![NodeRef::Single("y".to_string())],
            },
        );
        steps.insert(
            "y".to_string(),
            StepDecl {
                performative: "y".to_string(),
                predecessors: vec![NodeRef::Single("x".to_string())],
                successors: vec![],
            },
        );
        Dialect {
            causal_locality: Default::default(),
            roles: parse_roles(&"(ra rb rc)".parse::<SExpr>().unwrap()).unwrap(),
            name: "witness".to_string(),
            extends: Vec::new(),
            author: None,
            performatives: vec![
                PerformativeDef {
                    name: "x".to_string(),
                    params: Vec::new(),
                    template: "t".parse::<SExpr>().unwrap(),
                    role: Some(cbcl_core::role::RoleAnnotation {
                        from: "ra".to_string(),
                        to: ["rb".to_string()].into_iter().collect(),
                    }),
                },
                PerformativeDef {
                    name: "y".to_string(),
                    params: Vec::new(),
                    template: "t".parse::<SExpr>().unwrap(),
                    role: Some(cbcl_core::role::RoleAnnotation {
                        from: "rc".to_string(),
                        to: ["rb".to_string()].into_iter().collect(),
                    }),
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
    };

    // R6 rejects: rc is an endpoint of y but not of its predecessor x.
    let violations = r6_violations(&d);
    assert!(violations.contains(&R6Violation::NotCausallyLocal {
        performative: "y".to_string(),
        predecessor: "x".to_string(),
        role: "rc".to_string(),
    }));

    // Bypassing R6: rc's reachable local stores never contain mx (rc is
    // not an endpoint of x), so my stays Unknown in all of them.
    let cast = parse_cast(
        &"((ra @a) (rb @b) (rc @c))".parse::<SExpr>().unwrap(),
        &d.roles,
    )
    .unwrap();
    let root = Message::try_from(
        &"(with-roles ((ra @a) (rb @b) (rc @c)) (signed @a \"sig\" (hello :caused-by begin)))"
            .parse::<SExpr>()
            .unwrap(),
    )
    .unwrap();
    let my = Message::try_from(
        &"(signed @c \"sig\" (lang witness (y @b \"v\" :caused-by mx)))"
            .parse::<SExpr>()
            .unwrap(),
    )
    .unwrap();

    // every store rc can reach: subsets of {root, my}
    for include_root in [false, true] {
        let mut store = ThreadedMessageStore::new();
        if include_root {
            store.append(ContentHash("m-root".to_string()), tid(), root.clone());
        }
        store.append(ContentHash("my".to_string()), tid(), my.clone());
        let v = verify_causal_for_role(
            &my,
            &Endpoint {
                role: "rc".to_string(),
                occupant: None,
            },
            &d,
            &cast,
            &store,
            &tid(),
            &ContentHash("m-root".to_string()),
        );
        assert_eq!(
            v,
            VerificationResult::Unknown,
            "permanently Unknown for want of a third-party message"
        );
    }
}
