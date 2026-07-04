//! R6: role well-formedness — the dialect-level installation check
//! (SPEC-014 REQ-601..607, CON-603).
//!
//! Mirrors the `r5.rs` entry-point pattern: [`r6_violations`] returns every
//! violation found; an empty result means the dialect passes R6. Roles are
//! opt-in (REQ-607): a dialect with no `:roles` and no `:from`/`:to`
//! annotations passes trivially.
//!
//! Clause map (paper Def. R6 → this module):
//! - (i) role-completeness → REQ-601 [`R6Violation::MissingFromTo`]
//! - (ii) chooser coherence → REQ-603 [`R6Violation::ChooserIncoherent`]
//! - (iii) projectability — subsumed by (vi) in v1's raw-edge regime (ADR-605)
//! - (iv) role reachability → REQ-605 [`R6Violation::UnreachableRole`]
//! - (v) cardinality-resolved choice — trivially satisfied at dialect level
//!   in v1 (the only cardinalities are singleton and indexed); the runtime
//!   half is the cast binding (REQ-606/612)
//! - (vi) causal locality → REQ-604 [`R6Violation::NotCausallyLocal`], with
//!   the root convention: `begin` counts every declared role among its
//!   endpoint roles (ADR-603)
//!
//! The per-occupant (cast-instantiated) half of clause (vi) for indexed
//! roles is [`r6_instantiated_violations`]'s job (REQ-608), run at thread
//! open, not at installation.

#![forbid(unsafe_code)]

use crate::dialect::Dialect;
use crate::protocol::{repeat_base_name, CausalProtocol, NodeRef, BEGIN_KEYWORD};
use crate::role::{R6Violation, RoleAnnotation};
use alloc::collections::{BTreeMap, BTreeSet};
use alloc::string::String;
use alloc::vec::Vec;

/// The endpoint roles of an annotated performative: its sender plus every
/// member of its recipient set.
fn endpoints(ann: &RoleAnnotation) -> BTreeSet<&str> {
    let mut set: BTreeSet<&str> = ann.to.iter().map(String::as_str).collect();
    set.insert(ann.from.as_str());
    set
}

/// Flatten a `NodeRef` into the performative names it mentions.
fn node_ref_names(nr: &NodeRef) -> Vec<&str> {
    nr.performatives().collect()
}

fn push_unique(violations: &mut Vec<R6Violation>, v: R6Violation) {
    if !violations.contains(&v) {
        violations.push(v);
    }
}

/// Dialect-level R6 check (SPEC-014 REQ-601..605, 607).
///
/// Runs in O(|P|² · |R|): every clause quantifies over at most pairs of
/// performatives (the declared predecessor relation) and the role set, and
/// each atomic check is a lookup in the dialect's finite tables (NFR-600).
pub fn r6_violations(d: &Dialect) -> Vec<R6Violation> {
    let mut ops = 0u64;
    r6_violations_counted(d, &mut ops)
}

/// As [`r6_violations`], additionally tallying into `ops` the atomic table
/// lookups performed in the two load-bearing nested loops (causal locality
/// and reachability), which dominate the O(|P|² · |R|) budget. Used by the
/// NFR-600 operation-count guard (TEST-637) to catch an accidental
/// regression to a worse complexity class — there is one code path, so the
/// count cannot drift from what production runs.
#[doc(hidden)]
pub fn r6_violations_counted(d: &Dialect, ops: &mut u64) -> Vec<R6Violation> {
    let mut violations: Vec<R6Violation> = Vec::new();

    // Annotation table: performative name → annotation.
    let annotations: BTreeMap<&str, &RoleAnnotation> = d
        .performatives
        .iter()
        .filter_map(|p| p.role.as_ref().map(|ann| (p.name.as_str(), ann)))
        .collect();

    // REQ-607 opt-in / REQ-602 stray annotations: no :roles declared.
    if d.roles.is_empty() {
        for p in &d.performatives {
            if p.role.is_some() {
                push_unique(
                    &mut violations,
                    R6Violation::StrayAnnotation {
                        performative: p.name.clone(),
                    },
                );
            }
        }
        return violations;
    }

    let declared: BTreeSet<&str> = d.roles.iter().map(|r| r.name.as_str()).collect();

    // REQ-602: undeclared roles in annotations.
    for p in &d.performatives {
        if let Some(ann) = &p.role {
            if !declared.contains(ann.from.as_str()) {
                push_unique(
                    &mut violations,
                    R6Violation::UndeclaredRole {
                        performative: p.name.clone(),
                        role: ann.from.clone(),
                    },
                );
            }
            for r in &ann.to {
                if !declared.contains(r.as_str()) {
                    push_unique(
                        &mut violations,
                        R6Violation::UndeclaredRole {
                            performative: p.name.clone(),
                            role: r.clone(),
                        },
                    );
                }
            }
        }
    }

    let Some(cp) = &d.causal_protocol else {
        // No protocol: nothing is reachable from begin, so every declared
        // role fails reachability (fail closed, REQ-605).
        for role in &d.roles {
            push_unique(
                &mut violations,
                R6Violation::UnreachableRole {
                    role: role.name.clone(),
                },
            );
        }
        return violations;
    };

    // REQ-601 role-completeness: every protocol performative (begin
    // excepted) carries an annotation. A `(repeat k …)` copy such as
    // `x#2` inherits the base performative's annotation (SPEC-015
    // REQ-704), so the lookup — and the reported name, deduplicated
    // across copies — is the base name.
    for name in cp.steps.keys() {
        if name == BEGIN_KEYWORD {
            continue;
        }
        let base = repeat_base_name(name);
        if !annotations.contains_key(base) {
            push_unique(
                &mut violations,
                R6Violation::MissingFromTo {
                    performative: String::from(base),
                },
            );
        }
    }

    // Sender of a performative, if annotated; `begin` has no sender.
    // Copy names resolve to the base annotation (per-copy inheritance),
    // so chooser coherence holds per copy exactly when it holds for the
    // base alternatives.
    let sender = |name: &str| -> Option<&str> {
        annotations
            .get(repeat_base_name(name))
            .map(|ann| ann.from.as_str())
    };

    // REQ-603 chooser coherence, over every disjunctive alternative set:
    // (a) every `(any …)` member set, wherever it appears; (b) a step's
    // top-level predecessor entries when it offers more than one
    // alternative.
    let mut check_choice = |members: Vec<&str>| {
        let named: Vec<&str> = members
            .into_iter()
            .filter(|m| *m != BEGIN_KEYWORD)
            .collect();
        if named.len() < 2 {
            return;
        }
        let senders: BTreeSet<&str> = named.iter().filter_map(|m| sender(m)).collect();
        // Unannotated members are REQ-601's finding; only judge coherence
        // when at least two annotated members disagree.
        if senders.len() > 1 {
            push_unique(
                &mut violations,
                R6Violation::ChooserIncoherent {
                    members: named.iter().map(|m| String::from(*m)).collect(),
                },
            );
        }
    };

    for step in cp.steps.values() {
        for nr in step.predecessors.iter().chain(step.successors.iter()) {
            if let NodeRef::Any(set) = nr {
                check_choice(set.iter().map(String::as_str).collect());
            }
        }
        // Multi-entry predecessor lists are alternatives too (the deployed
        // verifier treats [Single(a), Single(b)] as a ∨ b). Threshold at the
        // meaningful boundary (≥ 2 entries) so an off-by-one mutation is
        // observable to the two-entry coherence test.
        if step.predecessors.len() >= 2 {
            let mut alts: Vec<&str> = Vec::new();
            for nr in &step.predecessors {
                alts.extend(node_ref_names(nr));
            }
            check_choice(alts);
        }
    }

    // REQ-604 causal locality (type level, root convention): every endpoint
    // role of t is an endpoint role of each predecessor type of t; `begin`
    // counts every declared role among its endpoints.
    for step in cp.steps.values() {
        if step.performative == BEGIN_KEYWORD {
            continue;
        }
        let Some(t_ann) = annotations.get(repeat_base_name(&step.performative)) else {
            continue; // REQ-601 already flagged
        };
        let t_endpoints = endpoints(t_ann);
        for nr in &step.predecessors {
            for pred in node_ref_names(nr) {
                if pred == BEGIN_KEYWORD {
                    continue; // root convention: begin covers every role
                }
                let Some(p_ann) = annotations.get(repeat_base_name(pred)) else {
                    continue; // REQ-601 already flagged
                };
                let p_endpoints = endpoints(p_ann);
                for role in &t_endpoints {
                    *ops += 1; // atomic causal-locality membership test
                    if !p_endpoints.contains(role) {
                        push_unique(
                            &mut violations,
                            R6Violation::NotCausallyLocal {
                                performative: step.performative.clone(),
                                predecessor: String::from(pred),
                                role: String::from(*role),
                            },
                        );
                    }
                }
            }
        }
    }

    // REQ-605 role reachability: every declared role is an endpoint of some
    // performative reachable from begin.
    let reachable = reachable_from_begin(cp, ops);
    for role in &d.roles {
        let covered = reachable.iter().any(|name| {
            *ops += 1; // atomic reachability coverage test
            annotations
                .get(repeat_base_name(name))
                .is_some_and(|ann| endpoints(ann).contains(role.name.as_str()))
        });
        if !covered {
            push_unique(
                &mut violations,
                R6Violation::UnreachableRole {
                    role: role.name.clone(),
                },
            );
        }
    }

    violations
}

/// Cast-instantiated R6(vi): per-occupant causal locality (SPEC-014
/// REQ-608), run once at thread open.
///
/// Evaluates `(performative, occupant)` pairs per ADR-604 without
/// materialising occupant copies. The failure pattern is a reference to a
/// predecessor `p` *sent by the indexed role* that some occupant endpoint
/// of the citing performative `t` never holds:
///
/// - an `(all …)` fan-in names every occupant's `(p, j)`, but occupant `k`
///   observes `(p, j)` for `j ≠ k` only when the indexed role is among
///   `p`'s recipients — otherwise `k` is an endpoint of a message whose
///   predecessor instances it never holds (the auction's
///   `declare-winner :to bidder` naming all reveals);
/// - a `Single`/`Any` reference is per-occupant — instance `(t, k)` cites
///   the sender's own `(p, k)` — so the *sender* is always covered, but a
///   co-occupant *recipient* of `t` is not (BUG-640): with
///   `reveal :to (auctioneer bidder)` and `commit :to auctioneer`,
///   bidder[i] receives reveal_j citing commit_j, which it never holds.
///
/// Pure and deterministic: `BTreeMap`/`BTreeSet` iteration only (NFR-601).
pub fn r6_instantiated_violations(d: &Dialect, cast: &crate::role::Cast) -> Vec<R6Violation> {
    let mut violations: Vec<R6Violation> = Vec::new();
    let annotations: BTreeMap<&str, &RoleAnnotation> = d
        .performatives
        .iter()
        .filter_map(|p| p.role.as_ref().map(|ann| (p.name.as_str(), ann)))
        .collect();
    let Some(cp) = &d.causal_protocol else {
        return violations;
    };

    for role in &d.roles {
        if !matches!(role.cardinality, crate::role::RoleCardinality::Indexed) {
            continue;
        }
        let Some(occupants) = cast.indexed.get(&role.name) else {
            continue; // parse_cast requires totality; nothing to check here
        };
        if occupants.len() < 2 {
            continue; // a lone occupant observes its own instances
        }
        for step in cp.steps.values() {
            let Some(t_ann) = annotations.get(repeat_base_name(&step.performative)) else {
                continue;
            };
            if !endpoints(t_ann).contains(role.name.as_str()) {
                continue;
            }
            for nr in &step.predecessors {
                // An `(all …)` fan-in itself spans occupants, so any
                // occupant endpoint of `t` is exposed. A `Single`/`Any`
                // reference is the sender's own instance — the sender is
                // fine — so only co-occupant *recipients* of `t` can be
                // left citing an instance they never held (BUG-640): with
                // `reveal :to (auctioneer bidder)` and
                // `commit :to auctioneer`, bidder[i] receives reveal_j
                // citing commit_j, which it never holds. Skip the
                // per-occupant instance forms unless the indexed role is
                // among the citing performative's recipients.
                if matches!(nr, NodeRef::Single(_) | NodeRef::Any(_))
                    && !t_ann.to.contains(&role.name)
                {
                    continue;
                }
                for pred in node_ref_names(nr) {
                    let Some(p_ann) = annotations.get(repeat_base_name(pred)) else {
                        continue;
                    };
                    let spanning = p_ann.from == role.name;
                    let observed_by_all = p_ann.to.contains(&role.name);
                    if spanning && !observed_by_all {
                        for k in occupants {
                            push_unique(
                                &mut violations,
                                R6Violation::PerOccupantLocalityFailure {
                                    performative: step.performative.clone(),
                                    occupant: k.0.clone(),
                                },
                            );
                        }
                    }
                }
            }
        }
    }
    violations
}

/// Performatives reachable from `begin`, following either recorded edge
/// direction (protocols may encode successors, predecessors, or both);
/// `begin` itself excluded from the result.
///
/// A worklist BFS over a forward adjacency map built once, so the whole
/// traversal is O(|P| + |edges|) — comfortably within the NFR-600
/// O(|P|²·|R|) budget and free of the fixpoint rescans that risked a worse
/// class. Each edge is relaxed at most once; `ops` tallies those
/// relaxations for the TEST-637 guard.
fn reachable_from_begin(cp: &CausalProtocol, ops: &mut u64) -> BTreeSet<String> {
    // Forward adjacency: an edge a → b whenever b lists a as a predecessor,
    // or a lists b as a successor (both encodings collapse to the same
    // happened-before direction).
    let mut adj: BTreeMap<&str, BTreeSet<&str>> = BTreeMap::new();
    for step in cp.steps.values() {
        let name = step.performative.as_str();
        for nr in &step.successors {
            for succ in nr.performatives() {
                adj.entry(name).or_default().insert(succ);
            }
        }
        for nr in &step.predecessors {
            for pred in nr.performatives() {
                adj.entry(pred).or_default().insert(name);
            }
        }
    }
    let mut reachable: BTreeSet<String> = BTreeSet::new();
    let mut frontier: Vec<&str> = alloc::vec![BEGIN_KEYWORD];
    while let Some(name) = frontier.pop() {
        if let Some(succs) = adj.get(name) {
            for &succ in succs {
                *ops += 1; // one relaxation per edge
                if succ != BEGIN_KEYWORD && reachable.insert(String::from(succ)) {
                    frontier.push(succ);
                }
            }
        }
    }
    reachable
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dialect::{base_dialect, Dialect, PerformativeDef, ResourceBounds};
    use crate::protocol::StepDecl;
    use crate::role::{RoleCardinality, RoleDecl};
    use crate::sexpr::{Atom, SExpr};
    use alloc::string::ToString;
    use alloc::vec;

    fn perf(name: &str, from: &str, to: &[&str]) -> PerformativeDef {
        PerformativeDef {
            name: name.to_string(),
            params: Vec::new(),
            template: SExpr::Atom(Atom::Symbol("t".to_string())),
            role: Some(RoleAnnotation {
                from: from.to_string(),
                to: to.iter().map(|s| s.to_string()).collect(),
            }),
        }
    }

    fn single(name: &str) -> NodeRef {
        NodeRef::Single(name.to_string())
    }

    fn any(names: &[&str]) -> NodeRef {
        NodeRef::Any(names.iter().map(|s| s.to_string()).collect())
    }

    fn step(name: &str, preds: Vec<NodeRef>, succs: Vec<NodeRef>) -> (String, StepDecl) {
        (
            name.to_string(),
            StepDecl {
                performative: name.to_string(),
                predecessors: preds,
                successors: succs,
            },
        )
    }

    fn dialect(
        roles: &[(&str, RoleCardinality)],
        perfs: Vec<PerformativeDef>,
        steps: Vec<(String, StepDecl)>,
    ) -> Dialect {
        Dialect {
            roles: roles
                .iter()
                .map(|(n, c)| RoleDecl {
                    name: n.to_string(),
                    cardinality: *c,
                })
                .collect(),
            name: "test".to_string(),
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
            causal_protocol: Some(CausalProtocol {
                steps: steps.into_iter().collect(),
            }),
            shapes: Vec::new(),
        }
    }

    const S: RoleCardinality = RoleCardinality::Singleton;

    /// The paper's OAuth fragment, as written (fails causal locality) —
    /// begin → (any login abort); login → passwd → auth; abort → quit.
    /// (`cancel` in the paper is renamed `abort` here: `cancel` is a core
    /// performative and R3 rejects its redefinition before R6 ever runs.)
    fn oauth(widened: bool) -> Dialect {
        let (login_to, cancel_to, passwd_to): (&[&str], &[&str], &[&str]) = if widened {
            (
                &["client", "authoriser"],
                &["client", "authoriser"],
                &["authoriser", "server"],
            )
        } else {
            (&["client"], &["client"], &["authoriser"])
        };
        dialect(
            &[("server", S), ("client", S), ("authoriser", S)],
            vec![
                perf("login", "server", login_to),
                perf("abort", "server", cancel_to),
                perf("passwd", "client", passwd_to),
                perf("auth", "authoriser", &["server"]),
                perf("quit", "client", &["authoriser"]),
            ],
            vec![
                step("begin", vec![], vec![any(&["login", "abort"])]),
                step("login", vec![single("begin")], vec![single("passwd")]),
                step("abort", vec![single("begin")], vec![single("quit")]),
                step("passwd", vec![single("login")], vec![single("auth")]),
                step("auth", vec![single("passwd")], vec![]),
                step("quit", vec![single("abort")], vec![]),
            ],
        )
    }

    // ---- REQ-604 / TEST-604: causal locality ----

    #[test]
    fn oauth_as_written_fails_causal_locality() {
        let violations = r6_violations(&oauth(false));
        assert!(violations.contains(&R6Violation::NotCausallyLocal {
            performative: "passwd".to_string(),
            predecessor: "login".to_string(),
            role: "authoriser".to_string(),
        }));
        assert!(violations.contains(&R6Violation::NotCausallyLocal {
            performative: "auth".to_string(),
            predecessor: "passwd".to_string(),
            role: "server".to_string(),
        }));
        assert!(violations.contains(&R6Violation::NotCausallyLocal {
            performative: "quit".to_string(),
            predecessor: "abort".to_string(),
            role: "authoriser".to_string(),
        }));
    }

    #[test]
    fn widened_oauth_passes() {
        assert_eq!(r6_violations(&oauth(true)), Vec::new());
    }

    #[test]
    fn warehouse_fails_causal_locality() {
        // Paper §projection: dispatch (warehouse→shipper) caused by accept
        // (tracking-svc→shipper): warehouse never sees accept.
        let d = dialect(
            &[("shipper", S), ("tracking-svc", S), ("warehouse", S)],
            vec![
                perf("track-shipment", "shipper", &["tracking-svc"]),
                perf("accept", "tracking-svc", &["shipper"]),
                perf("reject", "tracking-svc", &["shipper"]),
                perf("dispatch", "warehouse", &["shipper"]),
            ],
            vec![
                step("begin", vec![], vec![single("track-shipment")]),
                step(
                    "track-shipment",
                    vec![single("begin")],
                    vec![any(&["accept", "reject"])],
                ),
                step(
                    "accept",
                    vec![single("track-shipment")],
                    vec![single("dispatch")],
                ),
                step("reject", vec![single("track-shipment")], vec![]),
                step("dispatch", vec![single("accept")], vec![]),
            ],
        );
        let violations = r6_violations(&d);
        assert!(violations.contains(&R6Violation::NotCausallyLocal {
            performative: "dispatch".to_string(),
            predecessor: "accept".to_string(),
            role: "warehouse".to_string(),
        }));
    }

    #[test]
    fn first_steps_satisfy_locality_via_root_convention() {
        // begin counts every role as endpoint (ADR-603): a first step with
        // any endpoints passes locality against begin.
        let d = dialect(
            &[("a", S), ("b", S)],
            vec![perf("x", "a", &["b"]), perf("y", "b", &["a"])],
            vec![
                step("begin", vec![], vec![single("x")]),
                step("x", vec![single("begin")], vec![single("y")]),
                step("y", vec![single("x")], vec![]),
            ],
        );
        assert_eq!(r6_violations(&d), Vec::new());
    }

    // ---- REQ-603 / TEST-603: chooser coherence ----

    #[test]
    fn incoherent_any_choice_rejected() {
        let d = dialect(
            &[("a", S), ("b", S)],
            vec![perf("x", "a", &["b"]), perf("y", "b", &["a"])],
            vec![
                step("begin", vec![], vec![any(&["x", "y"])]),
                step("x", vec![single("begin")], vec![]),
                step("y", vec![single("begin")], vec![]),
            ],
        );
        assert!(r6_violations(&d)
            .iter()
            .any(|v| matches!(v, R6Violation::ChooserIncoherent { .. })));
    }

    #[test]
    fn three_member_incoherent_choice_rejected() {
        // A choice of *three* alternatives with mixed senders must still be
        // caught — exercises the `named.len() < 2` guard boundary above 2.
        let d = dialect(
            &[("a", S), ("b", S)],
            vec![
                perf("x", "a", &["b"]),
                perf("y", "a", &["b"]),
                perf("z", "b", &["a"]),
            ],
            vec![
                step("begin", vec![], vec![any(&["x", "y", "z"])]),
                step("x", vec![single("begin")], vec![]),
                step("y", vec![single("begin")], vec![]),
                step("z", vec![single("begin")], vec![]),
            ],
        );
        assert!(r6_violations(&d)
            .iter()
            .any(|v| matches!(v, R6Violation::ChooserIncoherent { .. })));
    }

    #[test]
    fn multi_entry_predecessor_alternatives_are_a_choice() {
        // [Single(x), Single(y)] is x ∨ y for the deployed verifier: same
        // coherence obligation as (any x y).
        let d = dialect(
            &[("a", S), ("b", S)],
            vec![
                perf("x", "a", &["b"]),
                perf("y", "b", &["a"]),
                perf("z", "a", &["b"]),
            ],
            vec![
                step("begin", vec![], vec![single("x"), single("y")]),
                step("x", vec![single("begin")], vec![single("z")]),
                step("y", vec![single("begin")], vec![single("z")]),
                step("z", vec![single("x"), single("y")], vec![]),
            ],
        );
        assert!(r6_violations(&d)
            .iter()
            .any(|v| matches!(v, R6Violation::ChooserIncoherent { .. })));
    }

    #[test]
    fn coherent_choice_passes() {
        let d = dialect(
            &[("a", S), ("b", S)],
            vec![perf("x", "a", &["b"]), perf("y", "a", &["b"])],
            vec![
                step("begin", vec![], vec![any(&["x", "y"])]),
                step("x", vec![single("begin")], vec![]),
                step("y", vec![single("begin")], vec![]),
            ],
        );
        assert_eq!(r6_violations(&d), Vec::new());
    }

    // ---- REQ-601 / TEST-601: role-completeness ----

    #[test]
    fn protocol_perf_without_annotation_rejected() {
        let mut unannotated = perf("x", "a", &["b"]);
        unannotated.role = None;
        let d = dialect(
            &[("a", S), ("b", S)],
            vec![unannotated, perf("y", "b", &["a"])],
            vec![
                step("begin", vec![], vec![single("x")]),
                step("x", vec![single("begin")], vec![single("y")]),
                step("y", vec![single("x")], vec![]),
            ],
        );
        assert!(r6_violations(&d).contains(&R6Violation::MissingFromTo {
            performative: "x".to_string()
        }));
    }

    // ---- REQ-602 / TEST-602: undeclared and stray roles ----

    #[test]
    fn undeclared_role_rejected() {
        let d = dialect(
            &[("a", S)],
            vec![perf("x", "a", &["ghost"])],
            vec![
                step("begin", vec![], vec![single("x")]),
                step("x", vec![single("begin")], vec![]),
            ],
        );
        assert!(r6_violations(&d).contains(&R6Violation::UndeclaredRole {
            performative: "x".to_string(),
            role: "ghost".to_string(),
        }));
    }

    #[test]
    fn stray_annotation_without_roles_rejected() {
        let mut d = dialect(&[], vec![perf("x", "a", &["b"])], vec![]);
        d.causal_protocol = None;
        assert_eq!(
            r6_violations(&d),
            vec![R6Violation::StrayAnnotation {
                performative: "x".to_string()
            }]
        );
    }

    // ---- REQ-605 / TEST-605: role reachability ----

    #[test]
    fn unreachable_role_rejected() {
        let d = dialect(
            &[("a", S), ("b", S), ("lurker", S)],
            vec![perf("x", "a", &["b"])],
            vec![
                step("begin", vec![], vec![single("x")]),
                step("x", vec![single("begin")], vec![]),
            ],
        );
        assert!(r6_violations(&d).contains(&R6Violation::UnreachableRole {
            role: "lurker".to_string()
        }));
    }

    #[test]
    fn roles_without_protocol_fail_reachability() {
        let mut d = dialect(&[("a", S)], vec![perf("x", "a", &["a"])], vec![]);
        d.causal_protocol = None;
        assert!(r6_violations(&d).contains(&R6Violation::UnreachableRole {
            role: "a".to_string()
        }));
    }

    // ---- REQ-607 / TEST-607: opt-in ----

    #[test]
    fn role_free_dialect_passes_trivially() {
        assert_eq!(r6_violations(&base_dialect()), Vec::new());
    }

    // ---- REQ-627: installation integration ----

    #[test]
    fn install_rejects_r6_violating_dialect() {
        use crate::dialect::{DialectInstallError, DialectRegistry};
        let mut reg = DialectRegistry::new();
        let d = oauth(false);
        let err = reg.install(d).unwrap_err();
        assert!(
            matches!(err, DialectInstallError::R6Violation { .. }),
            "expected R6Violation, got: {err}"
        );
    }

    #[test]
    fn install_accepts_widened_oauth() {
        use crate::dialect::DialectRegistry;
        let mut reg = DialectRegistry::new();
        if let Err(e) = reg.install(oauth(true)) {
            panic!("expected install to succeed, got: {e}");
        }
    }

    // ---- REQ-608 / TEST-608: cast-instantiated per-occupant locality ----

    fn all_of(names: &[&str]) -> NodeRef {
        NodeRef::All(names.iter().map(|s| s.to_string()).collect())
    }

    /// The SPEC-004 auction: indexed bidder, commit → reveal chains, and a
    /// declare-winner fan-in over all reveals.
    fn auction(winner_to: &[&str], reveal_to: &[&str], commit_to: &[&str]) -> Dialect {
        dialect(
            &[("auctioneer", S), ("bidder", RoleCardinality::Indexed)],
            vec![
                perf("commit", "bidder", commit_to),
                perf("reveal", "bidder", reveal_to),
                perf("declare-winner", "auctioneer", winner_to),
            ],
            vec![
                step("begin", vec![], vec![single("commit")]),
                step("commit", vec![single("begin")], vec![single("reveal")]),
                step("reveal", vec![single("commit")], vec![all_of(&["reveal"])]),
                step("declare-winner", vec![all_of(&["reveal"])], vec![]),
            ],
        )
    }

    fn bidders_cast() -> crate::role::Cast {
        use crate::role::{parse_cast, parse_roles};
        let roles = parse_roles(&"(auctioneer (* bidder))".parse::<SExpr>().unwrap()).unwrap();
        parse_cast(
            &"((auctioneer @auc) (bidder @b1 @b2 @b3))"
                .parse::<SExpr>()
                .unwrap(),
            &roles,
        )
        .unwrap()
    }

    fn two_bidder_cast() -> crate::role::Cast {
        use crate::role::{parse_cast, parse_roles};
        let roles = parse_roles(&"(auctioneer (* bidder))".parse::<SExpr>().unwrap()).unwrap();
        parse_cast(
            &"((auctioneer @auc) (bidder @b1 @b2))"
                .parse::<SExpr>()
                .unwrap(),
            &roles,
        )
        .unwrap()
    }

    #[test]
    fn auction_terminal_declare_winner_passes_both_levels() {
        let d = auction(&[], &["auctioneer"], &["auctioneer"]);
        assert_eq!(r6_violations(&d), Vec::new());
        assert_eq!(r6_instantiated_violations(&d, &bidders_cast()), Vec::new());
    }

    #[test]
    fn per_occupant_locality_fires_at_the_two_occupant_boundary() {
        // The `occupants.len() < 2` guard must admit exactly-two-occupant
        // casts: with two bidders, declare-winner :to bidder still fails
        // per-occupant locality for each.
        let d = auction(&["bidder"], &["auctioneer"], &["auctioneer"]);
        let violations = r6_instantiated_violations(&d, &two_bidder_cast());
        for k in ["@b1", "@b2"] {
            assert!(
                violations.contains(&R6Violation::PerOccupantLocalityFailure {
                    performative: "declare-winner".to_string(),
                    occupant: k.to_string(),
                }),
                "occupant {k} must be flagged at the 2-occupant boundary"
            );
        }
    }

    #[test]
    fn declare_winner_to_bidder_passes_type_level_but_fails_per_occupant() {
        // The paper's exact subtlety: :to bidder passes the dialect-level
        // check (bidder IS an endpoint role of reveal) yet leaves bidder k
        // an endpoint of a message naming bidder j's reveal.
        let d = auction(&["bidder"], &["auctioneer"], &["auctioneer"]);
        assert_eq!(r6_violations(&d), Vec::new());
        let violations = r6_instantiated_violations(&d, &bidders_cast());
        for k in ["@b1", "@b2", "@b3"] {
            assert!(
                violations.contains(&R6Violation::PerOccupantLocalityFailure {
                    performative: "declare-winner".to_string(),
                    occupant: k.to_string(),
                })
            );
        }
    }

    #[test]
    fn reveal_widened_without_commit_fails_per_occupant_locality() {
        // BUG-640 / TEST-641(a): widening reveal alone is *not* a repair —
        // bidder[i] now *receives* reveal_j citing commit_j, which it never
        // holds (commit still :to auctioneer only). Type-level R6 passes;
        // the per-occupant check must flag every bidder occupant.
        let d = auction(&["bidder"], &["auctioneer", "bidder"], &["auctioneer"]);
        assert_eq!(r6_violations(&d), Vec::new());
        let violations = r6_instantiated_violations(&d, &bidders_cast());
        for k in ["@b1", "@b2", "@b3"] {
            assert!(
                violations.contains(&R6Violation::PerOccupantLocalityFailure {
                    performative: "reveal".to_string(),
                    occupant: k.to_string(),
                }),
                "occupant {k} receives a reveal citing a commit it never holds"
            );
        }
    }

    #[test]
    fn full_prefix_widening_repairs_per_occupant_locality() {
        // BUG-640 / TEST-641(b): the actual repair widens the whole
        // commit → reveal prefix — commit and reveal both
        // :to (auctioneer bidder) — so every occupant holds every cited
        // instance. Clean at both the dialect and instantiated level.
        let d = auction(
            &["bidder"],
            &["auctioneer", "bidder"],
            &["auctioneer", "bidder"],
        );
        assert_eq!(r6_violations(&d), Vec::new());
        assert_eq!(r6_instantiated_violations(&d, &bidders_cast()), Vec::new());
    }

    #[test]
    fn lone_occupant_passes_per_occupant_locality() {
        use crate::role::{parse_cast, parse_roles};
        let d = auction(&["bidder"], &["auctioneer"], &["auctioneer"]);
        let roles = parse_roles(&"(auctioneer (* bidder))".parse::<SExpr>().unwrap()).unwrap();
        let cast = parse_cast(
            &"((auctioneer @auc) (bidder @only))"
                .parse::<SExpr>()
                .unwrap(),
            &roles,
        )
        .unwrap();
        assert_eq!(r6_instantiated_violations(&d, &cast), Vec::new());
    }
}
