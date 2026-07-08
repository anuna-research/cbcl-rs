//! Splice-coherence: a **de-risking prototype** of a candidate relaxation of
//! R6(vi) causal locality (NOT a shipped installation check).
//!
//! R6(vi) (`r6::r6_violations` / `NotCausallyLocal`) demands that every
//! endpoint role of a performative `t` is also an endpoint role of every legal
//! predecessor of `t`: a role must *observe* every message its own messages
//! causally cite. Splice-coherence is the proposed weaker condition under which
//! a role `r` may cite a *bystander* predecessor `b` (one `r` is not an endpoint
//! of) provided the bystander's TYPE is recoverable from the r-relevant messages
//! that bracket it:
//!
//! - (A) INTERVAL TYPE-FORCING — the bystander's performative type is uniquely
//!   determined by the r-relevant messages that causally bracket it (a `Single`
//!   or `All` predecessor edge forces the type; an `(any …)` of ≥2 distinct
//!   bystander types does not);
//! - (B) CHOICE-RECOVERY — an unobserved `(any …)` chooser among bystanders is
//!   admissible iff either (a) it is r-invariant (MERGE: every branch reaches the
//!   same r-relevant continuation) or (b) it is hash-pinned (each branch is the
//!   unique `Single` predecessor of a distinct r-relevant message, so whichever
//!   branch is taken, `r` holds an r-relevant message that type-forces it).
//!
//! This module is a faithful, static encoding of that *candidate* definition so
//! the de-risking study can run it over the real corpus. It quantifies over the
//! dialect's roles and causal protocol only (a pure function of the same data
//! `r6_violations` reads), and is decidable: a backward DAG walk over finitely
//! many bystander intervals (see `splice_coherence_violations`' complexity note).
//!
//! IMPORTANT (soundness caveat, documented for the de-risking verdict): the
//! *structural* coherence computed here is NOT the same as local verifiability
//! in the mechanised semantics. `protocol::predecessor_type` resolves a
//! `:caused-by` hash only from a held full message or a held (type-tagged)
//! envelope; a bare content-hash is type-opaque, so
//! `Projectability.permanently_unknown_of_nonlocal_pred` proves an r-relevant
//! message with an unheld predecessor is *permanently* `Unknown`. A `Single`
//! edge marked "type-forced" here does not let `r` itself decide the referent's
//! type. The tests below exhibit a protocol this structural check ACCEPTS that
//! has no correct projection — the evidence behind the study's verdict.

#![forbid(unsafe_code)]

use crate::dialect::Dialect;
use crate::protocol::{repeat_base_name, NodeRef, BEGIN_KEYWORD};
use crate::role::RoleAnnotation;
use alloc::collections::{BTreeMap, BTreeSet};
use alloc::string::String;
use alloc::vec::Vec;

/// Endpoint roles of an annotated performative: sender ∪ recipients.
fn endpoints(ann: &RoleAnnotation) -> BTreeSet<&str> {
    let mut set: BTreeSet<&str> = ann.to.iter().map(String::as_str).collect();
    set.insert(ann.from.as_str());
    set
}

/// Why a spliced citation onto a role is not coherent.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SpliceReason {
    /// (A) failed and neither (B)(a) MERGE nor (B)(b) HASH-PIN rescued it: an
    /// unobserved `(any …)` chooser among ≥2 distinct-typed bystanders whose
    /// branch `r` cannot recover.
    UnrecoverableChoice,
}

/// A failure of splice-coherence onto one role: the r-relevant message `m`
/// whose `:caused-by` reaches a bystander whose type `r` cannot recover.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SpliceFailure {
    pub role: String,
    /// The r-relevant message whose spliced citation cannot be verified.
    pub message: String,
    /// The bystander predecessor (the `(any …)` chooser) that breaks forcing.
    pub bystander: String,
    pub reason: SpliceReason,
}

/// How a spliced-citation edge onto `r` is discharged (for the study table).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Discharge {
    /// (A): a `Single`/`All` edge — the bystander's type is forced.
    TypeForced,
    /// (B)(a): an unobserved choice whose branches reach the same r-relevant
    /// continuation.
    Merge,
    /// (B)(b): an unobserved choice each of whose branches is the unique
    /// `Single` predecessor of a distinct r-relevant message.
    HashPinned,
}

/// One discharged spliced-citation edge (for reporting which disjunct fired).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DischargedEdge {
    pub role: String,
    pub message: String,
    pub bystander: String,
    pub how: Discharge,
}

struct Analyzer<'d> {
    ann: BTreeMap<&'d str, &'d RoleAnnotation>,
    /// name -> its predecessor node-refs.
    preds: BTreeMap<&'d str, &'d [NodeRef]>,
    /// forward edges a -> {b : a is a legal predecessor of b}.
    forward: BTreeMap<&'d str, BTreeSet<&'d str>>,
}

impl<'d> Analyzer<'d> {
    fn new(d: &'d Dialect) -> Option<Self> {
        let cp = d.causal_protocol.as_ref()?;
        let ann: BTreeMap<&str, &RoleAnnotation> = d
            .performatives
            .iter()
            .filter_map(|p| p.role.as_ref().map(|a| (p.name.as_str(), a)))
            .collect();
        let mut preds: BTreeMap<&str, &[NodeRef]> = BTreeMap::new();
        let mut forward: BTreeMap<&str, BTreeSet<&str>> = BTreeMap::new();
        for step in cp.steps.values() {
            preds.insert(step.performative.as_str(), step.predecessors.as_slice());
            for nr in &step.predecessors {
                for p in nr.performatives() {
                    forward
                        .entry(p)
                        .or_default()
                        .insert(step.performative.as_str());
                }
            }
            for nr in &step.successors {
                for s in nr.performatives() {
                    forward
                        .entry(step.performative.as_str())
                        .or_default()
                        .insert(s);
                }
            }
        }
        Some(Self {
            ann,
            preds,
            forward,
        })
    }

    fn endpoints_of(&self, name: &str) -> Option<BTreeSet<&'d str>> {
        self.ann.get(repeat_base_name(name)).map(|a| endpoints(a))
    }

    /// r-relevance: `r` is an endpoint of `name` (root convention: `begin`
    /// counts every role — it is a universal bracket).
    fn relevant(&self, name: &str, r: &str) -> bool {
        if name == BEGIN_KEYWORD {
            return true;
        }
        self.endpoints_of(name)
            .is_some_and(|e| e.contains(r))
    }

    /// r-relevant steps forward-reachable from `from` (its onward closure).
    fn forward_relevant(&self, from: &str, r: &str) -> BTreeSet<String> {
        let mut seen: BTreeSet<&str> = BTreeSet::new();
        let mut stack = alloc::vec![from];
        let mut out = BTreeSet::new();
        while let Some(n) = stack.pop() {
            if !seen.insert(n) {
                continue;
            }
            if n != from && n != BEGIN_KEYWORD && self.relevant(n, r) {
                out.insert(String::from(n));
            }
            if let Some(succs) = self.forward.get(n) {
                for &s in succs {
                    stack.push(s);
                }
            }
        }
        out
    }

    /// (B)(b): every branch `c` of the choice is the unique `Single`-predecessor
    /// of some *distinct* r-relevant message.
    fn hash_pinned(&self, branches: &BTreeSet<String>, r: &str) -> bool {
        let mut witnesses: BTreeSet<&str> = BTreeSet::new();
        for c in branches {
            // find an r-relevant step whose predecessors are exactly Single(c)
            let mut found = None;
            for (name, prs) in &self.preds {
                if !self.relevant(name, r) || *name == BEGIN_KEYWORD {
                    continue;
                }
                let cites_c_single = prs.len() == 1
                    && matches!(&prs[0], NodeRef::Single(x) if x == c);
                if cites_c_single && witnesses.insert(name) {
                    found = Some(*name);
                    break;
                }
            }
            if found.is_none() {
                return false;
            }
        }
        true
    }

    /// (B)(a): all branches reach the same onward r-relevant continuation.
    fn mergeable(&self, branches: &BTreeSet<String>, r: &str) -> bool {
        let mut it = branches.iter();
        let Some(first) = it.next() else {
            return true;
        };
        let base = self.forward_relevant(first, r);
        it.all(|c| self.forward_relevant(c, r) == base)
    }

    /// Walk backward from a bystander `b` cited by an r-relevant message,
    /// checking every predecessor edge is type-forced (A) or a (B)-recoverable
    /// choice, until every path reaches an r-relevant / `begin` bracket.
    /// Records the discharge of the *first* (immediate) edge into `edges`.
    fn check_bystander(
        &self,
        m: &str,
        b: &'d str,
        r: &str,
        immediate: Discharge,
        edges: &mut Vec<DischargedEdge>,
        failures: &mut Vec<SpliceFailure>,
    ) {
        edges.push(DischargedEdge {
            role: String::from(r),
            message: String::from(m),
            bystander: String::from(b),
            how: immediate,
        });
        let mut visited: BTreeSet<&str> = BTreeSet::new();
        let mut stack: Vec<&str> = alloc::vec![b];
        while let Some(node) = stack.pop() {
            if !visited.insert(node) {
                continue;
            }
            let Some(prs) = self.preds.get(node) else {
                continue;
            };
            for nr in *prs {
                match nr {
                    NodeRef::Single(_) | NodeRef::All(_) => {
                        // type-forced edge: descend into any bystander members
                        for p in nr.performatives() {
                            if p != BEGIN_KEYWORD && !self.relevant(p, r) {
                                stack.push(p);
                            }
                        }
                    }
                    NodeRef::Any(set) => {
                        // an (any …) among this node's predecessors
                        let bystander_branches: BTreeSet<String> = set
                            .iter()
                            .filter(|x| x.as_str() != BEGIN_KEYWORD && !self.relevant(x, r))
                            .cloned()
                            .collect();
                        if bystander_branches.len() < 2 {
                            // ≤1 distinct bystander type: forced. Descend using
                            // the &'d names from the node-ref itself.
                            for p in nr.performatives() {
                                if p != BEGIN_KEYWORD && !self.relevant(p, r) {
                                    stack.push(p);
                                }
                            }
                            continue;
                        }
                        // unobserved choice among ≥2 distinct-typed bystanders
                        let ok = self.mergeable(&bystander_branches, r)
                            || self.hash_pinned(&bystander_branches, r);
                        if !ok {
                            failures.push(SpliceFailure {
                                role: String::from(r),
                                message: String::from(m),
                                bystander: String::from(node),
                                reason: SpliceReason::UnrecoverableChoice,
                            });
                        }
                        // do not descend past an (unresolved) choice
                    }
                }
            }
        }
    }
}

/// Compute splice-coherence over a dialect: the failures, and (for the study
/// table) the discharged edges showing which disjunct carried each splice.
///
/// Pure static function over `d.roles` and `d.causal_protocol`. Decidable in
/// `O(|R| · |P|² )`: for each of `|R|` roles and each r-relevant step, a
/// backward walk touches each of `|P|` steps once, and each `(any …)` recovery
/// test scans the `|P|` steps.
pub fn analyze(d: &Dialect) -> (Vec<SpliceFailure>, Vec<DischargedEdge>) {
    let mut failures = Vec::new();
    let mut edges = Vec::new();
    let Some(a) = Analyzer::new(d) else {
        return (failures, edges);
    };
    if d.roles.is_empty() {
        return (failures, edges);
    }
    for role in &d.roles {
        let r = role.name.as_str();
        for (m, prs) in &a.preds {
            if *m == BEGIN_KEYWORD || !a.relevant(m, r) {
                continue;
            }
            for nr in *prs {
                let (members, forced): (Vec<&str>, bool) = match nr {
                    NodeRef::Single(_) | NodeRef::All(_) => {
                        (nr.performatives().collect(), true)
                    }
                    NodeRef::Any(set) => {
                        let bys: Vec<&str> = set
                            .iter()
                            .map(String::as_str)
                            .filter(|x| *x != BEGIN_KEYWORD && !a.relevant(x, r))
                            .collect();
                        (nr.performatives().collect(), bys.len() < 2)
                    }
                };
                if forced {
                    for pred in members {
                        if pred == BEGIN_KEYWORD || a.relevant(pred, r) {
                            continue; // observed / root bracket: no splice
                        }
                        // bystander cited by an (A) type-forced edge.
                        a.check_bystander(
                            m,
                            pred,
                            r,
                            Discharge::TypeForced,
                            &mut edges,
                            &mut failures,
                        );
                    }
                } else {
                    // m's own predecessor is an unobserved choice
                    let NodeRef::Any(set) = nr else { unreachable!() };
                    let branches: BTreeSet<String> = set
                        .iter()
                        .filter(|x| x.as_str() != BEGIN_KEYWORD && !a.relevant(x, r))
                        .cloned()
                        .collect();
                    if a.mergeable(&branches, r) {
                        record_choice(&a, m, &branches, r, Discharge::Merge, &mut edges);
                    } else if a.hash_pinned(&branches, r) {
                        record_choice(&a, m, &branches, r, Discharge::HashPinned, &mut edges);
                    } else {
                        for b in &branches {
                            failures.push(SpliceFailure {
                                role: String::from(r),
                                message: String::from(*m),
                                bystander: b.clone(),
                                reason: SpliceReason::UnrecoverableChoice,
                            });
                        }
                    }
                }
            }
        }
    }
    (failures, edges)
}

fn record_choice(
    _a: &Analyzer,
    m: &str,
    branches: &BTreeSet<String>,
    r: &str,
    how: Discharge,
    edges: &mut Vec<DischargedEdge>,
) {
    for b in branches {
        edges.push(DischargedEdge {
            role: String::from(r),
            message: String::from(m),
            bystander: b.clone(),
            how,
        });
    }
}

/// Splice-coherence failures over the whole dialect (empty ⇒ splice-coherent).
pub fn splice_coherence_violations(d: &Dialect) -> Vec<SpliceFailure> {
    analyze(d).0
}

/// Roles onto which the dialect is NOT splice-coherent.
pub fn non_coherent_roles(d: &Dialect) -> BTreeSet<String> {
    splice_coherence_violations(d)
        .into_iter()
        .map(|f| f.role)
        .collect()
}

/// Whether the dialect is splice-coherent onto every declared role.
pub fn is_splice_coherent(d: &Dialect) -> bool {
    splice_coherence_violations(d).is_empty()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dialect::{Dialect, PerformativeDef, ResourceBounds};
    use crate::protocol::{CausalProtocol, StepDecl};
    use crate::r6::r6_violations;
    use crate::role::{RoleCardinality, RoleDecl};
    use crate::sexpr::{Atom, SExpr};
    use alloc::string::ToString;
    use alloc::vec;

    const S: RoleCardinality = RoleCardinality::Singleton;

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
    fn single(n: &str) -> NodeRef {
        NodeRef::Single(n.to_string())
    }
    fn any(ns: &[&str]) -> NodeRef {
        NodeRef::Any(ns.iter().map(|s| s.to_string()).collect())
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
            causal_locality: Default::default(),
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

    /// OAuth as written (fails R6(vi)); §6.1.
    fn oauth() -> Dialect {
        dialect(
            &[("server", S), ("client", S), ("authoriser", S)],
            vec![
                perf("login", "server", &["client"]),
                perf("abort", "server", &["client"]),
                perf("passwd", "client", &["authoriser"]),
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

    #[test]
    fn oauth_is_splice_coherent_but_not_causally_local() {
        let d = oauth();
        // NOT causally local: R6(vi) fires (the paper's three hand-offs).
        assert!(!r6_violations(&d).is_empty());
        // Splice-coherent onto every role (via (A) type-forcing).
        let (failures, edges) = analyze(&d);
        assert_eq!(failures, Vec::new(), "OAuth must be splice-coherent");
        // The load-bearing splice is authoriser citing the bystander `login`
        // through passwd — discharged by TypeForced, NOT the (B)(b) hash-pin
        // disjunct the informal prediction credited.
        assert!(edges.iter().any(|e| e.role == "authoriser"
            && e.message == "passwd"
            && e.bystander == "login"
            && e.how == Discharge::TypeForced));
        // And there is genuinely a bystander citation (beyond R6(vi)).
        assert!(edges.iter().any(|e| e.role == "authoriser"));
    }

    /// (B)(b) HASH-PIN exerciser: `report`'s predecessor is an unobserved
    /// choice `(any hi lo)` of distinct bystander types; each branch is the
    /// unique Single-predecessor of a distinct w-relevant message
    /// (`seehi`/`seelo`), so (B)(b) fires and merge does NOT.
    fn hashpin() -> Dialect {
        dialect(
            &[("a", S), ("b", S), ("w", S)],
            vec![
                perf("hi", "a", &["b"]),
                perf("lo", "a", &["b"]),
                perf("seehi", "b", &["w"]),
                perf("seelo", "b", &["w"]),
                perf("report", "b", &["w"]),
            ],
            vec![
                step("begin", vec![], vec![any(&["hi", "lo"])]),
                step("hi", vec![single("begin")], vec![any(&["seehi", "report"])]),
                step("lo", vec![single("begin")], vec![any(&["seelo", "report"])]),
                step("seehi", vec![single("hi")], vec![]),
                step("seelo", vec![single("lo")], vec![]),
                step("report", vec![any(&["hi", "lo"])], vec![]),
            ],
        )
    }

    #[test]
    fn hashpin_choice_is_discharged_by_disjunct_b() {
        let d = hashpin();
        let (failures, edges) = analyze(&d);
        assert_eq!(failures, Vec::new(), "hash-pin dialect must be coherent");
        // report's (any hi lo) predecessor onto w is discharged by HashPinned,
        // not Merge (the branches reach distinct r-relevant seehi/seelo).
        assert!(edges.iter().any(|e| e.role == "w"
            && e.message == "report"
            && e.how == Discharge::HashPinned));
        assert!(!edges
            .iter()
            .any(|e| e.role == "w" && e.message == "report" && e.how == Discharge::Merge));
    }

    /// (B)(a) MERGE exerciser: the choice's branches reach the SAME r-relevant
    /// continuation, so `report`'s unobserved choice merges.
    fn mergecase() -> Dialect {
        dialect(
            &[("a", S), ("b", S), ("w", S)],
            vec![
                perf("hi", "a", &["b"]),
                perf("lo", "a", &["b"]),
                perf("report", "b", &["w"]),
            ],
            vec![
                step("begin", vec![], vec![any(&["hi", "lo"])]),
                step("hi", vec![single("begin")], vec![single("report")]),
                step("lo", vec![single("begin")], vec![single("report")]),
                step("report", vec![any(&["hi", "lo"])], vec![]),
            ],
        )
    }

    #[test]
    fn merge_choice_is_discharged_by_disjunct_a() {
        let d = mergecase();
        let (failures, edges) = analyze(&d);
        assert_eq!(failures, Vec::new());
        assert!(edges
            .iter()
            .any(|e| e.role == "w" && e.message == "report" && e.how == Discharge::Merge));
    }

    /// UNRECOVERABLE: `mark`'s predecessor is the unobserved choice `(any hi
    /// lo)`. The branches are NOT mergeable (only the `hi` branch reaches the
    /// w-relevant `gh`) and NOT hash-pinned (no branch is the *unique Single*
    /// predecessor of a distinct w-relevant message — `gh` cites `hi` only
    /// inside an `(any …)`). So neither (B)(a) nor (B)(b) rescues it: rejected.
    #[test]
    fn unmergeable_unpinned_choice_is_rejected() {
        let d = dialect(
            &[("a", S), ("b", S), ("w", S)],
            vec![
                perf("hi", "a", &["b"]),
                perf("lo", "a", &["b"]),
                perf("extra", "a", &["b"]),
                perf("gh", "b", &["w"]),
                perf("mark", "b", &["w"]),
            ],
            vec![
                step("begin", vec![], vec![any(&["hi", "lo", "extra"])]),
                step("hi", vec![single("begin")], vec![]),
                step("lo", vec![single("begin")], vec![]),
                step("extra", vec![single("begin")], vec![]),
                // gh reachable from hi (and extra) via an (any …), never a
                // Single — so it distinguishes the hi branch without pinning it.
                step("gh", vec![any(&["hi", "extra"])], vec![]),
                step("mark", vec![any(&["hi", "lo"])], vec![]),
            ],
        );
        let (failures, _) = analyze(&d);
        assert!(
            failures.iter().any(|f| f.message == "mark"
                && f.reason == SpliceReason::UnrecoverableChoice),
            "mark's unmergeable, unpinned choice must fail splice-coherence for w"
        );
    }

    /// THE SOUNDNESS WITNESS (de-risking evidence): this protocol is ACCEPTED
    /// by the structural splice check yet has NO correct projection. Role `w`
    /// must SEND a branch-dependent performative (`donehi` vs `donelo`) whose
    /// only causal witness is a bare content-hash inside `ack` — which is
    /// type-opaque, so `w` cannot decide which to send. R6(vi) correctly
    /// REJECTS it; structural splice-coherence wrongly ACCEPTS it.
    #[test]
    fn structural_coherence_accepts_an_unimplementable_protocol() {
        // donehi/donelo cite `hi`/`lo` via Single edges — each "type-forced".
        let d = dialect(
            &[("a", S), ("b", S), ("w", S), ("z", S)],
            vec![
                perf("hi", "a", &["b"]),
                perf("lo", "a", &["b"]),
                perf("ack", "b", &["w"]),
                perf("donehi", "w", &["z"]),
                perf("donelo", "w", &["z"]),
            ],
            vec![
                step("begin", vec![], vec![any(&["hi", "lo"])]),
                step("hi", vec![single("begin")], vec![single("ack")]),
                step("lo", vec![single("begin")], vec![single("ack")]),
                // ack: same label both branches, predecessor is the merge point.
                step("ack", vec![any(&["hi", "lo"])], vec![any(&["donehi", "donelo"])]),
                // w's SENDS cite hi/lo by Single edges — structurally forced…
                step("donehi", vec![single("hi")], vec![]),
                step("donelo", vec![single("lo")], vec![]),
            ],
        );
        // R6(vi) rejects (w is endpoint of donehi but not of its predecessor hi).
        assert!(r6_violations(&d).iter().any(|v| matches!(
            v,
            crate::role::R6Violation::NotCausallyLocal { performative, role, .. }
                if performative == "donehi" && role == "w"
        )));
        // ack's own predecessor (any hi lo) merges for w (both branches reach
        // the same onward r-relevant closure {donehi,donelo} from w's view are
        // distinct — so NOT merge). The donehi/donelo Single citations are
        // marked TypeForced. Net: the structural check finds w splice-coherent
        // on the SEND citations, exposing the unsoundness.
        let (failures, edges) = analyze(&d);
        let sends_forced = edges.iter().any(|e| {
            e.role == "w" && e.message == "donehi" && e.how == Discharge::TypeForced
        });
        assert!(
            sends_forced,
            "structural check marks w's branch-dependent SEND citation type-forced"
        );
        // Document (not assert green/red beyond the send edge) that the send
        // citations themselves raise no failure — the unsoundness.
        assert!(
            !failures.iter().any(|f| f.message == "donehi"),
            "structural splice-coherence raises no failure on w's unimplementable SEND"
        );
    }
}
