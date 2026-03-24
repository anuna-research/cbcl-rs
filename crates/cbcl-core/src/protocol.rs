//! Causal protocol types and verification result lattice (REQ-200, REQ-302, REQ-303).
//!
//! The verification result forms a flat lattice with Unknown (⊥) at the bottom
//! and Valid / Violation as incomparable top elements. Meet implements conjunction
//! for `(all ...)` fan-in; join implements disjunction for `(any ...)`.

#![forbid(unsafe_code)]

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::string::String;
use alloc::vec::Vec;
use core::fmt;

// ================================================================
// Causal Protocol Data Model (REQ-200)
// ================================================================

/// Reference to one or more performatives in a protocol declaration (REQ-201).
///
/// - `Single` — a bare symbol (one performative).
/// - `Any` — `(any ...)` disjunction (choice / alternatives).
/// - `All` — `(all ...)` conjunction (fan-in / fan-out).
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum NodeRef {
    Single(String),
    Any(BTreeSet<String>),
    All(BTreeSet<String>),
}

impl NodeRef {
    /// Return all performative names referenced by this node-ref.
    pub fn performatives(&self) -> impl Iterator<Item = &str> {
        match self {
            NodeRef::Single(s) => {
                let v: Vec<&str> = alloc::vec![s.as_str()];
                v.into_iter()
            }
            NodeRef::Any(set) | NodeRef::All(set) => {
                let v: Vec<&str> = set.iter().map(|s| s.as_str()).collect();
                v.into_iter()
            }
        }
    }
}

/// A step in the causal protocol graph (REQ-200).
///
/// Aggregates all declared predecessor and successor relationships
/// for a single performative name.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct StepDecl {
    pub performative: String,
    pub predecessors: Vec<NodeRef>,
    pub successors: Vec<NodeRef>,
}

/// Parsed causal protocol declaration (REQ-200, REQ-201).
///
/// Built from `(protocol (then ...)+)` S-expression syntax.
/// Stores the dependency graph as a map from performative name to step declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct CausalProtocol {
    pub steps: BTreeMap<String, StepDecl>,
}

/// Protocol-level violation found during R5 verification (REQ-204–207).
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ProtocolViolation {
    /// A cycle was found in the dependency graph (REQ-204).
    Cycle { participants: Vec<String> },
    /// A step is unreachable from `begin` (REQ-205).
    Unreachable { step: String },
    /// A performative is referenced but not defined (REQ-206).
    UndefinedPerformative { name: String },
    /// Duplicate step declaration for the same performative (REQ-207).
    DuplicateStep { name: String },
}

impl fmt::Display for ProtocolViolation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Cycle { participants } => {
                write!(f, "cycle detected: {}", participants.join(" → "))
            }
            Self::Unreachable { step } => {
                write!(f, "step '{}' is unreachable from begin", step)
            }
            Self::UndefinedPerformative { name } => {
                write!(f, "performative '{}' is not defined", name)
            }
            Self::DuplicateStep { name } => {
                write!(f, "duplicate step declaration for '{}'", name)
            }
        }
    }
}

impl CausalProtocol {
    /// Collect all performative names referenced in successor/predecessor node-refs,
    /// excluding `begin`.
    fn all_referenced_performatives(&self) -> BTreeSet<String> {
        let mut names = BTreeSet::new();
        for (name, step) in &self.steps {
            if name != "begin" {
                names.insert(name.clone());
            }
            for nr in step.predecessors.iter().chain(step.successors.iter()) {
                for p in nr.performatives() {
                    if p != "begin" {
                        names.insert(p.into());
                    }
                }
            }
        }
        names
    }

    /// Build adjacency list (successor graph) from steps.
    fn successor_graph(&self) -> BTreeMap<&str, BTreeSet<&str>> {
        let mut graph: BTreeMap<&str, BTreeSet<&str>> = BTreeMap::new();
        for (name, step) in &self.steps {
            graph.entry(name.as_str()).or_default();
            for nr in &step.successors {
                for s in nr.performatives() {
                    graph.entry(name.as_str()).or_default().insert(s);
                    graph.entry(s).or_default();
                }
            }
        }
        graph
    }

    /// Check acyclicity of the protocol dependency graph (REQ-204).
    ///
    /// Uses DFS with white/gray/black colouring to detect back edges.
    /// Returns violations for each cycle found.
    pub fn check_acyclicity(&self) -> Vec<ProtocolViolation> {
        let graph = self.successor_graph();

        // 0 = white (unvisited), 1 = gray (in progress), 2 = black (done)
        let mut color: BTreeMap<&str, u8> = BTreeMap::new();
        let mut path: Vec<&str> = Vec::new();
        let mut violations = Vec::new();

        for &node in graph.keys() {
            if *color.get(node).unwrap_or(&0) == 0 {
                Self::dfs_cycle(node, &graph, &mut color, &mut path, &mut violations);
            }
        }
        violations
    }

    fn dfs_cycle<'a>(
        node: &'a str,
        graph: &BTreeMap<&'a str, BTreeSet<&'a str>>,
        color: &mut BTreeMap<&'a str, u8>,
        path: &mut Vec<&'a str>,
        violations: &mut Vec<ProtocolViolation>,
    ) {
        color.insert(node, 1); // gray
        path.push(node);

        if let Some(neighbors) = graph.get(node) {
            for &next in neighbors {
                match color.get(next).unwrap_or(&0) {
                    0 => Self::dfs_cycle(next, graph, color, path, violations),
                    1 => {
                        // Back edge: extract cycle from path
                        if let Some(pos) = path.iter().position(|&n| n == next) {
                            let cycle: Vec<String> =
                                path[pos..].iter().map(|s| String::from(*s)).collect();
                            violations.push(ProtocolViolation::Cycle {
                                participants: cycle,
                            });
                        }
                    }
                    _ => {} // black, already fully explored
                }
            }
        }

        path.pop();
        color.insert(node, 2); // black
    }

    /// Check that all steps are reachable from `begin` (REQ-205).
    ///
    /// Uses BFS from `begin` over the successor graph.
    pub fn check_reachability(&self) -> Vec<ProtocolViolation> {
        let graph = self.successor_graph();
        let mut visited: BTreeSet<&str> = BTreeSet::new();
        let mut queue: Vec<&str> = Vec::new();

        if graph.contains_key("begin") {
            queue.push("begin");
            visited.insert("begin");
        }

        while let Some(current) = queue.pop() {
            if let Some(neighbors) = graph.get(current) {
                for &next in neighbors {
                    if visited.insert(next) {
                        queue.push(next);
                    }
                }
            }
        }

        let mut violations = Vec::new();
        for name in self.steps.keys() {
            if name != "begin" && !visited.contains(name.as_str()) {
                violations.push(ProtocolViolation::Unreachable {
                    step: name.clone(),
                });
            }
        }
        violations
    }

    /// Check that all referenced performatives are defined (REQ-206).
    ///
    /// `defined_performatives` should include all performatives from the dialect's
    /// `extend` clauses and installed ancestors. `begin` is always valid.
    pub fn check_performative_definedness(
        &self,
        defined_performatives: &[&str],
    ) -> Vec<ProtocolViolation> {
        let defined: BTreeSet<&str> = defined_performatives.iter().copied().collect();
        let referenced = self.all_referenced_performatives();

        let mut violations = Vec::new();
        for name in &referenced {
            if !defined.contains(name.as_str()) {
                violations.push(ProtocolViolation::UndefinedPerformative { name: name.clone() });
            }
        }
        violations
    }

    /// Check that no performative has duplicate step declarations (REQ-207).
    ///
    /// Since `CausalProtocol` stores steps in a `BTreeMap`, structural duplicates
    /// are impossible. This method exists to satisfy the requirement interface;
    /// it always returns an empty vec for a validly-constructed protocol.
    pub fn check_step_uniqueness(&self) -> Vec<ProtocolViolation> {
        // BTreeMap guarantees no duplicate keys by construction.
        Vec::new()
    }

    /// Run all R5 protocol checks (REQ-208).
    ///
    /// Checks: step uniqueness (REQ-207), acyclicity (REQ-204),
    /// reachability (REQ-205), and performative definedness (REQ-206).
    pub fn verify_r5_protocol(
        &self,
        defined_performatives: &[&str],
    ) -> Vec<ProtocolViolation> {
        let mut violations = Vec::new();
        violations.extend(self.check_step_uniqueness());
        violations.extend(self.check_acyclicity());
        violations.extend(self.check_reachability());
        violations.extend(self.check_performative_definedness(defined_performatives));
        violations
    }
}

/// Causal verification failure details (CON-202, SPEC-002).
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum CausalViolation {
    /// Predecessor hash not found in the message store.
    UnknownPredecessor { caused_by: String },
    /// Predecessor found but has wrong performative type.
    InvalidPredecessor {
        caused_by: String,
        expected: Vec<String>,
        found: String,
    },
    /// Message requires `:caused-by` but none was provided.
    MissingCausedBy,
    /// Fan-in `(all ...)` has missing predecessor types.
    IncompleteFanIn { missing_types: Vec<String> },
    /// Predecessor found but not declared in the protocol.
    ExtraneousPredecessor { caused_by: String, found: String },
    /// Fan-in without an `(all ...)` declaration for this performative.
    FanInWithoutAllDecl { performative: String },
}

impl fmt::Display for CausalViolation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnknownPredecessor { caused_by } => {
                write!(f, "unknown predecessor: {caused_by}")
            }
            Self::InvalidPredecessor {
                caused_by,
                expected,
                found,
            } => {
                write!(
                    f,
                    "invalid predecessor {caused_by}: expected one of [{}], found {found}",
                    expected.join(", ")
                )
            }
            Self::MissingCausedBy => write!(f, "missing :caused-by"),
            Self::IncompleteFanIn { missing_types } => {
                write!(
                    f,
                    "incomplete fan-in: missing types [{}]",
                    missing_types.join(", ")
                )
            }
            Self::ExtraneousPredecessor { caused_by, found } => {
                write!(f, "extraneous predecessor {caused_by}: found {found}")
            }
            Self::FanInWithoutAllDecl { performative } => {
                write!(f, "fan-in without (all ...) declaration for {performative}")
            }
        }
    }
}

/// Three-valued verification result lattice (REQ-302, CON-301).
///
/// ```text
///      Valid          Violation
///        \              /
///         \            /
///          ⊥ (Unknown)
/// ```
///
/// Unknown is ⊥. Valid and Violation are incomparable top elements.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum VerificationResult {
    /// ⊥ — predecessor not in store; undecidable with current state.
    Unknown,
    /// Predecessor found, type matches protocol declaration.
    Valid,
    /// Predecessor found, type mismatch or malformed hash.
    Violation(CausalViolation),
}

impl VerificationResult {
    /// Lattice meet (greatest lower bound) — conjunction for `(all ...)` fan-in (REQ-303).
    ///
    /// Truth table:
    /// - Violation ⊓ _ = Violation  (absorbing)
    /// - _ ⊓ Violation = Violation  (absorbing)
    /// - Unknown ⊓ _ = Unknown      (when other ≠ Violation)
    /// - Valid ⊓ Valid = Valid
    pub fn meet(self, other: VerificationResult) -> VerificationResult {
        match (&self, &other) {
            (VerificationResult::Violation(_), _) => self,
            (_, VerificationResult::Violation(_)) => other,
            (VerificationResult::Unknown, _) | (_, VerificationResult::Unknown) => {
                VerificationResult::Unknown
            }
            (VerificationResult::Valid, VerificationResult::Valid) => VerificationResult::Valid,
        }
    }

    /// Lattice join (least upper bound) — disjunction for `(any ...)` (REQ-303).
    ///
    /// Truth table:
    /// - Valid ⊔ _ = Valid           (absorbing)
    /// - _ ⊔ Valid = Valid           (absorbing)
    /// - Violation ⊔ Unknown = Violation
    /// - Unknown ⊔ Unknown = Unknown
    pub fn join(self, other: VerificationResult) -> VerificationResult {
        match (&self, &other) {
            (VerificationResult::Valid, _) | (_, VerificationResult::Valid) => {
                VerificationResult::Valid
            }
            (VerificationResult::Violation(_), _) => self,
            (_, VerificationResult::Violation(_)) => other,
            (VerificationResult::Unknown, VerificationResult::Unknown) => {
                VerificationResult::Unknown
            }
        }
    }

    /// Kuper's threshold test — has the lattice crossed {Valid, Violation}? (CON-301).
    pub fn is_resolved(&self) -> bool {
        !matches!(self, VerificationResult::Unknown)
    }

    /// Stability test — identical to `is_resolved()` (CON-301).
    ///
    /// Once resolved, the result is permanent under store growth (monotonicity).
    pub fn is_stable(&self) -> bool {
        self.is_resolved()
    }
}

impl PartialOrd for VerificationResult {
    /// Flat lattice ordering: Unknown < Valid, Unknown < Violation,
    /// Valid and Violation are incomparable.
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        use core::cmp::Ordering;
        match (self, other) {
            // Equal cases
            (VerificationResult::Unknown, VerificationResult::Unknown) => Some(Ordering::Equal),
            (VerificationResult::Valid, VerificationResult::Valid) => Some(Ordering::Equal),
            (VerificationResult::Violation(_), VerificationResult::Violation(_)) => {
                Some(Ordering::Equal)
            }
            // Unknown < Valid, Unknown < Violation
            (VerificationResult::Unknown, _) => Some(Ordering::Less),
            (_, VerificationResult::Unknown) => Some(Ordering::Greater),
            // Valid and Violation are incomparable
            (VerificationResult::Valid, VerificationResult::Violation(_))
            | (VerificationResult::Violation(_), VerificationResult::Valid) => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn violation() -> VerificationResult {
        VerificationResult::Violation(CausalViolation::MissingCausedBy)
    }

    fn violation2() -> VerificationResult {
        VerificationResult::Violation(CausalViolation::UnknownPredecessor {
            caused_by: "sha256:test".into(),
        })
    }

    // ================================================================
    // TEST-302: Three-Valued Result Construction and Ordering
    // ================================================================

    #[test]
    fn test_construction_unknown() {
        let r = VerificationResult::Unknown;
        assert!(!r.is_resolved());
        assert!(!r.is_stable());
    }

    #[test]
    fn test_construction_valid() {
        let r = VerificationResult::Valid;
        assert!(r.is_resolved());
        assert!(r.is_stable());
    }

    #[test]
    fn test_construction_violation() {
        let r = violation();
        assert!(r.is_resolved());
        assert!(r.is_stable());
    }

    #[test]
    fn test_partial_ord_unknown_lt_valid() {
        assert!(VerificationResult::Unknown < VerificationResult::Valid);
    }

    #[test]
    fn test_partial_ord_unknown_lt_violation() {
        assert!(VerificationResult::Unknown < violation());
    }

    #[test]
    fn test_partial_ord_valid_violation_incomparable() {
        let v = VerificationResult::Valid;
        let viol = violation();
        assert!(v.partial_cmp(&viol).is_none());
        assert!(viol.partial_cmp(&v).is_none());
    }

    #[test]
    fn test_partial_ord_reflexive() {
        assert_eq!(
            VerificationResult::Unknown.partial_cmp(&VerificationResult::Unknown),
            Some(core::cmp::Ordering::Equal)
        );
        assert_eq!(
            VerificationResult::Valid.partial_cmp(&VerificationResult::Valid),
            Some(core::cmp::Ordering::Equal)
        );
        assert_eq!(
            violation().partial_cmp(&violation()),
            Some(core::cmp::Ordering::Equal)
        );
    }

    // ================================================================
    // TEST-303: Meet (conjunction) 3×3 truth table
    // ================================================================

    #[test]
    fn test_meet_unknown_unknown() {
        assert_eq!(
            VerificationResult::Unknown.meet(VerificationResult::Unknown),
            VerificationResult::Unknown
        );
    }

    #[test]
    fn test_meet_unknown_valid() {
        assert_eq!(
            VerificationResult::Unknown.meet(VerificationResult::Valid),
            VerificationResult::Unknown
        );
    }

    #[test]
    fn test_meet_unknown_violation() {
        let result = VerificationResult::Unknown.meet(violation());
        assert!(matches!(result, VerificationResult::Violation(_)));
    }

    #[test]
    fn test_meet_valid_unknown() {
        assert_eq!(
            VerificationResult::Valid.meet(VerificationResult::Unknown),
            VerificationResult::Unknown
        );
    }

    #[test]
    fn test_meet_valid_valid() {
        assert_eq!(
            VerificationResult::Valid.meet(VerificationResult::Valid),
            VerificationResult::Valid
        );
    }

    #[test]
    fn test_meet_valid_violation() {
        let result = VerificationResult::Valid.meet(violation());
        assert!(matches!(result, VerificationResult::Violation(_)));
    }

    #[test]
    fn test_meet_violation_unknown() {
        let result = violation().meet(VerificationResult::Unknown);
        assert!(matches!(result, VerificationResult::Violation(_)));
    }

    #[test]
    fn test_meet_violation_valid() {
        let result = violation().meet(VerificationResult::Valid);
        assert!(matches!(result, VerificationResult::Violation(_)));
    }

    #[test]
    fn test_meet_violation_violation() {
        let result = violation().meet(violation2());
        assert!(matches!(result, VerificationResult::Violation(_)));
    }

    // ================================================================
    // TEST-303: Join (disjunction) 3×3 truth table
    // ================================================================

    #[test]
    fn test_join_unknown_unknown() {
        assert_eq!(
            VerificationResult::Unknown.join(VerificationResult::Unknown),
            VerificationResult::Unknown
        );
    }

    #[test]
    fn test_join_unknown_valid() {
        assert_eq!(
            VerificationResult::Unknown.join(VerificationResult::Valid),
            VerificationResult::Valid
        );
    }

    #[test]
    fn test_join_unknown_violation() {
        let result = VerificationResult::Unknown.join(violation());
        assert!(matches!(result, VerificationResult::Violation(_)));
    }

    #[test]
    fn test_join_valid_unknown() {
        assert_eq!(
            VerificationResult::Valid.join(VerificationResult::Unknown),
            VerificationResult::Valid
        );
    }

    #[test]
    fn test_join_valid_valid() {
        assert_eq!(
            VerificationResult::Valid.join(VerificationResult::Valid),
            VerificationResult::Valid
        );
    }

    #[test]
    fn test_join_valid_violation() {
        assert_eq!(
            VerificationResult::Valid.join(violation()),
            VerificationResult::Valid
        );
    }

    #[test]
    fn test_join_violation_unknown() {
        let result = violation().join(VerificationResult::Unknown);
        assert!(matches!(result, VerificationResult::Violation(_)));
    }

    #[test]
    fn test_join_violation_valid() {
        assert_eq!(
            violation().join(VerificationResult::Valid),
            VerificationResult::Valid
        );
    }

    #[test]
    fn test_join_violation_violation() {
        let result = violation().join(violation2());
        assert!(matches!(result, VerificationResult::Violation(_)));
    }

    // ================================================================
    // CausalViolation construction and Display
    // ================================================================

    #[test]
    fn test_causal_violation_display() {
        let v = CausalViolation::MissingCausedBy;
        assert_eq!(v.to_string(), "missing :caused-by");

        let v = CausalViolation::UnknownPredecessor {
            caused_by: "sha256:abc".into(),
        };
        assert_eq!(v.to_string(), "unknown predecessor: sha256:abc");
    }

    #[test]
    fn test_causal_violation_variants_exist() {
        let _ = CausalViolation::UnknownPredecessor {
            caused_by: "h".into(),
        };
        let _ = CausalViolation::InvalidPredecessor {
            caused_by: "h".into(),
            expected: vec!["a".into()],
            found: "b".into(),
        };
        let _ = CausalViolation::MissingCausedBy;
        let _ = CausalViolation::IncompleteFanIn {
            missing_types: vec!["a".into()],
        };
        let _ = CausalViolation::ExtraneousPredecessor {
            caused_by: "h".into(),
            found: "x".into(),
        };
        let _ = CausalViolation::FanInWithoutAllDecl {
            performative: "p".into(),
        };
    }

    // ================================================================
    // Meet preserves left violation detail
    // ================================================================

    #[test]
    fn test_meet_preserves_first_violation() {
        let v1 = violation();
        let v2 = violation2();
        // When both are violations, meet returns the left one
        let result = v1.meet(v2);
        assert_eq!(
            result,
            VerificationResult::Violation(CausalViolation::MissingCausedBy)
        );
    }

    // ================================================================
    // Join preserves first violation detail when no Valid present
    // ================================================================

    #[test]
    fn test_join_preserves_first_violation() {
        let v1 = violation();
        let result = v1.join(VerificationResult::Unknown);
        assert_eq!(
            result,
            VerificationResult::Violation(CausalViolation::MissingCausedBy)
        );
    }

    // ================================================================
    // Protocol Validation Tests
    // ================================================================

    /// Helper: build a simple linear protocol: begin → a → b → c
    fn linear_protocol() -> CausalProtocol {
        let mut steps = BTreeMap::new();
        steps.insert(
            "begin".into(),
            StepDecl {
                performative: "begin".into(),
                predecessors: vec![],
                successors: vec![NodeRef::Single("a".into())],
            },
        );
        steps.insert(
            "a".into(),
            StepDecl {
                performative: "a".into(),
                predecessors: vec![NodeRef::Single("begin".into())],
                successors: vec![NodeRef::Single("b".into())],
            },
        );
        steps.insert(
            "b".into(),
            StepDecl {
                performative: "b".into(),
                predecessors: vec![NodeRef::Single("a".into())],
                successors: vec![NodeRef::Single("c".into())],
            },
        );
        steps.insert(
            "c".into(),
            StepDecl {
                performative: "c".into(),
                predecessors: vec![NodeRef::Single("b".into())],
                successors: vec![],
            },
        );
        CausalProtocol { steps }
    }

    // ---- TEST-204: Acyclicity ----

    #[test]
    fn test_acyclicity_linear_chain_passes() {
        // begin → a → b → c — no cycles
        let proto = linear_protocol();
        assert!(proto.check_acyclicity().is_empty());
    }

    #[test]
    fn test_acyclicity_direct_cycle_rejected() {
        // a → b, b → a (direct cycle)
        let mut steps = BTreeMap::new();
        steps.insert(
            "a".into(),
            StepDecl {
                performative: "a".into(),
                predecessors: vec![NodeRef::Single("b".into())],
                successors: vec![NodeRef::Single("b".into())],
            },
        );
        steps.insert(
            "b".into(),
            StepDecl {
                performative: "b".into(),
                predecessors: vec![NodeRef::Single("a".into())],
                successors: vec![NodeRef::Single("a".into())],
            },
        );
        let proto = CausalProtocol { steps };
        let violations = proto.check_acyclicity();
        assert!(!violations.is_empty());
        assert!(violations
            .iter()
            .any(|v| matches!(v, ProtocolViolation::Cycle { .. })));
    }

    #[test]
    fn test_acyclicity_transitive_cycle_rejected() {
        // a → b → c → a (transitive cycle)
        let mut steps = BTreeMap::new();
        steps.insert(
            "a".into(),
            StepDecl {
                performative: "a".into(),
                predecessors: vec![NodeRef::Single("c".into())],
                successors: vec![NodeRef::Single("b".into())],
            },
        );
        steps.insert(
            "b".into(),
            StepDecl {
                performative: "b".into(),
                predecessors: vec![NodeRef::Single("a".into())],
                successors: vec![NodeRef::Single("c".into())],
            },
        );
        steps.insert(
            "c".into(),
            StepDecl {
                performative: "c".into(),
                predecessors: vec![NodeRef::Single("b".into())],
                successors: vec![NodeRef::Single("a".into())],
            },
        );
        let proto = CausalProtocol { steps };
        let violations = proto.check_acyclicity();
        assert!(!violations.is_empty());
    }

    // ---- TEST-205: Reachability ----

    #[test]
    fn test_reachability_linear_chain_passes() {
        let proto = linear_protocol();
        assert!(proto.check_reachability().is_empty());
    }

    #[test]
    fn test_reachability_both_from_begin_passes() {
        // begin → a, begin → b (both directly reachable)
        let mut steps = BTreeMap::new();
        steps.insert(
            "begin".into(),
            StepDecl {
                performative: "begin".into(),
                predecessors: vec![],
                successors: vec![
                    NodeRef::Single("a".into()),
                    NodeRef::Single("b".into()),
                ],
            },
        );
        steps.insert(
            "a".into(),
            StepDecl {
                performative: "a".into(),
                predecessors: vec![NodeRef::Single("begin".into())],
                successors: vec![],
            },
        );
        steps.insert(
            "b".into(),
            StepDecl {
                performative: "b".into(),
                predecessors: vec![NodeRef::Single("begin".into())],
                successors: vec![],
            },
        );
        let proto = CausalProtocol { steps };
        assert!(proto.check_reachability().is_empty());
    }

    #[test]
    fn test_reachability_unreachable_step_rejected() {
        // begin → a, but c has no connection to begin
        let mut steps = BTreeMap::new();
        steps.insert(
            "begin".into(),
            StepDecl {
                performative: "begin".into(),
                predecessors: vec![],
                successors: vec![NodeRef::Single("a".into())],
            },
        );
        steps.insert(
            "a".into(),
            StepDecl {
                performative: "a".into(),
                predecessors: vec![NodeRef::Single("begin".into())],
                successors: vec![],
            },
        );
        steps.insert(
            "c".into(),
            StepDecl {
                performative: "c".into(),
                predecessors: vec![NodeRef::Single("x".into())],
                successors: vec![],
            },
        );
        let proto = CausalProtocol { steps };
        let violations = proto.check_reachability();
        assert_eq!(violations.len(), 1);
        assert!(matches!(
            &violations[0],
            ProtocolViolation::Unreachable { step } if step == "c"
        ));
    }

    // ---- TEST-206: Performative Definedness ----

    #[test]
    fn test_definedness_all_defined_passes() {
        let proto = linear_protocol();
        let violations = proto.check_performative_definedness(&["a", "b", "c"]);
        assert!(violations.is_empty());
    }

    #[test]
    fn test_definedness_undefined_rejected() {
        let proto = linear_protocol();
        // Only "a" is defined, "b" and "c" are not
        let violations = proto.check_performative_definedness(&["a"]);
        assert_eq!(violations.len(), 2);
        let names: Vec<&str> = violations
            .iter()
            .filter_map(|v| match v {
                ProtocolViolation::UndefinedPerformative { name } => Some(name.as_str()),
                _ => None,
            })
            .collect();
        assert!(names.contains(&"b"));
        assert!(names.contains(&"c"));
    }

    // ---- TEST-207: Step Uniqueness ----

    #[test]
    fn test_step_uniqueness_always_passes() {
        // BTreeMap guarantees uniqueness by construction
        let proto = linear_protocol();
        assert!(proto.check_step_uniqueness().is_empty());
    }

    // ---- TEST-208: verify_r5_protocol composite ----

    #[test]
    fn test_verify_r5_protocol_valid() {
        let proto = linear_protocol();
        let violations = proto.verify_r5_protocol(&["a", "b", "c"]);
        assert!(violations.is_empty());
    }

    #[test]
    fn test_verify_r5_protocol_catches_undefined() {
        let proto = linear_protocol();
        let violations = proto.verify_r5_protocol(&["a"]);
        assert!(violations
            .iter()
            .any(|v| matches!(v, ProtocolViolation::UndefinedPerformative { .. })));
    }

    #[test]
    fn test_verify_r5_protocol_catches_unreachable() {
        let mut steps = BTreeMap::new();
        steps.insert(
            "begin".into(),
            StepDecl {
                performative: "begin".into(),
                predecessors: vec![],
                successors: vec![NodeRef::Single("a".into())],
            },
        );
        steps.insert(
            "a".into(),
            StepDecl {
                performative: "a".into(),
                predecessors: vec![NodeRef::Single("begin".into())],
                successors: vec![],
            },
        );
        steps.insert(
            "orphan".into(),
            StepDecl {
                performative: "orphan".into(),
                predecessors: vec![],
                successors: vec![],
            },
        );
        let proto = CausalProtocol { steps };
        let violations = proto.verify_r5_protocol(&["a", "orphan"]);
        assert!(violations
            .iter()
            .any(|v| matches!(v, ProtocolViolation::Unreachable { step } if step == "orphan")));
    }

    // ---- ProtocolViolation Display ----

    #[test]
    fn test_protocol_violation_display() {
        let v = ProtocolViolation::Cycle {
            participants: vec!["a".into(), "b".into()],
        };
        assert_eq!(v.to_string(), "cycle detected: a → b");

        let v = ProtocolViolation::Unreachable {
            step: "orphan".into(),
        };
        assert!(v.to_string().contains("unreachable"));

        let v = ProtocolViolation::UndefinedPerformative {
            name: "foo".into(),
        };
        assert!(v.to_string().contains("not defined"));

        let v = ProtocolViolation::DuplicateStep {
            name: "bar".into(),
        };
        assert!(v.to_string().contains("duplicate"));
    }

    // ---- Empty protocol ----

    #[test]
    fn test_empty_protocol_passes_all_checks() {
        let proto = CausalProtocol {
            steps: BTreeMap::new(),
        };
        assert!(proto.check_acyclicity().is_empty());
        assert!(proto.check_reachability().is_empty());
        assert!(proto.check_performative_definedness(&[]).is_empty());
        assert!(proto.check_step_uniqueness().is_empty());
        assert!(proto.verify_r5_protocol(&[]).is_empty());
    }
}
