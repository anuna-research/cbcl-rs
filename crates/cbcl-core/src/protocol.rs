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
}
