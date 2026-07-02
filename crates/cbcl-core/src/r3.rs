//! R3: Core preservation safety constraint.
//!
//! Mirrors `R3CorePreservation.lean` from the Lean 4 proof library.

#![forbid(unsafe_code)]

use alloc::string::String;
use alloc::vec::Vec;

use crate::dialect::Dialect;
use crate::message::is_core_performative_name;

/// Verify R3 for a dialect (REQ-080).
///
/// Returns true for cbcl-base. For other dialects, checks that no
/// performative has a core performative name.
pub fn verify_r3(d: &Dialect) -> bool {
    if d.name == "cbcl-base" {
        return true;
    }
    let pass = !d
        .performatives
        .iter()
        .any(|p| is_core_performative_name(&p.name));
    #[cfg(feature = "tracing")]
    tracing::event!(
        tracing::Level::INFO,
        constraint = "R3",
        dialect = %d.name,
        pass,
        "constraint_check_result"
    );
    pass
}

/// Collect the names of core performatives that a non-base dialect attempts
/// to redefine. Returns an empty vec when R3 is satisfied.
pub fn r3_violations(d: &Dialect) -> Vec<String> {
    if d.name == "cbcl-base" {
        return Vec::new();
    }
    d.performatives
        .iter()
        .filter(|p| is_core_performative_name(&p.name))
        .map(|p| p.name.clone())
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dialect::{base_dialect, Dialect, PerformativeDef, ResourceBounds};
    use crate::message::CORE_PERFORMATIVE_NAMES;
    use crate::sexpr::{Atom, SExpr};
    use alloc::string::String;
    use alloc::vec;

    fn test_dialect_with(perf_names: &[&str]) -> Dialect {
        Dialect {
            roles: Vec::new(),
            name: String::from("test-dialect"),
            extends: vec![String::from("cbcl")],
            author: None,
            performatives: perf_names
                .iter()
                .map(|n| PerformativeDef {
                    role: None,
                    name: String::from(*n),
                    params: vec![],
                    template: SExpr::Atom(Atom::Symbol(String::from(*n))),
                })
                .collect(),
            resources: ResourceBounds {
                max_depth: 8,
                max_expansion_size: 512,
                verification_time_ms: 10,
            },
            examples: vec![],
            signature: None,
            hash: None,
            protocol: None,
            causal_protocol: None,
            shapes: Vec::new(),
        }
    }

    #[test]
    fn base_dialect_passes_r3() {
        assert!(verify_r3(&base_dialect()));
        assert!(r3_violations(&base_dialect()).is_empty());
    }

    #[test]
    fn custom_dialect_without_core_names_passes() {
        let d = test_dialect_with(&["greet"]);
        assert!(verify_r3(&d));
        assert!(r3_violations(&d).is_empty());
    }

    #[test]
    fn custom_dialect_with_core_name_fails() {
        let d = test_dialect_with(&["tell"]);
        assert!(!verify_r3(&d));
        assert_eq!(r3_violations(&d), vec!["tell"]);
    }

    /// Every single core performative name triggers an R3 violation
    /// when used in a non-base dialect (test vectors r3-001 through r3-008).
    #[test]
    fn each_core_performative_triggers_r3() {
        for &name in CORE_PERFORMATIVE_NAMES {
            let d = test_dialect_with(&[name]);
            assert!(
                !verify_r3(&d),
                "expected R3 failure for core performative '{}'",
                name
            );
            assert_eq!(r3_violations(&d), vec![name]);
        }
    }

    #[test]
    fn multiple_violations_collected() {
        let d = test_dialect_with(&["tell", "custom-perf", "ask"]);
        assert!(!verify_r3(&d));
        let v = r3_violations(&d);
        assert_eq!(v, vec!["tell", "ask"]);
    }
}
