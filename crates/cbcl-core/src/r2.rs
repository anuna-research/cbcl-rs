//! R2: Resource bounds safety constraint.
//!
//! Mirrors `R2ResourceBounds.lean` from the Lean 4 proof library.

#![forbid(unsafe_code)]

use crate::dialect::Dialect;
use crate::sexpr::SExpr;

/// Tracks resource consumption during bounded evaluation (REQ-071).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResourceState {
    pub current_depth: u32,
    pub expansion_size: u32,
    pub max_depth: u32,
    pub max_exp_size: u32,
}

impl ResourceState {
    /// Create a new resource state from resource bounds.
    pub fn new(max_depth: u32, max_exp_size: u32) -> Self {
        Self {
            current_depth: 0,
            expansion_size: 0,
            max_depth,
            max_exp_size,
        }
    }

    /// Enter a deeper nesting level, returning None if bounds exceeded (REQ-071).
    ///
    /// Uses strict `<` matching `ResourceState.enterDepth` in
    /// `R2ResourceBounds.lean:36–40`.
    pub fn enter_depth(&self) -> Option<ResourceState> {
        let new_depth = self.current_depth + 1;
        if new_depth < self.max_depth {
            Some(ResourceState {
                current_depth: new_depth,
                ..self.clone()
            })
        } else {
            None
        }
    }

    /// Add expansion size, returning None if bounds exceeded (REQ-071).
    ///
    /// Uses strict `<` matching `ResourceState.addExpansion` in
    /// `R2ResourceBounds.lean:43–47`.
    pub fn add_expansion(&self, size: u32) -> Option<ResourceState> {
        let new_size = self.expansion_size + size;
        if new_size < self.max_exp_size {
            Some(ResourceState {
                expansion_size: new_size,
                ..self.clone()
            })
        } else {
            None
        }
    }

    /// Exit a nesting level.
    pub fn exit_depth(&self) -> ResourceState {
        ResourceState {
            current_depth: self.current_depth.saturating_sub(1),
            ..self.clone()
        }
    }

    /// Remaining depth steps before limit.
    ///
    /// Matches `ResourceState.remainingDepth` in `R2ResourceBounds.lean:33–34`.
    pub fn remaining_depth(&self) -> u32 {
        self.max_depth.saturating_sub(self.current_depth)
    }

    /// Create initial resource state from resource bounds.
    ///
    /// Matches `ResourceState.initial` in `R2ResourceBounds.lean:54–56`.
    pub fn initial(bounds: &crate::dialect::ResourceBounds) -> Self {
        Self {
            current_depth: 0,
            expansion_size: 0,
            max_depth: bounds.max_depth,
            max_exp_size: bounds.max_expansion_size,
        }
    }
}

/// Verify R2 for a dialect: resource bounds must be valid (REQ-070).
pub fn verify_r2(d: &Dialect) -> bool {
    let pass = d.resources.is_valid();
    #[cfg(feature = "tracing")]
    tracing::event!(
        tracing::Level::INFO,
        constraint = "R2",
        dialect = %d.name,
        pass,
        "constraint_check_result"
    );
    pass
}

/// Bounded evaluation with fuel (REQ-072, REQ-073).
///
/// Returns None if fuel is exhausted or resource bounds are exceeded.
/// Matches `CBCL.boundedEval` in `R2ResourceBounds.lean:71–88`.
///
/// For each non-empty list, enters a depth level, records the expression's
/// byte-size as expansion, recursively evaluates the head element, then
/// exits the depth level. Empty lists and atoms are returned immediately.
pub fn bounded_eval(fuel: usize, expr: &SExpr, rs: &mut ResourceState) -> Option<SExpr> {
    if fuel == 0 {
        return None;
    }
    match expr {
        SExpr::Atom(_) => Some(expr.clone()),
        SExpr::List(items) => {
            if items.is_empty() {
                return Some(expr.clone());
            }
            // Enter depth
            let mut rs_inner = rs.enter_depth()?;
            // Record expansion size
            rs_inner = rs_inner.add_expansion(expr.byte_size() as u32)?;
            // Recursively evaluate the head element
            let _ = bounded_eval(fuel - 1, &items[0], &mut rs_inner)?;
            // Exit depth and update caller's state
            *rs = rs_inner.exit_depth();
            Some(expr.clone())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dialect::ResourceBounds;
    use crate::sexpr::Atom;
    use alloc::string::String;
    use alloc::vec;

    // ---- REQ-073: fuel / atom basics ----

    #[test]
    fn fuel_zero_returns_none() {
        let expr = SExpr::Atom(Atom::Num(1));
        let mut rs = ResourceState::new(8, 512);
        assert_eq!(bounded_eval(0, &expr, &mut rs), None);
    }

    #[test]
    fn atom_with_fuel_returns_some() {
        let expr = SExpr::Atom(Atom::Num(1));
        let mut rs = ResourceState::new(8, 512);
        assert_eq!(bounded_eval(1, &expr, &mut rs), Some(expr));
    }

    #[test]
    fn empty_list_with_fuel_returns_some() {
        let expr = SExpr::List(vec![]);
        let mut rs = ResourceState::new(8, 512);
        assert_eq!(bounded_eval(1, &expr, &mut rs), Some(expr));
    }

    // ---- REQ-071: ResourceState depth tracking ----

    #[test]
    fn enter_depth_respects_bounds() {
        // max_depth=3, strict <: depths 0→1→2 ok, 2→3 fails
        let rs = ResourceState::new(3, 512);
        let rs1 = rs.enter_depth().unwrap();
        assert_eq!(rs1.current_depth, 1);
        let rs2 = rs1.enter_depth().unwrap();
        assert_eq!(rs2.current_depth, 2);
        assert!(rs2.enter_depth().is_none());
    }

    /// Test vector r2-004: max_depth=3, three enter-depth calls, third fails.
    #[test]
    fn tv_r2_004_depth_limit_enforcement() {
        let rs = ResourceState::new(3, 512);
        let rs1 = rs.enter_depth().unwrap();
        let rs2 = rs1.enter_depth().unwrap();
        // Third enter-depth exceeds limit of 3 (strict <)
        assert!(rs2.enter_depth().is_none());
    }

    /// Test vector r2-005: max_expansion_size=100, add 50 then 60 fails.
    #[test]
    fn tv_r2_005_expansion_size_enforcement() {
        let rs = ResourceState::new(16, 100);
        let rs1 = rs.add_expansion(50).unwrap();
        assert_eq!(rs1.expansion_size, 50);
        // Cumulative 110 > limit 100 (strict <)
        assert!(rs1.add_expansion(60).is_none());
    }

    #[test]
    fn add_expansion_at_boundary_fails() {
        // Strict <: expansion_size + size must be < max_exp_size
        let rs = ResourceState::new(8, 100);
        // Exactly at limit: 100 < 100 is false → None
        assert!(rs.add_expansion(100).is_none());
        // Just under limit
        assert!(rs.add_expansion(99).is_some());
    }

    #[test]
    fn exit_depth_decrements() {
        let rs = ResourceState::new(8, 512);
        let rs1 = rs.enter_depth().unwrap();
        assert_eq!(rs1.current_depth, 1);
        let rs2 = rs1.exit_depth();
        assert_eq!(rs2.current_depth, 0);
    }

    #[test]
    fn exit_depth_saturates_at_zero() {
        let rs = ResourceState::new(8, 512);
        let rs2 = rs.exit_depth();
        assert_eq!(rs2.current_depth, 0);
    }

    #[test]
    fn remaining_depth() {
        let rs = ResourceState::new(8, 512);
        assert_eq!(rs.remaining_depth(), 8);
        let rs1 = rs.enter_depth().unwrap();
        assert_eq!(rs1.remaining_depth(), 7);
    }

    // ---- ResourceState::initial ----

    #[test]
    fn initial_from_bounds() {
        let bounds = ResourceBounds {
            max_depth: 16,
            max_expansion_size: 1024,
            verification_time_ms: 50,
        };
        let rs = ResourceState::initial(&bounds);
        assert_eq!(rs.current_depth, 0);
        assert_eq!(rs.expansion_size, 0);
        assert_eq!(rs.max_depth, 16);
        assert_eq!(rs.max_exp_size, 1024);
    }

    // ---- REQ-070: verify_r2 ----

    #[test]
    fn base_dialect_passes_r2() {
        let d = crate::dialect::base_dialect();
        assert!(verify_r2(&d));
    }

    /// Test vector r2-001: valid bounds pass verification.
    #[test]
    fn tv_r2_001_valid_bounds() {
        let d = test_dialect_with_bounds(16, 1024, 100);
        assert!(verify_r2(&d));
    }

    /// Test vector r2-003: excessive max_depth (>64) fails.
    #[test]
    fn tv_r2_003_excessive_max_depth() {
        let d = test_dialect_with_bounds(100, 1024, 100);
        assert!(!verify_r2(&d));
    }

    /// Test vector r2-006: planning dialect bounds.
    #[test]
    fn tv_r2_006_planning_dialect() {
        let d = test_dialect_with_bounds(16, 1024, 10);
        assert!(verify_r2(&d));
    }

    /// Test vector r2-007: cross-chain dialect bounds.
    #[test]
    fn tv_r2_007_crosschain_dialect() {
        let d = test_dialect_with_bounds(12, 800, 40);
        assert!(verify_r2(&d));
    }

    /// Test vector r2-008: artifacts dialect bounds.
    #[test]
    fn tv_r2_008_artifacts_dialect() {
        let d = test_dialect_with_bounds(8, 512, 20);
        assert!(verify_r2(&d));
    }

    #[test]
    fn zero_bounds_fail_r2() {
        assert!(!verify_r2(&test_dialect_with_bounds(0, 512, 10)));
        assert!(!verify_r2(&test_dialect_with_bounds(8, 0, 10)));
        assert!(!verify_r2(&test_dialect_with_bounds(8, 512, 0)));
    }

    #[test]
    fn max_allowed_bounds_pass_r2() {
        assert!(verify_r2(&test_dialect_with_bounds(64, 8192, 1000)));
    }

    #[test]
    fn over_max_allowed_bounds_fail_r2() {
        assert!(!verify_r2(&test_dialect_with_bounds(65, 512, 10)));
        assert!(!verify_r2(&test_dialect_with_bounds(8, 8193, 10)));
        assert!(!verify_r2(&test_dialect_with_bounds(8, 512, 1001)));
    }

    // ---- REQ-072: bounded_eval on lists ----

    #[test]
    fn bounded_eval_nonempty_list() {
        let expr = SExpr::List(vec![
            SExpr::Atom(Atom::Symbol(String::from("tell"))),
            SExpr::Atom(Atom::Str(String::from("hi"))),
        ]);
        let mut rs = ResourceState::new(8, 512);
        let result = bounded_eval(10, &expr, &mut rs);
        assert_eq!(result, Some(expr));
        // Depth should be back to 0 after exit
        assert_eq!(rs.current_depth, 0);
        // Expansion size should have been recorded
        assert!(rs.expansion_size > 0);
    }

    #[test]
    fn bounded_eval_depth_exceeded() {
        let expr = SExpr::List(vec![SExpr::Atom(Atom::Num(1))]);
        // max_depth=1: strict <, so 0→1 fails immediately (1 < 1 is false)
        let mut rs = ResourceState::new(1, 512);
        assert_eq!(bounded_eval(10, &expr, &mut rs), None);
    }

    #[test]
    fn bounded_eval_expansion_exceeded() {
        // Create an expression with known byte size, using a small expansion limit
        let expr = SExpr::List(vec![SExpr::Atom(Atom::Symbol(String::from(
            "a-long-symbol-name",
        )))]);
        let byte_size = expr.byte_size() as u32;
        // Set max_exp_size to exactly the byte size — strict < means it fails
        let mut rs = ResourceState::new(8, byte_size);
        assert_eq!(bounded_eval(10, &expr, &mut rs), None);
    }

    #[test]
    fn bounded_eval_nested_list() {
        let inner = SExpr::List(vec![SExpr::Atom(Atom::Num(1))]);
        let outer = SExpr::List(vec![inner]);
        let mut rs = ResourceState::new(8, 512);
        let result = bounded_eval(10, &outer, &mut rs);
        assert_eq!(result, Some(outer));
        assert_eq!(rs.current_depth, 0);
    }

    #[test]
    fn bounded_eval_fuel_consumed_recursively() {
        // Nested lists consume fuel on each level:
        // outer list (fuel-1) → inner list (fuel-1) → atom (fuel-1)
        let inner = SExpr::List(vec![SExpr::Atom(Atom::Num(1))]);
        let outer = SExpr::List(vec![inner]);
        let mut rs = ResourceState::new(8, 512);
        // fuel=1: outer uses it, recurses with fuel=0 on inner → None
        assert_eq!(bounded_eval(1, &outer, &mut rs), None);
        // fuel=2: outer→inner with fuel=1, inner recurses with fuel=0 on atom → None
        let mut rs2 = ResourceState::new(8, 512);
        assert_eq!(bounded_eval(2, &outer, &mut rs2), None);
        // fuel=3: enough for outer→inner→atom
        let mut rs3 = ResourceState::new(8, 512);
        assert!(bounded_eval(3, &outer, &mut rs3).is_some());
    }

    // ---- Helpers ----

    fn test_dialect_with_bounds(
        max_depth: u32,
        max_expansion_size: u32,
        verification_time_ms: u32,
    ) -> crate::dialect::Dialect {
        crate::dialect::Dialect {
            name: String::from("test-dialect"),
            extends: alloc::vec![],
            author: None,
            performatives: alloc::vec![],
            resources: ResourceBounds {
                max_depth,
                max_expansion_size,
                verification_time_ms,
            },
            examples: alloc::vec![],
            signature: None,
            hash: None,
            protocol: None, shapes: Vec::new(),
        }
    }
}
