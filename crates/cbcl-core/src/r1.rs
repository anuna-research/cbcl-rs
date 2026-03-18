//! R1: No recursion safety constraint.
//!
//! Mirrors `R1NoRecursion.lean` from the Lean 4 proof library.

#![forbid(unsafe_code)]

use alloc::collections::{BTreeMap, BTreeSet};
use alloc::string::String;
use alloc::vec::Vec;

use crate::dialect::Dialect;
use crate::sexpr::{Atom, SExpr};

/// Check if an expression contains a self-reference to the given name (REQ-060).
pub fn contains_self_reference(name: &str, expr: &SExpr) -> bool {
    match expr {
        SExpr::Atom(Atom::Symbol(s)) => s == name,
        SExpr::Atom(_) => false,
        SExpr::List(items) => items.iter().any(|e| contains_self_reference(name, e)),
    }
}

/// Verify R1 for a single performative template (REQ-061).
pub fn verify_r1(perf_name: &str, template: &SExpr) -> bool {
    let pass = !contains_self_reference(perf_name, template);
    #[cfg(feature = "tracing")]
    tracing::event!(
        tracing::Level::INFO,
        constraint = "R1",
        performative = perf_name,
        pass,
        "constraint_check_result"
    );
    pass
}

/// Verify R1 for an entire dialect (REQ-062).
pub fn verify_r1_dialect(d: &Dialect) -> bool {
    if d.name == "cbcl-base" {
        return true;
    }
    let pass = r1_violations(d).is_empty();
    #[cfg(feature = "tracing")]
    tracing::event!(
        tracing::Level::INFO,
        constraint = "R1",
        dialect = %d.name,
        pass,
        "constraint_check_result"
    );
    pass
}

/// Collect the names of performatives that violate R1 (self-reference in template).
/// Returns an empty vec when R1 is satisfied.
pub fn r1_violations(d: &Dialect) -> Vec<String> {
    if d.name == "cbcl-base" {
        return Vec::new();
    }

    let graph = dependency_graph(d);
    let cyclic = cyclic_performatives(&graph);

    d.performatives
        .iter()
        .filter(|p| cyclic.contains(&p.name))
        .map(|p| p.name.clone())
        .collect()
}

fn dependency_graph(d: &Dialect) -> BTreeMap<String, BTreeSet<String>> {
    let performative_names = d
        .performatives
        .iter()
        .map(|p| p.name.clone())
        .collect::<BTreeSet<_>>();

    d.performatives
        .iter()
        .map(|p| {
            let mut referenced = BTreeSet::new();
            collect_symbol_references(&p.template, &mut referenced);
            referenced.retain(|name| performative_names.contains(name));
            (p.name.clone(), referenced)
        })
        .collect()
}

fn collect_symbol_references(expr: &SExpr, referenced: &mut BTreeSet<String>) {
    match expr {
        SExpr::Atom(Atom::Symbol(name)) => {
            referenced.insert(name.clone());
        }
        SExpr::Atom(_) => {}
        SExpr::List(items) => {
            for item in items {
                collect_symbol_references(item, referenced);
            }
        }
    }
}

fn cyclic_performatives(graph: &BTreeMap<String, BTreeSet<String>>) -> BTreeSet<String> {
    graph
        .keys()
        .filter(|name| reaches_cycle(name, name, graph, &mut BTreeSet::new()))
        .cloned()
        .collect()
}

fn reaches_cycle(
    start: &str,
    current: &str,
    graph: &BTreeMap<String, BTreeSet<String>>,
    visiting: &mut BTreeSet<String>,
) -> bool {
    let Some(dependencies) = graph.get(current) else {
        return false;
    };

    for dependency in dependencies {
        if dependency == start {
            return true;
        }
        if visiting.insert(dependency.clone()) {
            if reaches_cycle(start, dependency, graph, visiting) {
                return true;
            }
            visiting.remove(dependency);
        }
    }

    false
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dialect::{base_dialect, Dialect, DialectRegistry, PerformativeDef, ResourceBounds};
    use alloc::string::String;
    use alloc::vec;
    use core::str::FromStr;

    fn valid_bounds() -> ResourceBounds {
        ResourceBounds {
            max_depth: 8,
            max_expansion_size: 512,
            verification_time_ms: 10,
        }
    }

    fn make_dialect(name: &str, perfs: Vec<PerformativeDef>) -> Dialect {
        Dialect {
            name: String::from(name),
            extends: vec![String::from("cbcl")],
            author: None,
            performatives: perfs,
            resources: valid_bounds(),
            examples: vec![],
            signature: None,
            hash: None,
            protocol: None,
        }
    }

    fn perf(name: &str, template_str: &str) -> PerformativeDef {
        PerformativeDef {
            name: String::from(name),
            params: vec![],
            template: SExpr::from_str(template_str).unwrap(),
        }
    }

    // -- Unit tests for contains_self_reference --

    #[test]
    fn no_self_reference_in_atom() {
        let expr = SExpr::Atom(Atom::Num(42));
        assert!(!contains_self_reference("foo", &expr));
    }

    #[test]
    fn no_self_reference_in_string_atom() {
        let expr = SExpr::Atom(Atom::Str(String::from("foo")));
        assert!(!contains_self_reference("foo", &expr));
    }

    #[test]
    fn no_self_reference_in_bool() {
        assert!(!contains_self_reference(
            "foo",
            &SExpr::Atom(Atom::Bool(true))
        ));
    }

    #[test]
    fn no_self_reference_in_keyword() {
        let expr = SExpr::Atom(Atom::Keyword(String::from("foo")));
        assert!(!contains_self_reference("foo", &expr));
    }

    #[test]
    fn detects_self_reference() {
        let expr = SExpr::Atom(Atom::Symbol(String::from("foo")));
        assert!(contains_self_reference("foo", &expr));
    }

    #[test]
    fn no_match_different_symbol() {
        let expr = SExpr::Atom(Atom::Symbol(String::from("bar")));
        assert!(!contains_self_reference("foo", &expr));
    }

    #[test]
    fn detects_in_nested_list() {
        let expr = SExpr::from_str("(a (b (c foo)))").unwrap();
        assert!(contains_self_reference("foo", &expr));
    }

    #[test]
    fn no_match_in_empty_list() {
        assert!(!contains_self_reference("foo", &SExpr::List(vec![])));
    }

    #[test]
    fn base_dialect_passes_r1() {
        let d = base_dialect();
        assert!(verify_r1_dialect(&d));
        assert!(r1_violations(&d).is_empty());
    }

    // -- Test vectors r1-001 through r1-010 --

    /// r1-001: Direct recursion in performative definition must be rejected
    #[test]
    fn tv_r1_001_direct_recursion_rejected() {
        let template = SExpr::from_str("(literal (factorial (- n 1)))").unwrap();
        assert!(contains_self_reference("factorial", &template));
        assert!(!verify_r1("factorial", &template));
    }

    /// r1-002: Safe template (no self-reference) must be accepted
    #[test]
    fn tv_r1_002_safe_template_accepted() {
        let template = SExpr::from_str("(literal (tell recipient message))").unwrap();
        assert!(!contains_self_reference("notify", &template));
        assert!(verify_r1("notify", &template));
    }

    /// r1-003: Complex safe template with conditionals accepted
    #[test]
    fn tv_r1_003_complex_cond_safe() {
        let template = SExpr::from_str(
            "(cond ((= type urgent) (literal (tell @emergency msg))) (else (literal (tell @normal msg))))",
        )
        .unwrap();
        assert!(verify_r1("complex", &template));
    }

    /// r1-004: Safe multi-step sequence performative accepted
    #[test]
    fn tv_r1_004_safe_sequence() {
        let template = SExpr::from_str(
            "(sequence (literal (tell coordinator \"task-complete\")) (literal (ask database (record-completion task-id))) (literal (tell requester \"notification-sent\")))",
        )
        .unwrap();
        assert!(verify_r1("notify-complete", &template));
    }

    /// r1-005: Recursive performative via cond branch rejected
    #[test]
    fn tv_r1_005_recursion_in_cond_branch() {
        let template = SExpr::from_str(
            "(cond ((> count 0) (literal (bad-recursive (- count 1)))) (else (literal (tell done \"finished\"))))",
        )
        .unwrap();
        assert!(!verify_r1("bad-recursive", &template));
    }

    /// r1-006: Complex safe definition with multiple cond branches accepted
    #[test]
    fn tv_r1_006_complex_safe_cond() {
        let template = SExpr::from_str(
            "(cond ((= priority critical) (sequence (literal (tell emergency-team urgent-message)) (literal (ask coordinator emergency-protocols)))) ((= priority normal) (literal (tell standard-team normal-message))) (else (sequence (literal (tell default-handler message)) (literal (ask manager approval-required)))))",
        )
        .unwrap();
        assert!(verify_r1("smart-dispatch", &template));
    }

    /// r1-007: Recursive dialect definition rejected at installation
    #[test]
    fn tv_r1_007_recursive_dialect_rejected() {
        let d = make_dialect(
            "bad-recursive-dialect",
            vec![perf(
                "recursive-perf",
                "(sequence (literal (tell coordinator \"starting\")) (literal (recursive-perf remaining-data)) (literal (tell coordinator \"done\")))",
            )],
        );
        assert!(!verify_r1_dialect(&d));
        assert_eq!(r1_violations(&d), vec!["recursive-perf"]);
    }

    /// r1-008: Safe delegation dialect accepted at installation
    #[test]
    fn tv_r1_008_safe_delegation_dialect() {
        let d = make_dialect(
            "safe-delegation-dialect",
            vec![perf(
                "delegate-work",
                "(sequence (literal (tell coordinator \"delegating\")) (literal (ask (car workers) task)) (literal (tell coordinator \"delegated\")))",
            )],
        );
        assert!(verify_r1_dialect(&d));
        assert!(r1_violations(&d).is_empty());
    }

    /// r1-009: Indirect recursion via sequence rejected
    #[test]
    fn tv_r1_009_indirect_recursion_in_sequence() {
        let d = make_dialect(
            "indirect-recursive-dialect",
            vec![perf(
                "process-list",
                "(cond ((null? items) (literal (tell coordinator \"done\"))) (else (sequence (literal (tell worker (car items))) (literal (process-list (cdr items))))))",
            )],
        );
        assert!(!verify_r1_dialect(&d));
        assert_eq!(r1_violations(&d), vec!["process-list"]);
    }

    /// r1-010: Complex workflow with nested cond accepted
    #[test]
    fn tv_r1_010_complex_workflow_accepted() {
        let d = make_dialect(
            "complex-workflow-dialect",
            vec![perf(
                "workflow-execute",
                "(sequence (literal (tell logger \"workflow started\")) (cond ((eq? priority urgent) (sequence (literal (tell priority-handler steps)) (literal (ask supervisor \"approval\")))) ((eq? priority normal) (literal (tell normal-handler steps))) (else (literal (tell default-handler steps)))) (literal (tell logger \"workflow completed\")))",
            )],
        );
        assert!(verify_r1_dialect(&d));
    }

    /// R1 violation blocks dialect installation (integration test)
    #[test]
    fn install_rejects_r1_violation() {
        let mut reg = DialectRegistry::new();
        let d = make_dialect("bad-r1", vec![perf("recurse", "(literal (recurse x))")]);
        let err = reg.install(d).unwrap_err();
        match err {
            crate::dialect::DialectInstallError::R1Violation {
                dialect_name,
                recursive,
            } => {
                assert_eq!(dialect_name, "bad-r1");
                assert_eq!(recursive, vec!["recurse"]);
            }
            other => panic!("expected R1Violation, got {:?}", other),
        }
        assert_eq!(reg.len(), 1);
    }

    #[test]
    fn mutual_recursion_is_rejected() {
        let d = make_dialect(
            "mutual-recursion",
            vec![
                perf("ping", "(literal (pong x))"),
                perf("pong", "(literal (ping x))"),
            ],
        );
        assert!(!verify_r1_dialect(&d));
        assert_eq!(r1_violations(&d), vec!["ping", "pong"]);
    }

    /// Multiple R1 violations in a single dialect
    #[test]
    fn multiple_r1_violations() {
        let d = make_dialect(
            "multi-bad",
            vec![
                perf("a", "(literal (a x))"),
                perf("b", "(literal (tell x y))"),
                perf("c", "(literal (c z))"),
            ],
        );
        assert!(!verify_r1_dialect(&d));
        let v = r1_violations(&d);
        assert_eq!(v, vec!["a", "c"]);
    }
}
