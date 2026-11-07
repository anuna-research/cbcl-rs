//! REQ-303 / REQ-510: strong Kleene tables, lattice laws, and refinement.
//! Compare verdict classes: diagnostic payloads are not truth values.

use cbcl_core::protocol::{CausalViolation, VerificationResult};

fn values() -> [VerificationResult; 4] {
    [
        VerificationResult::Violation(CausalViolation::MissingCausedBy),
        VerificationResult::Unknown,
        VerificationResult::Valid,
        VerificationResult::Violation(CausalViolation::FanInWithoutAllDecl {
            performative: "reply".into(),
        }),
    ]
}

fn class(value: &VerificationResult) -> usize {
    match value {
        VerificationResult::Violation(_) => 0,
        VerificationResult::Unknown => 1,
        VerificationResult::Valid => 2,
    }
}

fn refines(before: &VerificationResult, after: &VerificationResult) -> bool {
    matches!(before, VerificationResult::Unknown) || class(before) == class(after)
}

#[test]
fn req303_strong_kleene_tables_exhaustive() {
    // Row and column order: false, unknown, true. Independent table oracle.
    let conjunction = [[0, 0, 0], [0, 1, 1], [0, 1, 2]];
    let disjunction = [[0, 1, 2], [1, 1, 2], [2, 2, 2]];
    for a in values() {
        for b in values() {
            let (i, j) = (class(&a), class(&b));
            assert_eq!(class(&a.clone().meet(b.clone())), conjunction[i][j]);
            assert_eq!(class(&a.clone().join(b.clone())), disjunction[i][j]);
        }
    }
}

#[test]
fn req510_absorption_and_distributivity_exhaustive() {
    for a in values() {
        for b in values() {
            assert_eq!(class(&a.clone().meet(a.clone().join(b.clone()))), class(&a));
            assert_eq!(class(&a.clone().join(a.clone().meet(b.clone()))), class(&a));
            for c in values() {
                assert_eq!(
                    class(&a.clone().meet(b.clone().join(c.clone()))),
                    class(&a.clone().meet(b.clone()).join(a.clone().meet(c.clone())))
                );
                assert_eq!(
                    class(&a.clone().join(b.clone().meet(c.clone()))),
                    class(&a.clone().join(b.clone()).meet(a.clone().join(c)))
                );
            }
        }
    }
}

#[test]
fn req303_resolving_unknowns_preserves_terminal_results() {
    for a in values() {
        for b in values() {
            for c in values() {
                for d in values() {
                    if refines(&a, &c) && refines(&b, &d) {
                        assert!(refines(
                            &a.clone().meet(b.clone()),
                            &c.clone().meet(d.clone())
                        ));
                        assert!(refines(&a.clone().join(b.clone()), &c.clone().join(d)));
                    }
                }
            }
        }
    }
}
