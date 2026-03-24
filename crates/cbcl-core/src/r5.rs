//! R5: Shape well-formedness validation (REQ-222).
//!
//! Installation-time checks for shape constraints:
//! 1. Performative name matches a performative defined in the dialect.
//! 2. All keywords are non-empty (valid CBCL keywords start with ':').
//! 3. All type constraints are one of the six recognised types (guaranteed by `TypeConstraint` enum).
//! 4. `max-depth` does not exceed the dialect's R2 resource bound.
//! 5. No duplicate require/optional for the same keyword at the same depth.

#![forbid(unsafe_code)]

use crate::dialect::Dialect;
use crate::shape::ShapeRule;
use alloc::string::String;
use alloc::vec::Vec;

/// Verify R5 for a dialect: protocol well-formedness (REQ-208) and shape
/// well-formedness (REQ-222).
pub fn verify_r5(d: &Dialect) -> bool {
    let pass = r5_violations(d).is_empty();
    #[cfg(feature = "tracing")]
    tracing::event!(
        tracing::Level::INFO,
        constraint = "R5",
        dialect = %d.name,
        pass,
        "constraint_check_result"
    );
    pass
}

/// Return all R5 violations found in a dialect's protocol and shape constraints.
pub fn r5_violations(d: &Dialect) -> Vec<String> {
    let mut violations = Vec::new();

    // Protocol validation (REQ-204–208).
    if let Some(ref proto) = d.causal_protocol {
        let defined: Vec<&str> = d.performative_names();
        let proto_violations = proto.verify_r5_protocol(&defined);
        for v in proto_violations {
            violations.push(alloc::format!("{}", v));
        }
    }

    // Shape validation (REQ-222).
    for shape in &d.shapes {
        // §1: Performative name must match a performative defined in the dialect.
        if !d.defines_performative(&shape.performative) {
            violations.push(alloc::format!(
                "shape targets unknown performative '{}'",
                shape.performative
            ));
        }

        // §2: All keywords must be non-empty (representing valid ':'-prefixed keywords).
        check_keywords_valid(&shape.rules, &mut violations);

        // §3: Type constraints are valid by construction (TypeConstraint enum).

        // §4: max-depth must not exceed the dialect's R2 resource bound.
        if let Some(shape_max_depth) = shape.max_depth() {
            if shape_max_depth > d.resources.max_depth {
                violations.push(alloc::format!(
                    "shape '{}' max-depth {} exceeds dialect R2 bound {}",
                    shape.performative, shape_max_depth, d.resources.max_depth
                ));
            }
        }

        // §5: No duplicate require/optional keywords at the same depth.
        if let Err(msg) = shape.no_duplicate_keywords() {
            violations.push(alloc::format!(
                "shape '{}': {}",
                shape.performative, msg
            ));
        }
    }
    violations
}

/// Recursively check that all keywords in shape rules are non-empty.
fn check_keywords_valid(rules: &[ShapeRule], violations: &mut Vec<String>) {
    for rule in rules {
        match rule {
            ShapeRule::Require {
                keyword, children, ..
            } => {
                if keyword.is_empty() {
                    violations.push(String::from("shape rule has empty keyword"));
                }
                check_keywords_valid(children, violations);
            }
            ShapeRule::Optional {
                keyword, children, ..
            } => {
                if keyword.is_empty() {
                    violations.push(String::from("shape rule has empty keyword"));
                }
                check_keywords_valid(children, violations);
            }
            ShapeRule::MaxDepth(_) => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dialect::{Dialect, PerformativeDef, ResourceBounds};
    use crate::sexpr::{Atom, SExpr};
    use crate::shape::{ShapeConstraint, ShapeRule, TypeConstraint};
    use alloc::string::String;
    use alloc::vec;

    fn test_dialect(performatives: Vec<&str>, shapes: Vec<ShapeConstraint>) -> Dialect {
        Dialect {
            name: String::from("test-dialect"),
            extends: vec![String::from("cbcl")],
            author: None,
            performatives: performatives
                .into_iter()
                .map(|name| PerformativeDef {
                    name: String::from(name),
                    params: vec![],
                    template: SExpr::List(vec![
                        SExpr::Atom(Atom::Symbol(String::from("effect"))),
                        SExpr::Atom(Atom::Symbol(String::from(name))),
                    ]),
                })
                .collect(),
            resources: ResourceBounds {
                max_depth: 16,
                max_expansion_size: 1024,
                verification_time_ms: 50,
            },
            examples: vec![],
            signature: None,
            hash: None,
            protocol: None,
            causal_protocol: None,
            shapes,
        }
    }

    // -- TEST-222: R5 shape well-formedness --

    #[test]
    fn valid_shape_passes_r5() {
        let d = test_dialect(
            vec!["propose-step"],
            vec![ShapeConstraint {
                performative: String::from("propose-step"),
                rules: vec![
                    ShapeRule::Require {
                        keyword: String::from("target"),
                        type_constraint: Some(TypeConstraint::String),
                        children: vec![],
                    },
                    ShapeRule::Optional {
                        keyword: String::from("priority"),
                        type_constraint: Some(TypeConstraint::Number),
                        default: None,
                        children: vec![],
                    },
                    ShapeRule::MaxDepth(8),
                ],
            }],
        );
        assert!(verify_r5(&d));
    }

    #[test]
    fn no_shapes_passes_r5() {
        let d = test_dialect(vec!["propose-step"], vec![]);
        assert!(verify_r5(&d));
    }

    #[test]
    fn unknown_performative_fails_r5() {
        let d = test_dialect(
            vec!["propose-step"],
            vec![ShapeConstraint {
                performative: String::from("nonexistent"),
                rules: vec![],
            }],
        );
        assert!(!verify_r5(&d));
        let v = r5_violations(&d);
        assert_eq!(v.len(), 1);
        assert!(v[0].contains("unknown performative"));
        assert!(v[0].contains("nonexistent"));
    }

    #[test]
    fn empty_keyword_fails_r5() {
        let d = test_dialect(
            vec!["propose-step"],
            vec![ShapeConstraint {
                performative: String::from("propose-step"),
                rules: vec![ShapeRule::Require {
                    keyword: String::new(),
                    type_constraint: None,
                    children: vec![],
                }],
            }],
        );
        assert!(!verify_r5(&d));
        let v = r5_violations(&d);
        assert!(v.iter().any(|s| s.contains("empty keyword")));
    }

    #[test]
    fn empty_keyword_in_optional_fails_r5() {
        let d = test_dialect(
            vec!["propose-step"],
            vec![ShapeConstraint {
                performative: String::from("propose-step"),
                rules: vec![ShapeRule::Optional {
                    keyword: String::new(),
                    type_constraint: None,
                    default: None,
                    children: vec![],
                }],
            }],
        );
        assert!(!verify_r5(&d));
    }

    #[test]
    fn max_depth_exceeds_r2_bound_fails_r5() {
        let d = test_dialect(
            vec!["propose-step"],
            vec![ShapeConstraint {
                performative: String::from("propose-step"),
                rules: vec![ShapeRule::MaxDepth(32)],
            }],
        );
        // dialect max_depth is 16, shape max_depth is 32
        assert!(!verify_r5(&d));
        let v = r5_violations(&d);
        assert!(v.iter().any(|s| s.contains("exceeds dialect R2 bound")));
    }

    #[test]
    fn max_depth_at_r2_bound_passes_r5() {
        let d = test_dialect(
            vec!["propose-step"],
            vec![ShapeConstraint {
                performative: String::from("propose-step"),
                rules: vec![ShapeRule::MaxDepth(16)],
            }],
        );
        assert!(verify_r5(&d));
    }

    #[test]
    fn duplicate_keywords_fails_r5() {
        let d = test_dialect(
            vec!["propose-step"],
            vec![ShapeConstraint {
                performative: String::from("propose-step"),
                rules: vec![
                    ShapeRule::Require {
                        keyword: String::from("target"),
                        type_constraint: None,
                        children: vec![],
                    },
                    ShapeRule::Optional {
                        keyword: String::from("target"),
                        type_constraint: None,
                        default: None,
                        children: vec![],
                    },
                ],
            }],
        );
        assert!(!verify_r5(&d));
        let v = r5_violations(&d);
        assert!(v.iter().any(|s| s.contains("duplicate keyword")));
    }

    #[test]
    fn multiple_violations_all_reported() {
        let d = test_dialect(
            vec!["propose-step"],
            vec![ShapeConstraint {
                performative: String::from("nonexistent"),
                rules: vec![
                    ShapeRule::Require {
                        keyword: String::new(),
                        type_constraint: None,
                        children: vec![],
                    },
                    ShapeRule::MaxDepth(64),
                ],
            }],
        );
        let v = r5_violations(&d);
        // Should have at least: unknown performative, empty keyword, max-depth exceeds bound
        assert!(v.len() >= 3, "expected >= 3 violations, got {}: {:?}", v.len(), v);
    }

    #[test]
    fn nested_empty_keyword_fails_r5() {
        let d = test_dialect(
            vec!["propose-step"],
            vec![ShapeConstraint {
                performative: String::from("propose-step"),
                rules: vec![ShapeRule::Require {
                    keyword: String::from("params"),
                    type_constraint: Some(TypeConstraint::List),
                    children: vec![ShapeRule::Require {
                        keyword: String::new(),
                        type_constraint: None,
                        children: vec![],
                    }],
                }],
            }],
        );
        assert!(!verify_r5(&d));
    }

    #[test]
    fn multiple_valid_shapes_pass_r5() {
        let d = test_dialect(
            vec!["propose-step", "track-shipment"],
            vec![
                ShapeConstraint {
                    performative: String::from("propose-step"),
                    rules: vec![ShapeRule::Require {
                        keyword: String::from("target"),
                        type_constraint: Some(TypeConstraint::String),
                        children: vec![],
                    }],
                },
                ShapeConstraint {
                    performative: String::from("track-shipment"),
                    rules: vec![ShapeRule::Require {
                        keyword: String::from("package"),
                        type_constraint: Some(TypeConstraint::String),
                        children: vec![],
                    }],
                },
            ],
        );
        assert!(verify_r5(&d));
    }

    #[test]
    fn base_dialect_passes_r5() {
        let d = crate::dialect::base_dialect();
        assert!(verify_r5(&d));
    }

    // -- TEST-208: R5 protocol validation at installation --

    use crate::protocol::{CausalProtocol, NodeRef, StepDecl};
    use alloc::collections::BTreeMap;

    fn protocol_dialect(
        performatives: Vec<&str>,
        proto: CausalProtocol,
    ) -> Dialect {
        Dialect {
            name: String::from("test-dialect"),
            extends: vec![String::from("cbcl")],
            author: None,
            performatives: performatives
                .into_iter()
                .map(|name| PerformativeDef {
                    name: String::from(name),
                    params: vec![],
                    template: SExpr::List(vec![
                        SExpr::Atom(Atom::Symbol(String::from("effect"))),
                        SExpr::Atom(Atom::Symbol(String::from(name))),
                    ]),
                })
                .collect(),
            resources: ResourceBounds {
                max_depth: 16,
                max_expansion_size: 1024,
                verification_time_ms: 50,
            },
            examples: vec![],
            signature: None,
            hash: None,
            protocol: None,
            causal_protocol: Some(proto),
            shapes: vec![],
        }
    }

    #[test]
    fn valid_protocol_passes_r5() {
        // begin → a → b (linear, all defined)
        let mut steps = BTreeMap::new();
        steps.insert("begin".into(), StepDecl {
            performative: "begin".into(),
            predecessors: vec![],
            successors: vec![NodeRef::Single("a".into())],
        });
        steps.insert("a".into(), StepDecl {
            performative: "a".into(),
            predecessors: vec![NodeRef::Single("begin".into())],
            successors: vec![NodeRef::Single("b".into())],
        });
        steps.insert("b".into(), StepDecl {
            performative: "b".into(),
            predecessors: vec![NodeRef::Single("a".into())],
            successors: vec![],
        });
        let proto = CausalProtocol { steps };
        let d = protocol_dialect(vec!["a", "b"], proto);
        assert!(verify_r5(&d));
    }

    #[test]
    fn cycle_in_protocol_fails_r5() {
        // a → b → a (cycle)
        let mut steps = BTreeMap::new();
        steps.insert("a".into(), StepDecl {
            performative: "a".into(),
            predecessors: vec![NodeRef::Single("b".into())],
            successors: vec![NodeRef::Single("b".into())],
        });
        steps.insert("b".into(), StepDecl {
            performative: "b".into(),
            predecessors: vec![NodeRef::Single("a".into())],
            successors: vec![NodeRef::Single("a".into())],
        });
        let proto = CausalProtocol { steps };
        let d = protocol_dialect(vec!["a", "b"], proto);
        assert!(!verify_r5(&d));
        let v = r5_violations(&d);
        assert!(v.iter().any(|s| s.contains("cycle")));
    }

    #[test]
    fn unreachable_step_fails_r5() {
        let mut steps = BTreeMap::new();
        steps.insert("begin".into(), StepDecl {
            performative: "begin".into(),
            predecessors: vec![],
            successors: vec![NodeRef::Single("a".into())],
        });
        steps.insert("a".into(), StepDecl {
            performative: "a".into(),
            predecessors: vec![NodeRef::Single("begin".into())],
            successors: vec![],
        });
        steps.insert("orphan".into(), StepDecl {
            performative: "orphan".into(),
            predecessors: vec![],
            successors: vec![],
        });
        let proto = CausalProtocol { steps };
        let d = protocol_dialect(vec!["a", "orphan"], proto);
        assert!(!verify_r5(&d));
        let v = r5_violations(&d);
        assert!(v.iter().any(|s| s.contains("unreachable")));
    }

    #[test]
    fn undefined_performative_fails_r5() {
        // Protocol references "track-ack" but dialect doesn't define it
        let mut steps = BTreeMap::new();
        steps.insert("begin".into(), StepDecl {
            performative: "begin".into(),
            predecessors: vec![],
            successors: vec![NodeRef::Single("track-ack".into())],
        });
        steps.insert("track-ack".into(), StepDecl {
            performative: "track-ack".into(),
            predecessors: vec![NodeRef::Single("begin".into())],
            successors: vec![],
        });
        let proto = CausalProtocol { steps };
        // "track-ack" is not in the performatives list
        let d = protocol_dialect(vec!["something-else"], proto);
        assert!(!verify_r5(&d));
        let v = r5_violations(&d);
        assert!(v.iter().any(|s| s.contains("not defined")));
    }

    #[test]
    fn no_protocol_passes_r5() {
        let d = test_dialect(vec!["propose-step"], vec![]);
        assert!(verify_r5(&d));
    }
}
