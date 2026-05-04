//! Structural shape constraints for dialect messages (REQ-220, REQ-223, REQ-224).
//!
//! Shape constraints declare the required structure of expanded messages:
//! which keyword parameters must or may be present, their expected atom types,
//! and maximum nesting depth.
//!
//! Shape checking is monotonic — it is a positive assertion about the structure
//! of an immutable S-expression. VPL ⊂ DCFL (Alur & Madhusudan 2004).

#![forbid(unsafe_code)]

use crate::sexpr::{Atom, SExpr};
use alloc::string::String;
use alloc::vec::Vec;
use core::fmt;

/// The six recognised type constraints for shape rules (REQ-221).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum TypeConstraint {
    String,
    Number,
    Bool,
    Symbol,
    Keyword,
    List,
}

impl TypeConstraint {
    /// Parse a type constraint from a symbol name.
    pub fn from_str(s: &str) -> Option<TypeConstraint> {
        match s {
            "string" => Some(TypeConstraint::String),
            "number" => Some(TypeConstraint::Number),
            "bool" => Some(TypeConstraint::Bool),
            "symbol" => Some(TypeConstraint::Symbol),
            "keyword" => Some(TypeConstraint::Keyword),
            "list" => Some(TypeConstraint::List),
            _ => None,
        }
    }

    /// Check whether an S-expression satisfies this type constraint.
    pub fn matches(&self, sexpr: &SExpr) -> bool {
        match (self, sexpr) {
            (TypeConstraint::String, SExpr::Atom(Atom::Str(_))) => true,
            (TypeConstraint::Number, SExpr::Atom(Atom::Num(_))) => true,
            (TypeConstraint::Bool, SExpr::Atom(Atom::Bool(_))) => true,
            (TypeConstraint::Symbol, SExpr::Atom(Atom::Symbol(_))) => true,
            (TypeConstraint::Keyword, SExpr::Atom(Atom::Keyword(_))) => true,
            (TypeConstraint::List, SExpr::List(_)) => true,
            _ => false,
        }
    }
}

impl fmt::Display for TypeConstraint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            TypeConstraint::String => "string",
            TypeConstraint::Number => "number",
            TypeConstraint::Bool => "bool",
            TypeConstraint::Symbol => "symbol",
            TypeConstraint::Keyword => "keyword",
            TypeConstraint::List => "list",
        };
        f.write_str(s)
    }
}

/// A single shape rule within a shape constraint (REQ-221).
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ShapeRule {
    /// A required keyword parameter.
    Require {
        keyword: String,
        type_constraint: Option<TypeConstraint>,
        children: Vec<ShapeRule>,
    },
    /// An optional keyword parameter with an optional default value.
    Optional {
        keyword: String,
        type_constraint: Option<TypeConstraint>,
        default: Option<SExpr>,
        children: Vec<ShapeRule>,
    },
    /// Maximum nesting depth for the message.
    MaxDepth(u32),
}

/// A shape constraint for a performative (REQ-220).
///
/// Declares the required structure of expanded messages for a specific
/// performative. Multiple shape constraints on the same performative
/// compose via conjunction (REQ-224).
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ShapeConstraint {
    /// The performative this shape constrains.
    pub performative: String,
    /// The rules that expanded messages must satisfy.
    pub rules: Vec<ShapeRule>,
}

/// A violation found during shape checking (REQ-223).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ShapeViolation {
    pub rule: String,
    pub field: Option<String>,
    pub expected: Option<String>,
    pub found: Option<String>,
    pub detail: String,
}

impl fmt::Display for ShapeViolation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "shape violation: {}", self.detail)
    }
}

impl ShapeConstraint {
    /// Check an expanded S-expression against this shape constraint (REQ-223).
    ///
    /// The `sexpr` should be the fully expanded message (after template expansion).
    /// Returns `Ok(())` if all rules are satisfied, or `Err` with the first violation.
    pub fn check(&self, sexpr: &SExpr) -> Result<(), ShapeViolation> {
        for rule in &self.rules {
            check_rule(rule, sexpr)?;
        }
        Ok(())
    }

    /// Check whether this constraint has any duplicate require/optional keywords
    /// at the same depth (REQ-222 §5).
    pub fn no_duplicate_keywords(&self) -> Result<(), String> {
        check_duplicate_keywords(&self.rules)
    }

    /// Return the first declared max-depth bound, if any.
    ///
    /// Prefer [`max_depths`](Self::max_depths) when validating every declared
    /// bound (e.g. the R5 install-time check); this accessor is retained for
    /// callers that only want a single representative bound.
    pub fn max_depth(&self) -> Option<u32> {
        self.max_depths().next()
    }

    /// Iterate over every `(max-depth …)` bound declared on this shape.
    ///
    /// A shape may declare more than one `MaxDepth` rule; install-time R5
    /// (REQ-222 §4) must check every bound against the dialect's R2 limit
    /// rather than only the first.
    pub fn max_depths(&self) -> impl Iterator<Item = u32> + '_ {
        self.rules.iter().filter_map(|r| match r {
            ShapeRule::MaxDepth(d) => Some(*d),
            _ => None,
        })
    }
}

/// Check a single rule against an S-expression.
fn check_rule(rule: &ShapeRule, sexpr: &SExpr) -> Result<(), ShapeViolation> {
    match rule {
        ShapeRule::Require {
            keyword,
            type_constraint,
            children,
        } => {
            let value = find_keyword_value(sexpr, keyword).ok_or_else(|| ShapeViolation {
                rule: alloc::format!("require :{keyword}"),
                field: Some(alloc::format!(":{keyword}")),
                expected: Some(String::from("present")),
                found: Some(String::from("missing")),
                detail: alloc::format!("required parameter :{keyword} is missing"),
            })?;
            if let Some(tc) = type_constraint {
                if !tc.matches(value) {
                    return Err(ShapeViolation {
                        rule: alloc::format!("require :{keyword} {tc}"),
                        field: Some(alloc::format!(":{keyword}")),
                        expected: Some(alloc::format!("{tc}")),
                        found: Some(describe_type(value)),
                        detail: alloc::format!(
                            "parameter :{keyword} expected type {tc}, found {}",
                            describe_type(value)
                        ),
                    });
                }
            }
            for child in children {
                check_rule(child, value)?;
            }
            Ok(())
        }
        ShapeRule::Optional {
            keyword,
            type_constraint,
            children,
            ..
        } => {
            if let Some(value) = find_keyword_value(sexpr, keyword) {
                if let Some(tc) = type_constraint {
                    if !tc.matches(value) {
                        return Err(ShapeViolation {
                            rule: alloc::format!("optional :{keyword} {tc}"),
                            field: Some(alloc::format!(":{keyword}")),
                            expected: Some(alloc::format!("{tc}")),
                            found: Some(describe_type(value)),
                            detail: alloc::format!(
                                "parameter :{keyword} expected type {tc}, found {}",
                                describe_type(value)
                            ),
                        });
                    }
                }
                for child in children {
                    check_rule(child, value)?;
                }
            }
            Ok(())
        }
        ShapeRule::MaxDepth(max) => {
            let depth = sexpr.depth() as u32;
            if depth > *max {
                Err(ShapeViolation {
                    rule: alloc::format!("max-depth {max}"),
                    field: None,
                    expected: Some(alloc::format!("<= {max}")),
                    found: Some(alloc::format!("{depth}")),
                    detail: alloc::format!("message depth {depth} exceeds max-depth {max}"),
                })
            } else {
                Ok(())
            }
        }
    }
}

/// Find the value following a keyword in an S-expression list.
///
/// Scans `(performative ... :keyword value ...)` and returns `value`.
fn find_keyword_value<'a>(sexpr: &'a SExpr, keyword: &str) -> Option<&'a SExpr> {
    let items = match sexpr {
        SExpr::List(items) => items,
        _ => return None,
    };
    let mut i = 0;
    while i < items.len() {
        if let SExpr::Atom(Atom::Keyword(k)) = &items[i] {
            if k == keyword {
                return items.get(i + 1);
            }
        }
        i += 1;
    }
    None
}

/// Describe the type of an S-expression value for error messages.
fn describe_type(sexpr: &SExpr) -> String {
    match sexpr {
        SExpr::Atom(Atom::Str(_)) => String::from("string"),
        SExpr::Atom(Atom::Num(_)) => String::from("number"),
        SExpr::Atom(Atom::Bool(_)) => String::from("bool"),
        SExpr::Atom(Atom::Symbol(_)) => String::from("symbol"),
        SExpr::Atom(Atom::Keyword(_)) => String::from("keyword"),
        SExpr::List(_) => String::from("list"),
    }
}

/// Check for duplicate require/optional keywords within the same parent
/// scope (REQ-222 §5).
///
/// Each `(...)` list in an expanded message has its own keyword namespace
/// (see `find_keyword_value` and the `Require` arm of `check_rule`, which
/// recurses children against the matched parent's value). The static check
/// mirrors that scoping: duplicates are sibling rules under the same
/// parent, not arbitrary co-depth rules across independent subtrees.
fn check_duplicate_keywords(rules: &[ShapeRule]) -> Result<(), String> {
    walk_keywords(rules, 0)
}

fn walk_keywords(rules: &[ShapeRule], depth: usize) -> Result<(), String> {
    let mut seen: alloc::collections::BTreeSet<String> = alloc::collections::BTreeSet::new();
    for rule in rules {
        let (keyword, children) = match rule {
            ShapeRule::Require {
                keyword, children, ..
            }
            | ShapeRule::Optional {
                keyword, children, ..
            } => (keyword, children),
            ShapeRule::MaxDepth(_) => continue,
        };
        if !seen.insert(keyword.clone()) {
            return Err(alloc::format!(
                "duplicate keyword :{keyword} at depth {depth}"
            ));
        }
        walk_keywords(children, depth + 1)?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::string::ToString;
    use alloc::vec;

    fn sym(s: &str) -> SExpr {
        SExpr::Atom(Atom::Symbol(String::from(s)))
    }

    fn kw(s: &str) -> SExpr {
        SExpr::Atom(Atom::Keyword(String::from(s)))
    }

    fn str_expr(s: &str) -> SExpr {
        SExpr::Atom(Atom::Str(String::from(s)))
    }

    fn num(n: i64) -> SExpr {
        SExpr::Atom(Atom::Num(n))
    }

    fn list(items: Vec<SExpr>) -> SExpr {
        SExpr::List(items)
    }

    // -- TypeConstraint tests --

    #[test]
    fn type_constraint_from_str() {
        assert_eq!(
            TypeConstraint::from_str("string"),
            Some(TypeConstraint::String)
        );
        assert_eq!(
            TypeConstraint::from_str("number"),
            Some(TypeConstraint::Number)
        );
        assert_eq!(TypeConstraint::from_str("bool"), Some(TypeConstraint::Bool));
        assert_eq!(
            TypeConstraint::from_str("symbol"),
            Some(TypeConstraint::Symbol)
        );
        assert_eq!(
            TypeConstraint::from_str("keyword"),
            Some(TypeConstraint::Keyword)
        );
        assert_eq!(TypeConstraint::from_str("list"), Some(TypeConstraint::List));
        assert_eq!(TypeConstraint::from_str("unknown"), None);
    }

    #[test]
    fn type_constraint_matches() {
        assert!(TypeConstraint::String.matches(&str_expr("hello")));
        assert!(!TypeConstraint::String.matches(&num(42)));
        assert!(TypeConstraint::Number.matches(&num(42)));
        assert!(TypeConstraint::Bool.matches(&SExpr::Atom(Atom::Bool(true))));
        assert!(TypeConstraint::Symbol.matches(&sym("x")));
        assert!(TypeConstraint::Keyword.matches(&kw("key")));
        assert!(TypeConstraint::List.matches(&list(vec![sym("a")])));
        assert!(!TypeConstraint::List.matches(&sym("a")));
    }

    #[test]
    fn type_constraint_display() {
        assert_eq!(TypeConstraint::String.to_string(), "string");
        assert_eq!(TypeConstraint::Number.to_string(), "number");
        assert_eq!(TypeConstraint::List.to_string(), "list");
    }

    // -- ShapeConstraint::check tests --

    #[test]
    fn check_require_present() {
        let shape = ShapeConstraint {
            performative: String::from("track-shipment"),
            rules: vec![ShapeRule::Require {
                keyword: String::from("package"),
                type_constraint: Some(TypeConstraint::String),
                children: vec![],
            }],
        };
        let msg = list(vec![
            sym("track-shipment"),
            kw("package"),
            str_expr("box-1"),
        ]);
        assert!(shape.check(&msg).is_ok());
    }

    #[test]
    fn check_require_missing() {
        let shape = ShapeConstraint {
            performative: String::from("track-shipment"),
            rules: vec![ShapeRule::Require {
                keyword: String::from("package"),
                type_constraint: Some(TypeConstraint::String),
                children: vec![],
            }],
        };
        let msg = list(vec![sym("track-shipment"), kw("route"), str_expr("A-B")]);
        let err = shape.check(&msg).unwrap_err();
        assert_eq!(err.field, Some(String::from(":package")));
        assert!(err.detail.contains("missing"));
    }

    #[test]
    fn check_require_wrong_type() {
        let shape = ShapeConstraint {
            performative: String::from("track-shipment"),
            rules: vec![ShapeRule::Require {
                keyword: String::from("package"),
                type_constraint: Some(TypeConstraint::String),
                children: vec![],
            }],
        };
        let msg = list(vec![sym("track-shipment"), kw("package"), num(42)]);
        let err = shape.check(&msg).unwrap_err();
        assert_eq!(err.expected, Some(String::from("string")));
        assert_eq!(err.found, Some(String::from("number")));
    }

    #[test]
    fn check_optional_absent_ok() {
        let shape = ShapeConstraint {
            performative: String::from("track-shipment"),
            rules: vec![ShapeRule::Optional {
                keyword: String::from("priority"),
                type_constraint: Some(TypeConstraint::String),
                default: Some(str_expr("normal")),
                children: vec![],
            }],
        };
        let msg = list(vec![sym("track-shipment")]);
        assert!(shape.check(&msg).is_ok());
    }

    #[test]
    fn check_optional_present_wrong_type() {
        let shape = ShapeConstraint {
            performative: String::from("track-shipment"),
            rules: vec![ShapeRule::Optional {
                keyword: String::from("priority"),
                type_constraint: Some(TypeConstraint::String),
                default: None,
                children: vec![],
            }],
        };
        let msg = list(vec![sym("track-shipment"), kw("priority"), num(1)]);
        let err = shape.check(&msg).unwrap_err();
        assert_eq!(err.expected, Some(String::from("string")));
    }

    #[test]
    fn check_max_depth_ok() {
        let shape = ShapeConstraint {
            performative: String::from("test"),
            rules: vec![ShapeRule::MaxDepth(4)],
        };
        // depth 1: (test :a "b")
        let msg = list(vec![sym("test"), kw("a"), str_expr("b")]);
        assert!(shape.check(&msg).is_ok());
    }

    #[test]
    fn check_max_depth_exceeded() {
        let shape = ShapeConstraint {
            performative: String::from("test"),
            rules: vec![ShapeRule::MaxDepth(1)],
        };
        // depth 2: (test (nested (deep)))
        let msg = list(vec![
            sym("test"),
            list(vec![sym("nested"), list(vec![sym("deep")])]),
        ]);
        let err = shape.check(&msg).unwrap_err();
        assert!(err.detail.contains("exceeds"));
    }

    #[test]
    fn check_nested_children() {
        // (shape propose-step
        //   (require :params list
        //     (require :target string)))
        let shape = ShapeConstraint {
            performative: String::from("propose-step"),
            rules: vec![ShapeRule::Require {
                keyword: String::from("params"),
                type_constraint: Some(TypeConstraint::List),
                children: vec![ShapeRule::Require {
                    keyword: String::from("target"),
                    type_constraint: Some(TypeConstraint::String),
                    children: vec![],
                }],
            }],
        };
        let msg = list(vec![
            sym("propose-step"),
            kw("params"),
            list(vec![kw("target"), str_expr("server-1")]),
        ]);
        assert!(shape.check(&msg).is_ok());
    }

    #[test]
    fn check_nested_children_missing_inner() {
        let shape = ShapeConstraint {
            performative: String::from("propose-step"),
            rules: vec![ShapeRule::Require {
                keyword: String::from("params"),
                type_constraint: Some(TypeConstraint::List),
                children: vec![ShapeRule::Require {
                    keyword: String::from("target"),
                    type_constraint: Some(TypeConstraint::String),
                    children: vec![],
                }],
            }],
        };
        let msg = list(vec![
            sym("propose-step"),
            kw("params"),
            list(vec![kw("other"), str_expr("x")]),
        ]);
        let err = shape.check(&msg).unwrap_err();
        assert!(err.detail.contains(":target"));
    }

    // -- no_duplicate_keywords tests --

    #[test]
    fn no_duplicate_keywords_ok() {
        let shape = ShapeConstraint {
            performative: String::from("test"),
            rules: vec![
                ShapeRule::Require {
                    keyword: String::from("a"),
                    type_constraint: None,
                    children: vec![],
                },
                ShapeRule::Optional {
                    keyword: String::from("b"),
                    type_constraint: None,
                    default: None,
                    children: vec![],
                },
            ],
        };
        assert!(shape.no_duplicate_keywords().is_ok());
    }

    #[test]
    fn no_duplicate_keywords_allows_shared_child_under_different_parents() {
        // Children rules are scoped to the matched parent list at runtime
        // (see `check_rule` Require branch), so `:x` under `:a` and `:x`
        // under `:b` live in independent keyword namespaces and must not
        // be reported as duplicates. Mirrors the pickup/dropoff :id pattern
        // that motivated this regression.
        let shape = ShapeConstraint {
            performative: String::from("test"),
            rules: vec![
                ShapeRule::Require {
                    keyword: String::from("a"),
                    type_constraint: Some(TypeConstraint::List),
                    children: vec![ShapeRule::Require {
                        keyword: String::from("x"),
                        type_constraint: None,
                        children: vec![],
                    }],
                },
                ShapeRule::Require {
                    keyword: String::from("b"),
                    type_constraint: Some(TypeConstraint::List),
                    children: vec![ShapeRule::Require {
                        keyword: String::from("x"),
                        type_constraint: None,
                        children: vec![],
                    }],
                },
            ],
        };
        assert!(shape.no_duplicate_keywords().is_ok());
    }

    #[test]
    fn no_duplicate_keywords_detects_duplicate_within_same_parent() {
        // Two child rules with the same keyword under the same parent
        // collide at runtime (they target the same value slot of `:a`),
        // so R5 must reject this even though the duplicates are nested.
        let shape = ShapeConstraint {
            performative: String::from("test"),
            rules: vec![ShapeRule::Require {
                keyword: String::from("a"),
                type_constraint: Some(TypeConstraint::List),
                children: vec![
                    ShapeRule::Require {
                        keyword: String::from("x"),
                        type_constraint: None,
                        children: vec![],
                    },
                    ShapeRule::Optional {
                        keyword: String::from("x"),
                        type_constraint: None,
                        default: None,
                        children: vec![],
                    },
                ],
            }],
        };
        let err = shape.no_duplicate_keywords().unwrap_err();
        assert!(err.contains(":x"), "expected :x to be flagged: {err}");
        assert!(err.contains("depth 1"), "expected depth in error: {err}");
    }

    #[test]
    fn no_duplicate_keywords_detects_duplicate() {
        let shape = ShapeConstraint {
            performative: String::from("test"),
            rules: vec![
                ShapeRule::Require {
                    keyword: String::from("a"),
                    type_constraint: None,
                    children: vec![],
                },
                ShapeRule::Optional {
                    keyword: String::from("a"),
                    type_constraint: None,
                    default: None,
                    children: vec![],
                },
            ],
        };
        let err = shape.no_duplicate_keywords().unwrap_err();
        assert!(err.contains(":a"));
    }

    // -- max_depth accessor --

    #[test]
    fn max_depth_accessor() {
        let shape = ShapeConstraint {
            performative: String::from("test"),
            rules: vec![
                ShapeRule::Require {
                    keyword: String::from("a"),
                    type_constraint: None,
                    children: vec![],
                },
                ShapeRule::MaxDepth(6),
            ],
        };
        assert_eq!(shape.max_depth(), Some(6));
    }

    #[test]
    fn max_depth_none() {
        let shape = ShapeConstraint {
            performative: String::from("test"),
            rules: vec![],
        };
        assert_eq!(shape.max_depth(), None);
    }

    // -- Composition via conjunction (REQ-224) --

    #[test]
    fn multiple_shapes_compose_via_conjunction() {
        let shape1 = ShapeConstraint {
            performative: String::from("track"),
            rules: vec![ShapeRule::Require {
                keyword: String::from("package"),
                type_constraint: Some(TypeConstraint::String),
                children: vec![],
            }],
        };
        let shape2 = ShapeConstraint {
            performative: String::from("track"),
            rules: vec![ShapeRule::Require {
                keyword: String::from("route"),
                type_constraint: Some(TypeConstraint::String),
                children: vec![],
            }],
        };
        // Must satisfy both
        let msg = list(vec![
            sym("track"),
            kw("package"),
            str_expr("box-1"),
            kw("route"),
            str_expr("A-B"),
        ]);
        assert!(shape1.check(&msg).is_ok());
        assert!(shape2.check(&msg).is_ok());

        // Missing route fails shape2
        let partial = list(vec![sym("track"), kw("package"), str_expr("box-1")]);
        assert!(shape1.check(&partial).is_ok());
        assert!(shape2.check(&partial).is_err());
    }

    // -- ShapeViolation display --

    #[test]
    fn shape_violation_display() {
        let v = ShapeViolation {
            rule: String::from("require :package string"),
            field: Some(String::from(":package")),
            expected: Some(String::from("string")),
            found: Some(String::from("number")),
            detail: String::from("parameter :package expected type string, found number"),
        };
        let s = v.to_string();
        assert!(s.contains("shape violation"));
        assert!(s.contains(":package"));
    }

    // -- find_keyword_value on non-list --

    #[test]
    fn check_on_atom_fails_for_require() {
        let shape = ShapeConstraint {
            performative: String::from("test"),
            rules: vec![ShapeRule::Require {
                keyword: String::from("a"),
                type_constraint: None,
                children: vec![],
            }],
        };
        assert!(shape.check(&sym("not-a-list")).is_err());
    }

    // -- Require without type constraint --

    #[test]
    fn require_without_type_constraint() {
        let shape = ShapeConstraint {
            performative: String::from("test"),
            rules: vec![ShapeRule::Require {
                keyword: String::from("data"),
                type_constraint: None,
                children: vec![],
            }],
        };
        // Any type of value is accepted
        let msg = list(vec![sym("test"), kw("data"), num(42)]);
        assert!(shape.check(&msg).is_ok());
    }
}
