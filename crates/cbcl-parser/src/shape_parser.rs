//! Shape constraint parser (REQ-221).
//!
//! Parses `(shape performative-name rule...)` S-expressions into
//! [`ShapeConstraint`] values.

#![forbid(unsafe_code)]

use alloc::string::String;
use alloc::vec::Vec;
use cbcl_core::sexpr::{Atom, SExpr};
use cbcl_core::shape::{ShapeConstraint, ShapeRule, TypeConstraint};

/// Parse a `(shape performative-name rule...)` S-expression into a [`ShapeConstraint`] (REQ-221).
///
/// Grammar:
/// ```text
/// shape-clause = "(" "shape" performative-name 1*(shape-rule) ")"
/// shape-rule   = require-rule / optional-rule / max-depth-rule
/// ```
pub fn parse_shape(sexpr: &SExpr) -> Result<ShapeConstraint, String> {
    let items = match sexpr {
        SExpr::List(items) => items,
        _ => return Err(String::from("shape clause must be a list")),
    };

    if items.len() < 3 {
        return Err(String::from(
            "shape clause requires at least: shape, performative-name, rule",
        ));
    }

    if !items[0].is_symbol("shape") {
        return Err(String::from("shape clause must start with 'shape'"));
    }

    let performative = match &items[1] {
        SExpr::Atom(Atom::Symbol(s)) => s.clone(),
        _ => return Err(String::from("performative name must be a symbol")),
    };

    let mut rules = Vec::new();
    for item in &items[2..] {
        rules.push(parse_shape_rule(item)?);
    }

    Ok(ShapeConstraint {
        performative,
        rules,
    })
}

/// Parse a single shape rule.
fn parse_shape_rule(sexpr: &SExpr) -> Result<ShapeRule, String> {
    let items = match sexpr {
        SExpr::List(items) if !items.is_empty() => items,
        _ => return Err(String::from("shape rule must be a non-empty list")),
    };

    let head = match &items[0] {
        SExpr::Atom(Atom::Symbol(s)) => s.as_str(),
        _ => return Err(String::from("shape rule must start with a symbol")),
    };

    match head {
        "require" => parse_require_rule(items),
        "optional" => parse_optional_rule(items),
        "max-depth" => parse_max_depth_rule(items),
        other => Err(alloc::format!("unknown shape rule: {other}")),
    }
}

/// Parse `(require :keyword [type-constraint] [child-rules...])`.
fn parse_require_rule(items: &[SExpr]) -> Result<ShapeRule, String> {
    if items.len() < 2 {
        return Err(String::from("require rule needs at least a keyword"));
    }

    let keyword = extract_keyword(&items[1])?;
    let mut idx = 2;
    let type_constraint = extract_type_constraint_at(items, &mut idx);
    let children = parse_child_rules(items, idx)?;

    Ok(ShapeRule::Require {
        keyword,
        type_constraint,
        children,
    })
}

/// Parse `(optional :keyword [type-constraint] [default-value] [child-rules...])`.
fn parse_optional_rule(items: &[SExpr]) -> Result<ShapeRule, String> {
    if items.len() < 2 {
        return Err(String::from("optional rule needs at least a keyword"));
    }

    let keyword = extract_keyword(&items[1])?;
    let mut idx = 2;
    let type_constraint = extract_type_constraint_at(items, &mut idx);

    // Default value: any non-list S-expression that isn't a type constraint symbol
    // or a child rule list. We consume it if it's an atom (not a list starting with
    // require/optional/max-depth).
    let default = extract_default_value(items, &mut idx);
    let children = parse_child_rules(items, idx)?;

    Ok(ShapeRule::Optional {
        keyword,
        type_constraint,
        default,
        children,
    })
}

/// Parse `(max-depth N)`.
fn parse_max_depth_rule(items: &[SExpr]) -> Result<ShapeRule, String> {
    if items.len() != 2 {
        return Err(String::from("max-depth rule requires exactly one number"));
    }
    match &items[1] {
        SExpr::Atom(Atom::Num(n)) if *n > 0 => Ok(ShapeRule::MaxDepth(*n as u32)),
        SExpr::Atom(Atom::Num(n)) => Err(alloc::format!("max-depth must be positive, got {n}")),
        _ => Err(String::from("max-depth value must be a number")),
    }
}

/// Extract a keyword name from a keyword S-expression.
fn extract_keyword(sexpr: &SExpr) -> Result<String, String> {
    match sexpr {
        SExpr::Atom(Atom::Keyword(k)) => Ok(k.clone()),
        _ => Err(String::from("expected a keyword (e.g. :name)")),
    }
}

/// Try to extract a type constraint at position `idx`, advancing `idx` if found.
fn extract_type_constraint_at(items: &[SExpr], idx: &mut usize) -> Option<TypeConstraint> {
    if *idx < items.len() {
        if let SExpr::Atom(Atom::Symbol(s)) = &items[*idx] {
            if let Some(tc) = TypeConstraint::from_str(s) {
                *idx += 1;
                return Some(tc);
            }
        }
    }
    None
}

/// Try to extract a default value at position `idx`, advancing `idx` if found.
///
/// A default value is any S-expression that is not a child rule (i.e., not a list
/// starting with require/optional/max-depth).
fn extract_default_value(items: &[SExpr], idx: &mut usize) -> Option<SExpr> {
    if *idx >= items.len() {
        return None;
    }
    // If it's a list that looks like a child rule, don't consume it as a default.
    if is_child_rule(&items[*idx]) {
        return None;
    }
    // Consume as default value.
    let val = items[*idx].clone();
    *idx += 1;
    Some(val)
}

/// Check if an S-expression looks like a child shape rule.
fn is_child_rule(sexpr: &SExpr) -> bool {
    if let SExpr::List(items) = sexpr {
        if let Some(SExpr::Atom(Atom::Symbol(s))) = items.first() {
            return matches!(s.as_str(), "require" | "optional" | "max-depth");
        }
    }
    false
}

/// Parse remaining items as child rules.
fn parse_child_rules(items: &[SExpr], start: usize) -> Result<Vec<ShapeRule>, String> {
    let mut children = Vec::new();
    for item in &items[start..] {
        children.push(parse_shape_rule(item)?);
    }
    Ok(children)
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec;

    fn sym(s: &str) -> SExpr {
        SExpr::Atom(Atom::Symbol(String::from(s)))
    }

    fn kw(s: &str) -> SExpr {
        SExpr::Atom(Atom::Keyword(String::from(s)))
    }

    fn num(n: i64) -> SExpr {
        SExpr::Atom(Atom::Num(n))
    }

    fn str_expr(s: &str) -> SExpr {
        SExpr::Atom(Atom::Str(String::from(s)))
    }

    fn list(items: Vec<SExpr>) -> SExpr {
        SExpr::List(items)
    }

    // -- Basic parsing --

    #[test]
    fn parse_simple_shape() {
        // (shape track-shipment (require :package string) (require :route string))
        let sexpr = list(vec![
            sym("shape"),
            sym("track-shipment"),
            list(vec![sym("require"), kw("package"), sym("string")]),
            list(vec![sym("require"), kw("route"), sym("string")]),
        ]);
        let shape = parse_shape(&sexpr).unwrap();
        assert_eq!(shape.performative, "track-shipment");
        assert_eq!(shape.rules.len(), 2);

        match &shape.rules[0] {
            ShapeRule::Require {
                keyword,
                type_constraint,
                children,
            } => {
                assert_eq!(keyword, "package");
                assert_eq!(*type_constraint, Some(TypeConstraint::String));
                assert!(children.is_empty());
            }
            _ => panic!("expected Require rule"),
        }
    }

    #[test]
    fn parse_shape_with_optional_and_default() {
        // (shape track-shipment
        //   (require :package string)
        //   (optional :priority string "normal")
        //   (max-depth 4))
        let sexpr = list(vec![
            sym("shape"),
            sym("track-shipment"),
            list(vec![sym("require"), kw("package"), sym("string")]),
            list(vec![
                sym("optional"),
                kw("priority"),
                sym("string"),
                str_expr("normal"),
            ]),
            list(vec![sym("max-depth"), num(4)]),
        ]);
        let shape = parse_shape(&sexpr).unwrap();
        assert_eq!(shape.performative, "track-shipment");
        assert_eq!(shape.rules.len(), 3);

        match &shape.rules[1] {
            ShapeRule::Optional {
                keyword,
                type_constraint,
                default,
                children,
            } => {
                assert_eq!(keyword, "priority");
                assert_eq!(*type_constraint, Some(TypeConstraint::String));
                assert_eq!(*default, Some(str_expr("normal")));
                assert!(children.is_empty());
            }
            _ => panic!("expected Optional rule"),
        }

        match &shape.rules[2] {
            ShapeRule::MaxDepth(d) => assert_eq!(*d, 4),
            _ => panic!("expected MaxDepth rule"),
        }
    }

    #[test]
    fn parse_shape_with_nested_rules() {
        // (shape propose-step
        //   (require :action symbol)
        //   (require :params list
        //     (require :target string)
        //     (optional :deadline string))
        //   (max-depth 6))
        let sexpr = list(vec![
            sym("shape"),
            sym("propose-step"),
            list(vec![sym("require"), kw("action"), sym("symbol")]),
            list(vec![
                sym("require"),
                kw("params"),
                sym("list"),
                list(vec![sym("require"), kw("target"), sym("string")]),
                list(vec![sym("optional"), kw("deadline"), sym("string")]),
            ]),
            list(vec![sym("max-depth"), num(6)]),
        ]);
        let shape = parse_shape(&sexpr).unwrap();
        assert_eq!(shape.rules.len(), 3);

        match &shape.rules[1] {
            ShapeRule::Require {
                keyword,
                type_constraint,
                children,
            } => {
                assert_eq!(keyword, "params");
                assert_eq!(*type_constraint, Some(TypeConstraint::List));
                assert_eq!(children.len(), 2);
            }
            _ => panic!("expected Require with children"),
        }
    }

    #[test]
    fn parse_require_without_type() {
        let sexpr = list(vec![
            sym("shape"),
            sym("test"),
            list(vec![sym("require"), kw("data")]),
        ]);
        let shape = parse_shape(&sexpr).unwrap();
        match &shape.rules[0] {
            ShapeRule::Require {
                keyword,
                type_constraint,
                ..
            } => {
                assert_eq!(keyword, "data");
                assert_eq!(*type_constraint, None);
            }
            _ => panic!("expected Require"),
        }
    }

    #[test]
    fn parse_optional_without_default() {
        let sexpr = list(vec![
            sym("shape"),
            sym("test"),
            list(vec![sym("optional"), kw("notes"), sym("string")]),
        ]);
        let shape = parse_shape(&sexpr).unwrap();
        match &shape.rules[0] {
            ShapeRule::Optional {
                keyword,
                type_constraint,
                default,
                ..
            } => {
                assert_eq!(keyword, "notes");
                assert_eq!(*type_constraint, Some(TypeConstraint::String));
                assert_eq!(*default, None);
            }
            _ => panic!("expected Optional"),
        }
    }

    // -- Error cases --

    #[test]
    fn reject_non_list() {
        assert!(parse_shape(&sym("not-a-list")).is_err());
    }

    #[test]
    fn reject_too_short() {
        let sexpr = list(vec![sym("shape"), sym("test")]);
        assert!(parse_shape(&sexpr).is_err());
    }

    #[test]
    fn reject_wrong_head() {
        let sexpr = list(vec![
            sym("not-shape"),
            sym("test"),
            list(vec![sym("require"), kw("a")]),
        ]);
        assert!(parse_shape(&sexpr).is_err());
    }

    #[test]
    fn reject_unknown_rule() {
        let sexpr = list(vec![
            sym("shape"),
            sym("test"),
            list(vec![sym("unknown-rule"), kw("a")]),
        ]);
        assert!(parse_shape(&sexpr).is_err());
    }

    #[test]
    fn reject_max_depth_zero() {
        let sexpr = list(vec![
            sym("shape"),
            sym("test"),
            list(vec![sym("max-depth"), num(0)]),
        ]);
        assert!(parse_shape(&sexpr).is_err());
    }

    #[test]
    fn reject_max_depth_negative() {
        let sexpr = list(vec![
            sym("shape"),
            sym("test"),
            list(vec![sym("max-depth"), num(-1)]),
        ]);
        assert!(parse_shape(&sexpr).is_err());
    }

    #[test]
    fn reject_require_without_keyword() {
        let sexpr = list(vec![
            sym("shape"),
            sym("test"),
            list(vec![sym("require")]),
        ]);
        assert!(parse_shape(&sexpr).is_err());
    }

    #[test]
    fn reject_require_with_non_keyword() {
        let sexpr = list(vec![
            sym("shape"),
            sym("test"),
            list(vec![sym("require"), sym("not-a-keyword")]),
        ]);
        assert!(parse_shape(&sexpr).is_err());
    }

    // -- Round-trip from text --

    #[test]
    fn parse_from_text() {
        let input = "(shape track-shipment (require :package string) (optional :priority string \"normal\") (max-depth 4))";
        let sexpr: SExpr = input.parse().unwrap();
        let shape = parse_shape(&sexpr).unwrap();
        assert_eq!(shape.performative, "track-shipment");
        assert_eq!(shape.rules.len(), 3);
        assert_eq!(shape.max_depth(), Some(4));
        assert!(shape.no_duplicate_keywords().is_ok());
    }

    #[test]
    fn parse_nested_from_text() {
        let input = "(shape propose-step (require :action symbol) (require :params list (require :target string) (optional :deadline string)) (max-depth 6))";
        let sexpr: SExpr = input.parse().unwrap();
        let shape = parse_shape(&sexpr).unwrap();
        assert_eq!(shape.performative, "propose-step");
        assert_eq!(shape.rules.len(), 3);
        assert!(shape.no_duplicate_keywords().is_ok());
    }
}
