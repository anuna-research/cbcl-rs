//! Template expansion engine (REQ-100, REQ-101).
//!
//! Mirrors `TemplateExpansion.lean` from the Lean 4 proof library.
//!
//! Supports the following template forms:
//! - Plain expressions: substitute bindings into the expression
//! - `(literal expr)`: substitute bindings and return the inner expression
//! - `(cond (test body) ... (else body))`: conditional branching
//! - `(= var value)`: equality predicate
//! - `(member var (values...))`: membership predicate
//! - `(type? var type-name)`: type predicate (number, string, agent)
//! - Sequence templates: outer list of template forms producing multiple outputs

#![forbid(unsafe_code)]

use crate::dialect::PerformativeDef;
use crate::r2::ResourceState;
use crate::sexpr::{Atom, SExpr};
use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::vec::Vec;

/// Named bindings for template expansion: symbol name → value.
pub type Bindings = BTreeMap<String, SExpr>;

/// Result of template expansion: either a single expression or a sequence.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExpandedTemplate {
    Single(SExpr),
    Sequence(Vec<SExpr>),
}

/// Expand a template with argument substitutions (REQ-100).
///
/// Respects resource bounds (R2): tracks depth and byte-size (REQ-101).
pub fn expand_template(
    def: &PerformativeDef,
    args: &[SExpr],
    rs: &mut ResourceState,
) -> Option<SExpr> {
    let _start_depth = rs.current_depth;
    let bindings = build_bindings(&def.params, args);
    let result = match eval_template(&def.template, &bindings, rs)? {
        ExpandedTemplate::Single(expr) => Some(expr),
        ExpandedTemplate::Sequence(exprs) => Some(SExpr::List(exprs)),
    };
    #[cfg(feature = "tracing")]
    tracing::event!(
        tracing::Level::INFO,
        performative = %def.name,
        start_depth = _start_depth,
        final_depth = rs.current_depth,
        expansion_size = rs.expansion_size,
        "template_expand_depth"
    );
    result
}

/// Expand a template with named bindings (REQ-100).
///
/// Returns an [`ExpandedTemplate`] which may be a single expression or a
/// sequence of expressions. Respects R2 resource bounds.
pub fn expand_template_with_bindings(
    template: &SExpr,
    bindings: &Bindings,
    rs: &mut ResourceState,
) -> Option<ExpandedTemplate> {
    let _start_depth = rs.current_depth;
    let result = eval_template(template, bindings, rs);
    #[cfg(feature = "tracing")]
    tracing::event!(
        tracing::Level::INFO,
        start_depth = _start_depth,
        final_depth = rs.current_depth,
        expansion_size = rs.expansion_size,
        success = result.is_some(),
        "template_expand_depth"
    );
    result
}

/// Evaluate a type predicate: `(type? var type-name)`.
///
/// Supported type names: `number`, `string`, `agent`, `symbol`, `bool`.
/// Agent values are symbols starting with `@`.
pub fn eval_type_predicate(value: &SExpr, type_name: &str) -> bool {
    match type_name {
        "number" => matches!(value, SExpr::Atom(Atom::Num(_))),
        "string" => matches!(value, SExpr::Atom(Atom::Str(_))),
        "symbol" => matches!(value, SExpr::Atom(Atom::Symbol(_))),
        "bool" => matches!(value, SExpr::Atom(Atom::Bool(_))),
        "agent" => match value {
            SExpr::Atom(Atom::Symbol(s)) => s.starts_with('@'),
            _ => false,
        },
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Internal implementation
// ---------------------------------------------------------------------------

/// Build bindings from positional params and args.
fn build_bindings(params: &[SExpr], args: &[SExpr]) -> Bindings {
    let mut bindings = Bindings::new();
    for (param, arg) in params.iter().zip(args.iter()) {
        if let SExpr::Atom(Atom::Symbol(name)) = param {
            bindings.insert(name.clone(), arg.clone());
        }
    }
    bindings
}

/// Core template evaluation.
fn eval_template(
    template: &SExpr,
    bindings: &Bindings,
    rs: &mut ResourceState,
) -> Option<ExpandedTemplate> {
    let rs_inner = rs.enter_depth()?;
    *rs = rs_inner;

    let result = eval_form(template, bindings, rs)?;

    let size = match &result {
        ExpandedTemplate::Single(expr) => expr.byte_size() as u32,
        ExpandedTemplate::Sequence(exprs) => {
            exprs.iter().map(|e| e.byte_size() as u32).sum::<u32>()
        }
    };
    *rs = rs.add_expansion(size)?;

    // R2 depth accounting (REQ-071). `enter_depth` above charges one level
    // per template-recursion step, but a *substituted* argument subtree is
    // spliced into the output by `substitute_expr`/`substitute_atom` without
    // being walked level-by-level, so its own nesting is never charged. A
    // deeply nested argument could therefore blow past the dialect's
    // `max-depth` unchecked. Charge the ACTUAL post-substitution output AST
    // depth here — measured with the same `SExpr::depth()` used everywhere
    // else — so the effective output depth is what is bounded. For a
    // sequence each element is an independent output message, so the deepest
    // message governs. Reject when the output nests strictly deeper than
    // `max_depth` (accept `depth <= max_depth`): this is the R2 boundary the
    // mls-ds/v1 profile relies on — a depth-`max_depth` expansion is legal,
    // a deeper one is an R2 resource violation.
    let output_depth = match &result {
        ExpandedTemplate::Single(expr) => expr.depth(),
        ExpandedTemplate::Sequence(exprs) => exprs.iter().map(|e| e.depth()).max().unwrap_or(0),
    };
    if output_depth as u32 > rs.max_depth {
        return None;
    }

    Some(result)
}

/// Evaluate a template form, dispatching on the head symbol.
fn eval_form(
    template: &SExpr,
    bindings: &Bindings,
    rs: &mut ResourceState,
) -> Option<ExpandedTemplate> {
    match template {
        SExpr::Atom(_) => {
            let subst = substitute_atom(template, bindings);
            Some(ExpandedTemplate::Single(subst))
        }
        SExpr::List(items) if items.is_empty() => {
            Some(ExpandedTemplate::Single(SExpr::List(Vec::new())))
        }
        SExpr::List(items) => {
            // Check for special forms by head symbol
            if let Some(head) = items.first() {
                // (literal expr)
                if head.is_symbol("literal") {
                    return eval_literal(items, bindings);
                }
                // (cond (test body) ... (else body))
                if head.is_symbol("cond") {
                    return eval_cond(&items[1..], bindings, rs);
                }
            }

            // Check if this is a sequence of template forms:
            // A list where every element is itself a list starting with
            // `literal` or `cond` is treated as a sequence.
            if is_sequence_template(items) {
                return eval_sequence(items, bindings, rs);
            }

            // Plain expression: substitute bindings throughout
            let result = substitute_expr(template, bindings);
            Some(ExpandedTemplate::Single(result))
        }
    }
}

/// `(literal expr)` — substitute bindings in `expr` and return it.
fn eval_literal(items: &[SExpr], bindings: &Bindings) -> Option<ExpandedTemplate> {
    if items.len() != 2 {
        return None;
    }
    let body = substitute_expr(&items[1], bindings);
    Some(ExpandedTemplate::Single(body))
}

/// `(cond (test body) ... (else body))` — evaluate conditions in order.
fn eval_cond(
    clauses: &[SExpr],
    bindings: &Bindings,
    rs: &mut ResourceState,
) -> Option<ExpandedTemplate> {
    for clause in clauses {
        match clause {
            SExpr::List(parts) if parts.len() == 2 => {
                // Check for (else body) form
                if parts[0].is_symbol("else") {
                    return eval_form(&parts[1], bindings, rs);
                }
                // (test body) form
                let test = &parts[0];
                let body = &parts[1];
                if eval_condition(test, bindings) {
                    return eval_form(body, bindings, rs);
                }
            }
            // Single-element: treat as else clause
            _ if clause.is_symbol("else") => {
                // bare `else` without body — shouldn't happen in well-formed templates
                return None;
            }
            _ => return None,
        }
    }
    // No clause matched and no else — expansion fails
    None
}

/// Evaluate a condition expression, returning true/false.
fn eval_condition(condition: &SExpr, bindings: &Bindings) -> bool {
    match condition {
        SExpr::List(items) if items.len() == 3 => {
            // (= var value)
            if items[0].is_symbol("=") {
                let lhs = resolve_value(&items[1], bindings);
                let rhs = resolve_value(&items[2], bindings);
                return values_equal(&lhs, &rhs);
            }
            // (member var (values...))
            if items[0].is_symbol("member") {
                let value = resolve_value(&items[1], bindings);
                if let SExpr::List(members) = &items[2] {
                    return members
                        .iter()
                        .any(|m| values_equal(&value, &resolve_value(m, bindings)));
                }
                return false;
            }
            // (type? var type-name)
            if items[0].is_symbol("type?") {
                let value = resolve_value(&items[1], bindings);
                if let SExpr::Atom(Atom::Symbol(type_name)) = &items[2] {
                    return eval_type_predicate(&value, type_name);
                }
                return false;
            }
            false
        }
        _ => false,
    }
}

/// Check if a list of items represents a sequence template.
///
/// A sequence template is a list where every element is a list starting
/// with `literal` or `cond`.
fn is_sequence_template(items: &[SExpr]) -> bool {
    !items.is_empty()
        && items.iter().all(|item| match item {
            SExpr::List(inner) => {
                !inner.is_empty() && (inner[0].is_symbol("literal") || inner[0].is_symbol("cond"))
            }
            _ => false,
        })
}

/// Evaluate a sequence of template forms.
fn eval_sequence(
    items: &[SExpr],
    bindings: &Bindings,
    rs: &mut ResourceState,
) -> Option<ExpandedTemplate> {
    let mut results = Vec::with_capacity(items.len());
    for item in items {
        match eval_form(item, bindings, rs)? {
            ExpandedTemplate::Single(expr) => results.push(expr),
            ExpandedTemplate::Sequence(exprs) => results.extend(exprs),
        }
    }
    Some(ExpandedTemplate::Sequence(results))
}

/// Resolve a value: if it's a symbol that exists in bindings, return
/// the bound value; otherwise return the expression itself.
fn resolve_value(expr: &SExpr, bindings: &Bindings) -> SExpr {
    if let SExpr::Atom(Atom::Symbol(name)) = expr {
        if let Some(val) = bindings.get(name.as_str()) {
            return val.clone();
        }
    }
    expr.clone()
}

/// Compare two values for equality.
///
/// Symbols are compared by name. A symbol and a string with the same
/// text are considered equal (to support bindings where a symbol value
/// is bound as a string in JSON test vectors).
fn values_equal(a: &SExpr, b: &SExpr) -> bool {
    if a == b {
        return true;
    }
    // Cross-type comparison: symbol vs symbol by name
    match (a, b) {
        (SExpr::Atom(Atom::Symbol(sa)), SExpr::Atom(Atom::Symbol(sb))) => sa == sb,
        _ => false,
    }
}

/// Substitute bindings into an atom.
fn substitute_atom(expr: &SExpr, bindings: &Bindings) -> SExpr {
    if let SExpr::Atom(Atom::Symbol(name)) = expr {
        if let Some(val) = bindings.get(name.as_str()) {
            return val.clone();
        }
    }
    expr.clone()
}

/// Recursively substitute bindings throughout an expression.
fn substitute_expr(template: &SExpr, bindings: &Bindings) -> SExpr {
    match template {
        SExpr::Atom(Atom::Symbol(name)) => {
            if let Some(val) = bindings.get(name.as_str()) {
                val.clone()
            } else {
                template.clone()
            }
        }
        SExpr::Atom(_) => template.clone(),
        SExpr::List(items) => {
            SExpr::List(items.iter().map(|e| substitute_expr(e, bindings)).collect())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec;

    // ---------------------------------------------------------------------------
    // Helper: build an SExpr from a string (uses FromStr)
    // ---------------------------------------------------------------------------
    fn parse(s: &str) -> SExpr {
        s.parse().unwrap()
    }

    fn bindings_from(pairs: &[(&str, SExpr)]) -> Bindings {
        pairs
            .iter()
            .map(|(k, v)| (String::from(*k), v.clone()))
            .collect()
    }

    // ---------------------------------------------------------------------------
    // Existing test: simple positional substitution via expand_template
    // ---------------------------------------------------------------------------

    #[test]
    fn simple_substitution() {
        let def = PerformativeDef {
            role: None,
            name: String::from("greet"),
            params: vec![SExpr::Atom(Atom::Symbol(String::from("x")))],
            template: SExpr::List(vec![
                SExpr::Atom(Atom::Symbol(String::from("hello"))),
                SExpr::Atom(Atom::Symbol(String::from("x"))),
            ]),
        };
        let args = vec![SExpr::Atom(Atom::Str(String::from("world")))];
        let mut rs = ResourceState::new(8, 512);
        let result = expand_template(&def, &args, &mut rs).unwrap();
        assert_eq!(
            result,
            SExpr::List(vec![
                SExpr::Atom(Atom::Symbol(String::from("hello"))),
                SExpr::Atom(Atom::Str(String::from("world"))),
            ])
        );
    }

    // ---------------------------------------------------------------------------
    // pipe-tpl-001: Literal template expansion with variable substitution
    // ---------------------------------------------------------------------------

    #[test]
    fn tv_pipe_tpl_001_literal_substitution() {
        let template = parse("(literal (tell @alice message))");
        let bindings = bindings_from(&[("message", SExpr::Atom(Atom::Str("hello".into())))]);
        let mut rs = ResourceState::new(8, 512);
        let result = expand_template_with_bindings(&template, &bindings, &mut rs).unwrap();
        assert_eq!(
            result,
            ExpandedTemplate::Single(parse("(tell @alice \"hello\")"))
        );
    }

    // ---------------------------------------------------------------------------
    // pipe-tpl-002: Conditional template - equality test selects first branch
    // ---------------------------------------------------------------------------

    #[test]
    fn tv_pipe_tpl_002_cond_equality() {
        let template = parse(
            "(cond ((= priority urgent) (literal (tell @emergency message))) (else (literal (tell @normal message))))",
        );
        let bindings = bindings_from(&[
            ("priority", SExpr::Atom(Atom::Symbol("urgent".into()))),
            ("message", SExpr::Atom(Atom::Str("fire!".into()))),
        ]);
        let mut rs = ResourceState::new(8, 512);
        let result = expand_template_with_bindings(&template, &bindings, &mut rs).unwrap();
        assert_eq!(
            result,
            ExpandedTemplate::Single(parse("(tell @emergency \"fire!\")"))
        );
    }

    #[test]
    fn tv_pipe_tpl_002_cond_equality_else_branch() {
        let template = parse(
            "(cond ((= priority urgent) (literal (tell @emergency message))) (else (literal (tell @normal message))))",
        );
        let bindings = bindings_from(&[
            ("priority", SExpr::Atom(Atom::Symbol("low".into()))),
            ("message", SExpr::Atom(Atom::Str("info".into()))),
        ]);
        let mut rs = ResourceState::new(8, 512);
        let result = expand_template_with_bindings(&template, &bindings, &mut rs).unwrap();
        assert_eq!(
            result,
            ExpandedTemplate::Single(parse("(tell @normal \"info\")"))
        );
    }

    // ---------------------------------------------------------------------------
    // pipe-tpl-003: Conditional template - membership test
    // ---------------------------------------------------------------------------

    #[test]
    fn tv_pipe_tpl_003_cond_membership() {
        let template = parse(
            "(cond ((member category (urgent critical)) (literal (tell @emergency message))) (else (literal (tell @normal message))))",
        );
        let bindings = bindings_from(&[
            ("category", SExpr::Atom(Atom::Symbol("urgent".into()))),
            ("message", SExpr::Atom(Atom::Str("alert".into()))),
        ]);
        let mut rs = ResourceState::new(8, 512);
        let result = expand_template_with_bindings(&template, &bindings, &mut rs).unwrap();
        assert_eq!(
            result,
            ExpandedTemplate::Single(parse("(tell @emergency \"alert\")"))
        );
    }

    #[test]
    fn tv_pipe_tpl_003_cond_membership_no_match() {
        let template = parse(
            "(cond ((member category (urgent critical)) (literal (tell @emergency message))) (else (literal (tell @normal message))))",
        );
        let bindings = bindings_from(&[
            ("category", SExpr::Atom(Atom::Symbol("info".into()))),
            ("message", SExpr::Atom(Atom::Str("note".into()))),
        ]);
        let mut rs = ResourceState::new(8, 512);
        let result = expand_template_with_bindings(&template, &bindings, &mut rs).unwrap();
        assert_eq!(
            result,
            ExpandedTemplate::Single(parse("(tell @normal \"note\")"))
        );
    }

    // ---------------------------------------------------------------------------
    // pipe-tpl-004/005/006: Type tests
    // ---------------------------------------------------------------------------

    #[test]
    fn tv_pipe_tpl_004_type_number() {
        assert!(eval_type_predicate(&SExpr::Atom(Atom::Num(42)), "number"));
        assert!(!eval_type_predicate(
            &SExpr::Atom(Atom::Str("42".into())),
            "number"
        ));
    }

    #[test]
    fn tv_pipe_tpl_005_type_string() {
        assert!(eval_type_predicate(
            &SExpr::Atom(Atom::Str("hello".into())),
            "string"
        ));
        assert!(!eval_type_predicate(&SExpr::Atom(Atom::Num(42)), "string"));
    }

    #[test]
    fn tv_pipe_tpl_006_type_agent() {
        assert!(eval_type_predicate(
            &SExpr::Atom(Atom::Symbol("@alice".into())),
            "agent"
        ));
        assert!(!eval_type_predicate(
            &SExpr::Atom(Atom::Symbol("alice".into())),
            "agent"
        ));
    }

    #[test]
    fn type_predicate_bool() {
        assert!(eval_type_predicate(&SExpr::Atom(Atom::Bool(true)), "bool"));
    }

    #[test]
    fn type_predicate_symbol() {
        assert!(eval_type_predicate(
            &SExpr::Atom(Atom::Symbol("foo".into())),
            "symbol"
        ));
    }

    #[test]
    fn type_predicate_unknown() {
        assert!(!eval_type_predicate(
            &SExpr::Atom(Atom::Num(1)),
            "unknown-type"
        ));
    }

    // ---------------------------------------------------------------------------
    // pipe-tpl-004/005/006 as condition evaluation within cond
    // ---------------------------------------------------------------------------

    #[test]
    fn type_condition_number() {
        let condition = parse("(type? value number)");
        let bindings = bindings_from(&[("value", SExpr::Atom(Atom::Num(42)))]);
        assert!(eval_condition(&condition, &bindings));
    }

    #[test]
    fn type_condition_string() {
        let condition = parse("(type? value string)");
        let bindings = bindings_from(&[("value", SExpr::Atom(Atom::Str("hello".into())))]);
        assert!(eval_condition(&condition, &bindings));
    }

    #[test]
    fn type_condition_agent() {
        let condition = parse("(type? value agent)");
        let bindings = bindings_from(&[("value", SExpr::Atom(Atom::Symbol("@alice".into())))]);
        assert!(eval_condition(&condition, &bindings));
    }

    // ---------------------------------------------------------------------------
    // pipe-tpl-007: Sequence template expansion
    // ---------------------------------------------------------------------------

    #[test]
    fn tv_pipe_tpl_007_sequence() {
        let template = parse(
            "((literal (tell @coordinator \"start\")) (literal (tell @worker \"task\")) (literal (tell @coordinator \"done\")))",
        );
        let bindings = Bindings::new();
        let mut rs = ResourceState::new(8, 4096);
        let result = expand_template_with_bindings(&template, &bindings, &mut rs).unwrap();
        assert_eq!(
            result,
            ExpandedTemplate::Sequence(vec![
                parse("(tell @coordinator \"start\")"),
                parse("(tell @worker \"task\")"),
                parse("(tell @coordinator \"done\")"),
            ])
        );
    }

    // ---------------------------------------------------------------------------
    // pipe-tpl-008: Template substitution with bindings
    // ---------------------------------------------------------------------------

    #[test]
    fn tv_pipe_tpl_008_plain_substitution() {
        let template = parse("(tell x (greeting y))");
        let bindings = bindings_from(&[
            ("x", SExpr::Atom(Atom::Symbol("alice".into()))),
            ("y", SExpr::Atom(Atom::Symbol("hello".into()))),
        ]);
        let mut rs = ResourceState::new(8, 512);
        let result = expand_template_with_bindings(&template, &bindings, &mut rs).unwrap();
        assert_eq!(
            result,
            ExpandedTemplate::Single(parse("(tell alice (greeting hello))"))
        );
    }

    // ---------------------------------------------------------------------------
    // R2 resource bounds enforcement
    // ---------------------------------------------------------------------------

    #[test]
    fn expansion_respects_depth_limit() {
        let template = parse("(literal (tell @alice \"hi\"))");
        let bindings = Bindings::new();
        // max_depth=1: strict <, so depth 0→1 fails
        let mut rs = ResourceState::new(1, 512);
        assert!(expand_template_with_bindings(&template, &bindings, &mut rs).is_none());
    }

    #[test]
    fn expansion_respects_size_limit() {
        let template = parse("(literal (tell @alice \"a very long message that exceeds bounds\"))");
        let bindings = Bindings::new();
        // Very small size limit
        let mut rs = ResourceState::new(8, 5);
        assert!(expand_template_with_bindings(&template, &bindings, &mut rs).is_none());
    }

    // ---------------------------------------------------------------------------
    // Edge cases
    // ---------------------------------------------------------------------------

    #[test]
    fn empty_bindings_no_substitution() {
        let template = parse("(tell @alice x)");
        let bindings = Bindings::new();
        let mut rs = ResourceState::new(8, 512);
        let result = expand_template_with_bindings(&template, &bindings, &mut rs).unwrap();
        // x stays as-is since no binding for it
        assert_eq!(result, ExpandedTemplate::Single(parse("(tell @alice x)")));
    }

    #[test]
    fn atom_template() {
        let template = parse("x");
        let bindings = bindings_from(&[("x", SExpr::Atom(Atom::Num(42)))]);
        let mut rs = ResourceState::new(8, 512);
        let result = expand_template_with_bindings(&template, &bindings, &mut rs).unwrap();
        assert_eq!(result, ExpandedTemplate::Single(SExpr::Atom(Atom::Num(42))));
    }

    #[test]
    fn cond_no_else_no_match() {
        let template = parse("(cond ((= x y) (literal (tell @a \"yes\"))))");
        let bindings = bindings_from(&[
            ("x", SExpr::Atom(Atom::Symbol("a".into()))),
            ("y", SExpr::Atom(Atom::Symbol("b".into()))),
        ]);
        let mut rs = ResourceState::new(8, 512);
        // No clause matches, no else → None
        assert!(expand_template_with_bindings(&template, &bindings, &mut rs).is_none());
    }

    #[test]
    fn equality_same_symbols() {
        let condition = parse("(= x y)");
        let bindings = bindings_from(&[
            ("x", SExpr::Atom(Atom::Symbol("same".into()))),
            ("y", SExpr::Atom(Atom::Symbol("same".into()))),
        ]);
        assert!(eval_condition(&condition, &bindings));
    }

    #[test]
    fn equality_different_symbols() {
        let condition = parse("(= x y)");
        let bindings = bindings_from(&[
            ("x", SExpr::Atom(Atom::Symbol("a".into()))),
            ("y", SExpr::Atom(Atom::Symbol("b".into()))),
        ]);
        assert!(!eval_condition(&condition, &bindings));
    }

    #[test]
    fn member_in_list() {
        let condition = parse("(member x (a b c))");
        let bindings = bindings_from(&[("x", SExpr::Atom(Atom::Symbol("b".into())))]);
        assert!(eval_condition(&condition, &bindings));
    }

    #[test]
    fn member_not_in_list() {
        let condition = parse("(member x (a b c))");
        let bindings = bindings_from(&[("x", SExpr::Atom(Atom::Symbol("d".into())))]);
        assert!(!eval_condition(&condition, &bindings));
    }

    #[test]
    fn nested_substitution_in_literal() {
        let template = parse("(literal (tell @alice (mood greeting)))");
        let bindings = bindings_from(&[
            ("mood", SExpr::Atom(Atom::Symbol("happy".into()))),
            ("greeting", SExpr::Atom(Atom::Str("hello!".into()))),
        ]);
        let mut rs = ResourceState::new(8, 512);
        let result = expand_template_with_bindings(&template, &bindings, &mut rs).unwrap();
        assert_eq!(
            result,
            ExpandedTemplate::Single(parse("(tell @alice (happy \"hello!\"))"))
        );
    }

    #[test]
    fn expand_template_backwards_compat() {
        // Ensure the original expand_template API still works with positional params
        let def = PerformativeDef {
            role: None,
            name: String::from("notify"),
            params: vec![
                SExpr::Atom(Atom::Symbol(String::from("recipient"))),
                SExpr::Atom(Atom::Symbol(String::from("msg"))),
            ],
            template: parse("(tell recipient msg)"),
        };
        let args = vec![
            SExpr::Atom(Atom::Symbol("@bob".into())),
            SExpr::Atom(Atom::Str("hey".into())),
        ];
        let mut rs = ResourceState::new(8, 512);
        let result = expand_template(&def, &args, &mut rs).unwrap();
        assert_eq!(result, parse("(tell @bob \"hey\")"));
    }

    // ---------------------------------------------------------------------------
    // Defect C (SPEC-024 mls-ds/v1): the ACTUAL post-substitution output depth
    // must be charged against `max-depth` (R2). A substituted argument subtree
    // that nests deeper than `max-depth` is an R2 resource violation; an output
    // whose depth is `<= max_depth` is accepted.
    // ---------------------------------------------------------------------------

    /// A left-nested list of exactly `depth` levels (`depth == 0` → an atom).
    fn nested(depth: usize) -> SExpr {
        if depth == 0 {
            SExpr::Atom(Atom::Num(0))
        } else {
            SExpr::List(alloc::vec![
                SExpr::Atom(Atom::Symbol("x".into())),
                nested(depth - 1),
            ])
        }
    }

    /// Like [`nested`] but the bottom leaf is a `leaf_bytes`-long string, to
    /// model a deep-*and*-large output (the mls-ds/v1 8 kB Add).
    fn nested_sized(depth: usize, leaf_bytes: usize) -> SExpr {
        if depth == 0 {
            SExpr::Atom(Atom::Str("a".repeat(leaf_bytes)))
        } else {
            SExpr::List(alloc::vec![
                SExpr::Atom(Atom::Symbol("x".into())),
                nested_sized(depth - 1, leaf_bytes),
            ])
        }
    }

    #[test]
    fn nested_helper_has_expected_depth() {
        assert_eq!(nested(0).depth(), 0);
        assert_eq!(nested(1).depth(), 1);
        assert_eq!(nested(9).depth(), 9);
        assert_eq!(nested_sized(9, 100).depth(), 9);
    }

    /// The depth of a *substituted* argument subtree is charged: wrapping a
    /// deep argument one level deep produces `1 + arg_depth`, and an argument
    /// deep enough to exceed `max_depth` is rejected — where before the fix it
    /// was accepted (only the template-recursion level was charged).
    #[test]
    fn substituted_subtree_depth_is_charged() {
        let template = parse("(commit payload)");
        let big = 1_000_000; // keep byte-size from being the limiting factor

        // arg depth 6 → output depth 7 ≤ max_depth 8 → accepted.
        let mut ok = ResourceState::new(8, big);
        let fit = bindings_from(&[("payload", nested(6))]);
        let out = expand_template_with_bindings(&template, &fit, &mut ok).unwrap();
        assert_eq!(
            out,
            ExpandedTemplate::Single(SExpr::List(alloc::vec![
                SExpr::Atom(Atom::Symbol("commit".into())),
                nested(6),
            ]))
        );
        match &out {
            ExpandedTemplate::Single(e) => assert_eq!(e.depth(), 7),
            _ => panic!("expected single"),
        }

        // arg depth 20 → output depth 21 ≫ max_depth 8 → R2 resource violation.
        let mut bad = ResourceState::new(8, big);
        let deep = bindings_from(&[("payload", nested(20))]);
        assert!(expand_template_with_bindings(&template, &deep, &mut bad).is_none());
    }

    /// mls-ds/v1 profile (max-depth 9): a depth-9 output is accepted, a
    /// depth-11 output is rejected. (The task's named boundary.)
    #[test]
    fn mls_ds_depth9_accepted_depth11_rejected() {
        let template = parse("payload");
        let big = 1_000_000;

        let mut rs9 = ResourceState::new(9, big);
        let d9 = bindings_from(&[("payload", nested(9))]);
        let out = expand_template_with_bindings(&template, &d9, &mut rs9).unwrap();
        assert_eq!(out, ExpandedTemplate::Single(nested(9)));

        let mut rs11 = ResourceState::new(9, big);
        let d11 = bindings_from(&[("payload", nested(11))]);
        assert!(expand_template_with_bindings(&template, &d11, &mut rs11).is_none());
    }

    /// Lock the boundary: an output of depth exactly `max_depth` is accepted
    /// (`depth <= max_depth`), depth `max_depth + 1` is rejected. This matches
    /// the acceptance "a legitimate depth-9 expansion under a max-depth-9
    /// dialect is still accepted" (i.e. the boundary is ≤, not strict <).
    #[test]
    fn output_depth_boundary_is_leq_max_depth() {
        let template = parse("payload");
        let big = 1_000_000;
        for md in [4u32, 9, 16] {
            let mut rs_ok = ResourceState::new(md, big);
            let b_ok = bindings_from(&[("payload", nested(md as usize))]);
            assert!(
                expand_template_with_bindings(&template, &b_ok, &mut rs_ok).is_some(),
                "output depth {md} under max_depth {md} must be accepted"
            );

            let mut rs_bad = ResourceState::new(md, big);
            let b_bad = bindings_from(&[("payload", nested(md as usize + 1))]);
            assert!(
                expand_template_with_bindings(&template, &b_bad, &mut rs_bad).is_none(),
                "output depth {}+1 under max_depth {md} must be rejected",
                md
            );
        }
    }

    /// The mls-ds/v1 known-good Add (depth 9, ~8 kB) does NOT regress: a
    /// depth-9, ~8 kB output is accepted under a max-depth-9 / generous-size
    /// budget; a depth-11 output of the same size class is still rejected on
    /// depth alone. (The depth fix must not disturb byte-size accounting.)
    #[test]
    fn mls_ds_known_good_add_depth9_8kb_not_regressed() {
        let template = parse("payload");
        let size_budget = 16_384; // > 8 kB, as the mls-ds profile allows

        let add = nested_sized(9, 8_050); // depth 9, ~8 kB
        assert_eq!(add.depth(), 9);
        assert!(add.byte_size() >= 8_000 && (add.byte_size() as u32) < size_budget);
        let mut rs = ResourceState::new(9, size_budget);
        let b = bindings_from(&[("payload", add.clone())]);
        assert_eq!(
            expand_template_with_bindings(&template, &b, &mut rs),
            Some(ExpandedTemplate::Single(add))
        );

        // Same size class but depth 11 → rejected purely on output depth.
        let mut rs2 = ResourceState::new(9, size_budget);
        let deep = bindings_from(&[("payload", nested_sized(11, 8_050))]);
        assert!(expand_template_with_bindings(&template, &deep, &mut rs2).is_none());
    }
}
