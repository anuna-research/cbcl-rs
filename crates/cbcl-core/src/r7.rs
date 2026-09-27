//! R7 (SPEC-019): installation checks for the `(state …)` clause, the
//! compiler-inserted `:replaces` field, self-addressed naming, and the
//! message-level state-shape check (R.4).

#![forbid(unsafe_code)]

use crate::dialect::Dialect;
use crate::message::Message;
use crate::sexpr::{Atom, SExpr};
use crate::shape::{ShapeConstraint, ShapeRule, ShapeViolation, TypeConstraint};
use crate::state::{
    field_type, keyword_fields, opener_verb, Rule, StateBounds, StateClause, RESERVED_REPLACES,
    ROUTING_KEYWORDS,
};
use alloc::collections::BTreeSet;
use alloc::format;
use alloc::string::{String, ToString};
use alloc::vec::Vec;
use core::fmt;

/// The prefix of a self-addressed dialect name (SPEC-019 R.6).
pub const OBJECT_PREFIX: &str = "object-";

/// An R7 installation violation (SPEC-019 CON-1905).
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum R7Violation {
    Malformed(String),
    UnknownVerb(String),
    UnknownField { verb: String, field: String },
    Typing(String),
    Replaces(String),
    Domain(String),
    Bounds(String),
    Name { expected: String, found: String },
}

impl fmt::Display for R7Violation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            R7Violation::Malformed(s) => write!(f, "malformed state clause: {s}"),
            R7Violation::UnknownVerb(v) => {
                write!(f, "state clause names undefined performative '{v}'")
            }
            R7Violation::UnknownField { verb, field } => {
                write!(
                    f,
                    "state clause names field :{field} not required by the shape of '{verb}'"
                )
            }
            R7Violation::Typing(s) => write!(f, "state clause typing: {s}"),
            R7Violation::Replaces(s) => write!(f, ":replaces: {s}"),
            R7Violation::Domain(s) => write!(f, "domain: {s}"),
            R7Violation::Bounds(s) => write!(f, "state bounds: {s}"),
            R7Violation::Name { expected, found } => {
                write!(
                    f,
                    "self-addressed dialect must be named '{expected}', found '{found}'"
                )
            }
        }
    }
}

/// The dialect's bounds, defaults when the clause is absent.
pub fn bounds_of(d: &Dialect) -> StateBounds {
    d.state_bounds.clone().unwrap_or_default()
}

/// Whether a verb's shape declares `:replaces` at the top level.
fn shape_has_replaces(shapes: &[ShapeConstraint], verb: &str) -> bool {
    field_type(shapes, verb, RESERVED_REPLACES).is_some()
        || shapes.iter().filter(|s| s.performative == verb).any(|s| {
            s.rules.iter().any(|r| matches!(r,
                ShapeRule::Require { keyword, .. } | ShapeRule::Optional { keyword, .. } if keyword == RESERVED_REPLACES))
        })
}

/// Insert `(require :replaces list)` into the shape of every verb the
/// clause names as a writer, delete, or remove verb (ADR-1901). Called by
/// the parser after all clauses are read. Idempotent.
pub fn insert_replaces(d: &mut Dialect) {
    let Some(clause) = d.state.as_ref() else {
        return;
    };
    let verbs: Vec<String> = clause
        .replaces_verbs()
        .into_iter()
        .map(String::from)
        .collect();
    for verb in verbs {
        if shape_has_replaces(&d.shapes, &verb) {
            continue;
        }
        let rule = ShapeRule::Require {
            keyword: String::from(RESERVED_REPLACES),
            type_constraint: Some(TypeConstraint::List),
            children: Vec::new(),
        };
        match d.shapes.iter_mut().find(|s| s.performative == verb) {
            Some(shape) => shape.rules.push(rule),
            None => d.shapes.push(ShapeConstraint {
                performative: verb,
                rules: alloc::vec![rule],
            }),
        }
    }
}

/// The keywords a verb's shape declares at the top level.
pub fn declared_keywords(shapes: &[ShapeConstraint], verb: &str) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    for shape in shapes.iter().filter(|s| s.performative == verb) {
        for rule in &shape.rules {
            if let ShapeRule::Require { keyword, .. } | ShapeRule::Optional { keyword, .. } = rule {
                out.insert(keyword.clone());
            }
        }
    }
    out
}

fn is_scalar(tc: &TypeConstraint) -> bool {
    matches!(
        tc,
        TypeConstraint::String | TypeConstraint::Number | TypeConstraint::Bool
    )
}

/// R7 installation checks (SPEC-019 REQ-1904–1910, 1927). Empty for a
/// dialect with neither clause (REQ-1909).
pub fn r7_violations(d: &Dialect) -> Vec<R7Violation> {
    let mut out = Vec::new();
    let bounds = bounds_of(d);
    let defaults = StateBounds::default();
    if let Some(b) = &d.state_bounds {
        if b.max_string > defaults.max_string
            || b.max_list > defaults.max_list
            || b.max_number > defaults.max_number
            || b.max_fields > defaults.max_fields
        {
            out.push(R7Violation::Bounds(String::from(
                "a bound may not exceed its default",
            )));
        }
        if b.max_string == 0 || b.max_list == 0 || b.max_number <= 0 || b.max_fields == 0 {
            out.push(R7Violation::Bounds(String::from(
                "a bound must be positive",
            )));
        }
    }
    let Some(clause) = d.state.as_ref() else {
        if d.name.starts_with(OBJECT_PREFIX) {
            check_name(d, &mut out);
        }
        return out;
    };

    // REQ-1904: at most max-fields fields.
    let field_count = clause.fields().count();
    if field_count == 0 {
        out.push(R7Violation::Malformed(String::from(
            "a state clause declares at least one field",
        )));
    }
    if field_count as u32 > bounds.max_fields {
        out.push(R7Violation::Bounds(format!(
            "{field_count} fields exceed max-fields {}",
            bounds.max_fields
        )));
    }
    let mut names: BTreeSet<&str> = BTreeSet::new();
    for (name, _) in clause.fields() {
        if !names.insert(name) {
            out.push(R7Violation::Malformed(format!("duplicate field '{name}'")));
        }
    }

    // REQ-1905: protocol with exactly one opener.
    let opener = match d.causal_protocol.as_ref() {
        None => {
            out.push(R7Violation::Malformed(String::from(
                "a state clause requires a protocol clause",
            )));
            None
        }
        Some(p) => {
            let o = opener_verb(p);
            if o.is_none() {
                out.push(R7Violation::Malformed(String::from(
                    "the protocol must have exactly one performative whose only predecessor is begin",
                )));
            }
            o.map(String::from)
        }
    };

    // REQ-1905: references resolve; REQ-1906: typing.
    let defined = |verb: &str| d.performatives.iter().any(|p| p.name == verb);
    for verb in clause.state_bearing_verbs() {
        if !defined(verb) {
            out.push(R7Violation::UnknownVerb(String::from(verb)));
        }
    }
    let ty = |verb: &str, key: &str| field_type(&d.shapes, verb, key);
    for (verb, key) in clause.data_fields() {
        if key == RESERVED_REPLACES {
            out.push(R7Violation::Replaces(format!(
                "'{verb}' reads :replaces as data"
            )));
            continue;
        }
        match ty(verb, key) {
            None => {
                if defined(verb) {
                    out.push(R7Violation::UnknownField {
                        verb: String::from(verb),
                        field: String::from(key),
                    });
                }
            }
            Some(TypeConstraint::Symbol) | Some(TypeConstraint::Keyword) => {
                out.push(R7Violation::Typing(format!(
                    "field :{key} of '{verb}' is a symbol or keyword; state-bearing fields are string, number, bool, or list"
                )));
            }
            Some(_) => {}
        }
    }
    let field_types: Vec<(String, &Rule)> =
        clause.fields().map(|(n, r)| (String::from(n), r)).collect();
    for (name, rule) in &field_types {
        match rule {
            Rule::LatestPerKey { verb, key, .. }
            | Rule::ValuesPerKey { verb, key, .. }
            | Rule::RegisterPerKey { verb, key, .. } => {
                if let Some(tc) = ty(verb, key) {
                    if !is_scalar(&tc) {
                        out.push(R7Violation::Typing(format!(
                            "map key :{key} of '{verb}' must be scalar (field '{name}')"
                        )));
                    }
                }
            }
            Rule::SetUnion { verb, key } | Rule::ObservedSet { add: verb, key, .. } => {
                if let Some(tc) = ty(verb, key) {
                    if !is_scalar(&tc) {
                        out.push(R7Violation::Typing(format!(
                            "value :{key} of '{verb}' must be scalar (field '{name}')"
                        )));
                    }
                }
            }
            Rule::Counter { inc, dec, key } => {
                if inc == dec {
                    out.push(R7Violation::Typing(format!(
                        "counter '{name}' names the same verb twice"
                    )));
                }
                for v in [inc, dec] {
                    if let Some(tc) = ty(v, key) {
                        if tc != TypeConstraint::Number {
                            out.push(R7Violation::Typing(format!(
                                "counter '{name}': :{key} of '{v}' must be a number"
                            )));
                        }
                    }
                }
            }
            Rule::Histogram { field } | Rule::Sum { field } => {
                let earlier = field_types
                    .iter()
                    .take_while(|(n, _)| n != name)
                    .find(|(n, _)| n == field);
                match earlier {
                    None => out.push(R7Violation::Typing(format!(
                        "'{name}' references field '{field}', which is not defined earlier in the clause"
                    ))),
                    Some((_, r)) => {
                        let map_like = matches!(
                            r,
                            Rule::LatestPerSigner { .. }
                                | Rule::LatestPerKey { .. }
                                | Rule::RegisterPerKey { .. }
                                | Rule::Events { .. }
                        );
                        if !map_like {
                            out.push(R7Violation::Typing(format!(
                                "'{name}' must reference a per-signer, per-key, register-per-key, or events field"
                            )));
                        }
                        if matches!(rule, Rule::Histogram { .. }) && matches!(r, Rule::Events { .. }) {
                            out.push(R7Violation::Typing(format!("histogram '{name}' may not reference an events field")));
                        }
                        if matches!(rule, Rule::Sum { .. }) {
                            let numeric = match r {
                                Rule::LatestPerSigner { verb, key } | Rule::Events { verb, key } => {
                                    ty(verb, key) == Some(TypeConstraint::Number)
                                }
                                Rule::LatestPerKey { verb, value, .. } | Rule::RegisterPerKey { verb, value, .. } => {
                                    ty(verb, value) == Some(TypeConstraint::Number)
                                }
                                _ => false,
                            };
                            if !numeric {
                                out.push(R7Violation::Typing(format!("sum '{name}' requires a numeric field")));
                            }
                        }
                    }
                }
            }
            _ => {}
        }
        // REQ-1907: a delete verb carries exactly the key and :replaces.
        if let Rule::ValuesPerKey {
            verb,
            key,
            delete: Some(dv),
            ..
        }
        | Rule::RegisterPerKey {
            verb,
            key,
            delete: Some(dv),
            ..
        } = rule
        {
            if dv == verb {
                out.push(R7Violation::Replaces(format!(
                    "delete verb of '{name}' equals its writer"
                )));
            }
            let kws = declared_keywords(&d.shapes, dv);
            let expected: BTreeSet<String> = [key.clone(), String::from(RESERVED_REPLACES)]
                .into_iter()
                .collect();
            if defined(dv) && kws != expected {
                out.push(R7Violation::Replaces(format!(
                    "delete verb '{dv}' must carry exactly :{key} and :replaces"
                )));
            }
            if let (Some(a), Some(b)) = (ty(verb, key), ty(dv, key)) {
                if a != b {
                    out.push(R7Violation::Typing(format!(
                        "key :{key} differs in type between '{verb}' and '{dv}'"
                    )));
                }
            }
        }
    }

    // REQ-1907: `:replaces` present exactly where the clause implies.
    let implied = clause.replaces_verbs();
    for p in &d.performatives {
        let has = shape_has_replaces(&d.shapes, &p.name);
        let should = implied.contains(p.name.as_str());
        if has && !should {
            out.push(R7Violation::Replaces(format!(
                "'{}' declares :replaces but no rule makes it a writer, delete, or remove verb",
                p.name
            )));
        }
        if should && !has {
            out.push(R7Violation::Replaces(format!(
                "'{}' is missing the reserved :replaces field",
                p.name
            )));
        }
    }
    // A delete verb serves one register.
    let mut delete_owner: alloc::collections::BTreeMap<&str, &str> =
        alloc::collections::BTreeMap::new();
    for (name, rule) in &field_types {
        if let Rule::ValuesPerKey {
            verb,
            delete: Some(dv),
            ..
        }
        | Rule::RegisterPerKey {
            verb,
            delete: Some(dv),
            ..
        } = rule
        {
            if let Some(prev) = delete_owner.insert(dv.as_str(), verb.as_str()) {
                if prev != verb {
                    out.push(R7Violation::Replaces(format!(
                        "delete verb '{dv}' serves two registers (field '{name}')"
                    )));
                }
            }
        }
    }

    // REQ-1908: domains.
    for (verb, key, field) in clause.domains() {
        if Some(verb) == opener.as_deref() {
            out.push(R7Violation::Domain(format!(
                "a domain may not filter the opener '{verb}'"
            )));
        }
        if let Some(tc) = ty(verb, key) {
            if tc != TypeConstraint::String {
                out.push(R7Violation::Domain(format!(
                    "domain key :{key} of '{verb}' must be a string"
                )));
            }
        }
        match clause.rule_of(field) {
            None => out.push(R7Violation::Domain(format!(
                "domain names undefined field '{field}'"
            ))),
            Some(rule) => {
                let over_opener = rule.verbs().iter().all(|v| Some(*v) == opener.as_deref());
                if !over_opener || rule.verbs().is_empty() {
                    out.push(R7Violation::Domain(format!(
                        "domain field '{field}' must be a rule over the opener only"
                    )));
                }
                if let Rule::Last { verb, key } = rule {
                    if ty(verb, key) != Some(TypeConstraint::List) {
                        out.push(R7Violation::Domain(format!(
                            "domain field '{field}' must be list-valued"
                        )));
                    }
                } else {
                    out.push(R7Violation::Domain(format!(
                        "domain field '{field}' must be a `last` over the opener's list"
                    )));
                }
            }
        }
    }

    // REQ-1927: a name that claims to be a self-address must be one. An
    // author-chosen name is a pointer and is left alone; identity is the
    // body hash either way (ADR-1903), and a consumer that needs
    // content-addressed names uses `canonical::dialect_name`.
    if d.name.starts_with(OBJECT_PREFIX) {
        check_name(d, &mut out);
    }
    out
}

fn check_name(d: &Dialect, out: &mut Vec<R7Violation>) {
    let expected = crate::canonical::dialect_name(d);
    if d.name != expected {
        out.push(R7Violation::Name {
            expected,
            found: d.name.clone(),
        });
    }
}

// ---------------------------------------------------------------------------
// Message-level state shape (R.4)
// ---------------------------------------------------------------------------

fn violation(rule: &str, field: Option<&str>, detail: String) -> ShapeViolation {
    ShapeViolation {
        rule: String::from(rule),
        field: field.map(|f| format!(":{f}")),
        expected: None,
        found: None,
        detail,
    }
}

fn is_scalar_value(v: &SExpr) -> bool {
    matches!(
        v,
        SExpr::Atom(Atom::Str(_)) | SExpr::Atom(Atom::Num(_)) | SExpr::Atom(Atom::Bool(_))
    )
}

/// R7 state-shape check (SPEC-019 R.4, REQ-1911–1914): closed field sets,
/// bounds on state-bearing fields, and the form of `:replaces`. Reads the
/// message alone. `Ok(())` for any act of a verb the clause does not name.
pub fn verify_state_shape(d: &Dialect, msg: &Message) -> Result<(), ShapeViolation> {
    let Some(clause) = d.state.as_ref() else {
        return Ok(());
    };
    let Some(simple) = msg.innermost_simple() else {
        return Ok(());
    };
    let Some(verb) = simple.performative().map(|p| p.name().to_string()) else {
        return Ok(());
    };
    if !clause.state_bearing_verbs().contains(verb.as_str()) {
        return Ok(());
    }
    let bounds = bounds_of(d);
    let declared = declared_keywords(&d.shapes, &verb);
    let fields = keyword_fields(simple);

    // Closed field set.
    if let Message::Simple { params, .. } = simple {
        let mut i = 0;
        while i < params.len() {
            match &params[i] {
                SExpr::Atom(Atom::Keyword(k)) => {
                    if !declared.contains(k) && !ROUTING_KEYWORDS.contains(&k.as_str()) {
                        return Err(violation(
                            "closed",
                            Some(k),
                            format!("undeclared field :{k} on '{verb}'"),
                        ));
                    }
                    i += 2;
                }
                other => {
                    return Err(violation(
                        "closed",
                        None,
                        format!("positional parameter {other} on '{verb}'"),
                    ));
                }
            }
        }
    }

    // Bounds on the fields rules and domains name.
    let named: BTreeSet<&str> = clause
        .data_fields()
        .into_iter()
        .filter(|(v, _)| *v == verb)
        .map(|(_, k)| k)
        .collect();
    for key in named {
        let Some(value) = fields.get(key) else {
            continue;
        };
        check_bounds(&verb, key, value, &bounds)?;
    }

    // `:replaces`: a list of at most max-list distinct addresses.
    if let Some(value) = fields.get(RESERVED_REPLACES) {
        let SExpr::List(items) = value else {
            return Err(violation(
                "replaces",
                Some(RESERVED_REPLACES),
                String::from(":replaces must be a list"),
            ));
        };
        if items.len() as u32 > bounds.max_list {
            return Err(violation(
                "replaces",
                Some(RESERVED_REPLACES),
                format!(":replaces names more than {} addresses", bounds.max_list),
            ));
        }
        let mut seen = BTreeSet::new();
        for item in items {
            let text = match item {
                SExpr::Atom(Atom::Symbol(s)) | SExpr::Atom(Atom::Str(s)) => s,
                _ => {
                    return Err(violation(
                        "replaces",
                        Some(RESERVED_REPLACES),
                        String::from(":replaces holds a non-address"),
                    ))
                }
            };
            if !is_address(text) {
                return Err(violation(
                    "replaces",
                    Some(RESERVED_REPLACES),
                    format!("'{text}' is not a content address"),
                ));
            }
            if !seen.insert(text) {
                return Err(violation(
                    "replaces",
                    Some(RESERVED_REPLACES),
                    format!("'{text}' named twice"),
                ));
            }
        }
    }
    Ok(())
}

/// A content address as the wire spells it: `sha256-` plus 64 lowercase hex.
pub fn is_address(s: &str) -> bool {
    let Some(hex) = s.strip_prefix("sha256-") else {
        return false;
    };
    hex.len() == 64 && hex.bytes().all(|b| matches!(b, b'0'..=b'9' | b'a'..=b'f'))
}

fn check_bounds(
    verb: &str,
    key: &str,
    value: &SExpr,
    bounds: &StateBounds,
) -> Result<(), ShapeViolation> {
    match value {
        SExpr::Atom(Atom::Str(s)) => {
            if s.len() as u32 > bounds.max_string {
                return Err(violation(
                    "size",
                    Some(key),
                    format!(
                        ":{key} of '{verb}' exceeds max-string {}",
                        bounds.max_string
                    ),
                ));
            }
        }
        SExpr::Atom(Atom::Num(n)) => {
            if n.unsigned_abs() > bounds.max_number as u64 {
                return Err(violation(
                    "size",
                    Some(key),
                    format!(
                        ":{key} of '{verb}' exceeds max-number {}",
                        bounds.max_number
                    ),
                ));
            }
        }
        SExpr::List(items) => {
            if items.len() as u32 > bounds.max_list {
                return Err(violation(
                    "size",
                    Some(key),
                    format!(":{key} of '{verb}' exceeds max-list {}", bounds.max_list),
                ));
            }
            for item in items {
                if !is_scalar_value(item) {
                    return Err(violation(
                        "size",
                        Some(key),
                        format!(":{key} of '{verb}' holds a non-scalar element"),
                    ));
                }
                check_bounds(verb, key, item, bounds)?;
            }
        }
        _ => {}
    }
    Ok(())
}

impl StateClause {
    /// Convenience: whether a verb is state-bearing.
    pub fn names_verb(&self, verb: &str) -> bool {
        self.state_bearing_verbs().contains(verb)
    }
}
