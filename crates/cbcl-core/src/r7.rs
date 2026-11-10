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

/// The prefix of a self-addressed dialect name (SPEC-019 R.6): the same
/// spelling as every content address on the wire.
pub const SELF_ADDRESS_PREFIX: &str = crate::multihash::TEXT_PREFIX;

/// An R7 installation violation (SPEC-019 CON-1905).
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum R7Violation {
    Malformed(String),
    UnknownVerb(String),
    UnknownField {
        verb: String,
        field: String,
    },
    Typing(String),
    Replaces(String),
    Domain(String),
    Bounds(String),
    Name {
        expected: String,
        found: String,
    },
    /// A threshold read not admitted by its field's carrier, or a set that
    /// is not pairwise incompatible (SPEC-038 REQ-3802, CON-3801).
    Threshold(String),
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
            R7Violation::Threshold(s) => write!(f, "threshold {s}"),
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
/// clause names as a register writer, signer writer, delete, or remove verb
/// (ADR-1901, REQ-1934). Called by
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
    let escrow_verbs: Vec<String> = clause
        .fields()
        .filter_map(|(_, r)| {
            if let Rule::BoundedCounter(c) = r {
                Some(
                    c.operation_verbs()
                        .into_iter()
                        .map(String::from)
                        .collect::<Vec<_>>(),
                )
            } else {
                None
            }
        })
        .flatten()
        .collect();
    for verb in escrow_verbs {
        for (keyword, ty) in [
            (crate::escrow::PREV, TypeConstraint::Symbol),
            (crate::escrow::DEPS, TypeConstraint::List),
        ] {
            if field_type(&d.shapes, &verb, keyword).is_some() {
                continue;
            }
            let rule = ShapeRule::Require {
                keyword: keyword.into(),
                type_constraint: Some(ty),
                children: Vec::new(),
            };
            match d.shapes.iter_mut().find(|s| s.performative == verb) {
                Some(s) => s.rules.push(rule),
                None => d.shapes.push(ShapeConstraint {
                    performative: verb.clone(),
                    rules: alloc::vec![rule],
                }),
            }
        }
    }
    let quorum_verbs: Vec<String> = clause
        .fields()
        .filter_map(|(_, r)| match r {
            Rule::BoundedCounter(c) if c.certification.is_quorum() => Some(
                c.operation_verbs()
                    .into_iter()
                    .map(String::from)
                    .collect::<Vec<_>>(),
            ),
            _ => None,
        })
        .flatten()
        .collect();
    for verb in quorum_verbs {
        let rule = ShapeRule::Require {
            keyword: crate::escrow::NONCE.into(),
            type_constraint: Some(TypeConstraint::String),
            children: Vec::new(),
        };
        if field_type(&d.shapes, &verb, crate::escrow::NONCE).is_none() {
            match d.shapes.iter_mut().find(|s| s.performative == verb) {
                Some(s) => s.rules.push(rule),
                None => d.shapes.push(ShapeConstraint {
                    performative: verb,
                    rules: alloc::vec![rule],
                }),
            }
        }
    }
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
    if let TypeConstraint::Contract(c) = tc {
        return c.representations() != 0 && c.representations() & !(1 | 2 | 4 | 8 | 16) == 0;
    }
    matches!(
        tc,
        TypeConstraint::String
            | TypeConstraint::Hlc
            | TypeConstraint::Integer
            | TypeConstraint::Number
            | TypeConstraint::Float
            | TypeConstraint::Decimal
            | TypeConstraint::Nonnegative
            | TypeConstraint::Bool
    )
}

/// R7 installation checks (SPEC-019 REQ-1904–1910, 1927). Empty for a
/// dialect with neither clause (REQ-1909).
pub fn r7_violations(d: &Dialect) -> Vec<R7Violation> {
    let mut out: Vec<R7Violation> = crate::escrow::declaration_errors(d)
        .into_iter()
        .map(R7Violation::Typing)
        .collect();
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
        if d.name.starts_with(SELF_ADDRESS_PREFIX) {
            check_name(d, &mut out);
        }
        return out;
    };

    // REQ-1904: at most max-fields fields; a threshold renders as a field
    // (SPEC-038 CON-3801) and counts as one.
    let field_count = clause.fields().count()
        + clause.thresholds().count()
        + clause
            .entries
            .iter()
            .filter(|entry| matches!(entry, crate::state::Entry::Condition { .. }))
            .count();
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
    for definition in clause.lattices() {
        if !names.insert(&definition.name) {
            out.push(R7Violation::Malformed(format!(
                "duplicate lattice/field name '{}'",
                definition.name
            )));
        }
        if let Err(reason) = definition.validate(bounds.max_list as usize) {
            out.push(R7Violation::Typing(format!(
                "lattice '{}': {reason}",
                definition.name
            )));
        }
    }
    for (field, rule) in clause.fields() {
        if let Rule::Lift(lift) = rule {
            match &lift.table {
                None => out.push(R7Violation::Typing(format!(
                    "field '{field}' references undefined or invalid lattice '{}'",
                    lift.lattice
                ))),
                Some(table) => {
                    if let Err(reason) = lift.validate(table) {
                        out.push(R7Violation::Typing(format!("lift '{field}': {reason}")));
                    }
                }
            }
        }
    }
    for (field, rule) in clause.fields() {
        match rule {
            Rule::Context { path, definition } => {
                if !definition.as_ref().is_some_and(|d| d.valid_path(path)) {
                    out.push(R7Violation::Typing(format!(
                        "context '{field}' names an unknown path or role"
                    )));
                }
            }
            _ => {}
        }
    }
    check_thresholds(d, clause, &mut names, &mut out);
    let mut frozen_fields = BTreeSet::new();
    for (field, verb, _) in clause.freezes() {
        if clause.rule_of(field).is_none() || !frozen_fields.insert(field) {
            out.push(R7Violation::Malformed(format!(
                "freeze field '{field}' is undefined or has multiple freeze declarations"
            )));
        }
        if !d
            .performatives
            .iter()
            .any(|p| p.name == verb && p.role.as_ref().is_some_and(|r| !r.from.is_empty()))
        {
            out.push(R7Violation::Malformed(format!(
                "freeze verb '{verb}' must be defined with a :from role"
            )));
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
            Some(TypeConstraint::Symbol) if crate::escrow::recipient_field(d, verb, key) => {}
            Some(TypeConstraint::Symbol) | Some(TypeConstraint::Keyword) => {
                out.push(R7Violation::Typing(format!(
                    "field :{key} of '{verb}' is a symbol or keyword; state-bearing fields are string, number, bool, or list"
                )));
            }
            Some(TypeConstraint::Contract(c)) if c.representations() & (32 | 64) != 0 => {
                out.push(R7Violation::Typing(format!(
                    "field :{key} of '{verb}' contract admits symbols or keywords"
                )));
            }
            Some(_) => {}
        }
    }
    let field_types: Vec<(String, &Rule)> =
        clause.fields().map(|(n, r)| (String::from(n), r)).collect();
    for (name, rule) in &field_types {
        if let Some((verb, clock)) = rule.clock_field() {
            if ty(verb, clock) != Some(TypeConstraint::Hlc) || !d.shapes.iter().filter(|s| s.performative == verb).any(|s| s.rules.iter().any(|r| matches!(r, ShapeRule::Require { keyword, type_constraint: Some(tc), .. } if keyword == clock && tc.representation() == Some(TypeConstraint::Hlc)))) {
                out.push(R7Violation::Typing(format!("LWW clock :{clock} of '{verb}' must be a required hlc field")));
            }
            if bounds.max_string < crate::hlc::WIRE_LEN as u32 {
                out.push(R7Violation::Bounds(
                    "max-string cannot hold a canonical HLC".into(),
                ));
            }
            let conflicts = match rule {
                Rule::LwwRegister { key, .. } | Rule::LwwPerSigner { key, .. } => clock == key,
                Rule::LwwMap { key, value, .. } => clock == key || clock == value,
                _ => false,
            };
            if conflicts
                || ROUTING_KEYWORDS.contains(&clock)
                || [
                    RESERVED_REPLACES,
                    crate::escrow::PREV,
                    crate::escrow::DEPS,
                    crate::escrow::NONCE,
                ]
                .contains(&clock)
            {
                out.push(R7Violation::Typing(
                    "LWW clock must be a distinct application field".into(),
                ));
            }
        }
        match rule {
            Rule::Progress { verb } => {
                if let Some(protocol) = &d.causal_protocol {
                    if let Err(reason) = crate::repeat::position_chain(protocol, verb) {
                        out.push(R7Violation::Typing(reason));
                    }
                }
            }
            Rule::LwwMap { verb, key, .. } | Rule::ValuesPerKey { verb, key, .. } => {
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
                        if !matches!(tc, TypeConstraint::Integer | TypeConstraint::Nonnegative) {
                            out.push(R7Violation::Typing(format!(
                                "counter '{name}': :{key} of '{v}' must be an integer"
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
                            Rule::LwwPerSigner { .. }
                                | Rule::LwwMap { .. }
                                | Rule::Events { .. }
                        );
                        if !map_like {
                            out.push(R7Violation::Typing(format!(
                                "'{name}' must reference an lww-per-signer, lww-map, or events field"
                            )));
                        }
                        if matches!(rule, Rule::Histogram { .. }) && matches!(r, Rule::Events { .. }) {
                            out.push(R7Violation::Typing(format!("histogram '{name}' may not reference an events field")));
                        }
                        if matches!(rule, Rule::Sum { .. }) {
                            let numeric = match r {
                                Rule::LwwPerSigner { verb, key, .. } | Rule::Events { verb, key } => {
                                    matches!(ty(verb, key), Some(TypeConstraint::Integer | TypeConstraint::Nonnegative))
                                }
                                Rule::LwwMap { verb, value, .. }  => {
                                    matches!(ty(verb, value), Some(TypeConstraint::Integer | TypeConstraint::Nonnegative))
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
        | Rule::LwwMap {
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
        | Rule::LwwMap {
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

    // Initial fields read only the protocol opener, without an ordering policy.
    for (name, rule) in clause.fields() {
        if let Rule::Initial { verb, .. } = rule {
            if Some(verb.as_str()) != opener.as_deref() {
                out.push(R7Violation::Typing(format!(
                    "initial field '{name}' must name the unique protocol opener"
                )));
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
            Some(Rule::Context { path, .. }) if crate::context::roster_role(path).is_some() => {}
            Some(rule) => {
                let over_opener = rule.verbs().iter().all(|v| Some(*v) == opener.as_deref());
                if !over_opener || rule.verbs().is_empty() {
                    out.push(R7Violation::Domain(format!(
                        "domain field '{field}' must be a rule over the opener only"
                    )));
                }
                if let Rule::Initial { verb, key } = rule {
                    if ty(verb, key) != Some(TypeConstraint::List) {
                        out.push(R7Violation::Domain(format!(
                            "domain field '{field}' must be list-valued"
                        )));
                    }
                } else {
                    out.push(R7Violation::Domain(format!(
                        "domain field '{field}' must be an `initial` over the opener's list"
                    )));
                }
            }
        }
    }

    // REQ-1927: a name that claims to be a self-address must be one. An
    // author-chosen name is a pointer and is left alone; identity is the
    // body hash either way (ADR-1903), and a consumer that needs
    // content-addressed names uses `canonical::dialect_name`.
    if d.name.starts_with(SELF_ADDRESS_PREFIX) {
        check_name(d, &mut out);
    }
    out
}

/// SPEC-038 REQ-3802 / CON-3801 at installation: a threshold's name is unique
/// among fields and thresholds; its field is declared earlier in the clause
/// and has a carrier; every element is admitted by that carrier, never by
/// the display (REQ-3809); and the elements are pairwise incompatible, in
/// `O(k²)` comparisons (NFR-3800). Fail closed: the message names the
/// offending element and carrier.
fn check_thresholds<'a>(
    dialect: &Dialect,
    clause: &'a StateClause,
    names: &mut BTreeSet<&'a str>,
    out: &mut Vec<R7Violation>,
) {
    use crate::state::{Condition, Entry};
    let mut declared: BTreeSet<&str> = BTreeSet::new();
    for entry in &clause.entries {
        let name = match entry {
            Entry::Field { name, .. } => {
                declared.insert(name.as_str());
                continue;
            }
            Entry::Threshold { name, .. } | Entry::Condition { name, .. } => name,
            _ => continue,
        };
        if !names.insert(name) {
            out.push(R7Violation::Malformed(format!(
                "duplicate field '{name}' (a threshold shares the field namespace)"
            )));
        }
        match entry {
            Entry::Threshold {
                field, elements, ..
            } => check_threshold_source(dialect, clause, name, field, elements, &declared, out),
            Entry::Condition { condition, .. } => {
                let bounds = bounds_of(dialect);
                if condition.size() > bounds.max_list as usize {
                    out.push(R7Violation::Bounds(format!(
                        "{name}: condition exceeds max-list {}",
                        bounds.max_list
                    )));
                }
                fn arity(condition: &Condition) -> bool {
                    match condition {
                        Condition::Read { .. } => true,
                        Condition::And(children) => {
                            children.len() >= 2 && children.iter().all(arity)
                        }
                    }
                }
                if !arity(condition) {
                    out.push(R7Violation::Threshold(format!(
                        "{name}: and requires at least two children"
                    )));
                }
                let mut leaves = Vec::new();
                condition.leaves(&mut leaves);
                for (field, element) in leaves {
                    fn bounded(expr: &SExpr, bounds: &StateBounds) -> bool {
                        match expr {
                            SExpr::Atom(Atom::Str(s)) => s.len() <= bounds.max_string as usize,
                            SExpr::Atom(Atom::Num(n)) => {
                                n.unsigned_abs() <= bounds.max_number as u64
                            }
                            SExpr::List(items) => items.iter().all(|item| bounded(item, bounds)),
                            _ => true,
                        }
                    }
                    if !bounded(&element.to_sexpr(), &bounds) {
                        out.push(R7Violation::Bounds(format!(
                            "{name}: condition element exceeds scalar bounds"
                        )));
                    }
                    check_threshold_source(
                        dialect,
                        clause,
                        name,
                        field,
                        core::slice::from_ref(element),
                        &declared,
                        out,
                    );
                }
            }
            _ => {}
        }
    }
}

fn check_threshold_source(
    dialect: &Dialect,
    clause: &StateClause,
    name: &str,
    field: &str,
    elements: &[crate::lattice::Element],
    declared: &BTreeSet<&str>,
    out: &mut Vec<R7Violation>,
) {
    use crate::lattice::{carrier_of, pairwise, relation};
    let rule = if declared.contains(field) {
        clause.rule_of(field)
    } else if clause.rule_of(field).is_some() {
        out.push(R7Violation::Threshold(format!(
            "{name}: field '{field}' is declared after the threshold; declare it earlier in the clause"
        )));
        None
    } else {
        out.push(R7Violation::Threshold(format!(
            "{name}: names undefined field '{field}'"
        )));
        None
    };
    let Some(rule) = rule else {
        return;
    };
    if clause
        .freezes()
        .any(|(f, _, policy)| f == field && policy == crate::state::FreezePolicy::Supersede)
    {
        out.push(R7Violation::Threshold(format!(
            "{name}: supersede freeze can revise '{field}'; use a separate unfrozen arrival field or the fault freeze policy"
        )));
        return;
    }
    let Some(carrier) = carrier_of(rule) else {
        out.push(R7Violation::Threshold(format!(
            "{name}: field '{field}' is a derived display with no carrier of its own"
        )));
        return;
    };
    let mut typed = true;
    for e in elements {
        if matches!(e, crate::lattice::Element::Sum(_)) {
            let monotone = match rule {
                Rule::Events { verb, key } => dialect
                    .shapes
                    .iter()
                    .filter(|s| s.performative == *verb)
                    .flat_map(|s| &s.rules)
                    .any(|r| {
                        matches!(r, ShapeRule::Require {
                        keyword, type_constraint: Some(TypeConstraint::Nonnegative), ..
                    } if keyword == key)
                    }),
                _ => false,
            };
            if !monotone {
                typed = false;
                out.push(R7Violation::Threshold(format!(
                    "{name}: (sum …) on '{field}' can be revised; use a snapshot, freeze, or an events source whose writer requires nonnegative amounts"
                )));
                continue;
            }
        }
        if !e.admitted_by(&carrier) {
            typed = false;
            out.push(R7Violation::Threshold(format!(
                "{name}: element {} is not admitted by carrier {} of field '{field}'",
                e.wire(),
                carrier.name()
            )));
        }
    }
    if !typed {
        return;
    }
    let compatibility = if let Rule::Lift(lift) = rule {
        if let Some(table) = &lift.table {
            // Precompute the largest stable projected value in each
            // principal upper set, excluding conflict top. This takes
            // O(n²) table comparisons once, independent of threshold count;
            // every threshold pair below then takes constant work.
            let projected: Vec<Option<i128>> = (0..table.elements.len())
                .map(
                    |i| match crate::finite::project(&lift.projection, table, i) {
                        crate::state::Value::Int(n) => Some(n),
                        crate::state::Value::Bool(b) => Some(i128::from(b)),
                        _ => None,
                    },
                )
                .collect();
            let maxima: Vec<Option<i128>> = (0..table.elements.len())
                .map(|a| {
                    (0..table.elements.len())
                        .filter(|&b| b != table.top && table.le(a, b))
                        .filter_map(|b| projected[b])
                        .max()
                })
                .collect();
            let reads: Vec<Result<usize, i128>> = elements
                .iter()
                .map(|e| match e {
                    crate::lattice::Element::Scalar(crate::state::Value::Str(name)) => {
                        Ok(table.index(name).expect("typed finite element"))
                    }
                    crate::lattice::Element::Scalar(crate::state::Value::Int(n)) => Err(*n),
                    crate::lattice::Element::Scalar(crate::state::Value::Bool(true)) => Err(1),
                    _ => unreachable!("typed finite element"),
                })
                .collect();
            let mut result = Ok(());
            'pairs: for i in 0..elements.len() {
                for j in i + 1..elements.len() {
                    let why = if elements[i] == elements[j] {
                        Some("duplicate")
                    } else if match (reads[i], reads[j]) {
                        (Ok(a), Ok(b)) => table.merge(a, b) != table.top,
                        (Ok(a), Err(n)) | (Err(n), Ok(a)) => maxima[a].is_some_and(|v| v >= n),
                        (Err(a), Err(b)) => maxima[table.bottom].is_some_and(|v| v >= a.max(b)),
                    } {
                        Some("compatible")
                    } else {
                        None
                    };
                    if let Some(why) = why {
                        result = Err((i, j, why));
                        break 'pairs;
                    }
                }
            }
            result
        } else {
            Ok(())
        }
    } else {
        pairwise(elements, relation)
    };
    if let Err((i, j, why)) = compatibility {
        out.push(R7Violation::Threshold(format!(
            "{name}: elements {} and {} are {why}",
            elements[i].wire(),
            elements[j].wire()
        )));
    }
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
        SExpr::Atom(
            Atom::Str(_) | Atom::Num(_) | Atom::Float(_) | Atom::Decimal(_) | Atom::Bool(_)
        )
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

    // Closed field set. Shape lookup reads the first keyword while state
    // extraction keeps the last: reject ambiguous data fields before either
    // interpretation can admit a different value (SPEC-038 REQ-3802).
    if let Message::Simple { params, .. } = simple {
        let mut seen_fields = BTreeSet::new();
        let mut i = 0;
        while i < params.len() {
            match &params[i] {
                SExpr::Atom(Atom::Keyword(k)) => {
                    if !ROUTING_KEYWORDS.contains(&k.as_str()) && !seen_fields.insert(k) {
                        return Err(violation(
                            "closed",
                            Some(k),
                            "duplicate state keyword".into(),
                        ));
                    }
                    if !declared.contains(k) && !ROUTING_KEYWORDS.contains(&k.as_str()) {
                        return Err(violation(
                            "closed",
                            Some(k),
                            format!("undeclared field :{k} on '{verb}'"),
                        ));
                    }
                    i += 2;
                }
                _other => {
                    return Err(violation(
                        "closed",
                        None,
                        format!("unexpected positional parameter on '{verb}'"),
                    ));
                }
            }
        }
    }

    // Preserve the R7-only export contract by delegating clock checks to the
    // declared shape type. Canonical recognition belongs to TypeConstraint::Hlc.
    for (_, rule) in clause.fields() {
        if let Some((writer, clock)) = rule.clock_field() {
            if writer == verb {
                let valid = fields
                    .get(clock)
                    .is_some_and(|value| TypeConstraint::Hlc.matches_builtin(value));
                if !valid {
                    return Err(violation(
                        "hlc",
                        Some(clock),
                        "expected canonical hlc-<16 lower hex>-<8 lower hex> string".into(),
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
        let allocation = clause.fields().any(|(_,r)|matches!(r, Rule::BoundedCounter(c) if c.ownership==crate::escrow::Ownership::Account&&c.initial_verb==verb&&(c.initial_key==key||c.headroom_key.as_deref()==Some(key))));
        if allocation {
            let parsed = crate::escrow::allocations(value)
                .map_err(|e| violation("allocations", Some(key), e))?;
            if parsed.len() > bounds.max_list as usize
                || parsed.iter().any(|(a, n)| {
                    a.len() > bounds.max_string as usize || *n > i128::from(bounds.max_number)
                })
            {
                return Err(violation(
                    "allocations",
                    Some(key),
                    "allocation bounds exceeded".into(),
                ));
            }
        } else if crate::escrow::recipient_field(d, &verb, key) {
            match value {
                SExpr::Atom(Atom::Symbol(s)) | SExpr::Atom(Atom::Str(s))
                    if s.starts_with('@')
                        && s.len() > 1
                        && s.len() <= bounds.max_string as usize => {}
                _ => {
                    return Err(violation(
                        "recipient",
                        Some(key),
                        "recipient must be an account key".into(),
                    ))
                }
            }
        } else {
            check_bounds(&verb, key, value, &bounds)?;
        }
    }

    if let Some((_, counter)) = crate::escrow::rule_for(d, &verb) {
        if counter.certification.is_quorum()
            && !matches!(fields.get(crate::escrow::NONCE),Some(SExpr::Atom(Atom::Str(s))) if !s.is_empty() && s.len()<=256)
        {
            return Err(violation(
                "escrow",
                Some(crate::escrow::NONCE),
                "missing or invalid transaction nonce".into(),
            ));
        }
        let prev = match fields.get(crate::escrow::PREV) {
            Some(SExpr::Atom(Atom::Symbol(s))) if is_address(s) => s,
            _ => {
                return Err(violation(
                    "escrow",
                    Some(crate::escrow::PREV),
                    "missing or invalid escrow-prev".into(),
                ))
            }
        };
        let deps = match fields.get(crate::escrow::DEPS) {
            Some(SExpr::List(xs)) if xs.len() <= bounds.max_list as usize => xs,
            _ => {
                return Err(violation(
                    "escrow",
                    Some(crate::escrow::DEPS),
                    "missing or oversized escrow-deps".into(),
                ))
            }
        };
        let mut last: Option<&str> = None;
        for dep in deps {
            match dep {
                SExpr::Atom(Atom::Symbol(s))
                    if is_address(s) && s != prev && last.map_or(true, |p| p < s.as_str()) =>
                {
                    last = Some(s)
                }
                _ => {
                    return Err(violation(
                        "escrow",
                        Some(crate::escrow::DEPS),
                        "dependencies must be sorted distinct addresses".into(),
                    ))
                }
            }
        }
    }

    // Compiler-owned bookkeeping is required on every replacement writer.
    if clause.replaces_verbs().contains(verb.as_str()) && !fields.contains_key(RESERVED_REPLACES) {
        return Err(violation(
            "replaces",
            Some(RESERVED_REPLACES),
            String::from("missing required :replaces list"),
        ));
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
                    "invalid content address".into(),
                ));
            }
            if !seen.insert(text) {
                return Err(violation(
                    "replaces",
                    Some(RESERVED_REPLACES),
                    "content address named twice".into(),
                ));
            }
        }
    }
    Ok(())
}

/// A content address as the wire spells it: `f1220` plus 64 lowercase hex.
pub fn is_address(s: &str) -> bool {
    crate::multihash::decode(s).is_some()
}

#[allow(clippy::collapsible_match)]
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
        SExpr::Atom(Atom::Float(n)) => {
            if n.get() < -(bounds.max_number as f64) || n.get() > bounds.max_number as f64 {
                return Err(violation(
                    "size",
                    Some(key),
                    format!(":{key} of '{verb}' exceeds max-number"),
                ));
            }
        }
        SExpr::Atom(Atom::Decimal(n)) => {
            let absolute = n.as_str().trim_start_matches('-');
            let whole = absolute.split('.').next().unwrap();
            let limit = bounds.max_number.to_string();
            if n.as_str().len() > bounds.max_string as usize
                || whole.len() > limit.len()
                || (whole.len() == limit.len()
                    && (whole > limit.as_str() || (whole == limit && absolute.contains('.'))))
            {
                return Err(violation(
                    "size",
                    Some(key),
                    format!(":{key} of '{verb}' exceeds numeric bounds"),
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
