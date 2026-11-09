//! State clause parser (SPEC-019 R.1, CON-1900).
//!
//! Parses `(state entry…)` and `(:state-bounds bound…)` S-expressions into
//! [`StateClause`] and [`StateBounds`]. Post-parse over the SExpr AST; every
//! head is a distinct symbol, so dispatch is LL(1) at every level. Fail
//! closed: an unknown head, a wrong arity, or a wrong atom kind is an error
//! and nothing is repaired.

#![forbid(unsafe_code)]

use alloc::string::String;
use alloc::vec::Vec;
use cbcl_core::lattice::Element;
use cbcl_core::sexpr::{Atom, SExpr};
use cbcl_core::state::{Condition, Entry, Rule, StateBounds, StateClause, Value};

fn symbol(s: &SExpr, what: &str) -> Result<String, String> {
    match s {
        SExpr::Atom(Atom::Symbol(x)) => Ok(x.clone()),
        other => Err(alloc::format!("{what} must be a symbol, got {other}")),
    }
}

fn keyword(s: &SExpr, what: &str) -> Result<String, String> {
    match s {
        SExpr::Atom(Atom::Keyword(x)) => Ok(x.clone()),
        other => Err(alloc::format!(
            "{what} must be a keyword field (:name), got {other}"
        )),
    }
}

fn is_field_name(s: &str) -> bool {
    let b = s.as_bytes();
    !b.is_empty()
        && b.len() <= 48
        && b[0].is_ascii_lowercase()
        && b.iter()
            .all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || *c == b'-')
}

/// Parse one rule `(head arg…)`.
pub fn parse_rule(sexpr: &SExpr) -> Result<Rule, String> {
    let items = match sexpr {
        SExpr::List(items) if !items.is_empty() => items,
        _ => return Err(String::from("a rule must be a non-empty list")),
    };
    let head = symbol(&items[0], "rule head")?;
    let args = &items[1..];
    if head == "context" {
        return Ok(Rule::Context {
            path: args
                .iter()
                .map(|a| symbol(a, "context path"))
                .collect::<Result<_, _>>()?,
            definition: None,
        });
    }
    if head == "lift" {
        return parse_finite_lift(args).map(|lift| Rule::Lift(alloc::boxed::Box::new(lift)));
    }
    let arity = |n: usize| -> Result<(), String> {
        if args.len() == n {
            Ok(())
        } else {
            Err(alloc::format!(
                "{head} takes {n} argument(s), got {}",
                args.len()
            ))
        }
    };
    let verb = |i: usize| symbol(&args[i], "verb");
    let key = |i: usize| keyword(&args[i], "field");
    Ok(match head.as_str() {
        "bounded-counter" => Rule::BoundedCounter(alloc::boxed::Box::new(parse_counter(args)?)),
        "lww-register" | "lww-per-signer" => {
            arity(3)?;
            let (verb, key, clock) = (verb(0)?, key(1)?, key(2)?);
            if head == "lww-register" {
                Rule::LwwRegister { verb, key, clock }
            } else {
                Rule::LwwPerSigner { verb, key, clock }
            }
        }
        "lww-map" => {
            if args.len() != 4 && args.len() != 5 {
                return Err(alloc::format!(
                    "{head} takes 4 or 5 arguments, got {}",
                    args.len()
                ));
            }
            Rule::LwwMap {
                verb: verb(0)?,
                key: key(1)?,
                value: key(2)?,
                clock: key(3)?,
                delete: if args.len() == 5 {
                    Some(verb(4)?)
                } else {
                    None
                },
            }
        }
        "last" | "latest-per-signer" | "latest-per-key" | "register-per-key" => {
            return Err(alloc::format!("retired state rule '{head}': use initial for opener fields or an explicit lww-* rule with a clock"));
        }
        "initial" => {
            arity(2)?;
            Rule::Initial {
                verb: verb(0)?,
                key: key(1)?,
            }
        }

        "exists" => {
            arity(1)?;
            Rule::Exists { verb: verb(0)? }
        }
        "count" => {
            arity(1)?;
            Rule::Count { verb: verb(0)? }
        }
        "progress" => {
            arity(1)?;
            Rule::Progress { verb: verb(0)? }
        }
        "events" => {
            arity(2)?;
            Rule::Events {
                verb: verb(0)?,
                key: key(1)?,
            }
        }
        "set-union" => {
            arity(2)?;
            Rule::SetUnion {
                verb: verb(0)?,
                key: key(1)?,
            }
        }
        "values" | "multi-value-register" => {
            arity(2)?;
            Rule::Values {
                verb: verb(0)?,
                key: key(1)?,
            }
        }
        "values-per-key" | "multi-value-map" => {
            if args.len() != 3 && args.len() != 4 {
                return Err(alloc::format!(
                    "{head} takes 3 or 4 arguments, got {}",
                    args.len()
                ));
            }
            let delete = if args.len() == 4 {
                Some(verb(3)?)
            } else {
                None
            };
            let (v, k, val) = (verb(0)?, key(1)?, key(2)?);
            Rule::ValuesPerKey {
                verb: v,
                key: k,
                value: val,
                delete,
            }
        }

        "observed-set" => {
            arity(3)?;
            Rule::ObservedSet {
                add: verb(0)?,
                remove: verb(1)?,
                key: key(2)?,
            }
        }
        "counter" => {
            arity(3)?;
            Rule::Counter {
                inc: verb(0)?,
                dec: verb(1)?,
                key: key(2)?,
            }
        }
        "histogram" => {
            arity(1)?;
            Rule::Histogram {
                field: symbol(&args[0], "field name")?,
            }
        }
        "sum" => {
            arity(1)?;
            Rule::Sum {
                field: symbol(&args[0], "field name")?,
            }
        }
        other => return Err(alloc::format!("unknown rule '{other}' (SPEC-019 REQ-1901)")),
    })
}

/// Parse a `(state entry…)` clause.
pub fn parse_state(sexpr: &SExpr) -> Result<StateClause, String> {
    let items = match sexpr {
        SExpr::List(items) => items,
        _ => return Err(String::from("state clause must be a list")),
    };
    if items.len() < 2 || !items[0].is_symbol("state") {
        return Err(String::from("state clause requires: state entry…"));
    }
    let mut entries = Vec::new();
    for entry in &items[1..] {
        let parts = match entry {
            SExpr::List(parts) if !parts.is_empty() => parts,
            _ => return Err(String::from("a state entry must be a non-empty list")),
        };
        if parts[0].is_symbol("lattice") {
            entries.push(Entry::Lattice(parse_finite_definition(parts)?));
            continue;
        }
        if parts[0].is_symbol("domain") {
            if parts.len() != 4 {
                return Err(String::from("domain takes: verb :key field"));
            }
            entries.push(Entry::Domain {
                verb: symbol(&parts[1], "domain verb")?,
                key: keyword(&parts[2], "domain key")?,
                field: symbol(&parts[3], "domain field")?,
            });
            continue;
        }
        if parts[0].is_symbol("freeze") {
            if !(3..=4).contains(&parts.len()) {
                return Err(String::from("freeze takes: field verb [supersede|fault]"));
            }
            let policy = match parts
                .get(3)
                .map(|x| symbol(x, "freeze policy"))
                .transpose()?
                .as_deref()
            {
                None | Some("supersede") => cbcl_core::state::FreezePolicy::Supersede,
                Some("fault") => cbcl_core::state::FreezePolicy::Fault,
                _ => return Err(String::from("freeze policy must be supersede or fault")),
            };
            entries.push(Entry::Freeze {
                field: symbol(&parts[1], "freeze field")?,
                verb: symbol(&parts[2], "freeze verb")?,
                policy,
            });
            continue;
        }
        if parts[0].is_symbol("threshold") {
            if parts.len() == 3 {
                let name = symbol(&parts[1], "threshold name")?;
                if !is_field_name(&name) {
                    return Err(String::from("invalid threshold name"));
                }
                entries.push(Entry::Condition {
                    name,
                    condition: parse_condition(&parts[2])?,
                });
                continue;
            }
            if parts.len() < 4 {
                return Err(String::from("threshold takes: name field element…"));
            }
            let name = symbol(&parts[1], "threshold name")?;
            if !is_field_name(&name) {
                return Err(alloc::format!(
                    "'{name}' is not a field name ([a-z][a-z0-9-]{{0,47}})"
                ));
            }
            entries.push(Entry::Threshold {
                name,
                field: symbol(&parts[2], "threshold field")?,
                elements: parts[3..]
                    .iter()
                    .map(parse_element)
                    .collect::<Result<Vec<_>, _>>()?,
            });
            continue;
        }
        if parts.len() != 2 {
            return Err(String::from("a field entry is: (name (rule …))"));
        }
        let name = symbol(&parts[0], "field name")?;
        if !is_field_name(&name) {
            return Err(alloc::format!(
                "'{name}' is not a field name ([a-z][a-z0-9-]{{0,47}})"
            ));
        }
        let rule = parse_rule(&parts[1])?;
        entries.push(Entry::Field { name, rule });
    }
    let mut clause = StateClause { entries };
    clause.resolve_lattices();
    Ok(clause)
}

fn tagged<'a>(value: &'a SExpr, tag: &str) -> Result<&'a [SExpr], String> {
    match value {
        SExpr::List(xs) if xs.first().is_some_and(|x| x.is_symbol(tag)) => Ok(&xs[1..]),
        _ => Err(alloc::format!("expected ({tag} …)")),
    }
}

fn finite_scalar(value: &SExpr) -> Result<SExpr, String> {
    match value {
        SExpr::Atom(Atom::Str(_) | Atom::Num(_) | Atom::Bool(_)) => Ok(value.clone()),
        _ => Err(String::from(
            "finite table values must be scalar strings, integers or booleans",
        )),
    }
}

fn parse_finite_definition(parts: &[SExpr]) -> Result<cbcl_core::finite::Definition, String> {
    if parts.len() != 6 {
        return Err(String::from(
            "lattice takes name, elements, bottom, top and join",
        ));
    }
    let name = symbol(&parts[1], "lattice name")?;
    if !is_field_name(&name) {
        return Err(String::from("invalid lattice name"));
    }
    let elements = tagged(&parts[2], "elements")?
        .iter()
        .map(|x| symbol(x, "lattice element"))
        .collect::<Result<Vec<_>, _>>()?;
    if elements.is_empty() || elements.iter().any(|x| !is_field_name(x)) {
        return Err(String::from(
            "lattice elements must be nonempty state-name symbols",
        ));
    }
    let bottom = tagged(&parts[3], "bottom")?;
    let top = tagged(&parts[4], "top")?;
    if bottom.len() != 1 || top.len() != 1 {
        return Err(String::from("bottom and top take one element each"));
    }
    let rows = tagged(&parts[5], "join")?
        .iter()
        .map(|row| match row {
            SExpr::List(xs) if xs.len() == 3 => Ok((
                symbol(&xs[0], "join lhs")?,
                symbol(&xs[1], "join rhs")?,
                symbol(&xs[2], "join result")?,
            )),
            _ => Err(String::from("join row must be (element element element)")),
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(cbcl_core::finite::Definition {
        name,
        elements,
        bottom: symbol(&bottom[0], "bottom")?,
        top: symbol(&top[0], "top")?,
        rows,
    })
}

fn parse_finite_lift(args: &[SExpr]) -> Result<cbcl_core::finite::Lift, String> {
    use cbcl_core::finite::{Lift, Projection, Row};
    if !(3..=4).contains(&args.len()) {
        return Err(String::from(
            "lift takes verb, into, contribute and optional project",
        ));
    }
    let into = tagged(&args[1], "into")?;
    if into.len() != 1 {
        return Err(String::from("into takes one lattice name"));
    }
    let entries = tagged(&args[2], "contribute")?;
    if entries.is_empty() {
        return Err(String::from("contribute requires at least one row"));
    }
    let rows = entries
        .iter()
        .map(|row| match row {
            SExpr::List(xs) if xs.len() == 3 => Ok(Row {
                key: keyword(&xs[0], "contribution key")?,
                value: finite_scalar(&xs[1])?,
                element: symbol(&xs[2], "contribution element")?,
            }),
            _ => Err(String::from(
                "contribution row must be (:key scalar element)",
            )),
        })
        .collect::<Result<Vec<_>, _>>()?;
    let projection = if let Some(p) = args.get(3) {
        let xs = tagged(p, "project")?;
        let (stable, rows) = match xs {
            [rows] => (false, rows),
            [flag, rows] if flag.is_symbol("stable") => (true, rows),
            _ => {
                return Err(String::from(
                    "project takes optional stable and one list of rows",
                ))
            }
        };
        let SExpr::List(rows) = rows else {
            return Err(String::from("project rows must be a list"));
        };
        if rows.is_empty() {
            return Err(String::from("project requires at least one row"));
        }
        let rows = rows
            .iter()
            .map(|row| match row {
                SExpr::List(xs) if xs.len() == 2 => {
                    Ok((symbol(&xs[0], "project element")?, finite_scalar(&xs[1])?))
                }
                _ => Err(String::from("project row must be (element scalar)")),
            })
            .collect::<Result<Vec<_>, _>>()?;
        Some(Projection { stable, rows })
    } else {
        None
    };
    Ok(Lift {
        verb: symbol(&args[0], "lift verb")?,
        lattice: symbol(&into[0], "lattice name")?,
        rows,
        projection,
        table: None,
    })
}

fn parse_condition(input: &SExpr) -> Result<Condition, String> {
    match input {
        SExpr::List(parts) if parts.len() == 3 && parts[0].is_symbol("read") => {
            Ok(Condition::Read {
                field: symbol(&parts[1], "condition field")?,
                element: parse_element(&parts[2])?,
            })
        }
        SExpr::List(parts) if parts.len() >= 3 && parts[0].is_symbol("and") => Ok(Condition::And(
            parts[1..]
                .iter()
                .map(parse_condition)
                .collect::<Result<Vec<_>, _>>()?,
        )),
        _ => Err(String::from(
            "condition is (read field element) or (and condition condition+)",
        )),
    }
}

/// Parse one threshold element (SPEC-038 CON-3801):
/// `scalar | (count n) | (member scalar) | (sum n) | (progress n) | fault`.
/// Typing against the field's carrier is an installation check (R7).
fn parse_element(sexpr: &SExpr) -> Result<Element, String> {
    let scalar = |s: &SExpr| -> Result<Value, String> {
        match s {
            SExpr::Atom(Atom::Str(_)) | SExpr::Atom(Atom::Num(_)) | SExpr::Atom(Atom::Bool(_)) => {
                Ok(Value::from_sexpr(s))
            }
            other => Err(alloc::format!(
                "threshold element must be a scalar, got {other}"
            )),
        }
    };
    match sexpr {
        SExpr::Atom(Atom::Symbol(s)) if s == "fault" => Err(String::from(
            "fault is a separate terminal outcome, not a threshold alternative",
        )),
        SExpr::Atom(Atom::Symbol(other)) => Err(alloc::format!(
            "unknown threshold element '{other}' (SPEC-038 CON-3801)"
        )),
        SExpr::Atom(_) => scalar(sexpr).map(Element::Scalar),
        SExpr::List(items) => {
            let [head, arg] = items.as_slice() else {
                return Err(String::from(
                    "a threshold element is: (count n) | (member x) | (sum n) | (progress n)",
                ));
            };
            let head = symbol(head, "threshold element head")?;
            let integer = || match arg {
                SExpr::Atom(Atom::Num(n)) => Ok(*n),
                other => Err(alloc::format!("{head} requires an integer, got {other}")),
            };
            Ok(match head.as_str() {
                "count" => Element::Count(integer()?),
                "sum" => Element::Sum(integer()?),
                "progress" => Element::Progress(integer()?),
                "member" => Element::Member(scalar(arg)?),
                other => {
                    return Err(alloc::format!(
                        "unknown threshold element '{other}' (SPEC-038 CON-3801)"
                    ))
                }
            })
        }
    }
}

/// Parse a `(:state-bounds bound…)` clause; absent bounds take defaults.
pub fn parse_state_bounds(sexpr: &SExpr) -> Result<StateBounds, String> {
    let items = match sexpr {
        SExpr::List(items) => items,
        _ => return Err(String::from(":state-bounds clause must be a list")),
    };
    if items.is_empty()
        || !matches!(&items[0], SExpr::Atom(Atom::Keyword(k)) if k == "state-bounds")
    {
        return Err(String::from(
            ":state-bounds clause requires: :state-bounds bound…",
        ));
    }
    let mut b = StateBounds::default();
    let mut seen: Vec<String> = Vec::new();
    for bound in &items[1..] {
        let parts = match bound {
            SExpr::List(parts) if parts.len() == 2 => parts,
            _ => return Err(String::from("a bound is: (max-… n)")),
        };
        let name = symbol(&parts[0], "bound name")?;
        let n = match &parts[1] {
            SExpr::Atom(Atom::Num(n)) if *n > 0 => *n,
            other => {
                return Err(alloc::format!(
                    "bound {name} must be a positive number, got {other}"
                ))
            }
        };
        if seen.contains(&name) {
            return Err(alloc::format!("duplicate bound {name}"));
        }
        seen.push(name.clone());
        match name.as_str() {
            "max-string" => {
                b.max_string = u32::try_from(n)
                    .map_err(|_| alloc::format!("bound {name} exceeds unsigned 32-bit range"))?;
            }
            "max-list" => {
                b.max_list = u32::try_from(n)
                    .map_err(|_| alloc::format!("bound {name} exceeds unsigned 32-bit range"))?;
            }
            "max-number" => b.max_number = n,
            "max-fields" => {
                b.max_fields = u32::try_from(n)
                    .map_err(|_| alloc::format!("bound {name} exceeds unsigned 32-bit range"))?;
            }
            other => return Err(alloc::format!("unknown bound '{other}'")),
        }
    }
    Ok(b)
}

/// Full recognition of the bounded-counter declaration (CON-1908/1909).
fn parse_counter(args: &[SExpr]) -> Result<cbcl_core::escrow::CounterRule, String> {
    use alloc::collections::BTreeMap;
    use cbcl_core::escrow::CounterRule;
    let mut options = BTreeMap::new();
    for option in args {
        let SExpr::List(xs) = option else {
            return Err(String::from("counter option must be a list"));
        };
        let Some(head) = xs.first() else {
            return Err(String::from("empty counter option"));
        };
        let name = symbol(head, "counter option")?;
        if ![
            "floor",
            "ceiling",
            "certification",
            "ownership",
            "initial",
            "initial-rights",
            "initial-headroom",
            "issuers",
            "increment",
            "decrement",
            "transfer",
            "transfer-headroom",
        ]
        .contains(&name.as_str())
        {
            return Err(alloc::format!("unknown bounded-counter option '{name}'"));
        }
        if options.insert(name.clone(), &xs[1..]).is_some() {
            return Err(alloc::format!("duplicate bounded-counter option '{name}'"));
        }
    }
    let get = |name: &str, n: usize| -> Result<&[SExpr], String> {
        let xs = options
            .get(name)
            .ok_or_else(|| alloc::format!("missing bounded-counter option '{name}'"))?;
        if xs.len() != n {
            return Err(alloc::format!("'{name}' takes {n} arguments"));
        }
        Ok(xs)
    };
    let integer = |name: &str| -> Result<i64, String> {
        match &get(name, 1)?[0] {
            SExpr::Atom(Atom::Num(n)) => Ok(*n),
            _ => Err(alloc::format!("'{name}' requires an integer")),
        }
    };
    let pair = |name: &str| -> Result<(String, String), String> {
        let xs = get(name, 2)?;
        Ok((symbol(&xs[0], "verb")?, keyword(&xs[1], "field")?))
    };
    let triple = |name: &str| -> Result<(String, String, String), String> {
        let xs = get(name, 3)?;
        Ok((
            symbol(&xs[0], "verb")?,
            keyword(&xs[1], "recipient field")?,
            keyword(&xs[2], "amount field")?,
        ))
    };
    let ownership = match options.get("ownership") {
        None => cbcl_core::escrow::Ownership::Account,
        Some(xs) if xs.len() == 1 => match symbol(&xs[0], "ownership")?.as_str() {
            "account" => cbcl_core::escrow::Ownership::Account,
            "collective" => cbcl_core::escrow::Ownership::Collective,
            _ => return Err("ownership must be account or collective".into()),
        },
        _ => return Err("ownership takes one argument".into()),
    };
    let collective = ownership == cbcl_core::escrow::Ownership::Collective;
    if collective
        && [
            "initial-rights",
            "initial-headroom",
            "transfer",
            "transfer-headroom",
        ]
        .iter()
        .any(|k| options.contains_key(*k))
    {
        return Err("collective counters use scalar initial and do not accept account allocation/transfer options".into());
    }
    if !collective && options.contains_key("initial") {
        return Err("account ownership requires initial-rights".into());
    }
    let (initial_verb, initial_key) = pair(if collective {
        "initial"
    } else {
        "initial-rights"
    })?;
    let ceiling = if options.contains_key("ceiling") {
        Some(integer("ceiling")?)
    } else {
        None
    };
    let headroom = if options.contains_key("initial-headroom") {
        Some(pair("initial-headroom")?)
    } else {
        None
    };
    if !collective && ceiling.is_some() != headroom.is_some() {
        return Err(String::from(
            "ceiling and initial-headroom must occur together",
        ));
    }
    if headroom
        .as_ref()
        .is_some_and(|(v, k)| v != &initial_verb || k == &initial_key)
    {
        return Err(String::from(
            "headroom needs the same opener and a distinct field",
        ));
    }
    let transfer_headroom = if options.contains_key("transfer-headroom") {
        Some(triple("transfer-headroom")?)
    } else {
        None
    };
    if transfer_headroom.is_some() && ceiling.is_none() {
        return Err(String::from("headroom transfer requires ceiling"));
    }
    let certification = match options.get("certification") {
        Some(xs) => parse_certification(xs)?,
        None => cbcl_core::certification::Certification::default(),
    };
    if collective && !certification.is_quorum() {
        return Err("collective counters require quorum-budget certification".into());
    }
    Ok(CounterRule {
        ownership,
        certification,
        floor: integer("floor")?,
        ceiling,
        initial_verb,
        initial_key,
        headroom_key: headroom.map(|(_, k)| k),
        issuer: match &get("issuers", 1)?[0] {
            SExpr::List(xs) if xs.is_empty() => String::new(),
            x => symbol(x, "issuer role or ()")?,
        },
        increment: pair("increment")?,
        decrement: pair("decrement")?,
        transfer: if collective {
            None
        } else {
            Some(triple("transfer")?)
        },
        transfer_headroom,
    })
}

fn parse_certification(args: &[SExpr]) -> Result<cbcl_core::certification::Certification, String> {
    use cbcl_core::certification::Certification;
    let Some(mode) = args.first() else {
        return Err("certification requires a profile".into());
    };
    match symbol(mode, "certification profile")?.as_str() {
        "host-gate" if args.len() == 1 => Ok(Certification::HostGate),
        "quorum-budget" => {
            let mut validators = None;
            let mut faults = None;
            let mut seen = alloc::collections::BTreeSet::new();
            for option in &args[1..] {
                let SExpr::List(xs) = option else {
                    return Err("certification option must be a list".into());
                };
                let Some(head) = xs.first() else {
                    return Err("empty certification option".into());
                };
                let name = symbol(head, "certification option")?;
                if !seen.insert(name.clone()) {
                    return Err(alloc::format!("duplicate certification option '{name}'"));
                }
                match name.as_str() {
                    "validators" => {
                        if xs.len() < 2 {
                            return Err("validators requires at least one key".into());
                        }
                        validators = Some(
                            xs[1..]
                                .iter()
                                .map(|x| symbol(x, "validator key"))
                                .collect::<Result<Vec<_>, _>>()?,
                        );
                    }
                    "faults" if xs.len() == 2 => match xs[1] {
                        SExpr::Atom(Atom::Num(n)) => {
                            faults = Some(
                                u32::try_from(n)
                                    .map_err(|_| "faults must be a nonnegative 32-bit integer")?,
                            )
                        }
                        _ => return Err("faults requires an integer".into()),
                    },
                    _ => {
                        return Err(alloc::format!(
                            "unknown or malformed certification option '{name}'"
                        ))
                    }
                }
            }
            Certification::quorum_budget(validators, faults)
        }
        _ => Err("unknown or malformed certification profile".into()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_the_checklist_clause() {
        let s: SExpr =
            "(state (title (initial open :title)) (items (lww-map check :item :done :clock drop)))"
                .parse()
                .unwrap();
        let c = parse_state(&s).unwrap();
        assert_eq!(c.entries.len(), 2);
        assert_eq!(
            c.entries[1],
            Entry::Field {
                name: "items".into(),
                rule: Rule::LwwMap {
                    verb: "check".into(),
                    key: "item".into(),
                    value: "done".into(),
                    delete: Some("drop".into()),
                    clock: "clock".into(),
                }
            }
        );
    }

    #[test]
    fn rejects_unknown_head_and_wrong_atom_kinds() {
        let s: SExpr = "(state (x (newest open :title)))".parse().unwrap();
        assert!(parse_state(&s).unwrap_err().contains("unknown rule"));
        let s: SExpr = "(state (x (initial open title)))".parse().unwrap();
        assert!(parse_state(&s).unwrap_err().contains("keyword"));
        let s: SExpr = "(state (Title (initial open :title)))".parse().unwrap();
        assert!(parse_state(&s).unwrap_err().contains("field name"));
    }

    #[test]
    fn parses_bounds_with_defaults() {
        let s: SExpr = "(:state-bounds (max-string 280) (max-list 24))"
            .parse()
            .unwrap();
        let b = parse_state_bounds(&s).unwrap();
        assert_eq!(
            (b.max_string, b.max_list, b.max_number, b.max_fields),
            (280, 24, 1_000_000_000_000, 32)
        );
    }
}
