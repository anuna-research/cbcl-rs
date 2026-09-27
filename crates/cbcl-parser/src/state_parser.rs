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
use cbcl_core::sexpr::{Atom, SExpr};
use cbcl_core::state::{Entry, Rule, StateBounds, StateClause};

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
        "last" => {
            arity(2)?;
            Rule::Last {
                verb: verb(0)?,
                key: key(1)?,
            }
        }
        "latest-per-signer" => {
            arity(2)?;
            Rule::LatestPerSigner {
                verb: verb(0)?,
                key: key(1)?,
            }
        }
        "latest-per-key" => {
            arity(3)?;
            Rule::LatestPerKey {
                verb: verb(0)?,
                key: key(1)?,
                value: key(2)?,
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
        "values" => {
            arity(2)?;
            Rule::Values {
                verb: verb(0)?,
                key: key(1)?,
            }
        }
        "values-per-key" | "register-per-key" => {
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
            if head == "values-per-key" {
                Rule::ValuesPerKey {
                    verb: v,
                    key: k,
                    value: val,
                    delete,
                }
            } else {
                Rule::RegisterPerKey {
                    verb: v,
                    key: k,
                    value: val,
                    delete,
                }
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
    Ok(StateClause { entries })
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
            "max-string" => b.max_string = n as u32,
            "max-list" => b.max_list = n as u32,
            "max-number" => b.max_number = n,
            "max-fields" => b.max_fields = n as u32,
            other => return Err(alloc::format!("unknown bound '{other}'")),
        }
    }
    Ok(b)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_the_checklist_clause() {
        let s: SExpr =
            "(state (title (last open :title)) (items (register-per-key check :item :done drop)))"
                .parse()
                .unwrap();
        let c = parse_state(&s).unwrap();
        assert_eq!(c.entries.len(), 2);
        assert_eq!(
            c.entries[1],
            Entry::Field {
                name: "items".into(),
                rule: Rule::RegisterPerKey {
                    verb: "check".into(),
                    key: "item".into(),
                    value: "done".into(),
                    delete: Some("drop".into())
                }
            }
        );
    }

    #[test]
    fn rejects_unknown_head_and_wrong_atom_kinds() {
        let s: SExpr = "(state (x (newest open :title)))".parse().unwrap();
        assert!(parse_state(&s).unwrap_err().contains("unknown rule"));
        let s: SExpr = "(state (x (last open title)))".parse().unwrap();
        assert!(parse_state(&s).unwrap_err().contains("keyword"));
        let s: SExpr = "(state (Title (last open :title)))".parse().unwrap();
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
