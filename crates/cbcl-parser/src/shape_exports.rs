//! `verify_message_shape`: a message against a dialect's `(shape …)` clauses,
//! as one implementation every binding wraps (SPEC-010 REQ-002). A host that
//! admits frames judges their shape here, never with predicates of its own:
//! the hub and the browser must agree on what a well-shaped frame is
//! (cbcl-rs issue #14).
//!
//! ```text
//! (verify-shape <dialect-or-chain> <performative> <message>)   → "ok" | blame S-expression
//! ```

#![forbid(unsafe_code)]

use alloc::format;
use alloc::string::String;
use cbcl_core::blame::ViolationError;
use cbcl_core::serializer::serialize;
use cbcl_core::sexpr::{Atom, SExpr};

use crate::parser;
use crate::state_exports::parse_and_install_dialect;

/// Verify a runtime message against a dialect's shape constraints.
pub fn verify_message_shape_str(input: &str) -> Result<String, String> {
    let frame = parser::parse(input).map_err(|e| format!("parse error: {e}"))?;
    let items = match &frame {
        SExpr::List(items) => items,
        _ => {
            return Err(String::from(
                "expected (verify-shape <dialect-or-chain> <performative> <message>)",
            ))
        }
    };
    if items.len() != 4 || !matches!(&items[0], SExpr::Atom(Atom::Symbol(s)) if s == "verify-shape")
    {
        return Err(String::from(
            "expected (verify-shape <dialect-or-chain> <performative> <message>)",
        ));
    }
    let performative = match &items[2] {
        SExpr::Atom(Atom::Symbol(s)) => s.clone(),
        _ => return Err(String::from("performative must be a symbol")),
    };
    let dialect_sexpr = &items[1];
    let message_sexpr = &items[3];

    let registry = parse_and_install_dialect(dialect_sexpr)?;

    // Composition by conjunction (REQ-224): every matching shape across the
    // whole installed registry must pass. Iterating all installed dialects
    // (not just the leaf) matches the full pipeline's behaviour, so a shape
    // declared on a parent dialect supplied via the `(dialects ...)` chain
    // form still fires for messages that target the parent's performative.
    // Blame attribution follows the dialect that owns the failing shape.
    for d in registry.iter() {
        for shape in &d.shapes {
            if shape.performative != performative {
                continue;
            }
            if let Err(violation) = shape.check(message_sexpr) {
                let blame = ViolationError::from_shape_violation(
                    &violation,
                    None,
                    None,
                    Some(message_sexpr.clone()),
                )
                .with_dialect_context(
                    &d.name,
                    d.author.as_deref(),
                    d.hash.as_deref(),
                    Some(&performative),
                );
                return Err(serialize(&blame.to_sexpr()));
            }
        }
    }
    Ok(String::from("ok"))
}


#[cfg(test)]
mod tests {
    use super::*;

    const D: &str = "(define d (cbcl) @a (extend vote (to choice) (tell to :choice choice)) (shape vote (require :choice string)))";

    #[test]
    fn shape_verdicts() {
        assert_eq!(verify_message_shape_str(&format!("(verify-shape {D} vote (vote @r :choice \"x\"))")).unwrap(), "ok");
        let blame = verify_message_shape_str(&format!("(verify-shape {D} vote (vote @r :choice 1))")).unwrap_err();
        assert!(blame.contains("choice"), "{blame}");
        assert!(verify_message_shape_str(&format!("(verify-shape {D} vote (vote @r))")).is_err());
        // No shape targets the performative: nothing to violate.
        assert_eq!(verify_message_shape_str(&format!("(verify-shape {D} other (other @r))")).unwrap(), "ok");
        assert!(verify_message_shape_str("(verify-shape").unwrap_err().starts_with("parse error"));
    }
}
