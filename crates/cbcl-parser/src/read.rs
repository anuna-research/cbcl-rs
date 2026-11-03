//! `read`: the parser's tree for a host that must look inside a frame
//! without recognising it again (SPEC-010 REQ-002: one parser). A client
//! dispatches on a performative, reads `:thread`, or lifts a `(define …)`
//! out of a teach frame; each of those is a read, not a judgement, and
//! every host makes it through this export rather than a reader of its own,
//! so no two readers of one frame can disagree (SPEC-013 REQ-018).
//!
//! The tree is JSON in the shape the web client's reader always produced:
//! a list is an array; a quoted string is `{"str": …}`; a symbol, keyword
//! (with its colon), number, or boolean is its source text.

use alloc::string::String;
use cbcl_core::sexpr::{Atom, SExpr};
use cbcl_core::state::Value;

fn json(expr: &SExpr, out: &mut String) {
    match expr {
        SExpr::List(items) => {
            out.push('[');
            for (i, item) in items.iter().enumerate() {
                if i > 0 {
                    out.push(',');
                }
                json(item, out);
            }
            out.push(']');
        }
        SExpr::Atom(Atom::Str(s)) => {
            out.push_str("{\"str\":");
            out.push_str(&Value::Str(s.clone()).render());
            out.push('}');
        }
        SExpr::Atom(Atom::Symbol(s)) => out.push_str(&Value::Str(s.clone()).render()),
        SExpr::Atom(Atom::Keyword(k)) => {
            let mut text = String::from(":");
            text.push_str(k);
            out.push_str(&Value::Str(text).render());
        }
        SExpr::Atom(Atom::Num(n)) => out.push_str(&Value::Str(alloc::format!("{n}")).render()),
        SExpr::Atom(Atom::Bool(b)) => out.push_str(if *b { "\"#t\"" } else { "\"#f\"" }),
    }
}

/// Parse one S-expression (comments included) and return its tree as JSON.
pub fn read_str(input: &str) -> Result<String, String> {
    let expr = crate::parser::parse(input).map_err(|e| alloc::format!("parse error: {e}"))?;
    let mut out = String::new();
    json(&expr, &mut out);
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tree_shape_matches_the_client_reader() {
        let text = "; a comment\n(lang d (check (@a @b) :item \"a)b\\\"\" :done #t :n -3 :caused-by begin))";
        assert_eq!(
            read_str(text).unwrap(),
            "[\"lang\",\"d\",[\"check\",[\"@a\",\"@b\"],\":item\",{\"str\":\"a)b\\\"\"},\":done\",\"#t\",\":n\",\"-3\",\":caused-by\",\"begin\"]]"
        );
        assert!(read_str("(tell").unwrap_err().starts_with("parse error"));
    }
}
