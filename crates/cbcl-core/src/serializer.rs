//! Canonical S-expression serialization.
//!
//! Mirrors `Serializer.lean` from the Lean 4 proof library.

#![forbid(unsafe_code)]

use crate::sexpr::{Atom, SExpr};
use alloc::string::String;

/// Serialize an S-expression to canonical text (REQ-050).
///
/// Round-trip guarantee: `parse(serialize(e)) == Ok(e)` for all valid `e`.
pub fn serialize(sexpr: &SExpr) -> String {
    let mut buf = String::new();
    write_sexpr(sexpr, &mut buf);
    buf
}

fn write_sexpr(sexpr: &SExpr, buf: &mut String) {
    match sexpr {
        SExpr::Atom(atom) => write_atom(atom, buf),
        SExpr::List(items) => {
            buf.push('(');
            for (i, item) in items.iter().enumerate() {
                if i > 0 {
                    buf.push(' ');
                }
                write_sexpr(item, buf);
            }
            buf.push(')');
        }
    }
}

fn write_atom(atom: &Atom, buf: &mut String) {
    match atom {
        Atom::Symbol(s) => buf.push_str(s),
        Atom::Str(s) => {
            buf.push('"');
            for ch in s.chars() {
                match ch {
                    '"' => buf.push_str("\\\""),
                    '\\' => buf.push_str("\\\\"),
                    '\n' => buf.push_str("\\n"),
                    '\r' => buf.push_str("\\r"),
                    '\t' => buf.push_str("\\t"),
                    c => buf.push(c),
                }
            }
            buf.push('"');
        }
        Atom::Num(n) => {
            use alloc::format;
            buf.push_str(&format!("{n}"));
        }
        Atom::Bool(b) => buf.push_str(if *b { "#t" } else { "#f" }),
        Atom::Keyword(k) => {
            buf.push(':');
            buf.push_str(k);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec;

    #[test]
    fn serialize_atom_types() {
        assert_eq!(
            serialize(&SExpr::Atom(Atom::Symbol("hello".into()))),
            "hello"
        );
        assert_eq!(serialize(&SExpr::Atom(Atom::Num(42))), "42");
        assert_eq!(serialize(&SExpr::Atom(Atom::Num(-7))), "-7");
        assert_eq!(serialize(&SExpr::Atom(Atom::Bool(true))), "#t");
        assert_eq!(serialize(&SExpr::Atom(Atom::Bool(false))), "#f");
        assert_eq!(serialize(&SExpr::Atom(Atom::Keyword("key".into()))), ":key");
    }

    #[test]
    fn serialize_string_escapes() {
        assert_eq!(
            serialize(&SExpr::Atom(Atom::Str("a\"b\\c\n".into()))),
            "\"a\\\"b\\\\c\\n\""
        );
    }

    #[test]
    fn serialize_list() {
        let l = SExpr::List(vec![
            SExpr::Atom(Atom::Symbol("tell".into())),
            SExpr::Atom(Atom::Str("hi".into())),
        ]);
        assert_eq!(serialize(&l), "(tell \"hi\")");
    }

    #[test]
    fn serialize_empty_list() {
        assert_eq!(serialize(&SExpr::List(vec![])), "()");
    }
}
