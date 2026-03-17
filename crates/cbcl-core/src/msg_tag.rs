//! Deterministic message tagging (DCFL).
//!
//! Mirrors `DeterministicUnion.lean` from the Lean 4 proof library.

#![forbid(unsafe_code)]

use crate::sexpr::{Atom, SExpr};
use alloc::string::String;

/// A deterministic message tag (NFR-030).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum MsgTag {
    /// Tagged by head symbol (e.g., `tell`, `ask`).
    Head(String),
    /// Tagged by head + second symbol (for `lang` messages).
    HeadAndSecond(String, String),
    /// Untaggable expression.
    Unknown,
}

/// Compute the deterministic tag of an S-expression (NFR-030–032).
///
/// Examines only the head symbol (or head + second for `lang` messages).
pub fn msg_tag(expr: &SExpr) -> MsgTag {
    match expr {
        SExpr::List(items) if !items.is_empty() => {
            if let SExpr::Atom(Atom::Symbol(head)) = &items[0] {
                if head == "lang" && items.len() > 1 {
                    if let SExpr::Atom(Atom::Symbol(second)) = &items[1] {
                        return MsgTag::HeadAndSecond(head.clone(), second.clone());
                    }
                }
                return MsgTag::Head(head.clone());
            }
            MsgTag::Unknown
        }
        _ => MsgTag::Unknown,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec;

    #[test]
    fn simple_head_tag() {
        let expr = SExpr::List(vec![
            SExpr::Atom(Atom::Symbol("tell".into())),
            SExpr::Atom(Atom::Str("hi".into())),
        ]);
        assert_eq!(msg_tag(&expr), MsgTag::Head("tell".into()));
    }

    #[test]
    fn lang_head_and_second() {
        let expr = SExpr::List(vec![
            SExpr::Atom(Atom::Symbol("lang".into())),
            SExpr::Atom(Atom::Symbol("my-dialect".into())),
        ]);
        assert_eq!(
            msg_tag(&expr),
            MsgTag::HeadAndSecond("lang".into(), "my-dialect".into())
        );
    }

    #[test]
    fn atom_is_unknown() {
        assert_eq!(msg_tag(&SExpr::Atom(Atom::Num(42))), MsgTag::Unknown);
    }

    #[test]
    fn empty_list_is_unknown() {
        assert_eq!(msg_tag(&SExpr::List(vec![])), MsgTag::Unknown);
    }
}
