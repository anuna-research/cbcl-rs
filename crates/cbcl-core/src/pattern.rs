//! Pattern matching for message dispatch.
//!
//! Mirrors `PatternMatch.lean` from the Lean 4 proof library.

#![forbid(unsafe_code)]

use crate::msg_tag::{msg_tag, MsgTag};
use crate::sexpr::SExpr;

/// A pattern match arm: tag to match and associated handler index.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MatchArm {
    pub tag: MsgTag,
    pub handler_index: usize,
}

/// Dispatch an expression to the first matching arm.
///
/// Returns the handler index of the first matching arm, or None.
pub fn dispatch(expr: &SExpr, arms: &[MatchArm]) -> Option<usize> {
    let tag = msg_tag(expr);
    arms.iter()
        .find(|arm| arm.tag == tag)
        .map(|arm| arm.handler_index)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sexpr::Atom;
    use alloc::vec;

    #[test]
    fn dispatch_matches_head() {
        let expr = SExpr::List(vec![
            SExpr::Atom(Atom::Symbol("tell".into())),
            SExpr::Atom(Atom::Str("data".into())),
        ]);
        let arms = vec![
            MatchArm {
                tag: MsgTag::Head("ask".into()),
                handler_index: 0,
            },
            MatchArm {
                tag: MsgTag::Head("tell".into()),
                handler_index: 1,
            },
        ];
        assert_eq!(dispatch(&expr, &arms), Some(1));
    }

    #[test]
    fn dispatch_returns_none_for_no_match() {
        let expr = SExpr::List(vec![SExpr::Atom(Atom::Symbol("bye".into()))]);
        let arms = vec![MatchArm {
            tag: MsgTag::Head("tell".into()),
            handler_index: 0,
        }];
        assert_eq!(dispatch(&expr, &arms), None);
    }
}
