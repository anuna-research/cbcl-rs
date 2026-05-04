//! Causal protocol parser (REQ-201).
//!
//! Parses `(protocol (then ...)+)` S-expressions into `CausalProtocol`.
//! Desugars variadic `(then a b c)` to pairwise edges: a→b, b→c.

#![forbid(unsafe_code)]

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::string::{String, ToString};
use alloc::vec::Vec;
use cbcl_core::protocol::{CausalProtocol, NodeRef, StepDecl};
use cbcl_core::sexpr::{Atom, SExpr};
use core::fmt;

/// Errors from parsing a `(protocol ...)` declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProtocolParseError {
    /// Top-level form is not a list.
    NotAList,
    /// First element is not `protocol`.
    NotProtocol,
    /// No `(then ...)` declarations found.
    NoThenClauses,
    /// A `(then ...)` clause has fewer than 2 node-refs.
    ThenTooFew,
    /// Expected a `(then ...)` clause but found something else.
    ExpectedThen { found: String },
    /// Node-ref is not a valid symbol, `(any ...)`, or `(all ...)`.
    InvalidNodeRef { detail: String },
    /// `(any ...)` or `(all ...)` has fewer than 2 arguments.
    GroupTooFew { kind: String },
    /// `(any ...)` or `(all ...)` contains a non-symbol argument.
    GroupNonSymbol { kind: String },
}

impl fmt::Display for ProtocolParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NotAList => write!(f, "protocol declaration must be a list"),
            Self::NotProtocol => write!(f, "expected 'protocol' keyword"),
            Self::NoThenClauses => {
                write!(f, "protocol must contain at least one (then ...) clause")
            }
            Self::ThenTooFew => write!(f, "(then ...) requires at least 2 node-refs"),
            Self::ExpectedThen { found } => {
                write!(f, "expected (then ...) clause, found: {found}")
            }
            Self::InvalidNodeRef { detail } => write!(f, "invalid node-ref: {detail}"),
            Self::GroupTooFew { kind } => {
                write!(f, "({kind} ...) requires at least 2 performative-refs")
            }
            Self::GroupNonSymbol { kind } => {
                write!(f, "({kind} ...) arguments must be symbols")
            }
        }
    }
}

/// Parse a `(protocol (then ...)+)` S-expression into a `CausalProtocol` (REQ-201).
pub fn parse_protocol(sexpr: &SExpr) -> Result<CausalProtocol, ProtocolParseError> {
    let items = match sexpr {
        SExpr::List(items) => items,
        _ => return Err(ProtocolParseError::NotAList),
    };

    if items.is_empty() || !items[0].is_symbol("protocol") {
        return Err(ProtocolParseError::NotProtocol);
    }

    if items.len() < 2 {
        return Err(ProtocolParseError::NoThenClauses);
    }

    let mut steps: BTreeMap<String, StepDecl> = BTreeMap::new();

    for clause in &items[1..] {
        let edges = parse_then_clause(clause)?;
        for (pred, succ) in edges {
            // For each performative in the predecessor, record the successor.
            for p in pred.performatives() {
                let step = steps.entry(p.into()).or_insert_with(|| StepDecl {
                    performative: p.into(),
                    predecessors: Vec::new(),
                    successors: Vec::new(),
                });
                step.successors.push(succ.clone());
            }
            // For each performative in the successor, record the predecessor.
            for s in succ.performatives() {
                let step = steps.entry(s.into()).or_insert_with(|| StepDecl {
                    performative: s.into(),
                    predecessors: Vec::new(),
                    successors: Vec::new(),
                });
                step.predecessors.push(pred.clone());
            }
        }
    }

    Ok(CausalProtocol { steps })
}

/// Parse a `(then node-ref node-ref ...)` clause and return pairwise edges.
///
/// Variadic: `(then a b c)` desugars to edges `[(a, b), (b, c)]`.
fn parse_then_clause(sexpr: &SExpr) -> Result<Vec<(NodeRef, NodeRef)>, ProtocolParseError> {
    let items = match sexpr {
        SExpr::List(items) if !items.is_empty() => items,
        SExpr::List(_) => {
            return Err(ProtocolParseError::ExpectedThen {
                found: "empty list".into(),
            })
        }
        _ => {
            return Err(ProtocolParseError::ExpectedThen {
                found: alloc::format!("{sexpr}"),
            })
        }
    };

    if !items[0].is_symbol("then") {
        return Err(ProtocolParseError::ExpectedThen {
            found: alloc::format!("{}", items[0]),
        });
    }

    let refs: Vec<NodeRef> = items[1..]
        .iter()
        .map(parse_node_ref)
        .collect::<Result<_, _>>()?;

    if refs.len() < 2 {
        return Err(ProtocolParseError::ThenTooFew);
    }

    // Desugar variadic to pairwise edges.
    let edges = refs
        .windows(2)
        .map(|w| (w[0].clone(), w[1].clone()))
        .collect();
    Ok(edges)
}

/// Parse a node-ref: bare symbol, `(any ...)`, or `(all ...)`.
fn parse_node_ref(sexpr: &SExpr) -> Result<NodeRef, ProtocolParseError> {
    match sexpr {
        SExpr::Atom(Atom::Symbol(s)) => Ok(NodeRef::Single(s.clone())),
        SExpr::List(items) if !items.is_empty() => {
            let head = match &items[0] {
                SExpr::Atom(Atom::Symbol(s)) => s.as_str(),
                _ => {
                    return Err(ProtocolParseError::InvalidNodeRef {
                        detail: alloc::format!("list head is not a symbol: {}", items[0]),
                    })
                }
            };

            match head {
                "any" | "all" => {
                    let kind = head.to_string();
                    if items.len() < 3 {
                        return Err(ProtocolParseError::GroupTooFew { kind: kind.clone() });
                    }
                    let mut set = BTreeSet::new();
                    for item in &items[1..] {
                        match item {
                            SExpr::Atom(Atom::Symbol(s)) => {
                                set.insert(s.clone());
                            }
                            _ => {
                                return Err(ProtocolParseError::GroupNonSymbol {
                                    kind: kind.clone(),
                                })
                            }
                        }
                    }
                    if head == "any" {
                        Ok(NodeRef::Any(set))
                    } else {
                        Ok(NodeRef::All(set))
                    }
                }
                _ => Err(ProtocolParseError::InvalidNodeRef {
                    detail: alloc::format!("unknown node-ref head: {head}"),
                }),
            }
        }
        _ => Err(ProtocolParseError::InvalidNodeRef {
            detail: alloc::format!("{sexpr}"),
        }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec;
    use cbcl_core::sexpr::{Atom, SExpr};

    fn sym(s: &str) -> SExpr {
        SExpr::Atom(Atom::Symbol(String::from(s)))
    }

    fn list(items: Vec<SExpr>) -> SExpr {
        SExpr::List(items)
    }

    // ================================================================
    // TEST-201: Compaction — pure sequence
    // ================================================================

    #[test]
    fn parse_compaction_protocol() {
        // (protocol (then begin pause pause-ack get-memory memory-dump set-memory set-memory-ack resume))
        let sexpr = list(vec![
            sym("protocol"),
            list(vec![
                sym("then"),
                sym("begin"),
                sym("pause"),
                sym("pause-ack"),
                sym("get-memory"),
                sym("memory-dump"),
                sym("set-memory"),
                sym("set-memory-ack"),
                sym("resume"),
            ]),
        ]);
        let proto = parse_protocol(&sexpr).unwrap();
        // begin -> pause -> pause-ack -> ... -> resume (7 edges)
        assert!(proto.steps.contains_key("begin"));
        assert!(proto.steps.contains_key("resume"));
        assert_eq!(proto.steps["begin"].successors.len(), 1);
        assert_eq!(
            proto.steps["begin"].successors[0],
            NodeRef::Single("pause".into())
        );
        assert_eq!(proto.steps["pause"].predecessors.len(), 1);
        assert_eq!(
            proto.steps["pause"].predecessors[0],
            NodeRef::Single("begin".into())
        );
        assert_eq!(proto.steps["resume"].predecessors.len(), 1);
        assert!(proto.steps["resume"].successors.is_empty());
    }

    // ================================================================
    // TEST-201: Document operations — choice + concurrent fan-out
    // ================================================================

    #[test]
    fn parse_document_ops_protocol() {
        // (protocol
        //   (then begin (any read write close))
        //   (then read content)
        //   (then write ack)
        //   (then (any content ack) (any read write close)))
        let sexpr = list(vec![
            sym("protocol"),
            list(vec![
                sym("then"),
                sym("begin"),
                list(vec![sym("any"), sym("read"), sym("write"), sym("close")]),
            ]),
            list(vec![sym("then"), sym("read"), sym("content")]),
            list(vec![sym("then"), sym("write"), sym("ack")]),
            list(vec![
                sym("then"),
                list(vec![sym("any"), sym("content"), sym("ack")]),
                list(vec![sym("any"), sym("read"), sym("write"), sym("close")]),
            ]),
        ]);
        let proto = parse_protocol(&sexpr).unwrap();
        assert!(proto.steps.contains_key("begin"));
        assert!(proto.steps.contains_key("read"));
        assert!(proto.steps.contains_key("write"));
        assert!(proto.steps.contains_key("close"));
        assert!(proto.steps.contains_key("content"));
        assert!(proto.steps.contains_key("ack"));

        // begin has one successor: (any read write close)
        assert_eq!(proto.steps["begin"].successors.len(), 1);
        let expected_any: BTreeSet<String> = ["read", "write", "close"]
            .iter()
            .map(|s| String::from(*s))
            .collect();
        assert_eq!(
            proto.steps["begin"].successors[0],
            NodeRef::Any(expected_any)
        );
    }

    // ================================================================
    // TEST-201: Request-response loop
    // ================================================================

    #[test]
    fn parse_request_response_protocol() {
        // (protocol (then (any begin response) request response))
        let sexpr = list(vec![
            sym("protocol"),
            list(vec![
                sym("then"),
                list(vec![sym("any"), sym("begin"), sym("response")]),
                sym("request"),
                sym("response"),
            ]),
        ]);
        let proto = parse_protocol(&sexpr).unwrap();
        assert!(proto.steps.contains_key("begin"));
        assert!(proto.steps.contains_key("request"));
        assert!(proto.steps.contains_key("response"));
        // request has predecessor (any begin response) and successor response
        assert_eq!(proto.steps["request"].predecessors.len(), 1);
        assert_eq!(proto.steps["request"].successors.len(), 1);
        assert_eq!(
            proto.steps["request"].successors[0],
            NodeRef::Single("response".into())
        );
    }

    // ================================================================
    // TEST-201: Scatter-gather — concurrent fan-out then fan-in
    // ================================================================

    #[test]
    fn parse_scatter_gather_protocol() {
        // (protocol
        //   (then begin (all search-a search-b search-c))
        //   (then search-a result-a)
        //   (then search-b result-b)
        //   (then search-c result-c)
        //   (then (all result-a result-b result-c) merge-results))
        let sexpr = list(vec![
            sym("protocol"),
            list(vec![
                sym("then"),
                sym("begin"),
                list(vec![
                    sym("all"),
                    sym("search-a"),
                    sym("search-b"),
                    sym("search-c"),
                ]),
            ]),
            list(vec![sym("then"), sym("search-a"), sym("result-a")]),
            list(vec![sym("then"), sym("search-b"), sym("result-b")]),
            list(vec![sym("then"), sym("search-c"), sym("result-c")]),
            list(vec![
                sym("then"),
                list(vec![
                    sym("all"),
                    sym("result-a"),
                    sym("result-b"),
                    sym("result-c"),
                ]),
                sym("merge-results"),
            ]),
        ]);
        let proto = parse_protocol(&sexpr).unwrap();
        assert!(proto.steps.contains_key("begin"));
        assert!(proto.steps.contains_key("merge-results"));
        assert!(proto.steps.contains_key("search-a"));
        assert!(proto.steps.contains_key("result-a"));

        // merge-results predecessor is (all result-a result-b result-c)
        assert_eq!(proto.steps["merge-results"].predecessors.len(), 1);
        let expected_all: BTreeSet<String> = ["result-a", "result-b", "result-c"]
            .iter()
            .map(|s| String::from(*s))
            .collect();
        assert_eq!(
            proto.steps["merge-results"].predecessors[0],
            NodeRef::All(expected_all)
        );
    }

    // ================================================================
    // TEST-201: Two-phase commit
    // ================================================================

    #[test]
    fn parse_two_phase_commit_protocol() {
        // (protocol
        //   (then begin prepare)
        //   (then prepare (any vote-yes vote-no))
        //   (then (all vote-yes vote-yes) commit)
        //   (then vote-no abort))
        let sexpr = list(vec![
            sym("protocol"),
            list(vec![sym("then"), sym("begin"), sym("prepare")]),
            list(vec![
                sym("then"),
                sym("prepare"),
                list(vec![sym("any"), sym("vote-yes"), sym("vote-no")]),
            ]),
            list(vec![
                sym("then"),
                list(vec![sym("all"), sym("vote-yes"), sym("vote-yes")]),
                sym("commit"),
            ]),
            list(vec![sym("then"), sym("vote-no"), sym("abort")]),
        ]);
        let proto = parse_protocol(&sexpr).unwrap();
        assert!(proto.steps.contains_key("begin"));
        assert!(proto.steps.contains_key("prepare"));
        assert!(proto.steps.contains_key("vote-yes"));
        assert!(proto.steps.contains_key("vote-no"));
        assert!(proto.steps.contains_key("commit"));
        assert!(proto.steps.contains_key("abort"));
    }

    // ================================================================
    // Error cases
    // ================================================================

    #[test]
    fn reject_non_list() {
        assert_eq!(
            parse_protocol(&sym("protocol")).unwrap_err(),
            ProtocolParseError::NotAList
        );
    }

    #[test]
    fn reject_not_protocol() {
        let sexpr = list(vec![
            sym("not-protocol"),
            list(vec![sym("then"), sym("a"), sym("b")]),
        ]);
        assert_eq!(
            parse_protocol(&sexpr).unwrap_err(),
            ProtocolParseError::NotProtocol
        );
    }

    #[test]
    fn reject_empty_protocol() {
        let sexpr = list(vec![sym("protocol")]);
        assert_eq!(
            parse_protocol(&sexpr).unwrap_err(),
            ProtocolParseError::NoThenClauses
        );
    }

    #[test]
    fn reject_then_too_few() {
        let sexpr = list(vec![sym("protocol"), list(vec![sym("then"), sym("a")])]);
        assert_eq!(
            parse_protocol(&sexpr).unwrap_err(),
            ProtocolParseError::ThenTooFew
        );
    }

    #[test]
    fn reject_non_then_clause() {
        let sexpr = list(vec![
            sym("protocol"),
            list(vec![sym("not-then"), sym("a"), sym("b")]),
        ]);
        assert!(matches!(
            parse_protocol(&sexpr).unwrap_err(),
            ProtocolParseError::ExpectedThen { .. }
        ));
    }

    #[test]
    fn reject_any_too_few() {
        let sexpr = list(vec![
            sym("protocol"),
            list(vec![
                sym("then"),
                list(vec![sym("any"), sym("a")]),
                sym("b"),
            ]),
        ]);
        assert!(matches!(
            parse_protocol(&sexpr).unwrap_err(),
            ProtocolParseError::GroupTooFew { .. }
        ));
    }

    #[test]
    fn reject_all_too_few() {
        let sexpr = list(vec![
            sym("protocol"),
            list(vec![
                sym("then"),
                list(vec![sym("all"), sym("a")]),
                sym("b"),
            ]),
        ]);
        assert!(matches!(
            parse_protocol(&sexpr).unwrap_err(),
            ProtocolParseError::GroupTooFew { .. }
        ));
    }

    #[test]
    fn reject_group_non_symbol() {
        let sexpr = list(vec![
            sym("protocol"),
            list(vec![
                sym("then"),
                list(vec![sym("any"), sym("a"), list(vec![sym("nested")])]),
                sym("b"),
            ]),
        ]);
        assert!(matches!(
            parse_protocol(&sexpr).unwrap_err(),
            ProtocolParseError::GroupNonSymbol { .. }
        ));
    }

    // ================================================================
    // Round-trip from text
    // ================================================================

    #[test]
    fn parse_from_text_compaction() {
        let input = "(protocol (then begin pause pause-ack get-memory memory-dump set-memory set-memory-ack resume))";
        let sexpr = crate::parser::parse(input).unwrap();
        let proto = parse_protocol(&sexpr).unwrap();
        assert_eq!(proto.steps.len(), 8);
    }

    #[test]
    fn parse_from_text_scatter_gather() {
        let input = "(protocol (then begin (all search-a search-b search-c)) (then search-a result-a) (then search-b result-b) (then search-c result-c) (then (all result-a result-b result-c) merge-results))";
        let sexpr = crate::parser::parse(input).unwrap();
        let proto = parse_protocol(&sexpr).unwrap();
        assert!(proto.steps.contains_key("merge-results"));
    }
}
