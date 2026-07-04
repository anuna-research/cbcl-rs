//! Causal protocol parser (REQ-201, SPEC-015 REQ-704).
//!
//! Parses `(protocol (then ...)+)` S-expressions into `CausalProtocol`.
//! Desugars variadic `(then a b c)` to pairwise edges: a→b, b→c.
//!
//! ## Bounded repetition (SPEC-015 REQ-704, CON-701)
//!
//! A `(repeat <k> <step>…)` form may appear in step position inside a
//! `(then …)` chain (and nowhere else); `<k>` is a `nat` (post-parse
//! predicate: positive integer atom) and each `<step>` is a node-ref or a
//! nested `repeat`. The form macro-expands **once, at parse** into `k`
//! sequential copies of its body spliced into the enclosing chain, so the
//! ordinary pairwise-edge desugaring chains the copies by `:caused-by`
//! type references and R1–R3, R5, R6 run over the *expanded* protocol.
//!
//! Synthesised copy names live in a non-user namespace: copy `i` of step
//! `x` is `x#i`, and `'#'` ([`cbcl_core::protocol::REPEAT_SEPARATOR`]) is
//! outside the legal symbol alphabet (`parser::is_symbol_char`; it
//! introduces `#t`/`#f`), so collision with any user-declared performative
//! is impossible by construction. Iteration seams are structural: a body
//! ending in `(any a b)` seams as `(any a#i b#i) → first-of-copy-i+1`
//! (the choice over the alternatives' copy-instances), one ending in
//! `(all …)` seams on the fan-in's copy-instance; nested `repeat`
//! multiplies bounds and suffixes again (`x#1#2`).

#![forbid(unsafe_code)]

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::string::{String, ToString};
use alloc::vec::Vec;
use cbcl_core::protocol::{CausalProtocol, NodeRef, StepDecl, BEGIN_KEYWORD, REPEAT_SEPARATOR};
use cbcl_core::sexpr::{Atom, SExpr};
use core::fmt;

/// Absolute ceiling on `(repeat …)` macro-expansion, equal to the largest
/// `max-expansion-size` any valid dialect may declare (R2,
/// `ResourceBounds::is_valid` caps it at 8192). An expansion beyond this
/// can never install, so the parser rejects it *before materialising it*
/// (typed, fail closed); the dialect's own declared budget is enforced
/// separately at install (SPEC-015 REQ-704).
const REPEAT_EXPANSION_CEILING: u64 = 8192;

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
    /// `(repeat ...)` count is not a `nat` (CON-701): a positive integer
    /// atom. Zero, negatives, and non-integer atoms are all rejected.
    RepeatCountNotNat { found: String },
    /// `(repeat ...)` has no protocol-steps in its body (CON-701 requires
    /// `protocol-step+`).
    RepeatEmptyBody,
    /// `(repeat ...)` body references `begin`; the protocol root is a
    /// keyword, not a repeatable step.
    RepeatContainsBegin,
    /// `(repeat ...)` expansion (nested repeats multiply) exceeds the
    /// absolute R2 ceiling — rejected before materialisation.
    RepeatBudgetExceeded { steps: u64 },
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
            Self::RepeatCountNotNat { found } => {
                write!(
                    f,
                    "(repeat ...) count must be a positive integer (CON-701 nat), found: {found}"
                )
            }
            Self::RepeatEmptyBody => {
                write!(f, "(repeat ...) requires at least one protocol-step")
            }
            Self::RepeatContainsBegin => {
                write!(f, "(repeat ...) body must not reference 'begin'")
            }
            Self::RepeatBudgetExceeded { steps } => {
                write!(
                    f,
                    "(repeat ...) expands to {steps} step instances, exceeding the \
                     R2 expansion ceiling {REPEAT_EXPANSION_CEILING}"
                )
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

    // One expansion budget for the whole protocol: every step instance a
    // `(repeat …)` form materialises is charged against the absolute R2
    // ceiling, so the parser's output size stays bounded by construction
    // (SPEC-015 REQ-704).
    let mut expansion_used: u64 = 0;

    for clause in &items[1..] {
        let edges = parse_then_clause(clause, &mut expansion_used)?;
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

/// Parse a `(then protocol-step ...)` clause and return pairwise edges.
///
/// Variadic: `(then a b c)` desugars to edges `[(a, b), (b, c)]`.
/// A `(repeat k …)` form in step position (SPEC-015 REQ-704) is
/// macro-expanded here — its copies splice into the chain, so the
/// pairwise desugaring produces both the intra-copy edges and the
/// structural seam edges between consecutive copies.
fn parse_then_clause(
    sexpr: &SExpr,
    expansion_used: &mut u64,
) -> Result<Vec<(NodeRef, NodeRef)>, ProtocolParseError> {
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

    let mut refs: Vec<NodeRef> = Vec::new();
    for item in &items[1..] {
        if is_repeat_form(item) {
            expand_repeat(item, &mut refs, expansion_used)?;
        } else {
            refs.push(parse_node_ref(item)?);
        }
    }

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

/// Is this S-expression a `(repeat …)` form?
fn is_repeat_form(sexpr: &SExpr) -> bool {
    matches!(sexpr, SExpr::List(items) if !items.is_empty() && items[0].is_symbol("repeat"))
}

/// CON-701 `nat`: a post-parse predicate on the recognised atom — the
/// atom must be an integer and positive. The S-expression lexer
/// recognises integer text into a canonical `i64` atom (a leading-zero
/// spelling does not survive recognition as a distinct atom), so the
/// predicate here is positivity on the recognised integer; zero,
/// negatives, symbols, strings, and lists are all typed rejections.
fn parse_nat(sexpr: &SExpr) -> Result<u64, ProtocolParseError> {
    match sexpr {
        SExpr::Atom(Atom::Num(n)) if *n >= 1 => Ok(*n as u64),
        other => Err(ProtocolParseError::RepeatCountNotNat {
            found: alloc::format!("{other}"),
        }),
    }
}

/// Charge `n` synthesised step instances against the protocol-wide
/// expansion budget; over the ceiling is a typed rejection *before*
/// anything is materialised.
fn charge_expansion(used: &mut u64, n: u64) -> Result<(), ProtocolParseError> {
    let total = used.saturating_add(n);
    if total > REPEAT_EXPANSION_CEILING {
        return Err(ProtocolParseError::RepeatBudgetExceeded { steps: total });
    }
    *used = total;
    Ok(())
}

/// Suffix every performative name in a node-ref with the copy index,
/// producing the copy-instance in the non-user `#` namespace:
/// `x` → `x#i`, `(any a b)` → `(any a#i b#i)`, `(all p q)` → `(all p#i q#i)`.
fn suffix_node_ref(nr: &NodeRef, index: u64) -> NodeRef {
    let suffix = |s: &String| alloc::format!("{s}{REPEAT_SEPARATOR}{index}");
    match nr {
        NodeRef::Single(s) => NodeRef::Single(suffix(s)),
        NodeRef::Any(set) => NodeRef::Any(set.iter().map(suffix).collect()),
        NodeRef::All(set) => NodeRef::All(set.iter().map(suffix).collect()),
    }
}

/// Macro-expand a `(repeat <k> <step>…)` form (SPEC-015 REQ-704, CON-701)
/// into `k` sequential copies of its body, appended to `out` so the
/// enclosing `(then …)` chain's pairwise desugaring wires the copies
/// together. Seams are structural: whatever node-ref ends the body —
/// single, `(any …)` choice, or `(all …)` fan-in — its copy-instance is
/// the predecessor of the next copy's first step.
///
/// Nested `repeat` expands innermost-first (its instances are suffixed
/// again by the outer form) and multiplies the charged budget.
fn expand_repeat(
    sexpr: &SExpr,
    out: &mut Vec<NodeRef>,
    used: &mut u64,
) -> Result<(), ProtocolParseError> {
    let items = match sexpr {
        SExpr::List(items) if !items.is_empty() && items[0].is_symbol("repeat") => items,
        _ => {
            return Err(ProtocolParseError::InvalidNodeRef {
                detail: alloc::format!("{sexpr}"),
            })
        }
    };
    if items.len() < 2 {
        return Err(ProtocolParseError::RepeatCountNotNat {
            found: "<missing>".into(),
        });
    }
    let k = parse_nat(&items[1])?;
    if items.len() < 3 {
        return Err(ProtocolParseError::RepeatEmptyBody);
    }

    // Parse the body: node-refs or nested repeat forms. Each materialised
    // instance is charged as it is produced.
    let mut body: Vec<NodeRef> = Vec::new();
    for step in &items[2..] {
        if is_repeat_form(step) {
            expand_repeat(step, &mut body, used)?;
        } else {
            let nr = parse_node_ref(step)?;
            if nr.performatives().any(|p| p == BEGIN_KEYWORD) {
                return Err(ProtocolParseError::RepeatContainsBegin);
            }
            charge_expansion(used, 1)?;
            body.push(nr);
        }
    }

    // The body's own instances were charged while parsing; the remaining
    // k−1 copies are charged multiplicatively (nested repeat therefore
    // multiplies bounds), before materialisation.
    let extra = (k - 1)
        .checked_mul(body.len() as u64)
        .ok_or(ProtocolParseError::RepeatBudgetExceeded { steps: u64::MAX })?;
    charge_expansion(used, extra)?;

    for i in 1..=k {
        out.extend(body.iter().map(|nr| suffix_node_ref(nr, i)));
    }
    Ok(())
}

/// Reject a symbol that trespasses on the synthesised-copy namespace.
///
/// The text parser can never produce a symbol containing
/// [`REPEAT_SEPARATOR`] (`'#'` is outside `is_symbol_char`), so this only
/// fires for programmatically built S-expression trees — kept fail-closed
/// so the non-user namespace stays non-user on every input path.
fn check_user_symbol(s: &str) -> Result<(), ProtocolParseError> {
    if s.contains(REPEAT_SEPARATOR) {
        return Err(ProtocolParseError::InvalidNodeRef {
            detail: alloc::format!(
                "'{s}' contains '{REPEAT_SEPARATOR}', reserved for synthesised repeat copies"
            ),
        });
    }
    Ok(())
}

/// Parse a node-ref: bare symbol, `(any ...)`, or `(all ...)`.
fn parse_node_ref(sexpr: &SExpr) -> Result<NodeRef, ProtocolParseError> {
    match sexpr {
        SExpr::Atom(Atom::Symbol(s)) => {
            check_user_symbol(s)?;
            Ok(NodeRef::Single(s.clone()))
        }
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
                                check_user_symbol(s)?;
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
