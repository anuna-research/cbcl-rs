//! SPEC-001 REQ-046: the parser refuses list nesting deeper than
//! `MAX_NESTING_DEPTH` with an ordinary `ParseError` carrying a byte offset,
//! and never exhausts the stack (BUG-007). Fuel (REQ-043) bounds work by
//! input length, not depth: a 6 KB frame of balanced parentheses overflowed
//! WebKit's WASM stack before the limit existed.
//!
//! The list is the grammar's only recursive form (docs/cbcl-grammar.ebnf,
//! Layer 1): there is no quote, datum comment, vector, or other collection
//! syntax. Strings and `;` comments are scanned iteratively, so parentheses
//! inside them are data and do not count; the tests below pin that.

use cbcl_core::dialect::DialectRegistry;
use cbcl_core::serializer::serialize;
use cbcl_core::sexpr::SExpr;
use cbcl_core::store::ThreadedMessageStore;
use cbcl_parser::parser::{parse, parse_with_fuel, ParseError, MAX_NESTING_DEPTH};
use cbcl_parser::state_exports::{admit_str, dialect_hash_str, fold_str};
use cbcl_parser::{
    define_text_str, describe_dialect_str, parse_message, parse_message_lax, read_act_str,
    read_str, run_pipeline, run_pipeline_full, verify_message_shape_str, PipelineContext,
    PipelineResult,
};

const N: usize = MAX_NESTING_DEPTH;

/// `depth` nested empty lists: `((…))`; its `SExpr::depth()` is `depth`.
fn nest(depth: usize) -> String {
    format!("{}{}", "(".repeat(depth), ")".repeat(depth))
}

/// A `tell` whose content brings the whole frame to list depth `depth`.
fn tell(depth: usize) -> String {
    format!("(tell @room {})", nest(depth - 1))
}

/// The refusal for `tell(N + 1)`: the first '(' past the limit, after the
/// 12-byte `(tell @room ` prefix and the N - 1 content levels before it.
fn tell_refusal() -> ParseError {
    too_deep("(tell @room ".len() + N - 1)
}

fn too_deep(offset: usize) -> ParseError {
    ParseError::NestingTooDeep {
        offset,
        limit: MAX_NESTING_DEPTH,
    }
}

#[test]
fn the_limit_is_conservative_for_webkit() {
    // WebKit overflowed at depth 3000 (source-adapter-rereview2 RR2-1);
    // the limit keeps an order of magnitude of margin below that, and stays
    // far above every corpus frame (deepest dialect: 4).
    assert_eq!(MAX_NESTING_DEPTH, 256);
}

#[test]
fn depth_n_minus_1_and_n_are_accepted_with_canonical_output_unchanged() {
    for depth in [1, N - 1, N] {
        let text = nest(depth);
        let expr = parse(&text).unwrap_or_else(|e| panic!("depth {depth}: {e}"));
        assert_eq!(expr.depth(), depth);
        assert_eq!(serialize(&expr), text, "canonical form at depth {depth}");
        assert_eq!(parse_with_fuel(&text, None), Ok(expr.clone()));
        assert_eq!(parse_with_fuel(&text, Some(usize::MAX)), Ok(expr));
    }
}

#[test]
fn depth_n_plus_1_is_refused_at_the_opening_parenthesis() {
    let text = nest(N + 1);
    assert_eq!(parse(&text), Err(too_deep(N)));
    assert_eq!(parse_with_fuel(&text, None), Err(too_deep(N)));
    assert_eq!(parse_with_fuel(&text, Some(usize::MAX)), Err(too_deep(N)));
    assert_eq!(
        parse(&text).unwrap_err().to_string(),
        "at byte 256: list nesting exceeds limit 256"
    );
}

#[test]
fn the_offset_is_the_byte_of_the_first_parenthesis_past_the_limit() {
    // Leading whitespace, a comment, atoms, and multibyte text before the
    // offending '(' all move the offset by their byte length.
    let prefix = "  ; é(((\n(tell @room \"é(\" ";
    let text = format!("{prefix}{}", nest(N));
    let expected = prefix.len() + (N - 1);
    assert_eq!(parse(&text), Err(too_deep(expected)));
}

#[test]
fn far_over_the_limit_is_refused_on_a_small_stack() {
    // 1,000,000 levels would need hundreds of MB of stack unbounded; a
    // 256 KiB thread proves the refusal happens before any deep recursion.
    let handle = std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(|| {
            let text = format!("(tell @room {}", "(".repeat(1_000_000));
            let first = parse(&text);
            let second = parse(&text);
            let after = parse("(tell @room \"hi\")");
            (first, second, after)
        })
        .unwrap();
    let (first, second, after) = handle.join().expect("no stack overflow");
    assert_eq!(first, Err(tell_refusal()));
    assert_eq!(second, first);
    assert!(after.is_ok());
}

#[test]
fn sibling_lists_do_not_accumulate_depth() {
    // Depth is the nesting of the current path, restored on every ')'.
    let wide = format!("({})", "()".repeat(10_000));
    assert_eq!(parse(&wide).unwrap().depth(), 2);
    let two_deep_subtrees = format!("({}{})", nest(N - 1), nest(N - 1));
    assert_eq!(parse(&two_deep_subtrees).unwrap().depth(), N);
    let many: String = format!("({})", nest(N - 1).repeat(50));
    assert_eq!(parse(&many).unwrap().depth(), N);
}

#[test]
fn every_list_level_counts_whatever_separates_the_parentheses() {
    // Atoms, strings, keywords, booleans, comments and whitespace between
    // levels neither add nor hide depth.
    let level = "(a \"s\" :k #t -1 ; c(\n ";
    let at = |d: usize| format!("{}{}", level.repeat(d), ")".repeat(d));
    assert_eq!(parse(&at(N)).unwrap().depth(), N);
    assert_eq!(parse(&at(N + 1)), Err(too_deep(level.len() * N)));
}

#[test]
fn parentheses_inside_strings_and_comments_are_not_nesting() {
    let deep = "(".repeat(100_000);
    let in_string = format!("(tell @room \"{deep}\")");
    assert_eq!(parse(&in_string).unwrap().depth(), 1);
    let in_comment = format!("; {deep}\n(tell @room \"hi\")");
    assert_eq!(parse(&in_comment).unwrap().depth(), 1);
}

#[test]
fn fuel_still_bounds_work_below_the_limit() {
    // Explicit fuel smaller than the node count still wins: the limit is
    // added to fuel, it does not replace it.
    assert!(matches!(
        parse_with_fuel(&nest(10), Some(5)),
        Err(ParseError::FuelExhausted { .. })
    ));
}

#[test]
fn every_text_entry_point_refuses_through_the_shared_parser() {
    let over = tell(N + 1);
    let reason = tell_refusal().to_string();
    let refusals: Vec<(&str, Result<String, String>)> = vec![
        ("read", read_str(&over)),
        ("define_text", define_text_str(&over)),
        ("describe_dialect", describe_dialect_str(&over)),
        ("read_act", read_act_str(&over)),
        ("verify_message_shape", verify_message_shape_str(&over)),
        ("fold", fold_str(&over)),
        ("admit", admit_str(&over)),
        ("dialect_hash", dialect_hash_str(&over)),
    ];
    for (name, result) in refusals {
        let err = result.expect_err(name);
        assert!(err.contains(&reason), "{name}: {err}");
    }
    assert_eq!(
        run_pipeline(&over),
        PipelineResult::ParseError(tell_refusal())
    );
    let registry = DialectRegistry::new();
    let store = ThreadedMessageStore::new();
    let ctx = PipelineContext::new(&registry, &store);
    assert_eq!(
        run_pipeline_full(&over, &ctx),
        PipelineResult::ParseError(tell_refusal())
    );
    // parse_message / parse_message_lax take a tree: the text reaches them
    // only through parse, which refuses first.
    assert_eq!(parse(&over), Err(tell_refusal()));
}

#[test]
fn every_text_entry_point_survives_depth_n() {
    // Downstream recursion (message recognition, JSON, Debug, canonical
    // serialisation, drop) is bounded by the same limit; at depth N each
    // export runs to an ordinary result rather than a fault.
    let at = tell(N);
    let tree: SExpr = parse(&at).unwrap();
    assert_eq!(tree.depth(), N);
    assert!(parse_message(&tree).is_ok());
    assert!(parse_message_lax(&tree).is_ok());
    assert!(read_str(&at)
        .unwrap()
        .starts_with("[\"tell\",\"@room\",[[["));
    assert!(matches!(run_pipeline(&at), PipelineResult::Success(_)));
    let registry = DialectRegistry::new();
    let store = ThreadedMessageStore::new();
    let ctx = PipelineContext::new(&registry, &store);
    assert!(matches!(
        run_pipeline_full(&at, &ctx),
        PipelineResult::Success(_)
    ));
    let _ = define_text_str(&at);
    let _ = describe_dialect_str(&at);
    let _ = read_act_str(&at);
    let _ = verify_message_shape_str(&at);
    let _ = fold_str(&at);
    let _ = admit_str(&at);
    let _ = format!("{tree:?}");
}

#[test]
fn a_refusal_leaves_the_parser_usable() {
    for _ in 0..3 {
        assert_eq!(parse(&tell(N + 1)), Err(tell_refusal()));
        assert_eq!(parse(&tell(N)).unwrap().depth(), N);
        assert!(parse("(tell @room \"hi\")").is_ok());
    }
}
