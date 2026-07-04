//! TEST-704 (SPEC-015 REQ-704, CON-701, ADR-701): `(repeat k …)` bounded
//! repetition — install-time macro-expansion into the non-user `#`
//! namespace, chained by `:caused-by` type references.
//!
//! Covered here:
//! - `(repeat 3 x y)` expands to the 6-step chain and matches a
//!   hand-unrolled equivalent under R5/R6 (verdicts and install outcome);
//! - R1 accepts (no template recursion is introduced);
//! - an expansion exceeding declared R2 bounds is a typed install
//!   rejection, and one exceeding the absolute R2 ceiling is a typed
//!   parse rejection before materialisation;
//! - a user dialect declaring a symbol lexically resembling a synthesised
//!   copy name still installs (no collision, by namespace construction —
//!   `#` is outside the symbol alphabet);
//! - bodies ending in `(any a b)` and `(all p q)` seam structurally and
//!   stay chooser-coherent per copy;
//! - `nat` is a post-parse predicate (zero / negative / non-integer
//!   counts are typed rejections) and nested `repeat` multiplies bounds.

use cbcl_core::dialect::{DialectInstallError, DialectRegistry};
use cbcl_core::protocol::{repeat_base_name, NodeRef};
use cbcl_core::r6::r6_violations;
use cbcl_parser::{parse, parse_dialect, parse_protocol, ProtocolParseError};

fn parse_dialect_src(src: &str) -> cbcl_core::dialect::Dialect {
    parse_dialect(&parse(src).expect("sexpr parses")).expect("dialect parses")
}

fn install(src: &str) -> Result<(), DialectInstallError> {
    let d = parse_dialect_src(src);
    let mut reg = DialectRegistry::new();
    reg.install(d)
}

fn single(name: &str) -> NodeRef {
    NodeRef::Single(name.into())
}

// ================================================================
// Expansion shape: (repeat 3 x y) → 6-step chain
// ================================================================

#[test]
fn repeat_3_x_y_expands_to_six_step_chain() {
    let sexpr = parse("(protocol (then begin (repeat 3 x y)))").unwrap();
    let proto = parse_protocol(&sexpr).unwrap();

    // begin plus 6 synthesised steps.
    let expected = ["x#1", "y#1", "x#2", "y#2", "x#3", "y#3"];
    assert_eq!(proto.steps.len(), 1 + expected.len());
    for name in expected {
        assert!(proto.steps.contains_key(name), "missing step {name}");
    }

    // The chain: begin → x#1 → y#1 → x#2 → y#2 → x#3 → y#3.
    assert_eq!(proto.steps["begin"].successors, vec![single("x#1")]);
    assert_eq!(proto.steps["x#1"].predecessors, vec![single("begin")]);
    assert_eq!(proto.steps["x#1"].successors, vec![single("y#1")]);
    assert_eq!(proto.steps["y#1"].successors, vec![single("x#2")]); // seam
    assert_eq!(proto.steps["x#2"].predecessors, vec![single("y#1")]);
    assert_eq!(proto.steps["y#2"].successors, vec![single("x#3")]); // seam
    assert_eq!(proto.steps["y#3"].predecessors, vec![single("x#3")]);
    assert!(proto.steps["y#3"].successors.is_empty());

    // Every synthesised name resolves to its declared base.
    for name in expected {
        assert_eq!(repeat_base_name(name), &name[..1]);
    }
}

// ================================================================
// R1 accepts; R5/R6 verdicts match a hand-unrolled equivalent
// ================================================================

/// The repeat form of the dialect: two roles, x (a→b), y (b→a).
fn repeat_dialect_src() -> &'static str {
    "(define rpt (cbcl) @author \
       (:roles (a b)) \
       (extend x (v) :from a :to (b) (tell @b)) \
       (extend y (v) :from b :to (a) (tell @a)) \
       (protocol (then begin (repeat 3 x y))))"
}

/// Hand-unrolled equivalent: the same six steps declared explicitly.
/// (User symbols cannot contain '#', so the hand form uses x1/y1/…;
/// what must match is the *verdict*, per TEST-704.)
fn hand_unrolled_src() -> &'static str {
    "(define hand (cbcl) @author \
       (:roles (a b)) \
       (extend x1 (v) :from a :to (b) (tell @b)) \
       (extend y1 (v) :from b :to (a) (tell @a)) \
       (extend x2 (v) :from a :to (b) (tell @b)) \
       (extend y2 (v) :from b :to (a) (tell @a)) \
       (extend x3 (v) :from a :to (b) (tell @b)) \
       (extend y3 (v) :from b :to (a) (tell @a)) \
       (protocol (then begin x1 y1 x2 y2 x3 y3)))"
}

#[test]
fn repeat_matches_hand_unrolled_under_r5_r6_and_r1_accepts() {
    let rpt = parse_dialect_src(repeat_dialect_src());
    let hand = parse_dialect_src(hand_unrolled_src());

    // Same expanded size in R2's currency.
    let rp = rpt.causal_protocol.as_ref().unwrap();
    let hp = hand.causal_protocol.as_ref().unwrap();
    assert_eq!(rp.expansion_size(), hp.expansion_size());
    assert_eq!(rp.expansion_size(), 6);

    // R6: identical (empty) verdicts — each copy inherits the base
    // performative's role annotation.
    assert_eq!(r6_violations(&rpt), r6_violations(&hand));
    assert_eq!(r6_violations(&rpt), Vec::new());

    // Full install runs R1 (no template recursion), R2 budget, R3, R5
    // (acyclicity, reachability, definedness via base names), R6.
    assert!(install(repeat_dialect_src()).is_ok());
    assert!(install(hand_unrolled_src()).is_ok());
}

#[test]
fn undefined_base_performative_is_flagged_once_by_r5() {
    // `y` never declared: the protocol's y#1..y#3 all resolve to the same
    // undefined base — one violation, named for the base.
    let src = "(define bad (cbcl) @author \
                 (extend x (v) (tell @x)) \
                 (protocol (then begin (repeat 3 x y))))";
    let err = install(src).unwrap_err();
    match err {
        DialectInstallError::R5Violation { shape_errors, .. } => {
            let about_y: Vec<&String> =
                shape_errors.iter().filter(|e| e.contains("'y'")).collect();
            assert_eq!(about_y.len(), 1, "one violation for base 'y': {shape_errors:?}");
        }
        other => panic!("expected R5Violation, got: {other}"),
    }
}

// ================================================================
// Over-budget: typed install rejection; ceiling: typed parse rejection
// ================================================================

#[test]
fn expansion_exceeding_declared_r2_bounds_is_rejected_at_install() {
    // 20 expanded steps against a declared budget of 8.
    let src = "(define tight (cbcl) @author \
                 (extend x (v) (tell @x)) \
                 (extend y (v) (tell @y)) \
                 (:resource-requirements ((max-depth 8) (max-expansion-size 8) (verification-time 10))) \
                 (protocol (then begin (repeat 10 x y))))";
    let err = install(src).unwrap_err();
    match err {
        DialectInstallError::R2ProtocolBudgetExceeded {
            expanded_steps,
            budget,
            ..
        } => {
            assert_eq!(expanded_steps, 20);
            assert_eq!(budget, 8);
        }
        other => panic!("expected R2ProtocolBudgetExceeded, got: {other}"),
    }
}

#[test]
fn hand_unrolled_protocol_is_priced_identically_at_install() {
    // The same 20 steps written by hand fail the same budget: the
    // declared-bounds currency does not distinguish sugar from unrolling.
    let mut steps = String::from("(then begin");
    let mut extends = String::new();
    for i in 1..=10 {
        extends.push_str(&format!(
            " (extend x{i} (v) (tell @x)) (extend y{i} (v) (tell @y))"
        ));
        steps.push_str(&format!(" x{i} y{i}"));
    }
    steps.push(')');
    let src = format!(
        "(define tight-hand (cbcl) @author{extends} \
           (:resource-requirements ((max-depth 8) (max-expansion-size 8) (verification-time 10))) \
           (protocol {steps}))"
    );
    let err = install(&src).unwrap_err();
    assert!(
        matches!(
            err,
            DialectInstallError::R2ProtocolBudgetExceeded {
                expanded_steps: 20,
                budget: 8,
                ..
            }
        ),
        "got: {err}"
    );
}

#[test]
fn expansion_beyond_absolute_ceiling_is_a_typed_parse_rejection() {
    // 9000 > 8192: no valid dialect could ever accept this, so the parser
    // rejects before materialising.
    let sexpr = parse("(protocol (then begin (repeat 9000 x)))").unwrap();
    let err = parse_protocol(&sexpr).unwrap_err();
    assert!(
        matches!(err, ProtocolParseError::RepeatBudgetExceeded { .. }),
        "got: {err:?}"
    );
}

#[test]
fn nested_repeat_multiplies_bounds() {
    // (repeat 3 (repeat 4 x)) = 12 instances, doubly suffixed.
    let sexpr = parse("(protocol (then begin (repeat 3 (repeat 4 x))))").unwrap();
    let proto = parse_protocol(&sexpr).unwrap();
    assert_eq!(proto.steps.len(), 1 + 12);
    assert!(proto.steps.contains_key("x#1#1"));
    assert!(proto.steps.contains_key("x#4#3"));
    assert_eq!(repeat_base_name("x#4#3"), "x");

    // Multiplicative against the ceiling: 100 × 100 = 10000 > 8192.
    let sexpr = parse("(protocol (then begin (repeat 100 (repeat 100 x))))").unwrap();
    assert!(matches!(
        parse_protocol(&sexpr).unwrap_err(),
        ProtocolParseError::RepeatBudgetExceeded { .. }
    ));
}

// ================================================================
// Namespace: no collision with lexically-similar user symbols
// ================================================================

#[test]
fn lexically_similar_user_symbol_still_installs() {
    // The closest spellings a user *can* write: x1, x-1, x.1. None can
    // collide with the synthesised x#1 — '#' is not a symbol character.
    let src = "(define similar (cbcl) @author \
                 (extend x (v) (tell @x)) \
                 (extend x1 (v) (tell @x)) \
                 (extend x-1 (v) (tell @x)) \
                 (extend x.1 (v) (tell @x)) \
                 (protocol (then begin (repeat 2 x) x1 x-1 x.1)))";
    assert!(install(src).is_ok(), "{:?}", install(src));

    // And the declared x1 is untouched by expansion: distinct from x#1.
    let d = parse_dialect_src(src);
    let proto = d.causal_protocol.unwrap();
    assert!(proto.steps.contains_key("x#1"));
    assert!(proto.steps.contains_key("x1"));
    assert_eq!(repeat_base_name("x1"), "x1"); // a user name is its own base
    assert_eq!(repeat_base_name("x#1"), "x");
}

#[test]
fn copy_names_are_unwritable_in_source() {
    // The alphabet evidence, executed: 'x#1' does not lex as a symbol —
    // '#' starts a boolean literal, so the text form is a parse error.
    assert!(parse("(protocol (then begin x#1))").is_err());
}

#[test]
fn programmatic_hash_symbol_is_rejected_fail_closed() {
    // Off the text path, a hand-built SExpr smuggling '#' into a node-ref
    // is rejected so the namespace stays non-user on every input path.
    use cbcl_core::sexpr::{Atom, SExpr};
    let sym = |s: &str| SExpr::Atom(Atom::Symbol(s.into()));
    let sexpr = SExpr::List(vec![
        sym("protocol"),
        SExpr::List(vec![sym("then"), sym("begin"), sym("x#1")]),
    ]);
    assert!(matches!(
        parse_protocol(&sexpr).unwrap_err(),
        ProtocolParseError::InvalidNodeRef { .. }
    ));
}

// ================================================================
// Structural seams: bodies ending in (any …) and (all …)
// ================================================================

#[test]
fn body_ending_in_any_seams_over_the_alternatives_copy_instances() {
    let sexpr = parse("(protocol (then begin (repeat 2 x (any a b)) done))").unwrap();
    let proto = parse_protocol(&sexpr).unwrap();

    let any_copy = |i: u64| {
        NodeRef::Any(
            [format!("a#{i}"), format!("b#{i}")]
                .into_iter()
                .collect(),
        )
    };
    // Copy 1's choice is the predecessor of copy 2's first step (the seam),
    // and copy 2's choice is the predecessor of the following step.
    assert_eq!(proto.steps["x#2"].predecessors, vec![any_copy(1)]);
    assert_eq!(proto.steps["done"].predecessors, vec![any_copy(2)]);
    // Intra-copy edge: x#i → (any a#i b#i).
    assert_eq!(proto.steps["x#1"].successors, vec![any_copy(1)]);
    assert_eq!(proto.steps["a#1"].predecessors, vec![single("x#1")]);
}

#[test]
fn body_ending_in_all_seams_on_the_fan_ins_copy_instance() {
    let sexpr = parse("(protocol (then begin (repeat 2 x (all p q)) done))").unwrap();
    let proto = parse_protocol(&sexpr).unwrap();

    let all_copy = |i: u64| {
        NodeRef::All(
            [format!("p#{i}"), format!("q#{i}")]
                .into_iter()
                .collect(),
        )
    };
    assert_eq!(proto.steps["x#2"].predecessors, vec![all_copy(1)]);
    assert_eq!(proto.steps["done"].predecessors, vec![all_copy(2)]);
}

#[test]
fn any_seam_stays_chooser_coherent_per_copy() {
    // a and b share the sender r2: each copy's (any a#i b#i) is coherent,
    // so the dialect installs clean.
    let coherent = "(define coh (cbcl) @author \
        (:roles (r1 r2)) \
        (extend x (v) :from r1 :to (r2) (tell @r2)) \
        (extend a (v) :from r2 :to (r1) (tell @r1)) \
        (extend b (v) :from r2 :to (r1) (tell @r1)) \
        (protocol (then begin (repeat 2 x (any a b)))))";
    assert!(install(coherent).is_ok(), "{:?}", install(coherent));

    // Mixed senders (a from r2, b from r1): every copy's choice is
    // incoherent — same verdict a hand-unrolled equivalent would get.
    let incoherent = "(define incoh (cbcl) @author \
        (:roles (r1 r2)) \
        (extend x (v) :from r1 :to (r2) (tell @r2)) \
        (extend a (v) :from r2 :to (r1) (tell @r1)) \
        (extend b (v) :from r1 :to (r2) (tell @r2)) \
        (protocol (then begin (repeat 2 x (any a b)))))";
    let err = install(incoherent).unwrap_err();
    match err {
        DialectInstallError::R6Violation { violations, .. } => {
            // One ChooserIncoherent per copy, over that copy's instances.
            for copy in [
                vec!["a#1".to_string(), "b#1".to_string()],
                vec!["a#2".to_string(), "b#2".to_string()],
            ] {
                assert!(
                    violations.contains(&cbcl_core::role::R6Violation::ChooserIncoherent {
                        members: copy.clone()
                    }),
                    "expected per-copy incoherence for {copy:?}: {violations:?}"
                );
            }
        }
        other => panic!("expected R6Violation, got: {other}"),
    }
}

// ================================================================
// CON-701 nat: post-parse predicate
// ================================================================

#[test]
fn nat_predicate_rejects_zero_negative_and_non_integer_counts() {
    for bad in [
        "(protocol (then begin (repeat 0 x)))",
        "(protocol (then begin (repeat -3 x)))",
        "(protocol (then begin (repeat many x)))",
        "(protocol (then begin (repeat \"3\" x)))",
        "(protocol (then begin (repeat (3) x)))",
    ] {
        let sexpr = parse(bad).unwrap();
        assert!(
            matches!(
                parse_protocol(&sexpr).unwrap_err(),
                ProtocolParseError::RepeatCountNotNat { .. }
            ),
            "expected RepeatCountNotNat for {bad}"
        );
    }
}

#[test]
fn repeat_rejects_empty_body_and_begin_in_body() {
    let sexpr = parse("(protocol (then begin (repeat 3)))").unwrap();
    assert!(matches!(
        parse_protocol(&sexpr).unwrap_err(),
        ProtocolParseError::RepeatEmptyBody
    ));

    let sexpr = parse("(protocol (then a (repeat 3 begin x)))").unwrap();
    assert!(matches!(
        parse_protocol(&sexpr).unwrap_err(),
        ProtocolParseError::RepeatContainsBegin
    ));
}

#[test]
fn repeat_1_is_the_identity_expansion() {
    // k = 1 is a legal nat: one copy, still namespaced.
    let sexpr = parse("(protocol (then begin (repeat 1 x y)))").unwrap();
    let proto = parse_protocol(&sexpr).unwrap();
    assert_eq!(proto.steps.len(), 3);
    assert_eq!(proto.steps["x#1"].successors, vec![single("y#1")]);
}
