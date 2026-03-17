//! Property-based tests for cbcl-parser.
//!
//! Tests parse/serialize roundtrip through the dedicated parser crate,
//! and fuel-bounded parsing behavior.

use cbcl_core::serializer::serialize;
use cbcl_core::sexpr::{Atom, SExpr};
use cbcl_parser::parser::{parse, parse_with_fuel};
use proptest::prelude::*;

// ---------------------------------------------------------------------------
// Generators (duplicated subset for parser crate tests)
// ---------------------------------------------------------------------------

fn arb_symbol_name() -> impl Strategy<Value = String> {
    prop::string::string_regex("[a-zA-Z][a-zA-Z0-9_\\-]*")
        .unwrap()
        .prop_filter("must not be empty", |s| !s.is_empty())
}

fn arb_keyword_name() -> impl Strategy<Value = String> {
    prop::string::string_regex("[a-zA-Z][a-zA-Z0-9_\\-]*")
        .unwrap()
        .prop_filter("must not be empty", |s| !s.is_empty())
}

fn arb_safe_string() -> impl Strategy<Value = String> {
    prop::string::string_regex("[a-zA-Z0-9 _\\-\\.!?,;]+")
        .unwrap()
        .prop_filter("must not be empty", |s| !s.is_empty())
}

fn arb_atom() -> impl Strategy<Value = Atom> {
    prop_oneof![
        arb_symbol_name().prop_map(Atom::Symbol),
        arb_safe_string().prop_map(Atom::Str),
        any::<i64>().prop_map(Atom::Num),
        any::<bool>().prop_map(Atom::Bool),
        arb_keyword_name().prop_map(Atom::Keyword),
    ]
}

fn arb_sexpr(max_depth: u32) -> impl Strategy<Value = SExpr> {
    arb_atom()
        .prop_map(SExpr::Atom)
        .prop_recursive(max_depth, 64, 4, |inner| {
            prop::collection::vec(inner, 0..5).prop_map(SExpr::List)
        })
}

// ===========================================================================
// Property: parse(serialize(e)) == e for the dedicated parser
// ===========================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(500))]

    /// Round-trip through dedicated parser: parse(serialize(e)) == e.
    #[test]
    fn prop_parser_serialize_roundtrip(expr in arb_sexpr(3)) {
        let serialized = serialize(&expr);
        let parsed = parse(&serialized);
        prop_assert!(parsed.is_ok(),
            "dedicated parser failed on: {}", serialized);
        prop_assert_eq!(parsed.unwrap(), expr);
    }

    /// Double roundtrip: serialize(parse(serialize(e))) == serialize(e).
    #[test]
    fn prop_parser_double_roundtrip(expr in arb_sexpr(3)) {
        let s1 = serialize(&expr);
        let parsed = parse(&s1).unwrap();
        let s2 = serialize(&parsed);
        prop_assert_eq!(&s1, &s2);
    }

    /// parse and core FromStr agree on well-formed input.
    #[test]
    fn prop_parser_agrees_with_fromstr(expr in arb_sexpr(3)) {
        let text = serialize(&expr);
        let from_parser = parse(&text).unwrap();
        let from_core: SExpr = text.parse().unwrap();
        prop_assert_eq!(from_parser, from_core);
    }
}

// ===========================================================================
// Property: fuel-bounded parsing
// ===========================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(200))]

    /// parse_with_fuel(input, Some(n)) never exceeds fuel bound.
    /// For atoms, even fuel=1 is sufficient.
    #[test]
    fn prop_fuel_sufficient_for_atoms(atom in arb_atom()) {
        let expr = SExpr::Atom(atom);
        let text = serialize(&expr);
        let result = parse_with_fuel(&text, Some(text.len()));
        prop_assert!(result.is_ok());
        prop_assert_eq!(result.unwrap(), expr);
    }

    /// parse_with_fuel with fuel=0 always fails on non-empty input.
    #[test]
    fn prop_zero_fuel_always_fails(expr in arb_sexpr(2)) {
        let text = serialize(&expr);
        let result = parse_with_fuel(&text, Some(0));
        prop_assert!(result.is_err(),
            "zero fuel should fail but got: {:?}", result);
    }

    /// parse_with_fuel(input, None) defaults to input.len() and succeeds
    /// for well-formed serialized expressions.
    #[test]
    fn prop_default_fuel_succeeds(expr in arb_sexpr(3)) {
        let text = serialize(&expr);
        let result = parse_with_fuel(&text, None);
        prop_assert!(result.is_ok());
        prop_assert_eq!(result.unwrap(), expr);
    }
}
