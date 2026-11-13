use cbcl_core::{
    canonical::canonical_encode,
    sexpr::{Atom, SExpr},
    shape::TypeConstraint,
};
use cbcl_parser::parse;

#[test]
fn numeric_roundtrip_and_canonical_normalization() {
    for (source, expected) in [
        ("1.25", "1.25"),
        ("1e2", "100.0"),
        ("-0.0", "0.0"),
        ("001.2300m", "1.23m"),
        ("-000.000m", "0m"),
        (
            "9007199254740993.12345678901234567890m",
            "9007199254740993.1234567890123456789m",
        ),
    ] {
        let atom = parse(source).unwrap();
        assert_eq!(atom.to_string(), expected);
        assert_eq!(cbcl_core::serializer::serialize(&atom), expected);
        assert_eq!(parse(expected).unwrap(), atom);
        assert_eq!(expected.parse::<SExpr>().unwrap(), atom);
        assert_eq!(
            canonical_encode(&atom),
            canonical_encode(&parse(expected).unwrap())
        );
        assert!(TypeConstraint::Integer
            .check(&atom, cbcl_core::contracts::DEFAULT_WORK)
            .is_err());
    }
    assert!(TypeConstraint::Float
        .check(&parse("1e2").unwrap(), cbcl_core::contracts::DEFAULT_WORK)
        .is_ok());
    assert!(TypeConstraint::Float
        .check(&parse("100m").unwrap(), cbcl_core::contracts::DEFAULT_WORK)
        .is_err());
    assert!(TypeConstraint::Decimal
        .check(&parse("100m").unwrap(), cbcl_core::contracts::DEFAULT_WORK)
        .is_ok());
    assert!(TypeConstraint::Nonnegative
        .check(&parse("1.5").unwrap(), cbcl_core::contracts::DEFAULT_WORK)
        .is_err());
    let atoms = [
        parse("1").unwrap(),
        parse("1.0").unwrap(),
        parse("1m").unwrap(),
        parse("\"1\"").unwrap(),
    ];
    for (i, a) in atoms.iter().enumerate() {
        for b in &atoms[i + 1..] {
            assert_ne!(canonical_encode(a), canonical_encode(b));
        }
    }
}

#[test]
fn invalid_numbers_fail_closed() {
    for text in ["1e9999", "1e", "1.2.3", "1..0m", "1e2m", "1.m"] {
        assert!(parse(text).is_err(), "{text}");
    }
    assert!(cbcl_core::numeric::Float::new(f64::NAN).is_err());
    assert!(cbcl_core::numeric::Float::new(f64::INFINITY).is_err());
}

#[test]
fn decimal_survives_state_and_serde_without_precision_loss() {
    let atom = parse("9007199254740993.1234567890123456789m").unwrap();
    let encoded = serde_json::to_string(&atom).unwrap();
    assert_eq!(serde_json::from_str::<SExpr>(&encoded).unwrap(), atom);
    let rendered = cbcl_core::state::Value::from_sexpr(&atom).render();
    assert_eq!(
        rendered,
        r#"{"decimal":"9007199254740993.1234567890123456789"}"#
    );
    assert!(matches!(parse("1").unwrap(), SExpr::Atom(Atom::Num(1))));
}

proptest::proptest! {
    #[test]
    fn finite_floats_roundtrip(bits in proptest::prelude::any::<u64>()) {
        if let Ok(value) = cbcl_core::numeric::Float::new(f64::from_bits(bits)) {
            let atom = SExpr::Atom(Atom::Float(value));
            proptest::prop_assert_eq!(parse(&atom.to_string()).unwrap(), atom);
        }
    }
}

#[test]
fn typed_state_fields_install_and_enforce_numeric_bounds() {
    let d = cbcl_parser::parse_dialect(&parse("(define prices (cbcl) @author (extend open (to price ratio) (tell to :price price :ratio ratio)) (protocol (then begin open)) (shape open (require :price decimal) (require :ratio float)) (state (price (initial open :price)) (ratio (initial open :ratio))))").unwrap()).unwrap();
    assert!(
        cbcl_core::r7::r7_violations(&d).is_empty(),
        "{:?}",
        cbcl_core::r7::r7_violations(&d)
    );
    let message = |price: &str, ratio: &str| {
        cbcl_parser::parse_message(
            &parse(&format!(
                "(lang prices (open @bob :price {price} :ratio {ratio}))"
            ))
            .unwrap(),
        )
        .unwrap()
    };
    assert!(cbcl_core::r7::verify_state_shape(&d, &message("12.34m", "0.5")).is_ok());
    assert!(
        cbcl_core::r7::verify_state_shape(&d, &message("999999999999999999999m", "0.5")).is_err()
    );
    assert!(cbcl_core::r7::verify_state_shape(&d, &message("12.34m", "1e300")).is_err());
}
