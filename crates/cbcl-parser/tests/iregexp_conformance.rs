//! SPEC-040 REQ-4003 / TEST-4003: pinned upstream and independent-engine goldens.
use cbcl_core::{
    contracts::{CheckError, DEFAULT_WORK},
    dialect::Dialect,
    sexpr::{Atom, SExpr},
    shape::ShapeRule,
};
use cbcl_parser::dialect_parser::parse_dialect;
use serde_json::Value;

fn install(pattern: &str) -> Result<Dialect, String> {
    let quoted = SExpr::Atom(Atom::Str(pattern.into()));
    let source = format!("(define regex-tests (cbcl) @author (extend submit (to value) (tell to :value value)) (shape submit (require :value (string (matches {quoted})))))");
    parse_dialect(&source.parse::<SExpr>().unwrap())
}
fn matches(dialect: &Dialect, text: &str) -> bool {
    let ShapeRule::Require {
        type_constraint: Some(contract),
        ..
    } = &dialect.shapes[0].rules[0]
    else {
        panic!("required contract")
    };
    match contract.check(&SExpr::Atom(Atom::Str(text.into())), DEFAULT_WORK) {
        Ok(()) => true,
        Err(CheckError::Violation(_)) => false,
        other => panic!(
            "conformance case unexpectedly exhausted resources or lacked compilation: {other:?}"
        ),
    }
}
#[test]
fn upstream_syntax_and_matching_goldens() {
    let fixture: Value = serde_json::from_str(include_str!(
        "../../../test-vectors/contracts/iregexp/upstream-cases.json"
    ))
    .unwrap();
    let syntax = fixture["syntax"].as_array().unwrap();
    for row in syntax {
        let pattern = row["pattern"].as_str().unwrap();
        let result = install(pattern);
        assert_eq!(
            result.is_ok(),
            row["valid"].as_bool().unwrap(),
            "{} {pattern:?}: {result:?}",
            row["origin"]
        );
        if let Err(error) = result {
            assert!(
                !error.contains("resource-limit"),
                "syntax rejection must not be an incidental budget failure: {error}"
            );
        }
    }
    let matching = fixture["matching"].as_array().unwrap();
    for row in matching {
        let pattern = row["pattern"].as_str().unwrap();
        let d = install(pattern)
            .unwrap_or_else(|error| panic!("{} {pattern:?}: {error}", row["origin"]));
        let text = row["text"].as_str().unwrap();
        assert_eq!(
            matches(&d, text),
            row["matches"].as_bool().unwrap(),
            "{} {pattern:?} {text:?}",
            row["origin"]
        );
    }
    eprintln!(
        "{} upstream syntax cases; {} upstream matching cases",
        syntax.len(),
        matching.len()
    );
}
#[test]
fn independent_ecmascript_reference_goldens() {
    let fixture: Value = serde_json::from_str(include_str!(
        "../../../test-vectors/contracts/iregexp/reference-cases.json"
    ))
    .unwrap();
    let samples = fixture["samples"].as_array().unwrap();
    let cases = fixture["cases"].as_array().unwrap();
    for row in cases {
        let pattern = row["pattern"].as_str().unwrap();
        let d = install(pattern).unwrap_or_else(|error| panic!("{pattern:?}: {error}"));
        let expected = row["matches"].as_str().unwrap();
        assert_eq!(expected.len(), samples.len());
        for (text, expected) in samples.iter().zip(expected.bytes()) {
            assert!(expected == b'0' || expected == b'1');
            let text = text.as_str().unwrap();
            assert_eq!(
                matches(&d, text),
                expected == b'1',
                "pattern {pattern:?}, text {text:?}"
            );
        }
    }
    eprintln!(
        "{} independent engine matching cases",
        cases.len() * samples.len()
    );
}

#[test]
fn rfc_literal_anchors_have_positive_and_negative_cases() {
    for (pattern, yes, no) in [("^ab.*", "^abc", "abc"), (".*bc$", "abc$", "abc")] {
        let dialect = install(pattern).unwrap();
        assert!(matches(&dialect, yes), "{pattern:?} must accept {yes:?}");
        assert!(!matches(&dialect, no), "{pattern:?} must reject {no:?}");
    }
}
