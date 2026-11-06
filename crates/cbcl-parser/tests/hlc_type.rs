//! SPEC-035 ADR-3504: HLC is a declared shape type, not a magic string field.
use cbcl_core::sexpr::{Atom, SExpr};
use cbcl_core::shape::{ShapeConstraint, TypeConstraint};
use cbcl_parser::{parse, parse_dialect};

const CLOCK: &str = "hlc-000001a3185c5000-00000000";

#[test]
fn hlc_type_recognizes_canonical_strings_without_clock_field_conventions() {
    assert_eq!(TypeConstraint::from_str("hlc"), Some(TypeConstraint::Hlc));
    assert_eq!(TypeConstraint::Hlc.to_string(), "hlc");
    assert!(TypeConstraint::Hlc.matches(&SExpr::Atom(Atom::Str(CLOCK.into()))));
    for malformed in [
        "",
        "ordinary string",
        "hlc-1-0",
        "hlc-000001A3185c5000-00000000",
        "hlc-000001a3185c5000-00000000x",
    ] {
        assert!(!TypeConstraint::Hlc.matches(&SExpr::Atom(Atom::Str(malformed.into()))));
    }
    for malformed in [
        SExpr::Atom(Atom::Symbol(CLOCK.into())),
        SExpr::Atom(Atom::Num(12)),
        SExpr::List(vec![]),
    ] {
        assert!(!TypeConstraint::Hlc.matches(&malformed));
    }
}

fn shape(text: &str) -> ShapeConstraint {
    cbcl_parser::shape_parser::parse_shape(&parse(text).unwrap()).unwrap()
}

#[test]
fn ordinary_required_optional_and_nested_shapes_own_hlc_validation() {
    let required = shape("(shape notice (require :observed-at hlc))");
    assert!(required
        .check(&parse(&format!("(notice @a :observed-at \"{CLOCK}\")")).unwrap())
        .is_ok());
    let error = required
        .check(&parse("(notice @a :observed-at \"invalid\")").unwrap())
        .unwrap_err();
    assert_eq!(error.expected.as_deref(), Some("hlc"));
    assert!(required.check(&parse("(notice @a)").unwrap()).is_err());

    let optional = shape("(shape notice (optional :observed-at hlc))");
    assert!(optional.check(&parse("(notice @a)").unwrap()).is_ok());
    assert!(optional
        .check(&parse("(notice @a :observed-at \"invalid\")").unwrap())
        .is_err());

    let nested = shape("(shape notice (require :envelope list (require :at hlc)))");
    assert!(nested
        .check(&parse(&format!("(notice @a :envelope (:at \"{CLOCK}\"))")).unwrap())
        .is_ok());
    assert!(nested
        .check(&parse("(notice @a :envelope (:at \"invalid\"))").unwrap())
        .is_err());
}

#[test]
fn hlc_is_signature_bound_and_preserved_by_schema_and_authoring() {
    let source = "(define clocks (cbcl) @a (extend open (to when) (tell to :when when)) (shape open (require :when hlc)) (protocol (then begin open)) (state (when (initial open :when))))";
    let typed = parse_dialect(&parse(source).unwrap()).unwrap();
    assert!(cbcl_core::r7::r7_violations(&typed).is_empty());
    let plain =
        parse_dialect(&parse(&source.replace(":when hlc", ":when string")).unwrap()).unwrap();
    assert_ne!(
        cbcl_core::canonical::dialect_name(&typed),
        cbcl_core::canonical::dialect_name(&plain)
    );
    assert_eq!(
        cbcl_core::state::render_schema(&cbcl_core::state::state_schema(
            typed.state.as_ref().unwrap(),
            &typed.shapes
        )),
        "{\"when\":{\"type\":\"opt-scalar\",\"of\":\"hlc\"}}"
    );

    let contract = serde_json::json!({"version":3,"kind":"contract","name":"clocks","author":"@a",
        "verbs":{"open":{"after":["begin"],"fields":{"when":"hlc"}}},
        "state":{"when":["initial","open","when"]}});
    let output: serde_json::Value =
        serde_json::from_str(&cbcl_parser::compile_contract_str(&contract.to_string()).unwrap())
            .unwrap();
    let described: serde_json::Value = serde_json::from_str(
        &cbcl_parser::describe_dialect_str(output["dialect"].as_str().unwrap()).unwrap(),
    )
    .unwrap();
    assert_eq!(described["verbs"]["open"]["fields"]["when"], "hlc");
}
