//! SPEC-040 REQ-4006: actionable constraint diagnostics without field contents.
use cbcl_core::{dialect::Dialect, sexpr::SExpr};
use cbcl_parser::{
    dialect_parser::parse_dialect, shape_exports::verify_message_shape_str as verify_shape,
};
fn dialect(types: &str, contract: &str) -> Result<Dialect, String> {
    parse_dialect(&format!("(define diagnostics (cbcl) @author (extend submit (to value) (tell to :value value)) (shape submit (require :value {contract})) {types})").parse::<SExpr>().unwrap())
}
fn error(types: &str, contract: &str, value: &str) -> String {
    dialect(types, contract).unwrap().shapes[0]
        .check(&format!("(submit :value {value})").parse().unwrap())
        .unwrap_err()
        .to_string()
}
#[test]
fn refinements_explain_the_failed_clause_without_values() {
    let builtin = cbcl_core::shape::TypeConstraint::Integer
        .check(
            &"9384827m".parse().unwrap(),
            cbcl_core::contracts::DEFAULT_WORK,
        )
        .unwrap_err()
        .to_string();
    assert!(
        builtin.contains("expected integer; found decimal"),
        "{builtin}"
    );
    assert!(!builtin.contains("9384827"));
    let message = error(
        "(type postal (string (matches \"[0-9]{4}\")))",
        "postal",
        "\"PRIVATE-ACCOUNT\"",
    );
    assert!(message.contains("postal"));
    assert!(message.contains("[0-9]{4}"), "{message}");
    assert!(!message.contains("PRIVATE-ACCOUNT"));
    let message = error("", "(string (length (>= 2) (<= 4)))", "\"PRIVATE-ACCOUNT\"");
    assert!(message.contains("<= 4"), "{message}");
    assert!(!message.contains("PRIVATE-ACCOUNT"));
    let message = error("", "(number (> 0))", "-9384827");
    assert!(message.contains("> 0"), "{message}");
    assert!(!message.contains("9384827"));
}
#[test]
fn composition_explains_each_alternative_and_conjunction_location() {
    let message = error(
        "(type positive (integer (> 0))) (type postal (string (matches \"[0-9]{4}\")))",
        "(or positive postal)",
        "#f",
    );
    for fragment in [
        "or", "branch 1", "branch 2", "positive", "postal", "integer", "string",
    ] {
        assert!(message.contains(fragment), "missing {fragment}: {message}");
    }
    let message = error("", "(and number (number (> 0)))", "-1");
    assert!(message.contains("and branch 2"), "{message}");
}
#[test]
fn regex_definition_errors_locate_unicode_source_characters() {
    let message = dialect("(type postal (string (matches \"😀\\\\v\")))", "postal").unwrap_err();
    assert!(message.contains("postal"), "{message}");
    assert!(message.contains("character 3"), "{message}");
    let message = dialect("", "(string (matches \"[z-a]\"))").unwrap_err();
    assert!(message.contains("character 2"), "{message}");
    assert!(message.contains("reversed"), "{message}");
}
#[test]
fn resource_errors_explain_work_or_input_and_keep_the_category() {
    let d = dialect("", "(number (> 0))").unwrap();
    let value = "(submit :value 1)".parse().unwrap();
    let err = d.shapes[0].check_with_work(&value, 1).unwrap_err();
    assert_eq!(err.rule, "resource-limit");
    assert!(err.detail.contains("available 1"), "{err}");
    assert!(err.detail.contains("268435457"), "{err}");
    let value = format!("(submit :value \"{}\")", "s".repeat(65536))
        .parse()
        .unwrap();
    let err = d.shapes[0].check(&value).unwrap_err();
    assert!(err.detail.contains("65536"), "{err}");
    assert!(err.detail.contains("storage"), "{err}");
}
#[test]
fn public_shape_errors_retain_nested_field_and_constraint_context() {
    let source="(define diagnostics (cbcl) @author (extend submit (to value) (tell to :value value)) (shape submit (require :outer list (require :inner (string (length (<= 2)))))))";
    let request =
        format!("(verify-shape {source} submit (submit :outer (:inner \"PRIVATE-ACCOUNT\")))");
    let err = verify_shape(&request).unwrap_err();
    assert!(err.contains(":outer/:inner"), "{err}");
    assert!(err.contains("<= 2"), "{err}");
    assert!(!err.contains("PRIVATE-ACCOUNT"));
}

#[test]
fn installation_context_and_public_resource_details_are_retained() {
    let message = dialect("", "(or integer missing)").unwrap_err();
    for fragment in [
        "dialect diagnostics",
        "shape submit/:value",
        "or branch 2",
        "unknown type missing",
    ] {
        assert!(message.contains(fragment), "{message}");
    }
    let message = dialect("(type a b) (type b a)", "a").unwrap_err();
    assert!(message.contains("a -> b -> a"), "{message}");
    let source="(define diagnostics (cbcl) @author (extend submit (to value) (tell to :value value)) (shape submit (require :value string)))";
    let request = format!(
        "(verify-shape {source} submit (submit :value \"{}\"))",
        "s".repeat(65536)
    );
    let err = verify_shape(&request).unwrap_err();
    assert!(err.contains("resource-limit"), "{err}");
    assert!(err.contains("storage exceeds 65536"), "{err}");
    assert!(!err.contains(&"s".repeat(32)));
}
#[test]
fn repeated_alias_failure_diagnostics_are_bounded() {
    let mut definitions = String::from("(type t0 integer)");
    for index in 1..10 {
        definitions.push_str(&format!(
            " (type t{index} (or t{} t{}))",
            index - 1,
            index - 1
        ));
    }
    let d = dialect(&definitions, "t9").unwrap();
    let cbcl_core::shape::ShapeRule::Require {
        type_constraint: Some(contract),
        ..
    } = &d.shapes[0].rules[0]
    else {
        panic!("required")
    };
    let message = contract
        .check(&"#f".parse().unwrap(), cbcl_core::contracts::DEFAULT_WORK)
        .unwrap_err()
        .to_string();
    assert!(message.len() <= 2100, "{} diagnostic bytes", message.len());
    assert!(message.contains("or"));
}

#[test]
fn many_unicode_alternatives_have_safe_truncation_and_an_omission_count() {
    let pattern =
        cbcl_core::sexpr::SExpr::Atom(cbcl_core::sexpr::Atom::Str("😀".repeat(60))).to_string();
    let branch = format!("(string (matches {pattern}))");
    let contract = format!("(or {})", vec![branch; 10].join(" "));
    let d = dialect("", &contract).unwrap();
    let cbcl_core::shape::ShapeRule::Require {
        type_constraint: Some(contract),
        ..
    } = &d.shapes[0].rules[0]
    else {
        panic!("required")
    };
    let message = contract
        .check(
            &"\"PRIVATE-ACCOUNT\"".parse().unwrap(),
            cbcl_core::contracts::DEFAULT_WORK,
        )
        .unwrap_err()
        .to_string();
    assert!(message.contains("2 further branches failed"), "{message}");
    assert!(message.contains("branch 8"), "{message}");
    assert!(message.len() <= 2100, "{} diagnostic bytes", message.len());
    assert!(!message.contains("PRIVATE-ACCOUNT"));
}

#[test]
fn default_child_resource_error_preserves_the_installation_category() {
    let source=format!("(define diagnostics (cbcl) @author (extend submit (to value) (tell to :value value)) (shape submit (optional :outer (default (:inner \"{}\")) (require :inner string))))", "s".repeat(65536));
    let message = parse_dialect(&source.parse::<SExpr>().unwrap()).unwrap_err();
    assert!(message.starts_with("resource-limit:"), "{message}");
    assert!(message.contains("storage exceeds 65536"), "{message}");
    assert!(message.contains("default"), "{message}");
    assert!(!message.contains(&"s".repeat(32)));
}
