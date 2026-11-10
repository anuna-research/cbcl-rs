//! SPEC-040 executable acceptance cases through the actual dialect and shape path.
use cbcl_core::{
    dialect::Dialect,
    sexpr::SExpr,
    shape::{ShapeRule, TypeConstraint},
};
use cbcl_parser::dialect_parser::parse_dialect;
fn dialect(types: &str, ty: &str) -> Result<Dialect, String> {
    parse_dialect(&format!("(define contracts (cbcl) @author (extend submit (to value) (tell to :value value)) (shape submit (require :value {ty})) {types})").parse::<SExpr>().unwrap())
}
fn check(d: &Dialect, value: &str) -> bool {
    d.shapes[0]
        .check(&format!("(submit :value {value})").parse::<SExpr>().unwrap())
        .is_ok()
}
#[test]
fn named_types_and_numeric_hierarchy() {
    for (value, kind) in [("1", "integer"), ("1.0", "float"), ("1m", "decimal")] {
        let value = value.parse::<SExpr>().unwrap();
        assert!(cbcl_core::template::eval_type_predicate(&value, kind));
        assert!(cbcl_core::template::eval_type_predicate(&value, "number"));
    }

    let d = dialect("(type positive (integer (> 0)))", "positive").unwrap();
    assert!(check(&d, "12"));
    assert!(!check(&d, "0"));
    assert!(!check(&d, "12.0"));
    assert!(!check(&d, "12m"));
    let d = dialect("", "number").unwrap();
    for v in ["12", "12.0", "12m"] {
        assert!(check(&d, v))
    }
}
#[test]
fn aliases_composition_enums_lengths() {
    let d = dialect("(type currency (one-of :AUD :USD :EUR))", "currency").unwrap();
    assert!(check(&d, ":AUD"));
    assert!(!check(&d, "\"AUD\""));
    let d = dialect("(type count (one-of 1))", "count").unwrap();
    assert!(check(&d, "1"));
    assert!(!check(&d, "1.0"));
    let d = dialect("(type name (string (length (>= 1) (<= 2))))", "name").unwrap();
    assert!(check(&d, "\"😀\""));
    assert!(check(&d, "\"é\""));
    assert!(!check(&d, "\"abc\""));
    let d = dialect("(type batch (list (length (> 0) (<= 2))))", "batch").unwrap();
    assert!(check(&d, "((1 2 3))"));
    assert!(!check(&d, "()"));
    let d = dialect(
        "(type later (one-of :AUD)) (type alias later) (type both (and alias keyword))",
        "(or both integer)",
    )
    .unwrap();
    assert!(check(&d, ":AUD"));
    assert!(check(&d, "2"));
    assert!(!check(&d, ":USD"));
}
#[test]
fn exact_bounds() {
    let d = dialect("", "(number (> 0.1m))").unwrap();
    assert!(check(&d, "0.1"));
    assert!(!check(&d, "0.1m"));
    let d = dialect("", "(integer (> 9007199254740992.0))").unwrap();
    assert!(check(&d, "9007199254740993"));
    assert!(!check(&d, "9007199254740992"));
    let d = dialect("", "(decimal (>= 0) (< 10000))").unwrap();
    assert!(check(&d, "0m"));
    assert!(!check(&d, "0.0"));
    assert!(!check(&d, "10000m"));
}
#[test]
fn iregexp_semantics() {
    for (pattern, yes, no) in [
        ("[0-9]{4}", "2000", "x2000y"),
        ("^x$", "^x$", "x"),
        (".", "😀", "\n"),
        ("a{2,}", "aaa", "a"),
        ("\\p{Nd}{4}", "٢٠٠٠", "abcd"),
        ("[a-z-[x]", "", ""),
    ] {
        if pattern == "[a-z-[x]" {
            continue;
        }
        let source = format!(
            "(type text (string (matches {})))",
            cbcl_core::serializer::serialize(&SExpr::Atom(cbcl_core::sexpr::Atom::Str(
                pattern.into()
            )))
        );
        let d = dialect(&source, "text").unwrap();
        for (value, expected) in [(yes, true), (no, false)] {
            let value = cbcl_core::serializer::serialize(&SExpr::Atom(
                cbcl_core::sexpr::Atom::Str(value.into()),
            ));
            assert_eq!(check(&d, &value), expected, "{pattern:?} {value}");
        }
    }
}
#[test]
fn rejects_invalid_definitions() {
    for (defs, ty) in [
        ("(type a b) (type b a)", "a"),
        ("(type a integer) (type a string)", "a"),
        ("(type integer string)", "integer"),
        ("", "unknown"),
        ("", "(and integer string)"),
        ("", "(one-of)"),
        ("", "(one-of 1 01)"),
        ("", "(one-of (x))"),
        ("", "(string (length (> 0) (< 1)))"),
        ("", "(list (length (<= -1)))"),
        ("", "(number (> 1) (<= 1))"),
        ("", "(string (matches \"(?=x)\"))"),
        ("", "(string (matches \"[^]\"))"),
        ("", "(string (matches \"[z-a]\"))"),
    ] {
        assert!(dialect(defs, ty).is_err(), "{defs} {ty}");
    }
}
#[test]
fn reserve_before_branch_evaluation() {
    let a = dialect(
        "(type costly (string (matches \"a*\")))",
        "(or costly string)",
    )
    .unwrap();
    let b = dialect(
        "(type costly (string (matches \"a*\")))",
        "(or string costly)",
    )
    .unwrap();
    fn tc(d: &Dialect) -> &TypeConstraint {
        let ShapeRule::Require {
            type_constraint: Some(tc),
            ..
        } = &d.shapes[0].rules[0]
        else {
            panic!()
        };
        tc
    }
    let value = "\"bbb\"".parse::<SExpr>().unwrap();
    let required = |t: &TypeConstraint| {
        if let TypeConstraint::Contract(c) = t {
            c.required_work().unwrap()
        } else {
            panic!()
        }
    };
    let work = required(tc(&a));
    assert_eq!(work, required(tc(&b)));
    for allowance in [1, work - 1] {
        assert_eq!(
            tc(&a).check(&value, allowance),
            Err(cbcl_core::contracts::CheckError::ResourceLimit)
        );
        assert_eq!(
            tc(&b).check(&value, allowance),
            Err(cbcl_core::contracts::CheckError::ResourceLimit)
        );
    }
    assert!(tc(&a).check(&value, work).is_ok());
    assert!(tc(&b).check(&value, work).is_ok());

    assert_eq!(
        tc(&a).check(&value, 0),
        Err(cbcl_core::contracts::CheckError::ResourceLimit)
    );
    assert_eq!(
        tc(&b).check(&value, 0),
        Err(cbcl_core::contracts::CheckError::ResourceLimit)
    );
    assert!(tc(&a)
        .check(&value, cbcl_core::contracts::DEFAULT_WORK)
        .is_ok());
}

#[test]
fn shared_binding_vectors_and_private_diagnostics() {
    let cases: serde_json::Value = serde_json::from_str(include_str!(
        "../../../test-vectors/contracts/flat-contracts.json"
    ))
    .unwrap();
    for c in cases.as_array().unwrap() {
        let r = cbcl_parser::verify_message_shape_str(c["frame"].as_str().unwrap());
        assert_eq!(r.is_ok(), c["accept"].as_bool().unwrap(), "{c}: {r:?}");
        if let Some(expected) = c["errorContains"].as_str() {
            assert!(r.unwrap_err().contains(expected), "{c}");
        }
    }
    let d="(define validation (cbcl) @author (extend submit (to value) (tell to :value value)) (shape submit (require :value (string (length (<= 2))))))";
    let err = cbcl_parser::verify_message_shape_str(&format!(
        "(verify-shape {d} submit (submit :value \"private-secret\"))"
    ))
    .unwrap_err();
    assert!(!err.contains("private-secret"));
    assert!(err.contains("length"));
    let long = "x".repeat(cbcl_core::contracts::MAX_INPUT_BYTES + 1);
    let err = cbcl_parser::verify_message_shape_str(&format!(
        "(verify-shape {d} submit (submit :value \"{long}\"))"
    ))
    .unwrap_err();
    assert!(err.contains("resource-limit"));
    assert!(!err.contains("sender"));
}

#[test]
fn declaration_order_signing_and_old_signature_rejection() {
    use cbcl_core::{
        canonical::{canonical_encode, dialect_canonical_bytes, to_signable_sexpr},
        r4::{check_r4, R4Result, Signer},
    };
    struct Bytes;
    impl Signer for Bytes {
        fn sign(&self, d: &[u8]) -> Vec<u8> {
            d.to_vec()
        }
        fn verify(&self, d: &[u8], s: &[u8]) -> bool {
            d == s
        }
    }
    let a = dialect("(type a integer) (type b a)", "b").unwrap();
    let b = dialect("(type b a) (type a integer)", "b").unwrap();
    assert_eq!(dialect_canonical_bytes(&a), dialect_canonical_bytes(&b));
    let mut signed = dialect("", "number").unwrap();
    let mut old = to_signable_sexpr(&signed);
    if let SExpr::List(xs) = &mut old {
        xs.retain(|x| !matches!(x,SExpr::List(ys) if ys.first().is_some_and(|h|h.is_symbol("types")||h.is_symbol("type-profile"))))
    }
    signed.signature = Some(canonical_encode(&old));
    assert_eq!(check_r4(&signed, &Bytes), R4Result::Invalid);
    signed.signature = Some(dialect_canonical_bytes(&signed));
    assert_eq!(check_r4(&signed, &Bytes), R4Result::Valid);
    for (left, right) in [
        ("(number (>= 0))", "(number (> 0))"),
        ("(one-of :AUD :USD)", "(one-of :USD :AUD)"),
        ("(list (length (<= 2)))", "(list (length (<= 3)))"),
    ] {
        let a = dialect("", left).unwrap();
        let b = dialect("", right).unwrap();
        assert_ne!(dialect_canonical_bytes(&a), dialect_canonical_bytes(&b));
    }
}

#[test]
fn depth_caps_do_not_depend_on_cached_name_order() {
    for reverse in [false, true] {
        let mut defs = String::new();
        for i in 0..40 {
            let name = if reverse { 39 - i } else { i };
            let target = if i == 0 {
                "integer".to_string()
            } else {
                format!("t{:02}", if reverse { 40 - i } else { i - 1 })
            };
            defs.push_str(&format!("(type t{name:02} {target}) "));
        }
        assert!(dialect(&defs, "integer")
            .unwrap_err()
            .contains("resource-limit"));
    }
    let mut defs = "(type a0 integer) ".to_string();
    for i in 1..15 {
        defs.push_str(&format!("(type a{i} (and a{} a{})) ", i - 1, i - 1));
    }
    let d = dialect(&defs, "a14").unwrap();
    assert!(check(&d, "1"));
}

#[test]
fn defaults_and_installation_are_atomic() {
    use cbcl_core::dialect::DialectRegistry;
    for field in [
        "(optional :value unknown (default 1))",
        "(optional :value integer (default 1.0))",
        "(optional :value list (default ()) (require :child integer))",
        "(optional :value integer misspelled)",
    ] {
        let s=format!("(define defaults (cbcl) @a (extend submit (to value) (tell to :value value)) (shape submit {field}))");
        assert!(
            parse_dialect(&s.parse::<SExpr>().unwrap()).is_err(),
            "{field}"
        );
    }
    let mut registry = DialectRegistry::new();
    let count = registry.len();
    let mut d = dialect("(type amount integer)", "amount").unwrap();
    d.types.insert("amount".into(), "missing".parse().unwrap());
    assert!(registry.install(d).is_err());
    assert_eq!(registry.len(), count);
}

#[test]
fn state_integer_proofs_and_symbol_restrictions() {
    let source = "(define stateful (cbcl) @a (extend open (to) (tell to)) (extend inc (to value) (tell to :value value)) (extend dec (to value) (tell to :value value)) (shape inc (require :value number)) (shape dec (require :value integer)) (protocol (then begin open) (then open inc) (then open dec)) (state (total (counter inc dec :value))))";
    let d = parse_dialect(&source.parse::<SExpr>().unwrap()).unwrap();
    let error = cbcl_core::dialect::DialectRegistry::new()
        .install(d)
        .unwrap_err()
        .to_string();
    assert!(error.contains("must be an integer"), "{error}");
    for ty in ["(or string symbol)", "(one-of 1 :one)"] {
        let source=format!("(define stateful (cbcl) @a (extend open (to value) (tell to :value value)) (shape open (require :value {ty})) (protocol (then begin open)) (state (value (initial open :value))))");
        let d = parse_dialect(&source.parse::<SExpr>().unwrap()).unwrap();
        let error = cbcl_core::dialect::DialectRegistry::new()
            .install(d)
            .unwrap_err()
            .to_string();
        assert!(
            error.contains("admits symbols or keywords"),
            "{ty}: {error}"
        );
    }
    let source="(define stateful (cbcl) @a (type amount (integer (> 0))) (extend open (to value) (tell to :value value)) (shape open (require :value amount)) (protocol (then begin open)) (state (total (initial open :value))))";
    let d = parse_dialect(&source.parse::<SExpr>().unwrap()).unwrap();
    assert!(cbcl_core::dialect::DialectRegistry::new()
        .install(d)
        .is_ok());
}

#[test]
fn schema_and_json_authoring_use_shared_contracts() {
    let json = r#"{"version":3,"kind":"contract","name":"example","types":{"amount":"(decimal (>= 0))"},"verbs":{"open":{"after":["begin"],"fields":{"value":"amount"}}},"state":{"value":["initial","open","value"]}}"#;
    let compiled: serde_json::Value =
        serde_json::from_str(&cbcl_parser::compile_contract_str(json).unwrap()).unwrap();
    let text = compiled["dialect"].as_str().unwrap();
    let description: serde_json::Value =
        serde_json::from_str(&cbcl_parser::describe_dialect_str(text).unwrap()).unwrap();
    assert_eq!(description["types"]["amount"]["source"], "(decimal (>= 0))");
    assert_eq!(
        description["types"]["amount"]["representations"][0],
        "decimal"
    );
    assert_eq!(
        description["verbs"]["open"]["contracts"]["value"]["source"],
        "amount"
    );
}

#[test]
fn integer_counter_and_hlc_aliases_install() {
    let vector: serde_json::Value = serde_json::from_str(include_str!(
        "../../../test-vectors/state/bounded-coin.json"
    ))
    .unwrap();
    let source = vector["contract"]
        .as_str()
        .unwrap()
        .replace(":amount integer", ":amount positive-amount");
    let mut form = cbcl_parser::parse(&source).unwrap();
    if let SExpr::List(xs) = &mut form {
        xs.push("(type positive-amount (integer (> 0)))".parse().unwrap())
    }
    let d = parse_dialect(&form).unwrap();
    cbcl_core::dialect::DialectRegistry::new()
        .install(d)
        .unwrap();
    let source="(define clocked (cbcl) @a (type instant hlc) (extend open (to value clock) (tell to :value value :clock clock)) (shape open (require :value string) (require :clock instant)) (protocol (then begin open)) (state (value (lww-register open :value :clock))))";
    let d = parse_dialect(&source.parse::<SExpr>().unwrap()).unwrap();
    cbcl_core::dialect::DialectRegistry::new()
        .install(d)
        .unwrap();
    for secret in ["private-positional-secret", "private-address-secret"] {
        let fields = if secret.contains("positional") {
            format!("{secret} :value \"ok\" :clock \"hlc-0000000000000001-00000000\" :replaces ()")
        } else {
            format!(":value \"ok\" :clock \"hlc-0000000000000001-00000000\" :replaces ({secret})")
        };
        let err = cbcl_parser::state_exports::verify_state_shape_str(&format!(
            "(verify-state-shape {source} (open {fields}))"
        ))
        .unwrap_err();
        assert!(!err.contains(secret), "{err}");
        assert!(err.contains("open"));
    }
}

#[test]
fn profile_boundaries_and_adversarial_measurements() {
    use cbcl_core::{contracts::*, sexpr::Atom};
    let maximum = "a".repeat(MAX_PATTERN_BYTES);
    assert!(dialect("", &format!("(string (matches \"{maximum}\"))")).is_ok());
    assert!(dialect("", &format!("(string (matches \"{maximum}a\"))"))
        .unwrap_err()
        .starts_with("resource-limit:"));
    assert!(dialect("", "(string (matches \"a{200000}\"))")
        .unwrap_err()
        .contains("resource-limit"));
    let members = (0..MAX_MEMBERS)
        .map(|n| format!(":k{n}"))
        .collect::<Vec<_>>()
        .join(" ");
    assert!(dialect("", &format!("(one-of {members})")).is_ok());
    assert!(dialect("", &format!("(one-of {members} :extra)"))
        .unwrap_err()
        .contains("resource-limit"));
    let definitions = (0..MAX_TYPES)
        .map(|n| format!("(type t{n} integer)"))
        .collect::<Vec<_>>()
        .join(" ");
    assert!(dialect(&definitions, "integer").is_ok());
    assert!(dialect(&(definitions + " (type extra integer)"), "integer")
        .unwrap_err()
        .contains("resource-limit"));
    let d = dialect("", "(number (>= 0))").unwrap();
    assert!(check(&d, &("9".repeat(MAX_NUMERIC_BYTES) + "m")));
    assert!(!check(&d, &("9".repeat(MAX_NUMERIC_BYTES + 1) + "m")));
    let d = dialect("", "(string (matches \"(a|aa)*b\"))").unwrap();
    let ShapeRule::Require {
        type_constraint: Some(tc),
        ..
    } = &d.shapes[0].rules[0]
    else {
        panic!()
    };
    for suffix in ["b", "a"] {
        let text = "a".repeat(MAX_INPUT_BYTES - 2) + suffix;
        let value = SExpr::Atom(Atom::Str(text));
        let now = std::time::Instant::now();
        let result = tc.check(&value, DEFAULT_WORK);
        assert_eq!(result.is_ok(), suffix == "b");
        println!(
            "SPEC040 max-input adversarial suffix={suffix}: {:?}",
            now.elapsed()
        );
    }
}

proptest::proptest! {
 #[test]
 fn exact_comparisons_match_small_independent_integer_oracle(a in proptest::num::i32::ANY,b in proptest::num::i32::ANY){
  use cbcl_core::{contracts::compare_numeric,sexpr::Atom,numeric::Float};
  let twice_b=2i64*b as i64+if b<0{-1}else{1};let expected=(2i64*a as i64).cmp(&twice_b);
  let decimal=Atom::Decimal(format!("{b}.5").parse().unwrap());let float=Atom::Float(Float::new(b as f64+if b<0{-0.5}else{0.5}).unwrap());
  proptest::prop_assert_eq!(compare_numeric(&Atom::Num(a as i64),&decimal),Some(expected));
  proptest::prop_assert_eq!(compare_numeric(&decimal,&float),Some(std::cmp::Ordering::Equal));
 }
 #[test]
 fn regex_matches_independent_ascii_format_oracle(text in "[A-Z0-9x]{0,8}"){
  let expected=(1..=5).contains(&text.len())&&text.as_bytes()[0].is_ascii_uppercase()&&text.as_bytes()[1..].iter().all(u8::is_ascii_digit);
  let d=dialect("","(string (matches \"[A-Z][0-9]{0,4}\"))").unwrap();
  proptest::prop_assert_eq!(check(&d,&format!("\"{text}\"")),expected);
 }
}

fn signing_migration_vector() -> serde_json::Value {
    use cbcl_core::canonical::{canonical_encode, dialect_name, to_signable_sexpr};
    use sha2::{Digest, Sha256};
    fn hex(bytes: &[u8]) -> String {
        bytes.iter().map(|b| format!("{b:02x}")).collect()
    }
    fn legacy(mut expression: SExpr) -> SExpr {
        if let SExpr::List(xs) = &mut expression {
            xs.retain(|x|!matches!(x,SExpr::List(ys) if ys.first().is_some_and(|h|h.is_symbol("types")||h.is_symbol("type-profile"))))
        }
        expression
    }
    let d = dialect("", "number").unwrap();
    let current = canonical_encode(&to_signable_sexpr(&d));
    let old = canonical_encode(&legacy(to_signable_sexpr(&d)));
    let mut body = d.clone();
    body.name.clear();
    let old_name = format!(
        "sha256-{}",
        hex(&Sha256::digest(canonical_encode(&legacy(
            to_signable_sexpr(&body)
        ))))
    );
    serde_json::json!({"format":1,"oldSigningForm":5,"newSigningForm":6,"profile":cbcl_core::contracts::PROFILE,"case":"unchanged number declaration changes meaning and requires reissue","oldName":old_name,"newName":dialect_name(&d),"oldCanonicalHex":hex(&old),"newCanonicalHex":hex(&current)})
}
#[test]
fn signing_migration_matches_explicit_fixture() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../test-vectors/contracts/signing-v6.json");
    let recorded: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(path).unwrap()).unwrap();
    assert_eq!(recorded, signing_migration_vector());
    assert_ne!(recorded["oldName"], recorded["newName"]);
}
#[test]
#[ignore = "explicit signing-form fixture authoring; never rewrites fixtures in normal tests"]
fn author_signing_v6_fixture() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../test-vectors/contracts/signing-v6.json");
    std::fs::write(
        path,
        serde_json::to_string_pretty(&signing_migration_vector()).unwrap() + "\n",
    )
    .unwrap();
}

#[test]
fn rfc_recognition_unicode_and_composed_lengths() {
    use cbcl_core::{serializer::serialize, sexpr::Atom};
    for pattern in [
        r"\d",
        r"\w",
        r"\s",
        r"\1",
        r"\$",
        r"\u1234",
        r"\p{IsBasicLatin}",
        r"\p{Cs}",
        "(?i)x",
        "(?=x)",
        "[a-z-[a]]",
        "[]",
        "[^]",
        "[z-a]",
        "a{3,2}",
        "a{,2}",
        "a**",
    ] {
        let text = serialize(&SExpr::Atom(Atom::Str(pattern.into())));
        assert!(
            dialect("", &format!("(string (matches {text}))")).is_err(),
            "{pattern}"
        );
    }
    for (pattern, yes, no) in [
        ("", "", "x"),
        (".", "😀", "\r"),
        (r"\p{Nd}", "𝟎", "Ⅳ"),
        (r"\P{Nd}", "Ⅳ", "𝟎"),
        (r"\n", "\n", "n"),
        ("[a&b]", "&", "c"),
    ] {
        let pattern = serialize(&SExpr::Atom(Atom::Str(pattern.into())));
        let d = dialect("", &format!("(string (matches {pattern}))")).unwrap();
        for (value, expected) in [(yes, true), (no, false)] {
            assert_eq!(
                check(&d, &serialize(&SExpr::Atom(Atom::Str(value.into())))),
                expected
            );
        }
    }
    let d=dialect("(type short (string (length (<= 3)))) (type sized (and short (string (length (>= 2)) (length (< 4)))))","sized").unwrap();
    assert!(check(&d, "\"ab\""));
    assert!(check(&d, "\"abc\""));
    assert!(!check(&d, "\"a\""));
    assert!(!check(&d, "\"abcd\""));
}

#[test]
fn serde_roundtrip_rebuilds_private_programs_from_signed_source() {
    let original = dialect("(type amount (integer (> 0)))", "amount").unwrap();
    let json = serde_json::to_string(&original).unwrap();
    assert!(!json.contains("compiled"));
    let decoded: Dialect = serde_json::from_str(&json).unwrap();
    let mut registry = cbcl_core::dialect::DialectRegistry::new();
    registry.install(decoded).unwrap();
    let restored = registry.iter().last().unwrap();
    assert_eq!(
        cbcl_core::canonical::dialect_canonical_bytes(&original),
        cbcl_core::canonical::dialect_canonical_bytes(restored)
    );
    assert!(check(restored, "1"));
    assert!(!check(restored, "0"));
    assert!(!check(restored, "1.0"));
}
