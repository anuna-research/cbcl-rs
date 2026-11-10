//! SPEC-042 TEST-4200 through TEST-4205: identity belongs to boundary representations.
use cbcl_core::{
    canonical::{canonical_encode, dialect_canonical_bytes, dialect_name},
    message::{Message, WrapperType},
    r4::{check_r4, R4Result, Signer},
    serializer::serialize,
    sexpr::SExpr,
    typed_addr::{field_sexpr, open, typed_root, FieldId},
};
use cbcl_parser::{parse, parse_dialect, parse_message};

fn msg(text: &str) -> Message {
    parse_message(&parse(text).unwrap()).unwrap()
}
fn text(message: &Message) -> String {
    serialize(&SExpr::from(message))
}
fn dialect(rules: &str) -> cbcl_core::dialect::Dialect {
    parse_dialect(
        &parse(&format!(
            "(define sample (extends cbcl) @author
          (extend transfer (recipient amount) (tell @recipient amount))
          (shape transfer {rules}))"
        ))
        .unwrap(),
    )
    .unwrap()
}

#[test]
fn keyword_permutations_share_bytes_roots_and_openings() {
    let a =
        msg("(lang coin (transfer @bob () :recipient @alice :amount 100 :thread t :sender @s))");
    let b =
        msg("(lang coin (transfer @bob () :amount 100 :sender @s :thread t :recipient @alice))");
    assert_eq!(text(&a), text(&b));
    assert_eq!(
        canonical_encode(&SExpr::from(&a)),
        canonical_encode(&SExpr::from(&b))
    );
    let suite = cbcl_core::keyid::SignatureSuite::Ed25519;
    let root = |m: &Message| typed_root(m.innermost_simple().unwrap());
    assert_eq!(
        cbcl_core::attest::attestation_v3_preimage(&suite, &root(&a)),
        cbcl_core::attest::attestation_v3_preimage(&suite, &root(&b)),
    );
    for (a, b) in [
        (&a, &b),
        (a.innermost_simple().unwrap(), b.innermost_simple().unwrap()),
    ] {
        assert_eq!(typed_root(a), typed_root(b));
        assert_eq!(
            field_sexpr(a, FieldId::Payload),
            field_sexpr(b, FieldId::Payload)
        );
        assert_eq!(open(a, FieldId::Payload), open(b, FieldId::Payload));
    }
    // Bypass the text parser: direct Rust construction must use the same boundary.
    let mut direct = a.clone();
    let Message::Dialect { inner, .. } = &mut direct else {
        panic!()
    };
    let Message::Simple { params, .. } = inner.as_mut() else {
        panic!()
    };
    params.swap(0, 2);
    params.swap(1, 3);
    assert_eq!(text(&direct), text(&a));
    assert_eq!(
        typed_root(direct.innermost_simple().unwrap()),
        typed_root(a.innermost_simple().unwrap())
    );
}

#[test]
fn wrapper_keywords_canonicalise_without_reordering_signature_material() {
    let a = msg("(signed \"signature\" :suite ed25519 :hash abc (envelope :to @bob :from @alice (tell @bob \"hi\")))");
    let b = msg("(signed \"signature\" :hash abc :suite ed25519 (envelope :from @alice :to @bob (tell @bob \"hi\")))");
    assert_eq!(text(&a), text(&b));
    assert_eq!(typed_root(&a), typed_root(&b));
    assert!(text(&a).starts_with("(signed \"signature\""));
    assert_eq!(a.wrapper_type(), Some(WrapperType::Signed));
}

#[test]
fn duplicate_and_valueless_keywords_are_rejected_at_recognition() {
    for input in [
        "(tell @b () :x 1 :x 2)",
        "(tell @b () :thread a :thread b)",
        "(tell @b () :sender @a :sender @c)",
        "(tell @b () :caused-by begin :caused-by other)",
        "(envelope :to @a :to @b (tell @b ()))",
        "(envelope :to (tell @b ()))",
        "(envelope :to @b (tell @b ()) :to @a)",
        "(envelope :to @b (tell @b ()) :x)",
        "(tell @b () :x)",
    ] {
        assert!(
            parse_message(&parse(input).unwrap()).is_err(),
            "accepted {input}"
        );
    }
}

#[test]
fn positional_and_nested_data_order_is_preserved() {
    let a = msg("(tell @b (:z 1 :a 2) extra :z (:z 1 :a 2) :a 3)");
    let b = msg("(tell @b (:a 2 :z 1) extra :a 3 :z (:z 1 :a 2))");
    assert_ne!(text(&a), text(&b));
    assert_ne!(typed_root(&a), typed_root(&b));
    assert!(text(&a).contains("(:z 1 :a 2)"));
    assert_eq!(text(&msg(&text(&a))), text(&a));
    assert_ne!(
        typed_root(&msg("(tell @b (a b))")),
        typed_root(&msg("(tell @b (b a))"))
    );
    // The generic S-expression encoder remains injective and order-sensitive.
    assert_ne!(
        canonical_encode(&parse("(:z 1 :a 2)").unwrap()),
        canonical_encode(&parse("(:a 2 :z 1)").unwrap())
    );
    let interleaved = msg("(tell @b payload :z 1 extra :a 2)");
    assert_eq!(text(&interleaved), "(tell @b payload :a 2 extra :z 1)");
    // Content and header positions already have a fixed typed representation.
    assert_eq!(
        text(&msg("(tell @b :z 1 payload :a 2)")),
        text(&msg("(tell @b payload :a 2 :z 1)"))
    );
}

#[test]
fn r7_receipt_accepts_raw_permutations_without_repair() {
    let d = parse_dialect(&parse(include_str!("../../../dialects/example-coin.cbcl")).unwrap())
        .unwrap();
    let mut a = msg("(lang example-coin (pay @bob () :recipient @alice :amount 10 :escrow-prev f1220aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa :escrow-deps () :from @bob))");
    fn reorder(m: &mut Message) {
        match m {
            Message::Simple { params, .. } => {
                let pairs = params
                    .chunks_exact(2)
                    .rev()
                    .flat_map(|p| p.iter().cloned())
                    .collect();
                *params = pairs;
            }
            Message::Dialect { inner, .. } => reorder(inner),
            _ => panic!(),
        }
    }
    cbcl_core::r7::verify_state_shape(&d, &a).unwrap();
    let canonical = a.clone();
    reorder(&mut a);
    let before = a.clone();
    cbcl_core::r7::verify_state_shape(&d, &a).unwrap();
    assert_eq!(a, before);
    assert_ne!(a, canonical);
    assert_eq!(
        typed_root(a.innermost_simple().unwrap()),
        typed_root(canonical.innermost_simple().unwrap())
    );
}

struct DigestSigner;
impl Signer for DigestSigner {
    fn sign(&self, data: &[u8]) -> Vec<u8> {
        use sha2::{Digest, Sha256};
        Sha256::digest(data).to_vec()
    }
    fn verify(&self, data: &[u8], sig: &[u8]) -> bool {
        self.sign(data) == sig
    }
}

#[test]
fn dialect_shape_order_is_canonical_before_signing_and_addressing() {
    let mut a = dialect("(require :recipient symbol) (require :amount integer) (optional :details list (require :z string) (require :a string))");
    let b = dialect("(optional :details list (require :a string) (require :z string)) (require :amount integer) (require :recipient symbol)");
    assert_eq!(
        a.shapes, b.shapes,
        "dialect creation normalises shapes once"
    );
    assert_eq!(dialect_name(&a), dialect_name(&b));
    assert_eq!(dialect_canonical_bytes(&a), dialect_canonical_bytes(&b));
    a.signature = Some(DigestSigner.sign(&dialect_canonical_bytes(&a)));
    let mut reordered = b;
    reordered.signature = a.signature.clone();
    // Directly constructed dialects must also use the canonical signing boundary.
    reordered.shapes[0].rules.reverse();
    assert_eq!(check_r4(&reordered, &DigestSigner), R4Result::Valid);
    reordered.performatives[0].params.reverse();
    assert_eq!(check_r4(&reordered, &DigestSigner), R4Result::Invalid);
    let mut changed = dialect("(require :amount string) (require :recipient symbol)");
    assert_ne!(dialect_name(&a), dialect_name(&changed));
    changed.signature = a.signature;
    assert_eq!(check_r4(&changed, &DigestSigner), R4Result::Invalid);
}

#[test]
fn versions_identify_the_boundary_change() {
    assert_eq!(cbcl_core::canonical::CANONICAL_FORM_VERSION, 7);
    assert_eq!(cbcl_core::typed_addr::TYPED_ADDR_VERSION, 2);
}
