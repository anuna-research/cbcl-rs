use cbcl_parser::{parse, parse_dialect};

#[test]
fn variadic_then_matches_pairwise_protocol() {
    let dialect = |protocol: &str| parse_dialect(&parse(&format!(
        "(define chain (cbcl) @author {protocol})"
    )).unwrap()).unwrap();
    let chain = dialect("(protocol (then begin one two three))");
    let pairs = dialect("(protocol (then begin one) (then one two) (then two three))");
    assert_eq!(chain.causal_protocol, pairs.causal_protocol);
    assert_eq!(cbcl_core::canonical::dialect_hash(&chain), cbcl_core::canonical::dialect_hash(&pairs));
}

#[test]
fn variadic_then_requires_an_edge() {
    for protocol in ["(protocol (then))", "(protocol (then begin))"] {
        assert!(parse_dialect(&parse(&format!("(define chain (cbcl) @author {protocol})")).unwrap()).is_err());
    }
}
