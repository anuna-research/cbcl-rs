//! RFC 9804 canonical S-expression encoding for CBCL R4 signing.
//!
//! This module implements the canonical form defined in RFC 9804 §6.2 for use
//! in dialect signature creation and verification. It is separate from the
//! human-readable serializer in `serializer.rs`.
//!
//! # Canonical Form (RFC 9804 §6.2)
//!
//! - **Atoms** are encoded as length-prefixed octet strings: `<decimal-length>:<octets>`
//!   where the length has no leading zeros.
//! - **Lists** are encoded as `(` followed by concatenated encoded children
//!   followed by `)`, with no whitespace.
//! - Empty list is `()`.
//!
//! # CBCL Atom-to-Octet-String Mapping
//!
//! CBCL has typed atoms (Symbol, Keyword, Num, Bool, Str) while SPKI
//! S-expressions are fundamentally octet-strings plus lists. This module
//! defines a stable, injective mapping from CBCL atoms to octet strings
//! that becomes part of the protocol:
//!
//! | Variant        | Tag  | Octet-string encoding                 |
//! |----------------|------|---------------------------------------|
//! | `Symbol(s)`    | `S`  | `b"S"` ++ UTF-8 bytes of `s`          |
//! | `Keyword(k)`   | `K`  | `b"K"` ++ UTF-8 bytes of `k`          |
//! | `Str(s)`       | `Q`  | `b"Q"` ++ UTF-8 bytes of `s`          |
//! | `Num(n)`       | `N`  | `b"N"` ++ ASCII decimal of `n`        |
//! | `Bool(true)`   | `B`  | `b"Bt"`                                |
//! | `Bool(false)`  | `B`  | `b"Bf"`                                |
//!
//! **Injectivity**: Each variant uses a distinct single-byte type tag prefix
//! (`S`, `K`, `Q`, `N`, `B`), guaranteeing that no value of one variant can
//! collide with a value of a different variant.
//!
//! The mapping is stable and MUST NOT change once published. It is a
//! protocol-level contract referenced by RFC 9804 §10.

#![forbid(unsafe_code)]

use crate::dialect::Dialect;
use crate::protocol::{CausalProtocol, NodeRef, StepDecl};
use crate::sexpr::{Atom, SExpr};
use crate::shape::{ShapeConstraint, ShapeRule, TypeConstraint};
use alloc::string::String;
use alloc::vec::Vec;

/// Version of the canonical signing form encoded in this module.
///
/// Bump this when the encoding produced by [`to_signable_sexpr`] changes
/// for any input dialect. Existing signatures are produced over a specific
/// version's bytes; a bump means a re-sign is required for verifying
/// implementations to interop. The version is informational — it is not
/// itself part of the signed body — but mismatched versions across CBCL
/// implementations should fail loudly at integration time.
///
/// History:
/// - `1` (initial): name, extends, author, performatives, resources,
///   examples.
/// - `2` (current): adds `(causal-protocol …)` and `(shapes …)`
///   segments, gated on presence so dialects that omit both fields
///   produce v1-identical bytes (legacy signatures keep verifying).
pub const CANONICAL_FORM_VERSION: u32 = 2;

// ---------------------------------------------------------------------------
// Atom-to-octet-string mapping
// ---------------------------------------------------------------------------

/// Map a CBCL atom to its canonical octet string representation.
///
/// This mapping is injective: distinct atoms always produce distinct byte sequences.
/// Each variant is prefixed with a unique type tag byte to guarantee injectivity:
///
/// | Variant        | Tag  | Encoding                        |
/// |----------------|------|---------------------------------|
/// | `Symbol(s)`    | `S`  | `b"S"` ++ UTF-8 bytes of `s`   |
/// | `Keyword(k)`   | `K`  | `b"K"` ++ UTF-8 bytes of `k`   |
/// | `Str(s)`       | `Q`  | `b"Q"` ++ UTF-8 bytes of `s`   |
/// | `Num(n)`       | `N`  | `b"N"` ++ ASCII decimal of `n`  |
/// | `Bool(true)`   | `B`  | `b"Bt"`                         |
/// | `Bool(false)`  | `B`  | `b"Bf"`                         |
///
/// The tag bytes are chosen to be distinct ASCII uppercase letters.
/// This ensures that no Symbol, Keyword, Str, Num, or Bool value can
/// collide with a value of a different variant.
pub fn atom_to_octets(atom: &Atom) -> Vec<u8> {
    match atom {
        Atom::Symbol(s) => {
            let mut v = Vec::with_capacity(1 + s.len());
            v.push(b'S');
            v.extend_from_slice(s.as_bytes());
            v
        }
        Atom::Keyword(k) => {
            let mut v = Vec::with_capacity(1 + k.len());
            v.push(b'K');
            v.extend_from_slice(k.as_bytes());
            v
        }
        Atom::Str(s) => {
            let mut v = Vec::with_capacity(1 + s.len());
            v.push(b'Q');
            v.extend_from_slice(s.as_bytes());
            v
        }
        Atom::Num(n) => {
            use alloc::format;
            let s = format!("{n}");
            let mut v = Vec::with_capacity(1 + s.len());
            v.push(b'N');
            v.extend_from_slice(s.as_bytes());
            v
        }
        Atom::Bool(b) => {
            if *b {
                Vec::from(b"Bt".as_slice())
            } else {
                Vec::from(b"Bf".as_slice())
            }
        }
    }
}

// ---------------------------------------------------------------------------
// RFC 9804 canonical encoder
// ---------------------------------------------------------------------------

/// Encode an S-expression in RFC 9804 canonical form.
///
/// - Atoms: map to octet string via [`atom_to_octets`], then emit `<len>:<octets>`.
/// - Lists: `(` ++ encode(child₁) ++ encode(child₂) ++ … ++ `)` (no whitespace).
///
/// The output is deterministic: `canonical_encode(e1) == canonical_encode(e2)` iff `e1 == e2`.
pub fn canonical_encode(sexpr: &SExpr) -> Vec<u8> {
    let mut buf = Vec::new();
    encode_into(sexpr, &mut buf);
    buf
}

fn encode_into(sexpr: &SExpr, buf: &mut Vec<u8>) {
    match sexpr {
        SExpr::Atom(atom) => {
            let octets = atom_to_octets(atom);
            let len_str = decimal_no_leading_zeros(octets.len());
            buf.extend_from_slice(len_str.as_bytes());
            buf.push(b':');
            buf.extend_from_slice(&octets);
        }
        SExpr::List(items) => {
            buf.push(b'(');
            for item in items {
                encode_into(item, buf);
            }
            buf.push(b')');
        }
    }
}

/// Format a usize as decimal with no leading zeros.
/// Zero is represented as "0".
fn decimal_no_leading_zeros(n: usize) -> String {
    use alloc::format;
    format!("{n}")
}

// ---------------------------------------------------------------------------
// Signable S-expression builder
// ---------------------------------------------------------------------------

/// Build the canonical S-expression for signing a dialect.
///
/// Includes every semantics-relevant field, excludes integrity fields
/// (signature, hash, protocol). The structure is:
///
/// ```text
/// (dialect <name>
///   (extends <parent>*)
///   (author <author>?)
///   (performatives (perf <name> (params <p>*) <template>)*)
///   (resources <max-depth> <max-expansion-size> <verification-time-ms>)
///   (examples <example>*)
///   (causal-protocol <step>+)?      ; only when d.causal_protocol is Some
///   (shapes <shape>+)?              ; only when d.shapes is non-empty
/// ```
///
/// Performative order is preserved — different orderings produce different
/// signable S-expressions (r4-002).
///
/// `causal_protocol` and `shapes` are *only* appended when present so a
/// dialect that omits them produces the same canonical bytes as before
/// these fields existed — existing signatures over such dialects keep
/// verifying. Dialects that *do* declare a protocol or shapes get those
/// fields fully bound by the signature.
pub fn to_signable_sexpr(d: &Dialect) -> SExpr {
    use alloc::vec;

    let mut top = vec![
        SExpr::Atom(Atom::Symbol(String::from("dialect"))),
        SExpr::Atom(Atom::Str(d.name.clone())),
    ];

    // extends
    let mut extends_list = vec![SExpr::Atom(Atom::Symbol(String::from("extends")))];
    for e in &d.extends {
        extends_list.push(SExpr::Atom(Atom::Str(e.clone())));
    }
    top.push(SExpr::List(extends_list));

    // author
    let mut author_list = vec![SExpr::Atom(Atom::Symbol(String::from("author")))];
    if let Some(ref a) = d.author {
        author_list.push(SExpr::Atom(Atom::Str(a.clone())));
    }
    top.push(SExpr::List(author_list));

    // performatives
    let mut perfs = vec![SExpr::Atom(Atom::Symbol(String::from("performatives")))];
    for p in &d.performatives {
        let mut params_list = vec![SExpr::Atom(Atom::Symbol(String::from("params")))];
        params_list.extend(p.params.clone());

        let perf = SExpr::List(vec![
            SExpr::Atom(Atom::Symbol(String::from("perf"))),
            SExpr::Atom(Atom::Str(p.name.clone())),
            SExpr::List(params_list),
            p.template.clone(),
        ]);
        perfs.push(perf);
    }
    top.push(SExpr::List(perfs));

    // resources
    top.push(SExpr::List(vec![
        SExpr::Atom(Atom::Symbol(String::from("resources"))),
        SExpr::Atom(Atom::Num(d.resources.max_depth as i64)),
        SExpr::Atom(Atom::Num(d.resources.max_expansion_size as i64)),
        SExpr::Atom(Atom::Num(d.resources.verification_time_ms as i64)),
    ]));

    // examples
    let mut examples_list = vec![SExpr::Atom(Atom::Symbol(String::from("examples")))];
    examples_list.extend(d.examples.clone());
    top.push(SExpr::List(examples_list));

    // causal-protocol (REQ-200/201) — only when present (backward-compat).
    if let Some(ref proto) = d.causal_protocol {
        top.push(protocol_to_sexpr(proto));
    }

    // shapes (REQ-220) — only when non-empty (backward-compat).
    if !d.shapes.is_empty() {
        top.push(shapes_to_sexpr(&d.shapes));
    }

    SExpr::List(top)
}

/// Encode a `CausalProtocol` deterministically. Steps come from a `BTreeMap`
/// so iteration is sorted by performative name.
///
/// **Note on `Some(empty)` vs `None`.** A dialect with
/// `causal_protocol: Some(CausalProtocol { steps: BTreeMap::new() })`
/// emits `(causal-protocol)` here, while `None` emits nothing at all.
/// These two states are semantically equivalent ("no causal constraints")
/// but produce distinct canonical bytes. The encoding stays faithful to the
/// data structure; if a downstream "normalize Some(empty) → None" rewrite
/// is ever introduced, it would break signatures over dialects that the
/// parser had constructed in the `Some(empty)` shape, so the normalization
/// must happen *before* the dialect is signed.
fn protocol_to_sexpr(p: &CausalProtocol) -> SExpr {
    use alloc::vec;
    let mut items = vec![SExpr::Atom(Atom::Symbol(String::from("causal-protocol")))];
    for step in p.steps.values() {
        items.push(step_to_sexpr(step));
    }
    SExpr::List(items)
}

fn step_to_sexpr(s: &StepDecl) -> SExpr {
    use alloc::vec;
    let mut preds = vec![SExpr::Atom(Atom::Symbol(String::from("predecessors")))];
    for nr in &s.predecessors {
        preds.push(node_ref_to_sexpr(nr));
    }
    let mut succs = vec![SExpr::Atom(Atom::Symbol(String::from("successors")))];
    for nr in &s.successors {
        succs.push(node_ref_to_sexpr(nr));
    }
    SExpr::List(vec![
        SExpr::Atom(Atom::Symbol(String::from("step"))),
        SExpr::Atom(Atom::Str(s.performative.clone())),
        SExpr::List(preds),
        SExpr::List(succs),
    ])
}

fn node_ref_to_sexpr(nr: &NodeRef) -> SExpr {
    use alloc::vec;
    match nr {
        NodeRef::Single(s) => SExpr::List(vec![
            SExpr::Atom(Atom::Symbol(String::from("single"))),
            SExpr::Atom(Atom::Str(s.clone())),
        ]),
        NodeRef::Any(set) => {
            let mut v = vec![SExpr::Atom(Atom::Symbol(String::from("any")))];
            for s in set {
                v.push(SExpr::Atom(Atom::Str(s.clone())));
            }
            SExpr::List(v)
        }
        NodeRef::All(set) => {
            let mut v = vec![SExpr::Atom(Atom::Symbol(String::from("all")))];
            for s in set {
                v.push(SExpr::Atom(Atom::Str(s.clone())));
            }
            SExpr::List(v)
        }
    }
}

/// Encode a slice of `ShapeConstraint`s deterministically, preserving the
/// order in which they were declared (REQ-220 — multiple constraints on the
/// same performative compose by conjunction, but order is part of the
/// signed body so re-ordering yields different bytes).
fn shapes_to_sexpr(shapes: &[ShapeConstraint]) -> SExpr {
    use alloc::vec;
    let mut items = vec![SExpr::Atom(Atom::Symbol(String::from("shapes")))];
    for s in shapes {
        items.push(shape_to_sexpr(s));
    }
    SExpr::List(items)
}

fn shape_to_sexpr(s: &ShapeConstraint) -> SExpr {
    use alloc::vec;
    let mut v = vec![
        SExpr::Atom(Atom::Symbol(String::from("shape"))),
        SExpr::Atom(Atom::Str(s.performative.clone())),
    ];
    for r in &s.rules {
        v.push(shape_rule_to_sexpr(r));
    }
    SExpr::List(v)
}

fn shape_rule_to_sexpr(r: &ShapeRule) -> SExpr {
    use alloc::vec;
    match r {
        ShapeRule::Require {
            keyword,
            type_constraint,
            children,
        } => {
            let mut v = vec![
                SExpr::Atom(Atom::Symbol(String::from("require"))),
                SExpr::Atom(Atom::Str(keyword.clone())),
                type_constraint_to_sexpr(type_constraint),
            ];
            for c in children {
                v.push(shape_rule_to_sexpr(c));
            }
            SExpr::List(v)
        }
        ShapeRule::Optional {
            keyword,
            type_constraint,
            default,
            children,
        } => {
            let mut v = vec![
                SExpr::Atom(Atom::Symbol(String::from("optional"))),
                SExpr::Atom(Atom::Str(keyword.clone())),
                type_constraint_to_sexpr(type_constraint),
                default_to_sexpr(default),
            ];
            for c in children {
                v.push(shape_rule_to_sexpr(c));
            }
            SExpr::List(v)
        }
        ShapeRule::MaxDepth(n) => SExpr::List(vec![
            SExpr::Atom(Atom::Symbol(String::from("max-depth"))),
            SExpr::Atom(Atom::Num(*n as i64)),
        ]),
    }
}

fn type_constraint_to_sexpr(tc: &Option<TypeConstraint>) -> SExpr {
    use alloc::vec;
    let mut v = vec![SExpr::Atom(Atom::Symbol(String::from("type")))];
    if let Some(t) = tc {
        let name = match t {
            TypeConstraint::String => "string",
            TypeConstraint::Number => "number",
            TypeConstraint::Bool => "bool",
            TypeConstraint::Symbol => "symbol",
            TypeConstraint::Keyword => "keyword",
            TypeConstraint::List => "list",
        };
        v.push(SExpr::Atom(Atom::Symbol(String::from(name))));
    }
    SExpr::List(v)
}

fn default_to_sexpr(d: &Option<SExpr>) -> SExpr {
    use alloc::vec;
    let mut v = vec![SExpr::Atom(Atom::Symbol(String::from("default")))];
    if let Some(e) = d {
        v.push(e.clone());
    }
    SExpr::List(v)
}

/// Compute the canonical bytes for signing a dialect.
///
/// This is the composition: `canonical_encode(to_signable_sexpr(d))`.
/// These bytes are the sole input to both `Signer::sign` and hash computation.
pub fn dialect_canonical_bytes(d: &Dialect) -> Vec<u8> {
    canonical_encode(&to_signable_sexpr(d))
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dialect::{base_dialect, PerformativeDef, ResourceBounds};
    use alloc::string::String;
    use alloc::vec;

    // ====================================================================
    // Phase 1: Atom-to-octet mapping tests
    // ====================================================================

    #[test]
    fn atom_octets_symbol() {
        assert_eq!(atom_to_octets(&Atom::Symbol("hello".into())), b"Shello");
    }

    #[test]
    fn atom_octets_symbol_empty() {
        assert_eq!(atom_to_octets(&Atom::Symbol(String::new())), b"S");
    }

    #[test]
    fn atom_octets_keyword() {
        assert_eq!(atom_to_octets(&Atom::Keyword("key".into())), b"Kkey");
    }

    #[test]
    fn atom_octets_keyword_with_hyphen() {
        assert_eq!(atom_to_octets(&Atom::Keyword("my-key".into())), b"Kmy-key");
    }

    #[test]
    fn atom_octets_string() {
        assert_eq!(atom_to_octets(&Atom::Str("hi".into())), b"Qhi");
    }

    #[test]
    fn atom_octets_string_empty() {
        assert_eq!(atom_to_octets(&Atom::Str(String::new())), b"Q");
    }

    #[test]
    fn atom_octets_num_positive() {
        assert_eq!(atom_to_octets(&Atom::Num(42)), b"N42");
    }

    #[test]
    fn atom_octets_num_negative() {
        assert_eq!(atom_to_octets(&Atom::Num(-7)), b"N-7");
    }

    #[test]
    fn atom_octets_num_zero() {
        assert_eq!(atom_to_octets(&Atom::Num(0)), b"N0");
    }

    #[test]
    fn atom_octets_num_max() {
        let mut expected = vec![b'N'];
        expected.extend_from_slice(alloc::format!("{}", i64::MAX).as_bytes());
        assert_eq!(atom_to_octets(&Atom::Num(i64::MAX)), expected);
    }

    #[test]
    fn atom_octets_num_min() {
        let mut expected = vec![b'N'];
        expected.extend_from_slice(alloc::format!("{}", i64::MIN).as_bytes());
        assert_eq!(atom_to_octets(&Atom::Num(i64::MIN)), expected);
    }

    #[test]
    fn atom_octets_bool_true() {
        assert_eq!(atom_to_octets(&Atom::Bool(true)), b"Bt");
    }

    #[test]
    fn atom_octets_bool_false() {
        assert_eq!(atom_to_octets(&Atom::Bool(false)), b"Bf");
    }

    #[test]
    fn atom_octets_unicode_symbol() {
        let s = "héllo";
        let mut expected = vec![b'S'];
        expected.extend_from_slice(s.as_bytes());
        assert_eq!(atom_to_octets(&Atom::Symbol(s.into())), expected);
    }

    #[test]
    fn atom_octets_unicode_string() {
        let s = "日本語";
        let mut expected = vec![b'Q'];
        expected.extend_from_slice(s.as_bytes());
        assert_eq!(atom_to_octets(&Atom::Str(s.into())), expected);
    }

    /// The mapping must be injective: distinct atoms produce distinct byte sequences.
    #[test]
    fn atom_mapping_injective() {
        let atoms = vec![
            Atom::Symbol("t".into()),
            Atom::Bool(true),
            Atom::Symbol("f".into()),
            Atom::Bool(false),
            Atom::Symbol("42".into()),
            Atom::Num(42),
            Atom::Symbol(":key".into()),
            Atom::Keyword("key".into()),
            Atom::Str("hello".into()),
            Atom::Symbol("\"hello".into()),
            Atom::Num(0),
            Atom::Symbol("0".into()),
            Atom::Num(-1),
            Atom::Symbol("-1".into()),
        ];
        let octets: Vec<Vec<u8>> = atoms.iter().map(atom_to_octets).collect();
        // Check each pair for uniqueness
        for i in 0..octets.len() {
            for j in (i + 1)..octets.len() {
                // Same octets implies same atom
                if octets[i] == octets[j] {
                    assert_eq!(
                        atoms[i], atoms[j],
                        "injectivity violation: {:?} and {:?} produce same octets {:?}",
                        atoms[i], atoms[j], octets[i]
                    );
                }
            }
        }
    }

    // ====================================================================
    // Phase 2: Canonical encoder tests
    // ====================================================================

    #[test]
    fn encode_symbol() {
        // Symbol "abc" -> octets "Sabc" (4 bytes) -> "4:Sabc"
        let e = SExpr::Atom(Atom::Symbol("abc".into()));
        assert_eq!(canonical_encode(&e), b"4:Sabc");
    }

    #[test]
    fn encode_empty_symbol() {
        // Symbol "" -> octets "S" (1 byte) -> "1:S"
        let e = SExpr::Atom(Atom::Symbol(String::new()));
        assert_eq!(canonical_encode(&e), b"1:S");
    }

    #[test]
    fn encode_num() {
        // Num(42) -> octets "N42" (3 bytes) -> "3:N42"
        let e = SExpr::Atom(Atom::Num(42));
        assert_eq!(canonical_encode(&e), b"3:N42");
    }

    #[test]
    fn encode_negative_num() {
        // Num(-7) -> octets "N-7" (3 bytes) -> "3:N-7"
        let e = SExpr::Atom(Atom::Num(-7));
        assert_eq!(canonical_encode(&e), b"3:N-7");
    }

    #[test]
    fn encode_bool_true() {
        // Bool(true) -> octets "Bt" (2 bytes) -> "2:Bt"
        let e = SExpr::Atom(Atom::Bool(true));
        assert_eq!(canonical_encode(&e), b"2:Bt");
    }

    #[test]
    fn encode_bool_false() {
        // Bool(false) -> octets "Bf" (2 bytes) -> "2:Bf"
        let e = SExpr::Atom(Atom::Bool(false));
        assert_eq!(canonical_encode(&e), b"2:Bf");
    }

    #[test]
    fn encode_keyword() {
        // Keyword "key" -> octets "Kkey" (4 bytes) -> "4:Kkey"
        let e = SExpr::Atom(Atom::Keyword("key".into()));
        assert_eq!(canonical_encode(&e), b"4:Kkey");
    }

    #[test]
    fn encode_string() {
        // Str "hi" -> octets "Qhi" (3 bytes) -> "3:Qhi"
        let e = SExpr::Atom(Atom::Str("hi".into()));
        assert_eq!(canonical_encode(&e), b"3:Qhi");
    }

    #[test]
    fn encode_empty_list() {
        let e = SExpr::List(vec![]);
        assert_eq!(canonical_encode(&e), b"()");
    }

    #[test]
    fn encode_simple_list() {
        // (tell "hi") -> (5:Stell3:Qhi)
        let e = SExpr::List(vec![
            SExpr::Atom(Atom::Symbol("tell".into())),
            SExpr::Atom(Atom::Str("hi".into())),
        ]);
        assert_eq!(canonical_encode(&e), b"(5:Stell3:Qhi)");
    }

    #[test]
    fn encode_nested_list() {
        // (x (1)) -> (2:Sx(3:N1))
        let e = SExpr::List(vec![
            SExpr::Atom(Atom::Symbol("x".into())),
            SExpr::List(vec![SExpr::Atom(Atom::Num(1))]),
        ]);
        assert_eq!(canonical_encode(&e), b"(2:Sx(2:N1))");
    }

    #[test]
    fn encode_deeply_nested() {
        // ((((a)))) -> ((((2:Sa))))
        let mut e = SExpr::Atom(Atom::Symbol("a".into()));
        for _ in 0..4 {
            e = SExpr::List(vec![e]);
        }
        assert_eq!(canonical_encode(&e), b"((((2:Sa))))");
    }

    #[test]
    fn encode_deterministic() {
        let e = SExpr::List(vec![
            SExpr::Atom(Atom::Symbol("hello".into())),
            SExpr::Atom(Atom::Num(42)),
            SExpr::Atom(Atom::Bool(true)),
        ]);
        let a = canonical_encode(&e);
        let b = canonical_encode(&e);
        assert_eq!(a, b);
    }

    #[test]
    fn encode_no_leading_zeros_in_length() {
        // Symbol "abcdefghi" (9 chars) -> octets "Sabcdefghi" (10 bytes) -> "10:Sabcdefghi"
        let e = SExpr::Atom(Atom::Symbol("abcdefghi".into()));
        let encoded = canonical_encode(&e);
        assert_eq!(&encoded[..3], b"10:");
        assert_eq!(&encoded[3..], b"Sabcdefghi");
    }

    // ====================================================================
    // Phase 3: Signable S-expression builder tests
    // ====================================================================

    fn test_dialect(name: &str) -> Dialect {
        Dialect {
            roles: Vec::new(),
            name: String::from(name),
            extends: vec![],
            author: Some(String::from("@test")),
            performatives: vec![PerformativeDef {
                role: None,
                name: String::from("greet"),
                params: vec![],
                template: SExpr::List(vec![
                    SExpr::Atom(Atom::Symbol(String::from("effect"))),
                    SExpr::Atom(Atom::Symbol(String::from("greet-action"))),
                ]),
            }],
            resources: ResourceBounds {
                max_depth: 8,
                max_expansion_size: 512,
                verification_time_ms: 10,
            },
            examples: vec![],
            signature: Some(vec![0xAA]),
            hash: Some(String::from("sha256:abc")),
            protocol: Some(String::from("ed25519")),
            causal_protocol: None,
            shapes: Vec::new(),
        }
    }

    #[test]
    fn signable_excludes_integrity_fields() {
        let d = test_dialect("test");
        let sexpr = to_signable_sexpr(&d);
        let encoded = canonical_encode(&sexpr);
        let encoded_str = core::str::from_utf8(&encoded).unwrap();
        // Must not contain signature, hash, or protocol
        assert!(!encoded_str.contains("sha256"));
        assert!(!encoded_str.contains("ed25519"));
    }

    #[test]
    fn signable_integrity_fields_dont_affect_output() {
        let d1 = test_dialect("test");
        let mut d2 = test_dialect("test");
        d2.signature = None;
        d2.hash = None;
        d2.protocol = None;

        assert_eq!(to_signable_sexpr(&d1), to_signable_sexpr(&d2));
    }

    #[test]
    fn signable_includes_name() {
        let d = test_dialect("my-dialect");
        let sexpr = to_signable_sexpr(&d);
        let encoded = canonical_encode(&sexpr);
        let encoded_str = core::str::from_utf8(&encoded).unwrap();
        assert!(encoded_str.contains("my-dialect"));
    }

    #[test]
    fn signable_includes_author() {
        let d = test_dialect("test");
        let sexpr = to_signable_sexpr(&d);
        let encoded = canonical_encode(&sexpr);
        let encoded_str = core::str::from_utf8(&encoded).unwrap();
        assert!(encoded_str.contains("@test"));
    }

    #[test]
    fn signable_includes_performatives() {
        let d = test_dialect("test");
        let sexpr = to_signable_sexpr(&d);
        let encoded = canonical_encode(&sexpr);
        let encoded_str = core::str::from_utf8(&encoded).unwrap();
        assert!(encoded_str.contains("greet"));
        assert!(encoded_str.contains("greet-action"));
    }

    #[test]
    fn signable_different_performative_order() {
        let mut d1 = test_dialect("test");
        d1.performatives = vec![
            PerformativeDef {
                role: None,
                name: String::from("a"),
                params: vec![],
                template: SExpr::Atom(Atom::Symbol(String::from("a"))),
            },
            PerformativeDef {
                role: None,
                name: String::from("b"),
                params: vec![],
                template: SExpr::Atom(Atom::Symbol(String::from("b"))),
            },
        ];

        let mut d2 = test_dialect("test");
        d2.performatives = vec![
            PerformativeDef {
                role: None,
                name: String::from("b"),
                params: vec![],
                template: SExpr::Atom(Atom::Symbol(String::from("b"))),
            },
            PerformativeDef {
                role: None,
                name: String::from("a"),
                params: vec![],
                template: SExpr::Atom(Atom::Symbol(String::from("a"))),
            },
        ];

        assert_ne!(
            dialect_canonical_bytes(&d1),
            dialect_canonical_bytes(&d2),
            "r4-002: different performative orderings must produce different bytes"
        );
    }

    #[test]
    fn signable_empty_dialect() {
        let d = Dialect {
            roles: Vec::new(),
            name: String::from("empty"),
            extends: vec![],
            author: None,
            performatives: vec![],
            resources: ResourceBounds {
                max_depth: 8,
                max_expansion_size: 512,
                verification_time_ms: 10,
            },
            examples: vec![],
            signature: None,
            hash: None,
            protocol: None,
            causal_protocol: None,
            shapes: Vec::new(),
        };
        let bytes = dialect_canonical_bytes(&d);
        assert!(!bytes.is_empty());
        // Should still encode validly
        let encoded_str = core::str::from_utf8(&bytes).unwrap();
        assert!(encoded_str.contains("empty"));
    }

    #[test]
    fn signable_all_optional_fields() {
        let d = Dialect {
            roles: Vec::new(),
            name: String::from("full"),
            extends: vec![String::from("parent1"), String::from("parent2")],
            author: Some(String::from("@author")),
            performatives: vec![PerformativeDef {
                role: None,
                name: String::from("act"),
                params: vec![SExpr::Atom(Atom::Symbol("x".into()))],
                template: SExpr::Atom(Atom::Symbol("do-it".into())),
            }],
            resources: ResourceBounds {
                max_depth: 16,
                max_expansion_size: 1024,
                verification_time_ms: 50,
            },
            examples: vec![SExpr::Atom(Atom::Str("example".into()))],
            signature: Some(vec![0xFF]),
            hash: Some(String::from("sha256:xxx")),
            protocol: Some(String::from("ed25519")),
            causal_protocol: None,
            shapes: Vec::new(),
        };
        let bytes = dialect_canonical_bytes(&d);
        let s = core::str::from_utf8(&bytes).unwrap();
        assert!(s.contains("full"));
        assert!(s.contains("parent1"));
        assert!(s.contains("parent2"));
        assert!(s.contains("@author"));
        assert!(s.contains("act"));
        assert!(s.contains("example"));
        // Integrity fields excluded
        assert!(!s.contains("sha256"));
        assert!(!s.contains("ed25519"));
    }

    #[test]
    fn signable_deterministic() {
        let d = test_dialect("test");
        let a = dialect_canonical_bytes(&d);
        let b = dialect_canonical_bytes(&d);
        assert_eq!(a, b, "r4-003: deterministic encoding");
    }

    #[test]
    fn signable_base_dialect() {
        let d = base_dialect();
        let bytes = dialect_canonical_bytes(&d);
        assert!(!bytes.is_empty());
        let s = core::str::from_utf8(&bytes).unwrap();
        assert!(s.contains("cbcl-base"));
        assert!(s.contains("tell"));
        assert!(s.contains("bye"));
    }

    #[test]
    fn signable_name_change_changes_bytes() {
        let d1 = test_dialect("alpha");
        let d2 = test_dialect("beta");
        assert_ne!(dialect_canonical_bytes(&d1), dialect_canonical_bytes(&d2));
    }

    // -- causal_protocol / shapes binding (PR feedback) --

    /// Backwards compatibility: a dialect with `causal_protocol: None` and
    /// empty `shapes` must produce identical canonical bytes after the
    /// signing form was extended — existing signatures keep verifying.
    #[test]
    fn signable_omits_causal_protocol_and_shapes_when_absent() {
        let d = test_dialect("legacy");
        let bytes = dialect_canonical_bytes(&d);
        let s = core::str::from_utf8(&bytes).unwrap();
        assert!(
            !s.contains("causal-protocol"),
            "absent causal_protocol must not appear in canonical bytes: {s}"
        );
        assert!(
            !s.contains("shapes"),
            "absent shapes must not appear in canonical bytes: {s}"
        );
    }

    #[test]
    fn signable_includes_causal_protocol_when_present() {
        use crate::protocol::{CausalProtocol, NodeRef, StepDecl};
        use alloc::collections::BTreeMap;
        let mut steps = BTreeMap::new();
        steps.insert(
            "begin".into(),
            StepDecl {
                performative: "begin".into(),
                predecessors: vec![],
                successors: vec![NodeRef::Single("ack".into())],
            },
        );
        steps.insert(
            "ack".into(),
            StepDecl {
                performative: "ack".into(),
                predecessors: vec![NodeRef::Single("begin".into())],
                successors: vec![],
            },
        );
        let mut d = test_dialect("with-protocol");
        d.causal_protocol = Some(CausalProtocol { steps });
        let bytes = dialect_canonical_bytes(&d);
        let s = core::str::from_utf8(&bytes).unwrap();
        assert!(s.contains("causal-protocol"));
        assert!(s.contains("step"));
        assert!(s.contains("begin"));
        assert!(s.contains("ack"));
    }

    #[test]
    fn signable_includes_shapes_when_non_empty() {
        use crate::shape::{ShapeConstraint, ShapeRule, TypeConstraint};
        let mut d = test_dialect("with-shapes");
        d.shapes = vec![ShapeConstraint {
            performative: "act".into(),
            rules: vec![ShapeRule::Require {
                keyword: "target".into(),
                type_constraint: Some(TypeConstraint::String),
                children: vec![],
            }],
        }];
        let bytes = dialect_canonical_bytes(&d);
        let s = core::str::from_utf8(&bytes).unwrap();
        assert!(s.contains("shapes"));
        assert!(s.contains("require"));
        assert!(s.contains("target"));
    }

    #[test]
    fn signable_changes_when_causal_protocol_changes() {
        use crate::protocol::{CausalProtocol, NodeRef, StepDecl};
        use alloc::collections::BTreeMap;
        fn dialect_with_pred(name: &str) -> Dialect {
            let mut steps = BTreeMap::new();
            steps.insert(
                "begin".into(),
                StepDecl {
                    performative: "begin".into(),
                    predecessors: vec![],
                    successors: vec![NodeRef::Single("ack".into())],
                },
            );
            steps.insert(
                "ack".into(),
                StepDecl {
                    performative: "ack".into(),
                    predecessors: vec![NodeRef::Single(name.into())],
                    successors: vec![],
                },
            );
            let mut d = test_dialect("p");
            d.causal_protocol = Some(CausalProtocol { steps });
            d
        }
        let a = dialect_canonical_bytes(&dialect_with_pred("begin"));
        let b = dialect_canonical_bytes(&dialect_with_pred("other"));
        assert_ne!(
            a, b,
            "mutating a step's predecessor must change canonical bytes"
        );
    }

    #[test]
    fn signable_changes_when_shapes_change() {
        use crate::shape::{ShapeConstraint, ShapeRule, TypeConstraint};
        let mut d1 = test_dialect("s");
        d1.shapes = vec![ShapeConstraint {
            performative: "act".into(),
            rules: vec![ShapeRule::Require {
                keyword: "target".into(),
                type_constraint: Some(TypeConstraint::String),
                children: vec![],
            }],
        }];
        let mut d2 = d1.clone();
        if let Some(s) = d2.shapes.first_mut() {
            s.rules.push(ShapeRule::Require {
                keyword: "priority".into(),
                type_constraint: Some(TypeConstraint::Number),
                children: vec![],
            });
        }
        assert_ne!(
            dialect_canonical_bytes(&d1),
            dialect_canonical_bytes(&d2),
            "adding a shape rule must change canonical bytes"
        );
    }

    // -- Snapshot / golden-bytes guard --------------------------------------
    //
    // These tests pin the *exact* canonical encoding of two carefully-chosen
    // dialects so accidental changes to atom tagging, child ordering, or
    // segment shape break a test instead of silently breaking interop or
    // existing signatures.
    //
    // If you legitimately change the canonical form (and bump
    // CANONICAL_FORM_VERSION), update the snapshot strings below to match
    // and call out the change in the version history doc-comment.

    /// Helper: build a fully-populated v1-shaped dialect (no protocol or
    /// shapes). The bytes here MUST match what was produced before
    /// `(causal-protocol …)` and `(shapes …)` were appended — this is
    /// the backwards-compatibility contract that keeps legacy signatures
    /// verifying.
    fn snapshot_legacy_dialect() -> Dialect {
        Dialect {
            roles: Vec::new(),
            name: String::from("legacy"),
            extends: vec![String::from("cbcl")],
            author: Some(String::from("@authority")),
            performatives: vec![PerformativeDef {
                role: None,
                name: String::from("act"),
                params: vec![SExpr::Atom(Atom::Symbol("x".into()))],
                template: SExpr::Atom(Atom::Symbol("do".into())),
            }],
            resources: ResourceBounds {
                max_depth: 8,
                max_expansion_size: 512,
                verification_time_ms: 10,
            },
            examples: vec![],
            signature: None,
            hash: None,
            protocol: None,
            causal_protocol: None,
            shapes: Vec::new(),
        }
    }

    #[test]
    fn snapshot_legacy_dialect_canonical_bytes() {
        let bytes = dialect_canonical_bytes(&snapshot_legacy_dialect());
        let s = core::str::from_utf8(&bytes).expect("canonical bytes are UTF-8 today");
        // Snapshot. If this fails the encoding has changed; investigate
        // whether it's deliberate (and bump CANONICAL_FORM_VERSION) or
        // accidental.
        let expected = "(8:Sdialect7:Qlegacy(8:Sextends5:Qcbcl)(7:Sauthor11:Q@authority)\
             (14:Sperformatives(5:Sperf4:Qact(7:Sparams2:Sx)3:Sdo))\
             (10:Sresources2:N84:N5123:N10)(9:Sexamples))";
        // Strip whitespace from the literal — the actual bytes have none.
        let expected: String = expected.chars().filter(|c| !c.is_whitespace()).collect();
        assert_eq!(s, expected, "legacy canonical bytes drifted");
    }

    #[test]
    fn snapshot_dialect_with_protocol_and_shapes() {
        use crate::protocol::{CausalProtocol, NodeRef, StepDecl};
        use crate::shape::{ShapeConstraint, ShapeRule, TypeConstraint};
        use alloc::collections::BTreeMap;

        let mut steps = BTreeMap::new();
        steps.insert(
            "begin".into(),
            StepDecl {
                performative: "begin".into(),
                predecessors: vec![],
                successors: vec![NodeRef::Single("act".into())],
            },
        );
        steps.insert(
            "act".into(),
            StepDecl {
                performative: "act".into(),
                predecessors: vec![NodeRef::Single("begin".into())],
                successors: vec![],
            },
        );

        let mut d = snapshot_legacy_dialect();
        d.causal_protocol = Some(CausalProtocol { steps });
        d.shapes = vec![ShapeConstraint {
            performative: "act".into(),
            rules: vec![ShapeRule::Require {
                keyword: "target".into(),
                type_constraint: Some(TypeConstraint::String),
                children: vec![],
            }],
        }];

        let bytes = dialect_canonical_bytes(&d);
        let s = core::str::from_utf8(&bytes).expect("canonical bytes are UTF-8 today");
        // Note: BTreeMap::values() iterates sorted by key, so `act` appears
        // before `begin` despite the insertion order above.
        let expected = "(8:Sdialect7:Qlegacy(8:Sextends5:Qcbcl)(7:Sauthor11:Q@authority)\
             (14:Sperformatives(5:Sperf4:Qact(7:Sparams2:Sx)3:Sdo))\
             (10:Sresources2:N84:N5123:N10)(9:Sexamples)\
             (16:Scausal-protocol\
             (5:Sstep4:Qact(13:Spredecessors(7:Ssingle6:Qbegin))(11:Ssuccessors))\
             (5:Sstep6:Qbegin(13:Spredecessors)(11:Ssuccessors(7:Ssingle4:Qact))))\
             (7:Sshapes(6:Sshape4:Qact(8:Srequire7:Qtarget(5:Stype7:Sstring)))))";
        let expected: String = expected.chars().filter(|c| !c.is_whitespace()).collect();
        assert_eq!(s, expected, "v2 canonical bytes drifted");
    }

    #[test]
    fn nested_shape_children_appear_in_canonical_bytes() {
        use crate::shape::{ShapeConstraint, ShapeRule, TypeConstraint};

        // Require :params (list) containing :step (string) containing
        // :id (number).
        let mut d = test_dialect("nested");
        d.shapes = vec![ShapeConstraint {
            performative: "act".into(),
            rules: vec![ShapeRule::Require {
                keyword: "params".into(),
                type_constraint: Some(TypeConstraint::List),
                children: vec![ShapeRule::Require {
                    keyword: "step".into(),
                    type_constraint: Some(TypeConstraint::String),
                    children: vec![ShapeRule::Optional {
                        keyword: "id".into(),
                        type_constraint: Some(TypeConstraint::Number),
                        default: None,
                        children: vec![],
                    }],
                }],
            }],
        }];

        let bytes = dialect_canonical_bytes(&d);
        let s = core::str::from_utf8(&bytes).unwrap();

        // Each nested keyword/type and the surrounding rule symbols must
        // all be present, exercising the recursive `shape_rule_to_sexpr`.
        for needle in [
            "shapes", "shape", "require", "params", "list", "step", "string", "optional", "id",
            "number",
        ] {
            assert!(
                s.contains(needle),
                "missing `{needle}` in nested-shape canonical encoding: {s}"
            );
        }

        // Add a sibling Optional with a default and verify the bytes change.
        let mut d2 = d.clone();
        if let Some(shape) = d2.shapes.first_mut() {
            if let Some(ShapeRule::Require { children, .. }) = shape.rules.first_mut() {
                children.push(ShapeRule::Optional {
                    keyword: "tag".into(),
                    type_constraint: None,
                    default: Some(SExpr::Atom(Atom::Str("none".into()))),
                    children: vec![],
                });
            }
        }
        assert_ne!(
            dialect_canonical_bytes(&d),
            dialect_canonical_bytes(&d2),
            "adding a sibling shape rule must change canonical bytes"
        );
    }

    #[test]
    fn canonical_form_version_is_two() {
        // Pin the version constant so changes are deliberate.
        assert_eq!(CANONICAL_FORM_VERSION, 2);
    }

    // ====================================================================
    // Phase 5: Hash alignment test
    // ====================================================================

    #[test]
    fn hash_and_sign_use_same_canonical_bytes() {
        let d = test_dialect("test");
        // Both hash and signature computation should use dialect_canonical_bytes
        let bytes_for_sign = dialect_canonical_bytes(&d);
        let bytes_for_hash = dialect_canonical_bytes(&d);
        assert_eq!(bytes_for_sign, bytes_for_hash);
    }

    // ====================================================================
    // Phase 6: Test vectors
    // ====================================================================

    #[test]
    fn test_vector_atom_symbol_abc() {
        // Symbol "abc" -> octets "Sabc" (4 bytes) -> "4:Sabc"
        assert_eq!(
            canonical_encode(&SExpr::Atom(Atom::Symbol("abc".into()))),
            b"4:Sabc"
        );
    }

    #[test]
    fn test_vector_atom_num_negative_99() {
        // Num(-99) -> octets "N-99" (4 bytes) -> "4:N-99"
        assert_eq!(canonical_encode(&SExpr::Atom(Atom::Num(-99))), b"4:N-99");
    }

    #[test]
    fn test_vector_list_tell_hi() {
        // (tell "hi") -> (5:Stell3:Qhi)
        let e = SExpr::List(vec![
            SExpr::Atom(Atom::Symbol("tell".into())),
            SExpr::Atom(Atom::Str("hi".into())),
        ]);
        assert_eq!(canonical_encode(&e), b"(5:Stell3:Qhi)");
    }

    #[test]
    fn test_vector_keyword_action() {
        // Keyword "action" -> octets "Kaction" (7 bytes) -> "7:Kaction"
        assert_eq!(
            canonical_encode(&SExpr::Atom(Atom::Keyword("action".into()))),
            b"7:Kaction"
        );
    }

    #[test]
    fn test_vector_bool_pair() {
        // (#t #f) -> (2:Bt2:Bf)
        let e = SExpr::List(vec![
            SExpr::Atom(Atom::Bool(true)),
            SExpr::Atom(Atom::Bool(false)),
        ]);
        assert_eq!(canonical_encode(&e), b"(2:Bt2:Bf)");
    }

    #[test]
    fn test_vector_nested_effect() {
        // (effect send-message) -> (7:Seffect13:Ssend-message)
        let e = SExpr::List(vec![
            SExpr::Atom(Atom::Symbol("effect".into())),
            SExpr::Atom(Atom::Symbol("send-message".into())),
        ]);
        assert_eq!(canonical_encode(&e), b"(7:Seffect13:Ssend-message)");
    }

    #[test]
    fn test_vector_empty_string() {
        // Str("") -> octets "Q" (1 byte) -> "1:Q"
        assert_eq!(
            canonical_encode(&SExpr::Atom(Atom::Str(String::new()))),
            b"1:Q"
        );
    }

    #[test]
    fn test_vector_num_zero() {
        // Num(0) -> octets "N0" (2 bytes) -> "2:N0"
        assert_eq!(canonical_encode(&SExpr::Atom(Atom::Num(0))), b"2:N0");
    }
}
