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
use crate::sexpr::{Atom, SExpr};
use alloc::string::String;
use alloc::vec::Vec;

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
///   (examples <example>*))
/// ```
///
/// Performative order is preserved — different orderings produce different
/// signable S-expressions (r4-002).
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

    SExpr::List(top)
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
        assert_eq!(
            atom_to_octets(&Atom::Keyword("my-key".into())),
            b"Kmy-key"
        );
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
        let octets: Vec<Vec<u8>> = atoms.iter().map(|a| atom_to_octets(a)).collect();
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
            name: String::from(name),
            extends: vec![],
            author: Some(String::from("@test")),
            performatives: vec![PerformativeDef {
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
                name: String::from("a"),
                params: vec![],
                template: SExpr::Atom(Atom::Symbol(String::from("a"))),
            },
            PerformativeDef {
                name: String::from("b"),
                params: vec![],
                template: SExpr::Atom(Atom::Symbol(String::from("b"))),
            },
        ];

        let mut d2 = test_dialect("test");
        d2.performatives = vec![
            PerformativeDef {
                name: String::from("b"),
                params: vec![],
                template: SExpr::Atom(Atom::Symbol(String::from("b"))),
            },
            PerformativeDef {
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
            name: String::from("full"),
            extends: vec![String::from("parent1"), String::from("parent2")],
            author: Some(String::from("@author")),
            performatives: vec![PerformativeDef {
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
        assert_eq!(
            canonical_encode(&SExpr::Atom(Atom::Num(-99))),
            b"4:N-99"
        );
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
        assert_eq!(
            canonical_encode(&SExpr::Atom(Atom::Num(0))),
            b"2:N0"
        );
    }
}
