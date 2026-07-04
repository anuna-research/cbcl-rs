//! R4: Integrity (Signer trait).
//!
//! The trait is defined in the pure core; concrete implementations live
//! in the effectful shell or downstream crates.
//!
//! Verification produces an [`R4Result`] that distinguishes between valid
//! signatures, unsigned dialects (accepted with warning), and invalid
//! signatures (rejected).

#![forbid(unsafe_code)]

use crate::canonical::dialect_canonical_bytes;
use crate::dialect::Dialect;
use alloc::vec::Vec;

/// Abstraction for Ed25519 (or similar) signing (REQ-090).
pub trait Signer {
    /// Sign the given data, returning the signature bytes.
    fn sign(&self, data: &[u8]) -> Vec<u8>;
    /// Verify that `sig` is a valid signature over `data`.
    fn verify(&self, data: &[u8], sig: &[u8]) -> bool;
}

/// Result of R4 signature verification.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum R4Result {
    /// Dialect has a valid signature.
    Valid,
    /// Dialect has no signature — accepted with warning.
    Unsigned,
    /// Dialect has a signature that failed verification.
    Invalid,
}

impl R4Result {
    /// Returns `true` if the dialect should be accepted (valid or unsigned).
    pub fn is_acceptable(&self) -> bool {
        matches!(self, R4Result::Valid | R4Result::Unsigned)
    }
}

/// Check R4: dialect signature integrity with detailed result.
///
/// - `Valid` — signature present and verified against the canonical body.
/// - `Unsigned` — no signature present (accepted with warning per spec).
/// - `Invalid` — signature present but verification failed.
pub fn check_r4(d: &Dialect, signer: &dyn Signer) -> R4Result {
    let result = {
        let Some(ref sig) = d.signature else {
            return R4Result::Unsigned;
        };
        let body = dialect_sign_body(d);
        if signer.verify(&body, sig) {
            R4Result::Valid
        } else {
            R4Result::Invalid
        }
    };
    #[cfg(feature = "tracing")]
    {
        let pass = result == R4Result::Valid;
        tracing::event!(
            tracing::Level::INFO,
            constraint = "R4",
            dialect = %d.name,
            result = ?result,
            pass,
            "constraint_check_result"
        );
    }
    result
}

/// Verify R4: dialect signature integrity (REQ-091).
///
/// Returns `true` only if the dialect has a signature and it verifies.
/// Unsigned dialects return `false`. Use [`check_r4`] for the three-way result.
pub fn verify_r4(d: &Dialect, signer: &dyn Signer) -> bool {
    check_r4(d, signer) == R4Result::Valid
}

/// Compute the canonical serialized body of a dialect for signing.
///
/// Uses RFC 9804 canonical S-expression encoding. The signable S-expression
/// includes all semantics-relevant fields (name, extends, author, performatives,
/// resources, examples) and excludes integrity fields (signature, hash, protocol).
///
/// Order-dependent — different orderings produce different bodies (r4-002).
/// Deterministic — same dialect always produces the same body (r4-003).
pub fn dialect_sign_body(d: &Dialect) -> Vec<u8> {
    dialect_canonical_bytes(d)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dialect::{base_dialect, Dialect, PerformativeDef, ResourceBounds};
    use crate::sexpr::{Atom, SExpr};
    use alloc::string::String;
    use alloc::vec;

    /// Mock signer that accepts signatures equal to `[0xAA, 0xBB]`.
    struct MockSigner;

    impl Signer for MockSigner {
        fn sign(&self, _data: &[u8]) -> Vec<u8> {
            vec![0xAA, 0xBB]
        }
        fn verify(&self, _data: &[u8], sig: &[u8]) -> bool {
            sig == [0xAA, 0xBB]
        }
    }

    /// Signer that verifies based on data content (for authority tests).
    struct AuthoritySigner {
        trusted_name: &'static str,
    }

    impl Signer for AuthoritySigner {
        fn sign(&self, _data: &[u8]) -> Vec<u8> {
            vec![0xCC, 0xDD]
        }
        fn verify(&self, data: &[u8], sig: &[u8]) -> bool {
            // Only verify if the data starts with the trusted dialect name
            let data_str = core::str::from_utf8(data).unwrap_or("");
            data_str.starts_with(self.trusted_name) && sig == [0xCC, 0xDD]
        }
    }

    fn test_dialect(name: &str) -> Dialect {
        Dialect {
            roles: Vec::new(),
            causal_locality: Default::default(),
            name: String::from(name),
            extends: vec![],
            author: Some(String::from("@test-authority")),
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
            signature: None,
            hash: None,
            protocol: None,
            causal_protocol: None,
            shapes: Vec::new(),
        }
    }

    // ---- Basic verify_r4 tests ----

    #[test]
    fn unsigned_dialect_fails_r4() {
        let d = base_dialect();
        assert!(!verify_r4(&d, &MockSigner));
    }

    #[test]
    fn signed_dialect_passes_r4() {
        let mut d = base_dialect();
        d.signature = Some(vec![0xAA, 0xBB]);
        assert!(verify_r4(&d, &MockSigner));
    }

    #[test]
    fn bad_signature_fails_r4() {
        let mut d = base_dialect();
        d.signature = Some(vec![0xFF, 0xFF]);
        assert!(!verify_r4(&d, &MockSigner));
    }

    // ---- check_r4 three-way result tests ----

    #[test]
    fn check_r4_unsigned_returns_unsigned() {
        let d = base_dialect();
        assert_eq!(check_r4(&d, &MockSigner), R4Result::Unsigned);
    }

    #[test]
    fn check_r4_valid_signature_returns_valid() {
        let mut d = base_dialect();
        d.signature = Some(vec![0xAA, 0xBB]);
        assert_eq!(check_r4(&d, &MockSigner), R4Result::Valid);
    }

    #[test]
    fn check_r4_invalid_signature_returns_invalid() {
        let mut d = base_dialect();
        d.signature = Some(vec![0xFF, 0xFF]);
        assert_eq!(check_r4(&d, &MockSigner), R4Result::Invalid);
    }

    #[test]
    fn r4_result_acceptability() {
        assert!(R4Result::Valid.is_acceptable());
        assert!(R4Result::Unsigned.is_acceptable());
        assert!(!R4Result::Invalid.is_acceptable());
    }

    // ---- Test vector r4-001: unknown authority rejection ----

    #[test]
    fn r4_001_rejects_unknown_authority() {
        let mut d = test_dialect("test-dialect");
        d.signature = Some(vec![0xCC, 0xDD]);

        // Signer that only trusts "trusted-dialect"
        let signer = AuthoritySigner {
            trusted_name: "trusted-dialect",
        };
        // "test-dialect" is not the trusted name, so verification fails
        assert_eq!(check_r4(&d, &signer), R4Result::Invalid);
        assert!(!verify_r4(&d, &signer));
    }

    // ---- Test vector r4-002: different orderings produce different encodings ----

    #[test]
    fn r4_002_different_orderings_different_encodings() {
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

        let body1 = dialect_sign_body(&d1);
        let body2 = dialect_sign_body(&d2);
        assert_ne!(
            body1, body2,
            "different orderings must produce different encodings"
        );
    }

    // ---- Test vector r4-003: deterministic encoding ----

    #[test]
    fn r4_003_deterministic_encoding() {
        let d = test_dialect("test");
        let body1 = dialect_sign_body(&d);
        let body2 = dialect_sign_body(&d);
        assert_eq!(body1, body2, "encode(d) == encode(d) must always hold");
    }

    // ---- Test vector r4-004: hash, signature, protocol fields preserved ----

    #[test]
    fn r4_004_integrity_fields_preserved() {
        let d = Dialect {
            roles: Vec::new(),
            causal_locality: Default::default(),
            name: String::from("test-integrity-fields"),
            extends: vec![],
            author: None,
            performatives: vec![],
            resources: ResourceBounds {
                max_depth: 8,
                max_expansion_size: 512,
                verification_time_ms: 10,
            },
            examples: vec![],
            signature: Some(b"sig123".to_vec()),
            hash: Some(String::from("sha256:abcd1234")),
            protocol: Some(String::from("ed25519")),
            causal_protocol: None,
            shapes: Vec::new(),
        };
        assert_eq!(d.hash.as_deref(), Some("sha256:abcd1234"));
        assert_eq!(d.signature.as_deref(), Some(b"sig123".as_slice()));
        assert_eq!(d.protocol.as_deref(), Some("ed25519"));
    }

    // ---- dialect_sign_body includes all components ----

    #[test]
    fn sign_body_includes_name_and_performatives() {
        let d = test_dialect("my-dialect");
        let body = dialect_sign_body(&d);
        let body_str = core::str::from_utf8(&body).unwrap();
        assert!(body_str.contains("my-dialect"));
        assert!(body_str.contains("greet"));
    }

    #[test]
    fn sign_body_empty_performatives() {
        let mut d = test_dialect("empty");
        d.performatives = vec![];
        let body = dialect_sign_body(&d);
        let body_str = core::str::from_utf8(&body).unwrap();
        assert!(body_str.contains("empty"));
        // Should still contain structural elements (extends, author, resources, etc.)
        assert!(body_str.contains("performatives"));
    }
}
