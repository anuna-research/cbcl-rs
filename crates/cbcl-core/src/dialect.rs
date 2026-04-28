//! Dialect definitions, resource bounds, and dialect registry.
//!
//! Mirrors `Dialect.lean` and the dialect-management parts of `Agent.lean`
//! from the Lean 4 proof library.

#![forbid(unsafe_code)]

use crate::protocol::CausalProtocol;
use crate::r1::{r1_violations, verify_r1_dialect};
use crate::r2::verify_r2;
use crate::r3::{r3_violations, verify_r3};
use crate::r4::{check_r4, R4Result, Signer};
use crate::r5::{r5_violations_with_ancestors, verify_r5_with_ancestors};
use crate::sexpr::{Atom, SExpr};
use crate::shape::ShapeConstraint;
use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

/// Resource bounds for dialect evaluation (REQ-020).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ResourceBounds {
    pub max_depth: u32,
    pub max_expansion_size: u32,
    pub verification_time_ms: u32,
}

impl ResourceBounds {
    /// Check if bounds are valid (REQ-024).
    pub fn is_valid(&self) -> bool {
        self.max_depth > 0
            && self.max_depth <= 64
            && self.max_expansion_size > 0
            && self.max_expansion_size <= 8192
            && self.verification_time_ms > 0
            && self.verification_time_ms <= 1000
    }
}

/// Error returned when dialect installation fails.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DialectInstallError {
    /// A performative template references its own name (R1 violation).
    R1Violation {
        dialect_name: String,
        recursive: Vec<String>,
    },
    /// The dialect's resource bounds are invalid (R2 violation).
    R2Violation { dialect_name: String },
    /// The dialect redefines one or more core performatives (R3 violation).
    R3Violation {
        dialect_name: String,
        redefined: Vec<String>,
    },
    /// The dialect's signature failed verification (R4 violation).
    R4Violation { dialect_name: String },
    /// A shape constraint is malformed (R5 violation).
    R5Violation {
        dialect_name: String,
        shape_errors: Vec<String>,
    },
}

impl fmt::Display for DialectInstallError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DialectInstallError::R1Violation {
                dialect_name,
                recursive,
            } => {
                write!(
                    f,
                    "R1 violation: dialect '{}' has recursive performative(s): {}",
                    dialect_name,
                    recursive.join(", ")
                )
            }
            DialectInstallError::R2Violation { dialect_name } => {
                write!(
                    f,
                    "R2 violation: dialect '{}' has invalid resource bounds",
                    dialect_name,
                )
            }
            DialectInstallError::R3Violation {
                dialect_name,
                redefined,
            } => {
                write!(
                    f,
                    "R3 violation: dialect '{}' redefines core performative(s): {}",
                    dialect_name,
                    redefined.join(", ")
                )
            }
            DialectInstallError::R4Violation { dialect_name } => {
                write!(
                    f,
                    "R4 violation: dialect '{}' has an invalid signature",
                    dialect_name,
                )
            }
            DialectInstallError::R5Violation {
                dialect_name,
                shape_errors,
            } => {
                write!(
                    f,
                    "R5 violation: dialect '{}' has malformed shape(s): {}",
                    dialect_name,
                    shape_errors.join("; ")
                )
            }
        }
    }
}

/// A performative definition within a dialect (REQ-021).
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct PerformativeDef {
    pub name: String,
    pub params: Vec<SExpr>,
    pub template: SExpr,
}

/// A CBCL dialect (REQ-022).
///
/// Mirrors `CBCL.Dialect` in `Dialect.lean:34–44`.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Dialect {
    pub name: String,
    /// Parent dialect names (Lean: `extends_ : List String`).
    pub extends: Vec<String>,
    pub author: Option<String>,
    pub performatives: Vec<PerformativeDef>,
    pub resources: ResourceBounds,
    pub examples: Vec<SExpr>,
    pub signature: Option<Vec<u8>>,
    pub hash: Option<String>,
    pub protocol: Option<String>,
    /// Causal protocol declaration (REQ-200, REQ-201).
    pub causal_protocol: Option<CausalProtocol>,
    /// Shape constraints for expanded messages (REQ-220).
    pub shapes: Vec<ShapeConstraint>,
}

impl Dialect {
    /// Check if this dialect defines a performative with the given name (REQ-025).
    pub fn defines_performative(&self, name: &str) -> bool {
        self.performatives.iter().any(|p| p.name == name)
    }

    /// Find a performative definition by name (REQ-025).
    pub fn find_performative(&self, name: &str) -> Option<&PerformativeDef> {
        self.performatives.iter().find(|p| p.name == name)
    }

    /// Return the names of all performatives in this dialect.
    pub fn performative_names(&self) -> Vec<&str> {
        self.performatives.iter().map(|p| p.name.as_str()).collect()
    }
}

/// Effect-template helper: `(effect <action>)`.
fn effect_template(action: &str) -> SExpr {
    SExpr::List(vec![
        SExpr::Atom(Atom::Symbol(String::from("effect"))),
        SExpr::Atom(Atom::Symbol(String::from(action))),
    ])
}

/// Map from core performative name to its effect action, matching Lean `baseDialect`.
const CORE_EFFECT_ACTIONS: [(&str, &str); 8] = [
    ("tell", "send-message"),
    ("ask", "send-query"),
    ("reply", "send-reply"),
    ("error", "signal-error"),
    ("ok", "acknowledge"),
    ("cancel", "cancel-conversation"),
    ("hello", "announce-presence"),
    ("bye", "announce-departure"),
];

/// The base dialect with 8 core performatives (REQ-023).
///
/// Templates use the `(effect <action>)` form matching `baseDialect` in
/// `Dialect.lean:53–68`.
pub fn base_dialect() -> Dialect {
    Dialect {
        name: String::from("cbcl-base"),
        extends: Vec::new(),
        author: Some(String::from("@cbcl-system")),
        performatives: CORE_EFFECT_ACTIONS
            .iter()
            .map(|&(name, action)| PerformativeDef {
                name: String::from(name),
                params: Vec::new(),
                template: effect_template(action),
            })
            .collect(),
        resources: ResourceBounds {
            max_depth: 8,
            max_expansion_size: 512,
            verification_time_ms: 10,
        },
        examples: Vec::new(),
        signature: None,
        hash: None,
        protocol: None,
        causal_protocol: None,
        shapes: Vec::new(),
    }
}

// ---------------------------------------------------------------------------
// DialectRegistry — ordered collection with base dialect at index 0
// ---------------------------------------------------------------------------

/// An ordered dialect collection with the base dialect always at index 0.
///
/// Mirrors the `dialects : List Dialect` field on `Agent` in `Agent.lean`,
/// extracted as a first-class type so it can be shared across agent and
/// pipeline contexts.
///
/// Invariant: `dialects[0] == base_dialect()`.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct DialectRegistry {
    dialects: Vec<Dialect>,
}

impl DialectRegistry {
    /// Create a new registry containing only the base dialect.
    pub fn new() -> Self {
        Self {
            dialects: vec![base_dialect()],
        }
    }

    /// Install a dialect after verifying R1, R2, and R3 (REQ-034, REQ-060–062, REQ-070, REQ-080).
    ///
    /// Returns an error if the dialect contains recursive performatives (R1),
    /// has invalid resource bounds (R2), or redefines any of the 8 core
    /// performatives (R3).
    /// Matches `Agent.installDialect` in `Agent.lean:38–39`
    /// with the R1 precondition from `R1NoRecursion.lean:38–40`,
    /// the R2 precondition from `R2ResourceBounds.lean:59–63`,
    /// and the R3 precondition from `R3CorePreservation.lean:57`.
    pub fn install(&mut self, d: Dialect) -> Result<(), DialectInstallError> {
        if !verify_r1_dialect(&d) {
            return Err(DialectInstallError::R1Violation {
                recursive: r1_violations(&d),
                dialect_name: d.name,
            });
        }
        if !verify_r2(&d) {
            return Err(DialectInstallError::R2Violation {
                dialect_name: d.name,
            });
        }
        if !verify_r3(&d) {
            return Err(DialectInstallError::R3Violation {
                redefined: r3_violations(&d),
                dialect_name: d.name,
            });
        }
        let ancestors = self.resolve_ancestors(&d);
        if !verify_r5_with_ancestors(&d, &ancestors) {
            return Err(DialectInstallError::R5Violation {
                shape_errors: r5_violations_with_ancestors(&d, &ancestors),
                dialect_name: d.name,
            });
        }
        #[cfg(feature = "tracing")]
        tracing::event!(
            tracing::Level::INFO,
            dialect = %d.name,
            "dialect_install_count"
        );
        self.dialects.push(d);
        Ok(())
    }

    /// Resolve `d.extends` to currently-installed ancestor dialects (REQ-206).
    ///
    /// Names that do not match an installed dialect are silently skipped —
    /// install-time R5 will only credit performatives from ancestors that the
    /// registry actually knows about.
    fn resolve_ancestors<'a>(&'a self, d: &Dialect) -> Vec<&'a Dialect> {
        d.extends
            .iter()
            .filter_map(|name| self.find_by_name(name))
            .collect()
    }

    /// Install a dialect after verifying R1–R4 (REQ-034, REQ-060–062, REQ-070, REQ-080, REQ-090–091).
    ///
    /// Like [`install`](Self::install) but additionally checks R4 signature
    /// integrity using the provided signer. Unsigned dialects are accepted
    /// (the spec allows them with a warning); dialects with *invalid*
    /// signatures are rejected with [`DialectInstallError::R4Violation`].
    ///
    /// Returns `((), R4Result)` on success so callers can inspect whether the
    /// dialect was signed or unsigned.
    pub fn install_with_signer(
        &mut self,
        d: Dialect,
        signer: &dyn Signer,
    ) -> Result<R4Result, DialectInstallError> {
        // R1–R3 checks (same as install)
        if !verify_r1_dialect(&d) {
            return Err(DialectInstallError::R1Violation {
                recursive: r1_violations(&d),
                dialect_name: d.name,
            });
        }
        if !verify_r2(&d) {
            return Err(DialectInstallError::R2Violation {
                dialect_name: d.name,
            });
        }
        if !verify_r3(&d) {
            return Err(DialectInstallError::R3Violation {
                redefined: r3_violations(&d),
                dialect_name: d.name,
            });
        }
        let ancestors = self.resolve_ancestors(&d);
        if !verify_r5_with_ancestors(&d, &ancestors) {
            return Err(DialectInstallError::R5Violation {
                shape_errors: r5_violations_with_ancestors(&d, &ancestors),
                dialect_name: d.name,
            });
        }
        // R4 check: invalid signatures are rejected; unsigned is accepted.
        //
        // The canonical signing form (`canonical::to_signable_sexpr`) does not
        // yet cover `causal_protocol` or `shapes`. These fields now drive
        // runtime acceptance, so a Valid signature over the rest of the
        // dialect would not bind their semantics. Until the signing form is
        // extended, reject signed dialects that carry these fields rather
        // than silently accept a signature with under-specified coverage.
        let r4 = check_r4(&d, signer);
        if r4 == R4Result::Invalid {
            return Err(DialectInstallError::R4Violation {
                dialect_name: d.name,
            });
        }
        if r4 == R4Result::Valid && !signature_covers_runtime_fields(&d) {
            return Err(DialectInstallError::R4Violation {
                dialect_name: d.name,
            });
        }
        #[cfg(feature = "tracing")]
        tracing::event!(
            tracing::Level::INFO,
            dialect = %d.name,
            r4_result = ?r4,
            "dialect_install_count"
        );
        self.dialects.push(d);
        Ok(r4)
    }

    /// The number of installed dialects (including the base dialect).
    pub fn len(&self) -> usize {
        self.dialects.len()
    }

    /// Always false — the registry always contains at least the base dialect.
    pub fn is_empty(&self) -> bool {
        false
    }

    /// Well-formedness check: base dialect is at index 0 (REQ-032).
    pub fn is_well_formed(&self) -> bool {
        !self.dialects.is_empty() && self.dialects[0] == base_dialect()
    }

    /// Get a dialect by index.
    pub fn get(&self, index: usize) -> Option<&Dialect> {
        self.dialects.get(index)
    }

    /// Get a dialect by name.
    pub fn find_by_name(&self, name: &str) -> Option<&Dialect> {
        self.dialects.iter().find(|d| d.name == name)
    }

    /// Search dialects in reverse order for one that defines the given
    /// performative (REQ-033).
    ///
    /// Matches `Agent.findPerformativeDialect` in `Agent.lean:34–35`.
    pub fn find_performative_dialect(&self, name: &str) -> Option<&Dialect> {
        self.dialects
            .iter()
            .rev()
            .find(|d| d.defines_performative(name))
    }

    /// Iterate over all installed dialects in order.
    pub fn iter(&self) -> core::slice::Iter<'_, Dialect> {
        self.dialects.iter()
    }

    /// Return a slice of all installed dialects.
    pub fn as_slice(&self) -> &[Dialect] {
        &self.dialects
    }
}

impl Default for DialectRegistry {
    fn default() -> Self {
        Self::new()
    }
}

/// Whether the dialect's R4 signing form covers every field that drives
/// runtime acceptance.
///
/// `canonical::to_signable_sexpr` does not currently encode
/// `causal_protocol` or `shapes`, so a Valid signature on a dialect that
/// declares either field would leave those semantics unbound by the
/// signature. Treat such dialects as having an inadequate signature until
/// the canonical form is extended.
fn signature_covers_runtime_fields(d: &Dialect) -> bool {
    d.causal_protocol.is_none() && d.shapes.is_empty()
}

impl<'a> IntoIterator for &'a DialectRegistry {
    type Item = &'a Dialect;
    type IntoIter = core::slice::Iter<'a, Dialect>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn base_dialect_has_8_performatives() {
        let d = base_dialect();
        assert_eq!(d.performatives.len(), 8);
        assert_eq!(d.name, "cbcl-base");
    }

    #[test]
    fn base_dialect_templates_are_effect_forms() {
        let d = base_dialect();
        let tell = d.find_performative("tell").unwrap();
        // Template should be (effect send-message)
        match &tell.template {
            SExpr::List(items) => {
                assert_eq!(items.len(), 2);
                assert!(items[0].is_symbol("effect"));
                assert!(items[1].is_symbol("send-message"));
            }
            _ => panic!("expected list template"),
        }
    }

    #[test]
    fn base_dialect_resource_bounds_valid() {
        let d = base_dialect();
        assert!(d.resources.is_valid());
    }

    #[test]
    fn base_dialect_extends_is_empty() {
        let d = base_dialect();
        assert!(d.extends.is_empty());
    }

    #[test]
    fn defines_and_find_performative() {
        let d = base_dialect();
        assert!(d.defines_performative("tell"));
        assert!(!d.defines_performative("nonexistent"));
        assert!(d.find_performative("ask").is_some());
    }

    #[test]
    fn performative_names() {
        let d = base_dialect();
        let names = d.performative_names();
        assert_eq!(names.len(), 8);
        assert!(names.contains(&"tell"));
        assert!(names.contains(&"bye"));
    }

    #[test]
    fn resource_bounds_validation() {
        let valid = ResourceBounds {
            max_depth: 8,
            max_expansion_size: 512,
            verification_time_ms: 10,
        };
        assert!(valid.is_valid());

        let invalid = ResourceBounds {
            max_depth: 0,
            max_expansion_size: 512,
            verification_time_ms: 10,
        };
        assert!(!invalid.is_valid());

        let too_large = ResourceBounds {
            max_depth: 65,
            max_expansion_size: 512,
            verification_time_ms: 10,
        };
        assert!(!too_large.is_valid());
    }

    // ---- DialectRegistry tests ----

    #[test]
    fn registry_new_has_base_dialect() {
        let reg = DialectRegistry::new();
        assert_eq!(reg.len(), 1);
        assert!(reg.is_well_formed());
        assert_eq!(reg.get(0).unwrap().name, "cbcl-base");
    }

    #[test]
    fn registry_install_appends() {
        let mut reg = DialectRegistry::new();
        let planning = Dialect {
            name: String::from("cbcl-planning"),
            extends: vec![String::from("cbcl")],
            author: Some(String::from("@planning-authority")),
            performatives: vec![PerformativeDef {
                name: String::from("propose-step"),
                params: vec![],
                template: effect_template("propose"),
            }],
            resources: ResourceBounds {
                max_depth: 16,
                max_expansion_size: 1024,
                verification_time_ms: 50,
            },
            examples: vec![],
            signature: None,
            hash: None,
            protocol: Some(String::from("ed25519")), causal_protocol: None, shapes: Vec::new(),
        };
        reg.install(planning).unwrap();
        assert_eq!(reg.len(), 2);
        assert!(reg.is_well_formed());
        assert_eq!(reg.get(1).unwrap().name, "cbcl-planning");
    }

    #[test]
    fn registry_find_performative_dialect_reverse_order() {
        let mut reg = DialectRegistry::new();
        // Install two dialects that define the same custom performative.
        for name in &["first", "second"] {
            reg.install(Dialect {
                name: String::from(*name),
                extends: vec![String::from("cbcl")],
                author: None,
                performatives: vec![PerformativeDef {
                    name: String::from("greet"),
                    params: vec![],
                    template: effect_template("greet-action"),
                }],
                resources: ResourceBounds {
                    max_depth: 8,
                    max_expansion_size: 512,
                    verification_time_ms: 10,
                },
                examples: vec![],
                signature: None,
                hash: None,
                protocol: None, causal_protocol: None, shapes: Vec::new(),
            })
            .unwrap();
        }
        // Reverse-order search should find the later dialect first.
        let found = reg.find_performative_dialect("greet").unwrap();
        assert_eq!(found.name, "second");
    }

    #[test]
    fn registry_install_rejects_r3_violation() {
        let mut reg = DialectRegistry::new();
        let bad = Dialect {
            name: String::from("bad-dialect"),
            extends: vec![String::from("cbcl")],
            author: None,
            performatives: vec![PerformativeDef {
                name: String::from("tell"),
                params: vec![],
                template: effect_template("custom-tell"),
            }],
            resources: ResourceBounds {
                max_depth: 8,
                max_expansion_size: 512,
                verification_time_ms: 10,
            },
            examples: vec![],
            signature: None,
            hash: None,
            protocol: None, causal_protocol: None, shapes: Vec::new(),
        };
        let err = reg.install(bad).unwrap_err();
        match err {
            DialectInstallError::R3Violation {
                dialect_name,
                redefined,
            } => {
                assert_eq!(dialect_name, "bad-dialect");
                assert_eq!(redefined, vec!["tell"]);
            }
            other => panic!("expected R3Violation, got {:?}", other),
        }
        // Registry unchanged.
        assert_eq!(reg.len(), 1);
    }

    #[test]
    fn registry_install_rejects_r2_violation() {
        let mut reg = DialectRegistry::new();
        let bad = Dialect {
            name: String::from("bad-bounds"),
            extends: vec![String::from("cbcl")],
            author: None,
            performatives: vec![],
            resources: ResourceBounds {
                max_depth: 100, // exceeds max allowed 64
                max_expansion_size: 512,
                verification_time_ms: 10,
            },
            examples: vec![],
            signature: None,
            hash: None,
            protocol: None, causal_protocol: None, shapes: Vec::new(),
        };
        let err = reg.install(bad).unwrap_err();
        match err {
            DialectInstallError::R2Violation { dialect_name } => {
                assert_eq!(dialect_name, "bad-bounds");
            }
            _ => panic!("expected R2Violation"),
        }
        // Registry unchanged.
        assert_eq!(reg.len(), 1);
    }

    #[test]
    fn registry_install_rejects_zero_bounds() {
        let mut reg = DialectRegistry::new();
        let bad = Dialect {
            name: String::from("zero-depth"),
            extends: vec![],
            author: None,
            performatives: vec![],
            resources: ResourceBounds {
                max_depth: 0,
                max_expansion_size: 512,
                verification_time_ms: 10,
            },
            examples: vec![],
            signature: None,
            hash: None,
            protocol: None, causal_protocol: None, shapes: Vec::new(),
        };
        assert!(matches!(
            reg.install(bad),
            Err(DialectInstallError::R2Violation { .. })
        ));
    }

    #[test]
    fn registry_find_by_name() {
        let reg = DialectRegistry::new();
        assert!(reg.find_by_name("cbcl-base").is_some());
        assert!(reg.find_by_name("nonexistent").is_none());
    }

    #[test]
    fn registry_is_never_empty() {
        let reg = DialectRegistry::new();
        assert!(!reg.is_empty());
    }

    #[test]
    fn registry_multi_dialect_install() {
        // Matches test vector dial-ver-006: base + 3 installed = 4
        let mut reg = DialectRegistry::new();
        for name in &[
            "cbcl-planning",
            "cbcl-crosschain-transfer",
            "cbcl-artifacts",
        ] {
            reg.install(Dialect {
                name: String::from(*name),
                extends: vec![String::from("cbcl")],
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
                protocol: Some(String::from("ed25519")), causal_protocol: None, shapes: Vec::new(),
            })
            .unwrap();
        }
        assert_eq!(reg.len(), 4);
        assert!(reg.is_well_formed());
    }

    #[test]
    fn registry_iter() {
        let reg = DialectRegistry::new();
        let names: Vec<&str> = reg.iter().map(|d| d.name.as_str()).collect();
        assert_eq!(names, vec!["cbcl-base"]);
    }

    #[test]
    fn registry_default() {
        let reg = DialectRegistry::default();
        assert!(reg.is_well_formed());
    }

    // ---- R4 integration tests ----

    use crate::r4::{R4Result, Signer};

    struct MockSigner;

    impl Signer for MockSigner {
        fn sign(&self, _data: &[u8]) -> Vec<u8> {
            alloc::vec![0xAA, 0xBB]
        }
        fn verify(&self, _data: &[u8], sig: &[u8]) -> bool {
            sig == [0xAA, 0xBB]
        }
    }

    #[test]
    fn registry_install_with_signer_accepts_unsigned() {
        let mut reg = DialectRegistry::new();
        let d = Dialect {
            name: String::from("unsigned-dialect"),
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
            protocol: None, causal_protocol: None, shapes: Vec::new(),
        };
        let result = reg.install_with_signer(d, &MockSigner).unwrap();
        assert_eq!(result, R4Result::Unsigned);
        assert_eq!(reg.len(), 2);
    }

    #[test]
    fn registry_install_with_signer_accepts_valid_signature() {
        let mut reg = DialectRegistry::new();
        let d = Dialect {
            name: String::from("signed-dialect"),
            extends: vec![],
            author: None,
            performatives: vec![],
            resources: ResourceBounds {
                max_depth: 8,
                max_expansion_size: 512,
                verification_time_ms: 10,
            },
            examples: vec![],
            signature: Some(alloc::vec![0xAA, 0xBB]),
            hash: None,
            protocol: Some(String::from("ed25519")), causal_protocol: None, shapes: Vec::new(),
        };
        let result = reg.install_with_signer(d, &MockSigner).unwrap();
        assert_eq!(result, R4Result::Valid);
        assert_eq!(reg.len(), 2);
    }

    #[test]
    fn registry_install_with_signer_rejects_invalid_signature() {
        let mut reg = DialectRegistry::new();
        let d = Dialect {
            name: String::from("bad-sig-dialect"),
            extends: vec![],
            author: None,
            performatives: vec![],
            resources: ResourceBounds {
                max_depth: 8,
                max_expansion_size: 512,
                verification_time_ms: 10,
            },
            examples: vec![],
            signature: Some(alloc::vec![0xFF, 0xFF]),
            hash: None,
            protocol: Some(String::from("ed25519")), causal_protocol: None, shapes: Vec::new(),
        };
        let err = reg.install_with_signer(d, &MockSigner).unwrap_err();
        match err {
            DialectInstallError::R4Violation { dialect_name } => {
                assert_eq!(dialect_name, "bad-sig-dialect");
            }
            other => panic!("expected R4Violation, got {:?}", other),
        }
        // Registry unchanged.
        assert_eq!(reg.len(), 1);
    }

    #[test]
    fn registry_install_with_signer_still_checks_r1_r2_r3() {
        let mut reg = DialectRegistry::new();
        // R3 violation: redefines "tell"
        let d = Dialect {
            name: String::from("bad-r3"),
            extends: vec![],
            author: None,
            performatives: vec![PerformativeDef {
                name: String::from("tell"),
                params: vec![],
                template: effect_template("custom-tell"),
            }],
            resources: ResourceBounds {
                max_depth: 8,
                max_expansion_size: 512,
                verification_time_ms: 10,
            },
            examples: vec![],
            signature: Some(alloc::vec![0xAA, 0xBB]),
            hash: None,
            protocol: None, causal_protocol: None, shapes: Vec::new(),
        };
        let err = reg.install_with_signer(d, &MockSigner).unwrap_err();
        assert!(matches!(err, DialectInstallError::R3Violation { .. }));
    }

    #[test]
    fn r4_violation_display() {
        let err = DialectInstallError::R4Violation {
            dialect_name: String::from("bad"),
        };
        let msg = alloc::format!("{}", err);
        assert!(msg.contains("R4 violation"));
        assert!(msg.contains("bad"));
    }

    // -- R4 must bind causal_protocol/shapes (PR feedback P1) --

    #[test]
    fn signed_dialect_with_causal_protocol_rejected_until_signing_form_extended() {
        use crate::protocol::{CausalProtocol, NodeRef, StepDecl};
        let mut reg = DialectRegistry::new();
        let mut steps = alloc::collections::BTreeMap::new();
        steps.insert("greet".into(), StepDecl {
            performative: "greet".into(),
            predecessors: vec![NodeRef::Single("begin".into())],
            successors: vec![],
        });
        steps.insert("begin".into(), StepDecl {
            performative: "begin".into(),
            predecessors: vec![],
            successors: vec![NodeRef::Single("greet".into())],
        });
        let d = Dialect {
            name: String::from("signed-with-protocol"),
            extends: vec![String::from("cbcl")],
            author: None,
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
            signature: Some(alloc::vec![0xAA, 0xBB]),
            hash: None,
            protocol: None,
            causal_protocol: Some(CausalProtocol { steps }),
            shapes: Vec::new(),
        };
        let err = reg.install_with_signer(d, &MockSigner).unwrap_err();
        assert!(
            matches!(err, DialectInstallError::R4Violation { .. }),
            "expected R4 violation for signed dialect with causal_protocol"
        );
    }

    #[test]
    fn signed_dialect_with_shapes_rejected_until_signing_form_extended() {
        use crate::shape::{ShapeConstraint, ShapeRule, TypeConstraint};
        let mut reg = DialectRegistry::new();
        let d = Dialect {
            name: String::from("signed-with-shapes"),
            extends: vec![String::from("cbcl")],
            author: None,
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
            signature: Some(alloc::vec![0xAA, 0xBB]),
            hash: None,
            protocol: None,
            causal_protocol: None,
            shapes: vec![ShapeConstraint {
                performative: String::from("greet"),
                rules: vec![ShapeRule::Require {
                    keyword: String::from("target"),
                    type_constraint: Some(TypeConstraint::String),
                    children: vec![],
                }],
            }],
        };
        let err = reg.install_with_signer(d, &MockSigner).unwrap_err();
        assert!(
            matches!(err, DialectInstallError::R4Violation { .. }),
            "expected R4 violation for signed dialect with shapes"
        );
    }
}
