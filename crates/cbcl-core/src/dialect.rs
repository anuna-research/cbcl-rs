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
use crate::r6::{derive_envelope_routes, r6_violations};
use crate::role::{CausalLocality, R6Violation as R6ViolationDetail, RoleAnnotation, RoleDecl};
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
    /// The protocol's expanded step count — after `(repeat k …)`
    /// macro-expansion (SPEC-015 REQ-704) — is not within the dialect's
    /// declared R2 expansion budget. This is what keeps `k` honest:
    /// repetition is priced in R2's existing declared-bounds currency.
    R2ProtocolBudgetExceeded {
        dialect_name: String,
        /// Post-expansion protocol step count (`begin` excluded).
        expanded_steps: u32,
        /// The dialect's declared `max-expansion-size` bound.
        budget: u32,
    },
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
    /// The dialect's role layer is ill-formed (R6 violation, SPEC-014
    /// REQ-627).
    R6Violation {
        dialect_name: String,
        violations: Vec<R6ViolationDetail>,
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
            DialectInstallError::R2ProtocolBudgetExceeded {
                dialect_name,
                expanded_steps,
                budget,
            } => {
                write!(
                    f,
                    "R2 violation: dialect '{}' protocol expands to {} steps, \
                     exceeding the declared expansion budget {}",
                    dialect_name, expanded_steps, budget,
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
            DialectInstallError::R6Violation {
                dialect_name,
                violations,
            } => {
                write!(f, "R6 violation: dialect '{dialect_name}':")?;
                for v in violations {
                    write!(f, " {v};")?;
                }
                Ok(())
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
    /// `:from`/`:to` role annotation (SPEC-014 REQ-621, CON-600).
    #[cfg_attr(feature = "serde", serde(default))]
    pub role: Option<RoleAnnotation>,
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
    /// Canonical content hash, `sha256:<lowercase-hex64>` over
    /// [`crate::canonical::dialect_canonical_bytes`] (SPEC-014 REQ-628).
    ///
    /// Invariant: every dialect installed into a [`DialectRegistry`] has
    /// `Some(..)` — installation computes the hash when this is `None`.
    /// A pre-declared hash (e.g. a `:hash` clause in dialect source) is
    /// preserved verbatim so wrappers can compare the claim against the
    /// computed value and reject mismatches.
    pub hash: Option<String>,
    pub protocol: Option<String>,
    /// Causal protocol declaration (REQ-200, REQ-201).
    pub causal_protocol: Option<CausalProtocol>,
    /// Shape constraints for expanded messages (REQ-220).
    pub shapes: Vec<ShapeConstraint>,
    /// Declared roles (SPEC-014 REQ-621, CON-600); empty = role-free dialect.
    #[cfg_attr(feature = "serde", serde(default))]
    pub roles: Vec<RoleDecl>,
    /// `(:causal-locality derive|reject)` (SPEC-015 REQ-709, ADR-704):
    /// under `Derive`, R6(vi) failures compile into the recorded
    /// envelope-routing table instead of rejecting; the default `Reject`
    /// preserves v1 semantics bit-for-bit.
    #[cfg_attr(feature = "serde", serde(default))]
    pub causal_locality: CausalLocality,
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
        causal_locality: CausalLocality::Reject,
        roles: Vec::new(),
        name: String::from("cbcl-base"),
        extends: Vec::new(),
        author: Some(String::from("@cbcl-system")),
        performatives: CORE_EFFECT_ACTIONS
            .iter()
            .map(|&(name, action)| PerformativeDef {
                role: None,
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
    pub fn install(&mut self, mut d: Dialect) -> Result<(), DialectInstallError> {
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
        Self::check_protocol_expansion_budget(&d)?;
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
        // R6 (SPEC-014 REQ-627; SPEC-015 REQ-709): dialect-level role
        // checks; role-free dialects pass trivially (REQ-607). Under
        // `(:causal-locality derive)`, R6(vi) findings compile into the
        // envelope-routing table instead of rejecting.
        Self::apply_r6(&mut d)?;
        Self::ensure_hash(&mut d);
        #[cfg(feature = "tracing")]
        tracing::event!(
            tracing::Level::INFO,
            dialect = %d.name,
            "dialect_install_count"
        );
        self.dialects.push(d);
        Ok(())
    }

    /// R6 gate (SPEC-014 REQ-627; SPEC-015 REQ-709, ADR-704).
    ///
    /// Under the default `(:causal-locality reject)` any violation rejects,
    /// exactly as v1. Under `derive`, R6(vi) `NotCausallyLocal` findings
    /// stop being rejection conditions and become the derivation's
    /// worklist: every *other* violation class still rejects, and when none
    /// remain the envelope-widening closure is derived
    /// ([`derive_envelope_routes`]) and recorded on the dialect. Payload
    /// `:to` sets are untouched — the closure only adds envelope routes.
    fn apply_r6(d: &mut Dialect) -> Result<(), DialectInstallError> {
        let r6 = r6_violations(d);
        let deriving = matches!(d.causal_locality, CausalLocality::Derive(_));
        let violations: Vec<R6ViolationDetail> = if deriving {
            r6.into_iter()
                .filter(|v| !matches!(v, R6ViolationDetail::NotCausallyLocal { .. }))
                .collect()
        } else {
            r6
        };
        if !violations.is_empty() {
            return Err(DialectInstallError::R6Violation {
                violations,
                dialect_name: d.name.clone(),
            });
        }
        if deriving {
            // Deterministic and idempotent: the closure is a pure function
            // of the dialect body, so every independent install records the
            // identical table (the replicated-choreographer property
            // extended from projection to repair).
            d.causal_locality = CausalLocality::Derive(derive_envelope_routes(d));
        }
        Ok(())
    }

    /// Populate `d.hash` with the canonical content hash when absent
    /// (SPEC-014 REQ-628: every installed dialect carries `Some(hash)`).
    ///
    /// A pre-declared hash is left untouched: overwriting it would defeat
    /// wrappers that compare the declared claim against the computed value
    /// after install (e.g. the wasm bindings' `:hash` verification).
    ///
    /// SIMPLIFY: only *installed* dialects are hashed — the base dialect
    /// seeded by `DialectRegistry::new()` keeps `hash: None` because
    /// `is_well_formed()` (and callers) compare `dialects[0]` against
    /// `base_dialect()` by equality. Upgrade path: make `base_dialect()`
    /// itself return `hash: Some(dialect_hash(..))` and update the golden
    /// expectations that pin its serialized form.
    fn ensure_hash(d: &mut Dialect) {
        if d.hash.is_none() {
            d.hash = Some(crate::canonical::dialect_hash(d));
        }
    }

    /// SPEC-015 REQ-704: the protocol's expanded step count counts against
    /// R2's declared expansion budget. By install time, `(repeat k …)`
    /// forms are already macro-expanded into the `CausalProtocol` (the
    /// parser expands once at parse), so the count here *is* the expanded
    /// size; a hand-unrolled equivalent protocol is priced identically.
    ///
    /// Uses R2's strict-`<` idiom (`ResourceState::add_expansion` in
    /// `R2ResourceBounds.lean:43–47`): a count at or above the declared
    /// bound is a typed rejection.
    fn check_protocol_expansion_budget(d: &Dialect) -> Result<(), DialectInstallError> {
        if let Some(cp) = &d.causal_protocol {
            let expanded_steps = cp.expansion_size();
            if expanded_steps >= d.resources.max_expansion_size {
                return Err(DialectInstallError::R2ProtocolBudgetExceeded {
                    dialect_name: d.name.clone(),
                    expanded_steps,
                    budget: d.resources.max_expansion_size,
                });
            }
        }
        Ok(())
    }

    /// Resolve `d.extends` to currently-installed ancestor dialects (REQ-206).
    ///
    /// Names that do not match an installed dialect are silently skipped —
    /// install-time R5 will only credit performatives from ancestors that the
    /// registry actually knows about. The shorthand `cbcl` is aliased to the
    /// canonical base dialect name `cbcl-base` since dialect literals
    /// commonly write `(extends cbcl)` while the registry stores the base
    /// under its full name.
    ///
    /// Public so standalone tooling (e.g. `cbcl verify`) can match install-time
    /// R5 semantics by feeding the result into [`crate::r5::verify_r5_with_ancestors`].
    pub fn resolve_ancestors<'a>(&'a self, d: &Dialect) -> Vec<&'a Dialect> {
        d.extends
            .iter()
            .filter_map(|name| {
                let resolved = if name == "cbcl" {
                    "cbcl-base"
                } else {
                    name.as_str()
                };
                self.find_by_name(resolved)
            })
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
        mut d: Dialect,
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
        Self::check_protocol_expansion_budget(&d)?;
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
        // R6 (SPEC-014 REQ-627; SPEC-015 REQ-709): as in `install`. The
        // derived routing table is excluded from the canonical signing
        // form (only the declared mode is signed), so recording it here
        // cannot invalidate the signature checked next.
        Self::apply_r6(&mut d)?;
        // R4 check: invalid signatures are rejected; unsigned is accepted.
        // The canonical signing form (`canonical::to_signable_sexpr`) covers
        // every semantics-relevant field, including `causal_protocol` and
        // `shapes`, so a Valid signature binds runtime acceptance.
        let r4 = check_r4(&d, signer);
        if r4 == R4Result::Invalid {
            return Err(DialectInstallError::R4Violation {
                dialect_name: d.name,
            });
        }
        // The hash is over the signable form, which excludes integrity
        // fields, so populating it after the R4 check cannot invalidate
        // the just-verified signature.
        Self::ensure_hash(&mut d);
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

    /// The base dialect, if it defines `name` (REQ-033).
    ///
    /// This is the *only* name-based lookup dispatch performs, and it is
    /// confined to the base dialect because R3 guarantees the eight core
    /// performatives have exactly one definer. A custom performative is never
    /// looked up this way: it is resolved against the dialect its `(lang …)`
    /// wrapper names, so which definition applies is fixed by the message
    /// rather than by the installed set. That is what allows two dialects to
    /// define the same performative name without conflict.
    ///
    /// Matches `Agent.baseDefinerOf` in `Agent.lean`.
    pub fn base_definer_of(&self, name: &str) -> Option<&Dialect> {
        self.dialects
            .first()
            .filter(|d| d.defines_performative(name))
    }

    /// Every installed dialect defining `name`, in installation order.
    ///
    /// Introspection only — capability queries, diagnostics, tooling. It is
    /// deliberately not a dispatch path: several dialects may legitimately
    /// define one name, and choosing between them is the `(lang …)` wrapper's
    /// job, not the registry's.
    pub fn dialects_defining<'a>(&'a self, name: &'a str) -> impl Iterator<Item = &'a Dialect> {
        self.dialects
            .iter()
            .filter(move |d| d.defines_performative(name))
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
            roles: Vec::new(),
            causal_locality: Default::default(),
            name: String::from("cbcl-planning"),
            extends: vec![String::from("cbcl")],
            author: Some(String::from("@planning-authority")),
            performatives: vec![PerformativeDef {
                role: None,
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
            protocol: Some(String::from("ed25519")),
            causal_protocol: None,
            shapes: Vec::new(),
        };
        reg.install(planning).unwrap();
        assert_eq!(reg.len(), 2);
        assert!(reg.is_well_formed());
        assert_eq!(reg.get(1).unwrap().name, "cbcl-planning");
    }

    /// A dialect defining a single custom performative `greet`.
    fn greeter(name: &str) -> Dialect {
        Dialect {
            roles: Vec::new(),
            causal_locality: Default::default(),
            name: String::from(name),
            extends: vec![String::from("cbcl")],
            author: None,
            performatives: vec![PerformativeDef {
                role: None,
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
            protocol: None,
            causal_protocol: None,
            shapes: Vec::new(),
        }
    }

    #[test]
    fn base_definer_of_finds_core_performatives() {
        let reg = DialectRegistry::new();
        assert_eq!(reg.base_definer_of("tell").unwrap().name, "cbcl-base");
    }

    /// REQ-033: core dispatch consults the base dialect only, so installing
    /// dialects can never change what a core performative means.
    #[test]
    fn base_definer_of_ignores_installed_dialects() {
        let mut reg = DialectRegistry::new();
        reg.install(greeter("first")).unwrap();
        assert!(reg.base_definer_of("greet").is_none());
    }

    /// REQ-033: two dialects defining one performative name is legitimate.
    /// The `(lang …)` wrapper chooses between them, so the registry reports
    /// both instead of picking or rejecting.
    #[test]
    fn dialects_defining_reports_every_definer_in_install_order() {
        let mut reg = DialectRegistry::new();
        reg.install(greeter("first")).unwrap();
        reg.install(greeter("second")).unwrap();
        let names: Vec<&str> = reg
            .dialects_defining("greet")
            .map(|d| d.name.as_str())
            .collect();
        assert_eq!(names, vec!["first", "second"]);
    }

    #[test]
    fn registry_install_rejects_r3_violation() {
        let mut reg = DialectRegistry::new();
        let bad = Dialect {
            roles: Vec::new(),
            causal_locality: Default::default(),
            name: String::from("bad-dialect"),
            extends: vec![String::from("cbcl")],
            author: None,
            performatives: vec![PerformativeDef {
                role: None,
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
            protocol: None,
            causal_protocol: None,
            shapes: Vec::new(),
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
            roles: Vec::new(),
            causal_locality: Default::default(),
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
            protocol: None,
            causal_protocol: None,
            shapes: Vec::new(),
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
            roles: Vec::new(),
            causal_locality: Default::default(),
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
            protocol: None,
            causal_protocol: None,
            shapes: Vec::new(),
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
                roles: Vec::new(),
                causal_locality: Default::default(),
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
                protocol: Some(String::from("ed25519")),
                causal_protocol: None,
                shapes: Vec::new(),
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
            roles: Vec::new(),
            causal_locality: Default::default(),
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
            protocol: None,
            causal_protocol: None,
            shapes: Vec::new(),
        };
        let result = reg.install_with_signer(d, &MockSigner).unwrap();
        assert_eq!(result, R4Result::Unsigned);
        assert_eq!(reg.len(), 2);
    }

    #[test]
    fn registry_install_with_signer_accepts_valid_signature() {
        let mut reg = DialectRegistry::new();
        let d = Dialect {
            roles: Vec::new(),
            causal_locality: Default::default(),
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
            protocol: Some(String::from("ed25519")),
            causal_protocol: None,
            shapes: Vec::new(),
        };
        let result = reg.install_with_signer(d, &MockSigner).unwrap();
        assert_eq!(result, R4Result::Valid);
        assert_eq!(reg.len(), 2);
    }

    #[test]
    fn registry_install_with_signer_rejects_invalid_signature() {
        let mut reg = DialectRegistry::new();
        let d = Dialect {
            roles: Vec::new(),
            causal_locality: Default::default(),
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
            protocol: Some(String::from("ed25519")),
            causal_protocol: None,
            shapes: Vec::new(),
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
            roles: Vec::new(),
            causal_locality: Default::default(),
            name: String::from("bad-r3"),
            extends: vec![],
            author: None,
            performatives: vec![PerformativeDef {
                role: None,
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
            protocol: None,
            causal_protocol: None,
            shapes: Vec::new(),
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

    // -- R4 binds causal_protocol/shapes via canonical signing form --

    /// A signer whose verifier accepts only signatures produced by `sign(d)`
    /// over `dialect_canonical_bytes(d)` — useful for confirming that
    /// mutating bound fields invalidates the signature.
    struct CanonicalSigner;

    impl Signer for CanonicalSigner {
        fn sign(&self, data: &[u8]) -> Vec<u8> {
            // Trivial reversible "signature": a hash of the bytes.
            let mut sum: u32 = 0x9e3779b9;
            for &b in data {
                sum = sum.wrapping_mul(33).wrapping_add(b as u32);
            }
            sum.to_le_bytes().to_vec()
        }
        fn verify(&self, data: &[u8], sig: &[u8]) -> bool {
            self.sign(data) == sig
        }
    }

    fn signed_dialect_with_protocol_and_shapes() -> Dialect {
        use crate::protocol::{CausalProtocol, NodeRef, StepDecl};
        use crate::shape::{ShapeConstraint, ShapeRule, TypeConstraint};
        let mut steps = alloc::collections::BTreeMap::new();
        steps.insert(
            "begin".into(),
            StepDecl {
                performative: "begin".into(),
                predecessors: vec![],
                successors: vec![NodeRef::Single("greet".into())],
            },
        );
        steps.insert(
            "greet".into(),
            StepDecl {
                performative: "greet".into(),
                predecessors: vec![NodeRef::Single("begin".into())],
                successors: vec![],
            },
        );
        Dialect {
            roles: Vec::new(),
            causal_locality: Default::default(),
            name: String::from("bound-by-signature"),
            extends: vec![String::from("cbcl")],
            author: None,
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
            causal_protocol: Some(CausalProtocol { steps }),
            shapes: vec![ShapeConstraint {
                performative: String::from("greet"),
                rules: vec![ShapeRule::Require {
                    keyword: String::from("target"),
                    type_constraint: Some(TypeConstraint::String),
                    children: vec![],
                }],
            }],
        }
    }

    #[test]
    fn signed_dialect_with_causal_protocol_now_installs() {
        // What used to be rejected as a stopgap should now install: the
        // canonical signing form covers causal_protocol.
        let mut d = signed_dialect_with_protocol_and_shapes();
        d.shapes = Vec::new(); // protocol-only case
        let bytes = crate::canonical::dialect_canonical_bytes(&d);
        d.signature = Some(CanonicalSigner.sign(&bytes));

        let mut reg = DialectRegistry::new();
        let result = reg.install_with_signer(d, &CanonicalSigner).unwrap();
        assert_eq!(result, R4Result::Valid);
    }

    #[test]
    fn signed_dialect_with_shapes_now_installs() {
        let mut d = signed_dialect_with_protocol_and_shapes();
        d.causal_protocol = None; // shapes-only case
        let bytes = crate::canonical::dialect_canonical_bytes(&d);
        d.signature = Some(CanonicalSigner.sign(&bytes));

        let mut reg = DialectRegistry::new();
        let result = reg.install_with_signer(d, &CanonicalSigner).unwrap();
        assert_eq!(result, R4Result::Valid);
    }

    #[test]
    fn mutating_causal_protocol_invalidates_existing_signature() {
        use crate::protocol::{NodeRef, StepDecl};
        // Sign a dialect, then mutate its causal_protocol without re-signing.
        // The previously-valid signature must no longer verify.
        let original = signed_dialect_with_protocol_and_shapes();
        let bytes = crate::canonical::dialect_canonical_bytes(&original);
        let sig = CanonicalSigner.sign(&bytes);

        let mut tampered = original;
        tampered.signature = Some(sig);
        // Replace the protocol's `greet` step with a different predecessor.
        if let Some(ref mut p) = tampered.causal_protocol {
            p.steps.insert(
                "greet".into(),
                StepDecl {
                    performative: "greet".into(),
                    predecessors: vec![NodeRef::Single("ok".into())],
                    successors: vec![],
                },
            );
        }

        let mut reg = DialectRegistry::new();
        let err = reg
            .install_with_signer(tampered, &CanonicalSigner)
            .unwrap_err();
        assert!(
            matches!(err, DialectInstallError::R4Violation { .. }),
            "expected R4 violation after causal_protocol tamper, got {err:?}"
        );
    }

    #[test]
    fn mutating_shapes_invalidates_existing_signature() {
        use crate::shape::{ShapeRule, TypeConstraint};
        let original = signed_dialect_with_protocol_and_shapes();
        let bytes = crate::canonical::dialect_canonical_bytes(&original);
        let sig = CanonicalSigner.sign(&bytes);

        let mut tampered = original;
        tampered.signature = Some(sig);
        // Add a new rule to the existing shape.
        if let Some(shape) = tampered.shapes.first_mut() {
            shape.rules.push(ShapeRule::Require {
                keyword: String::from("priority"),
                type_constraint: Some(TypeConstraint::Number),
                children: vec![],
            });
        }

        let mut reg = DialectRegistry::new();
        let err = reg
            .install_with_signer(tampered, &CanonicalSigner)
            .unwrap_err();
        assert!(
            matches!(err, DialectInstallError::R4Violation { .. }),
            "expected R4 violation after shapes tamper, got {err:?}"
        );
    }

    // -- "cbcl" extends shorthand resolves to base (PR feedback P2) --

    #[test]
    fn cbcl_shorthand_extends_resolves_to_base_at_install() {
        use crate::protocol::{CausalProtocol, NodeRef, StepDecl};
        let mut reg = DialectRegistry::new();
        // Child dialect extends "cbcl" (shorthand for cbcl-base) and its
        // protocol references the inherited core performative `ok`. Without
        // the alias, install would reject this as undefined.
        let mut steps = alloc::collections::BTreeMap::new();
        steps.insert(
            "begin".into(),
            StepDecl {
                performative: "begin".into(),
                predecessors: vec![],
                successors: vec![NodeRef::Single("ok".into())],
            },
        );
        steps.insert(
            "ok".into(),
            StepDecl {
                performative: "ok".into(),
                predecessors: vec![NodeRef::Single("begin".into())],
                successors: vec![],
            },
        );
        let d = Dialect {
            roles: Vec::new(),
            causal_locality: Default::default(),
            name: String::from("uses-ok"),
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
            protocol: None,
            causal_protocol: Some(CausalProtocol { steps }),
            shapes: Vec::new(),
        };
        reg.install(d)
            .expect("dialect extending cbcl should install");
    }

    // ---- install-time content hashing (SPEC-014 REQ-628) ----

    fn hashless_dialect(name: &str) -> Dialect {
        Dialect {
            roles: Vec::new(),
            causal_locality: Default::default(),
            name: String::from(name),
            extends: vec![String::from("cbcl")],
            author: Some(String::from("@hash-tests")),
            performatives: vec![PerformativeDef {
                role: None,
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
            protocol: None,
            causal_protocol: None,
            shapes: Vec::new(),
        }
    }

    #[test]
    fn install_populates_canonical_hash() {
        let d = hashless_dialect("hashed");
        let expected = crate::canonical::dialect_hash(&d);
        let mut reg = DialectRegistry::new();
        reg.install(d).unwrap();
        let installed = reg.find_by_name("hashed").unwrap();
        let h = installed.hash.as_deref().expect("install must set hash");
        assert_eq!(h, expected);
        let hex = h.strip_prefix("sha256:").expect("sha256: prefix");
        assert_eq!(hex.len(), 64);
        assert!(hex
            .chars()
            .all(|c| c.is_ascii_digit() || ('a'..='f').contains(&c)));
    }

    #[test]
    fn install_hash_is_stable_across_registries() {
        let mut reg1 = DialectRegistry::new();
        let mut reg2 = DialectRegistry::new();
        reg1.install(hashless_dialect("stable")).unwrap();
        reg2.install(hashless_dialect("stable")).unwrap();
        assert_eq!(
            reg1.find_by_name("stable").unwrap().hash,
            reg2.find_by_name("stable").unwrap().hash
        );
    }

    #[test]
    fn install_hash_changes_when_performative_renamed() {
        let mut renamed = hashless_dialect("same-name");
        renamed.performatives[0].name = String::from("salute");
        let mut reg1 = DialectRegistry::new();
        let mut reg2 = DialectRegistry::new();
        reg1.install(hashless_dialect("same-name")).unwrap();
        reg2.install(renamed).unwrap();
        assert_ne!(
            reg1.find_by_name("same-name").unwrap().hash,
            reg2.find_by_name("same-name").unwrap().hash,
            "renaming a performative must change the installed hash"
        );
    }

    #[test]
    fn install_preserves_declared_hash() {
        // A declared :hash claim is kept verbatim so wrappers can compare it
        // against the computed value and reject mismatches.
        let mut d = hashless_dialect("claimed");
        d.hash = Some(String::from("sha256:abcd1234"));
        let mut reg = DialectRegistry::new();
        reg.install(d).unwrap();
        assert_eq!(
            reg.find_by_name("claimed").unwrap().hash.as_deref(),
            Some("sha256:abcd1234")
        );
    }

    #[test]
    fn install_with_signer_populates_canonical_hash() {
        let d = hashless_dialect("signer-hashed");
        let expected = crate::canonical::dialect_hash(&d);
        let mut reg = DialectRegistry::new();
        reg.install_with_signer(d, &MockSigner).unwrap();
        assert_eq!(
            reg.find_by_name("signer-hashed").unwrap().hash.as_deref(),
            Some(expected.as_str())
        );
    }

    #[test]
    fn install_hash_of_signed_dialect_keeps_signature_valid() {
        // Populating `hash` post-R4 must not perturb the signable bytes:
        // sign, install, and confirm both hash presence and R4Result::Valid.
        let mut d = hashless_dialect("signed-and-hashed");
        d.protocol = Some(String::from("ed25519"));
        d.signature = Some(CanonicalSigner.sign(&crate::canonical::dialect_canonical_bytes(&d)));
        let mut reg = DialectRegistry::new();
        let r4 = reg.install_with_signer(d, &CanonicalSigner).unwrap();
        assert_eq!(r4, R4Result::Valid);
        assert!(reg
            .find_by_name("signed-and-hashed")
            .unwrap()
            .hash
            .is_some());
    }
}
