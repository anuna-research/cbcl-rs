//! Canonical suite-typed key identity (SPEC-015 REQ-708).
//!
//! Key material carries a signature-suite identifier as part of its
//! identity: the surface spelling is `@[suite:]name` (CON-700), an omitted
//! suite normalises to `ed25519` at parse, and equality is over the
//! (suite, name) pair — never the surface spelling — so `@alice` and
//! `@ed25519:alice` are one identity. Spelling aliases can therefore
//! neither evade the equivocation predicate (REQ-705) nor spuriously fail
//! cast conformance.
//!
//! A suite this implementation does not know is still *representable*
//! (two keys identical in bytes but differing in suite are distinct
//! identities), but every sign/verify dispatch on it is a typed rejection
//! in `attest.rs` — never a skipped check, never a fallback guess
//! (LangSec discipline: reject, don't repair).
//!
//! This module is deliberately independent of the cast machinery in
//! `role.rs`; [`KeyId::parse`] is the pure canonicalisation function cast
//! code can adopt when it moves to suite-typed identity.

#![forbid(unsafe_code)]

use alloc::string::String;
use core::fmt;

/// Name of the v2 default (and unmarked legacy) signature suite (REQ-708).
pub const DEFAULT_SUITE_NAME: &str = "ed25519";

/// A signature suite named in key identity and attestation preimages.
///
/// `Other` keeps unimplemented suites representable so identity comparison
/// works across them; it is *not* a licence to verify — see
/// [`crate::attest::AttestError::UnknownSuite`].
// SIMPLIFY: single implemented suite. Adding one (post-quantum,
// deployment-specific) is a variant here plus a dispatch arm in
// `attest.rs` — a registry entry, not a discipline version bump (REQ-708).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum SignatureSuite {
    /// Ed25519 — the v2 default and the unmarked legacy reading.
    Ed25519,
    /// A syntactically well-formed suite name this implementation does not
    /// implement. Sign/verify dispatch on it yields a typed rejection.
    Other(String),
}

impl SignatureSuite {
    /// Parse a suite name. Anything other than the registered names maps
    /// to `Other` (distinct identity, unverifiable here).
    pub fn parse(s: &str) -> Self {
        if s == DEFAULT_SUITE_NAME {
            SignatureSuite::Ed25519
        } else {
            SignatureSuite::Other(String::from(s))
        }
    }

    /// The canonical suite name as it appears in attestation preimages.
    pub fn as_str(&self) -> &str {
        match self {
            SignatureSuite::Ed25519 => DEFAULT_SUITE_NAME,
            SignatureSuite::Other(s) => s.as_str(),
        }
    }

    /// Whether this implementation can sign/verify under the suite.
    pub fn is_implemented(&self) -> bool {
        matches!(self, SignatureSuite::Ed25519)
    }
}

impl fmt::Display for SignatureSuite {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// Typed rejection for a malformed key spelling (fail closed — a key that
/// does not parse is never coerced into one that does).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum KeyIdError {
    /// The spelling does not start with the `@` sigil.
    MissingSigil,
    /// `@:name` — an explicit-but-empty suite marker.
    EmptySuite,
    /// `@` or `@suite:` — no key name.
    EmptyName,
}

impl fmt::Display for KeyIdError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            KeyIdError::MissingSigil => f.write_str("key identifier must start with '@'"),
            KeyIdError::EmptySuite => f.write_str("key identifier has an empty suite marker"),
            KeyIdError::EmptyName => f.write_str("key identifier has an empty name"),
        }
    }
}

/// Canonical key identity: the (suite, name) pair (REQ-708).
///
/// Constructed via [`KeyId::parse`], which normalises the surface spelling;
/// derived equality/ordering are therefore over canonical identity, and the
/// original spelling is never retained.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct KeyId {
    pub suite: SignatureSuite,
    pub name: String,
}

impl KeyId {
    /// Parse `@[suite:]name` into canonical identity (CON-700).
    ///
    /// An omitted suite normalises to `ed25519` here, at parse — no later
    /// consumer ever sees an "unmarked" key. This is the pure
    /// canonicalisation function cast code can adopt (SPEC-015 review
    /// finding 4).
    pub fn parse(spelling: &str) -> Result<Self, KeyIdError> {
        let rest = spelling.strip_prefix('@').ok_or(KeyIdError::MissingSigil)?;
        let (suite, name) = match rest.split_once(':') {
            Some(("", _)) => return Err(KeyIdError::EmptySuite),
            Some((s, n)) => (SignatureSuite::parse(s), n),
            None => (SignatureSuite::Ed25519, rest),
        };
        if name.is_empty() {
            return Err(KeyIdError::EmptyName);
        }
        Ok(KeyId {
            suite,
            name: String::from(name),
        })
    }

    /// The canonical spelling, suite always explicit: `@<suite>:<name>`.
    ///
    /// Attestation preimages use this form so both verifier classes
    /// (envelope holder, full-message holder) reconstruct identical bytes
    /// regardless of how the sender spelled the key (REQ-701).
    pub fn canonical_spelling(&self) -> String {
        use alloc::format;
        format!("@{}:{}", self.suite.as_str(), self.name)
    }
}

impl fmt::Display for KeyId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "@{}:{}", self.suite.as_str(), self.name)
    }
}

// ---------------------------------------------------------------------------
// Tests (TEST-708 — identity half)
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::collections::BTreeSet;
    use alloc::string::ToString;

    #[test]
    fn omitted_suite_normalises_to_ed25519() {
        let k = KeyId::parse("@alice").unwrap();
        assert_eq!(k.suite, SignatureSuite::Ed25519);
        assert_eq!(k.name, "alice");
    }

    /// TEST-708: `@alice` and `@ed25519:alice` are one identity.
    #[test]
    fn alias_spellings_are_one_identity() {
        let bare = KeyId::parse("@alice").unwrap();
        let explicit = KeyId::parse("@ed25519:alice").unwrap();
        assert_eq!(bare, explicit);

        // …and they dedupe in a canonical set (the equivocation predicate
        // and cast conformance both compare through such sets).
        let mut set = BTreeSet::new();
        set.insert(bare);
        set.insert(explicit);
        assert_eq!(set.len(), 1);
    }

    /// TEST-708: same key bytes under two suites are distinct identities.
    #[test]
    fn same_name_different_suite_is_distinct() {
        let ed = KeyId::parse("@ed25519:alice").unwrap();
        let pq = KeyId::parse("@pq-frodo:alice").unwrap();
        assert_ne!(ed, pq);
        assert_eq!(pq.suite, SignatureSuite::Other("pq-frodo".to_string()));
        assert!(!pq.suite.is_implemented());
    }

    #[test]
    fn canonical_spelling_is_suite_explicit() {
        let k = KeyId::parse("@alice").unwrap();
        assert_eq!(k.canonical_spelling(), "@ed25519:alice");
        assert_eq!(alloc::format!("{k}"), "@ed25519:alice");
    }

    #[test]
    fn malformed_spellings_are_typed_rejections() {
        assert_eq!(KeyId::parse("alice"), Err(KeyIdError::MissingSigil));
        assert_eq!(KeyIdError::MissingSigil, KeyId::parse("").unwrap_err());
        assert_eq!(KeyId::parse("@:alice"), Err(KeyIdError::EmptySuite));
        assert_eq!(KeyId::parse("@"), Err(KeyIdError::EmptyName));
        assert_eq!(KeyId::parse("@ed25519:"), Err(KeyIdError::EmptyName));
    }

    #[test]
    fn name_may_contain_further_colons() {
        // Only the first ':' separates suite from name (did:crdt-style
        // typed identifiers keep their internal structure).
        let k = KeyId::parse("@ed25519:did:crdt:xyz").unwrap();
        assert_eq!(k.name, "did:crdt:xyz");
    }

    #[test]
    fn suite_parse_roundtrip() {
        assert_eq!(SignatureSuite::parse("ed25519"), SignatureSuite::Ed25519);
        assert_eq!(SignatureSuite::parse("ed25519").as_str(), "ed25519");
        let other = SignatureSuite::parse("sphincs+");
        assert_eq!(other.as_str(), "sphincs+");
        assert!(!other.is_implemented());
    }
}
