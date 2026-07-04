//! R4 v2 attestation signing discipline (SPEC-015 REQ-701/REQ-708,
//! ADR-700, CON-700).
//!
//! v2 signatures are computed over the RFC 9804 canonical bytes of a
//! domain-tagged *attestation* committing to the signature suite, the
//! content hash, and the message header:
//!
//! ```text
//! (cbcl-attest-v2 <suite> <hash> <perf-name> <from-key> (<to-key>*)
//!                 <thread> [<caused-ref>])
//! ```
//!
//! The attestation is never transmitted; both verifier classes reconstruct
//! the identical preimage — an envelope holder from the envelope's fields,
//! a full-message holder from the message and its computed hash (REQ-701).
//! Verification therefore never requires the payload.
//!
//! The legacy v1 discipline (sign the full canonical bytes) coexists:
//! messages and envelopes carry an explicit [`SignatureDiscipline`] marker,
//! and [`verify_with_discipline`] *dispatches* on it rather than guessing.
//! A v1 signature can never satisfy an envelope (v2) verification call —
//! the mismatch is the typed [`AttestError::DisciplineMismatch`], fail
//! closed (REQ-701, review finding 6).
//!
//! Canonical encoding is `canonical.rs`'s — this module builds the
//! attestation `SExpr` and defers all byte production to
//! [`canonical_encode`]; there is exactly one canonicalizer.

#![forbid(unsafe_code)]

use crate::canonical::canonical_encode;
use crate::keyid::{KeyId, SignatureSuite};
use crate::message::CausedBy;
use crate::protocol::BEGIN_KEYWORD;
use crate::r4::Signer;
use crate::sexpr::{Atom, SExpr};
use alloc::collections::BTreeSet;
use alloc::string::String;
use alloc::vec::Vec;
use core::fmt;

/// Domain tag heading every v2 attestation preimage (ADR-700). The `-v2`
/// version tag governs the *discipline* (what is signed); the suite field
/// governs the *algorithm* (how); they vary independently.
pub const ATTEST_DOMAIN_TAG: &str = "cbcl-attest-v2";

/// The authenticated header a v2 signature commits to, alongside the
/// content hash (REQ-700/REQ-701).
///
/// These are exactly the fields a redacted-envelope verifier reads; binding
/// the hash alone would leave every one of them forgeable from gossiped
/// (hash, signature) pairs (SPEC-015 review finding 1).
///
/// The suite named in the preimage is `from.suite` — the signing key's
/// suite — so a signature can never be re-interpreted under a different
/// suite (REQ-708) and suite/key consistency holds by construction.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct AttestationHeader {
    /// Content hash of the message being vouched for (`sha256:<hex64>`).
    pub content_hash: String,
    /// Performative name.
    pub performative: String,
    /// Sender key (canonical identity; its suite names the signature suite).
    pub from: KeyId,
    /// Recipient set, canonically ordered by (suite, name).
    pub to: BTreeSet<KeyId>,
    /// Thread identifier.
    pub thread: String,
    /// `:caused-by` list; `None` when the message carries none (the
    /// grammar's optional `[caused-ref]`, CON-700).
    pub caused_by: Option<CausedBy>,
}

/// Build the attestation S-expression (CON-700 `attestation` production).
///
/// Pure; never transmitted. Keys are rendered in canonical suite-explicit
/// spelling so any alias spelling of the same identity reconstructs
/// identical bytes.
pub fn attestation_sexpr(h: &AttestationHeader) -> SExpr {
    use alloc::vec;
    let mut items = vec![
        SExpr::Atom(Atom::Symbol(String::from(ATTEST_DOMAIN_TAG))),
        SExpr::Atom(Atom::Symbol(String::from(h.from.suite.as_str()))),
        SExpr::Atom(Atom::Symbol(h.content_hash.clone())),
        SExpr::Atom(Atom::Symbol(h.performative.clone())),
        SExpr::Atom(Atom::Symbol(h.from.canonical_spelling())),
        SExpr::List(
            h.to
                .iter()
                .map(|k| SExpr::Atom(Atom::Symbol(k.canonical_spelling())))
                .collect(),
        ),
        SExpr::Atom(Atom::Str(h.thread.clone())),
    ];
    if let Some(cb) = &h.caused_by {
        // Mirrors the `:caused-by` value encoding of `From<Message> for
        // SExpr` (message.rs) so both verifier classes agree.
        items.push(match cb {
            CausedBy::Begin => SExpr::Atom(Atom::Symbol(String::from(BEGIN_KEYWORD))),
            CausedBy::Single(hash) => SExpr::Atom(Atom::Symbol(hash.clone())),
            CausedBy::Multiple(hashes) => SExpr::List(
                hashes
                    .iter()
                    .map(|hash| SExpr::Atom(Atom::Symbol(hash.clone())))
                    .collect(),
            ),
        });
    }
    SExpr::List(items)
}

/// The RFC 9804 canonical bytes of the attestation — the sole input to
/// v2 signing and verification (ADR-700).
pub fn attestation_preimage(h: &AttestationHeader) -> Vec<u8> {
    canonical_encode(&attestation_sexpr(h))
}

/// Explicit signing-discipline discriminator carried by messages and
/// envelopes (REQ-701): verification *dispatches* on it, never guesses.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum SignatureDiscipline {
    /// Legacy v1: signature over the full canonical message bytes.
    V1Full,
    /// v2: signature over the attestation preimage (ADR-700).
    V2Attested,
}

impl SignatureDiscipline {
    /// Canonical marker string as carried on the wire.
    pub fn as_str(&self) -> &'static str {
        match self {
            SignatureDiscipline::V1Full => "v1",
            SignatureDiscipline::V2Attested => ATTEST_DOMAIN_TAG,
        }
    }

    /// Parse a marker string; anything unrecognised is a typed rejection
    /// (never a fallback guess).
    pub fn parse(s: &str) -> Result<Self, AttestError> {
        match s {
            "v1" => Ok(SignatureDiscipline::V1Full),
            ATTEST_DOMAIN_TAG => Ok(SignatureDiscipline::V2Attested),
            other => Err(AttestError::UnknownDiscipline(String::from(other))),
        }
    }
}

impl fmt::Display for SignatureDiscipline {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// Typed rejection for the v2 attestation paths — fail closed, never a
/// skipped check (REQ-701/REQ-708, LangSec discipline).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AttestError {
    /// The named suite is not implemented by this verifier (REQ-708:
    /// reject, don't repair — and never skip).
    UnknownSuite(String),
    /// An unrecognised discipline marker string.
    UnknownDiscipline(String),
    /// The signature's declared discipline does not match the discipline
    /// of the verification call — e.g. a v1 signature presented to an
    /// envelope (v2) path (REQ-701, review finding 6).
    DisciplineMismatch {
        /// Discipline the signature declares.
        marker: SignatureDiscipline,
        /// Discipline the verification input requires.
        input: SignatureDiscipline,
    },
    /// The presented key is not the attestation's `from` key.
    KeyMismatch,
    /// Cryptographic verification failed over the reconstructed preimage.
    InvalidSignature,
}

impl fmt::Display for AttestError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AttestError::UnknownSuite(s) => write!(f, "unknown signature suite '{s}'"),
            AttestError::UnknownDiscipline(s) => {
                write!(f, "unknown signature discipline marker '{s}'")
            }
            AttestError::DisciplineMismatch { marker, input } => write!(
                f,
                "signature discipline mismatch: signature declares '{marker}', \
                 verification input requires '{input}'"
            ),
            AttestError::KeyMismatch => f.write_str("key does not match attestation's from key"),
            AttestError::InvalidSignature => f.write_str("signature verification failed"),
        }
    }
}

/// Sign the v2 attestation for `header` (ADR-700).
///
/// `signer` embodies the private key named by `header.from`.
// SIMPLIFY: `Signer` carries no key identity, so caller must pair signer
// and `from` key correctly; a keyed multi-suite signer registry is the
// upgrade path when a second suite lands (REQ-708 registry-entry rule).
pub fn sign_attestation_v2(
    signer: &dyn Signer,
    header: &AttestationHeader,
) -> Result<Vec<u8>, AttestError> {
    match &header.from.suite {
        SignatureSuite::Ed25519 => Ok(signer.sign(&attestation_preimage(header))),
        SignatureSuite::Other(s) => Err(AttestError::UnknownSuite(s.clone())),
    }
}

/// Verify a v2 signature from key + header fields + hash alone — the
/// payload is never an input (REQ-701).
///
/// Order of checks: suite dispatch (typed rejection for unimplemented
/// suites, REQ-708), key identity, then cryptographic verification over
/// the reconstructed preimage.
pub fn verify_attestation_v2(
    signer: &dyn Signer,
    key: &KeyId,
    header: &AttestationHeader,
    sig: &[u8],
) -> Result<(), AttestError> {
    // Suite dispatch first: an attestation (or presented key) naming an
    // unimplemented suite is rejected before any guessy work. An ed25519
    // signature thereby verifies only against an ed25519-naming
    // attestation (TEST-708).
    // SIMPLIFY: one dispatch arm; adding a suite is a `keyid.rs` registry
    // entry plus an arm here, not a discipline version bump (REQ-708).
    if let SignatureSuite::Other(s) = &header.from.suite {
        return Err(AttestError::UnknownSuite(s.clone()));
    }
    if let SignatureSuite::Other(s) = &key.suite {
        return Err(AttestError::UnknownSuite(s.clone()));
    }
    if key != &header.from {
        return Err(AttestError::KeyMismatch);
    }
    if signer.verify(&attestation_preimage(header), sig) {
        Ok(())
    } else {
        Err(AttestError::InvalidSignature)
    }
}

/// What a verification call holds: the discriminated counterpart to
/// [`SignatureDiscipline`].
#[derive(Debug, Clone, Copy)]
pub enum SigningInput<'a> {
    /// Full canonical message bytes (legacy v1 discipline).
    V1Full(&'a [u8]),
    /// Key + authenticated header (v2 discipline; payload-free).
    V2Attested {
        key: &'a KeyId,
        header: &'a AttestationHeader,
    },
}

impl SigningInput<'_> {
    /// The discipline this input requires.
    pub fn discipline(&self) -> SignatureDiscipline {
        match self {
            SigningInput::V1Full(_) => SignatureDiscipline::V1Full,
            SigningInput::V2Attested { .. } => SignatureDiscipline::V2Attested,
        }
    }
}

/// Verify a signature under its declared discipline marker (REQ-701).
///
/// Dispatches, never guesses: the marker must match the input's
/// discipline, otherwise the typed [`AttestError::DisciplineMismatch`] —
/// so a v1 full-bytes signature can never satisfy an envelope (v2)
/// verification call, and vice versa. The v1 arm preserves the legacy
/// semantics bit-for-bit (`Signer::verify` over the full bytes).
pub fn verify_with_discipline(
    marker: SignatureDiscipline,
    input: &SigningInput<'_>,
    signer: &dyn Signer,
    sig: &[u8],
) -> Result<(), AttestError> {
    match (marker, input) {
        (SignatureDiscipline::V1Full, SigningInput::V1Full(bytes)) => {
            if signer.verify(bytes, sig) {
                Ok(())
            } else {
                Err(AttestError::InvalidSignature)
            }
        }
        (SignatureDiscipline::V2Attested, SigningInput::V2Attested { key, header }) => {
            verify_attestation_v2(signer, key, header, sig)
        }
        (marker, input) => Err(AttestError::DisciplineMismatch {
            marker,
            input: input.discipline(),
        }),
    }
}

// ---------------------------------------------------------------------------
// Tests (TEST-701; TEST-708 — suite-dispatch half)
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::string::ToString;
    use alloc::vec::Vec;

    /// Data-dependent test signer: sig = SHA-256(secret ‖ data). Distinct
    /// secrets model distinct keys; any change to the signed bytes changes
    /// the expected signature, which is what TEST-701's tampering cases
    /// need (the constant-signature mocks in `r4.rs` cannot express them).
    struct TestSigner {
        secret: &'static [u8],
    }

    impl Signer for TestSigner {
        fn sign(&self, data: &[u8]) -> Vec<u8> {
            use sha2::{Digest, Sha256};
            let mut h = Sha256::new();
            h.update(self.secret);
            h.update(data);
            h.finalize().to_vec()
        }
        fn verify(&self, data: &[u8], sig: &[u8]) -> bool {
            self.sign(data) == sig
        }
    }

    const ALICE: TestSigner = TestSigner { secret: b"alice" };
    const BOB: TestSigner = TestSigner { secret: b"bob" };

    fn key(s: &str) -> KeyId {
        KeyId::parse(s).unwrap()
    }

    fn header() -> AttestationHeader {
        let mut to = BTreeSet::new();
        to.insert(key("@bob"));
        to.insert(key("@carol"));
        AttestationHeader {
            content_hash: String::from(
                "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
            ),
            performative: String::from("reveal-bid"),
            from: key("@alice"),
            to,
            thread: String::from("conv-7"),
            caused_by: Some(CausedBy::Single(String::from(
                "sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb",
            ))),
        }
    }

    // ---- preimage construction (ADR-700, CON-700) ----

    #[test]
    fn preimage_is_domain_tagged_and_names_the_suite() {
        let bytes = attestation_preimage(&header());
        let s = core::str::from_utf8(&bytes).unwrap();
        // "cbcl-attest-v2" (14 chars) + 'S' tag = 15 octets.
        assert!(s.starts_with("(15:Scbcl-attest-v2"), "got: {s}");
        assert!(s.contains("8:Sed25519"), "suite must be committed: {s}");
    }

    #[test]
    fn preimage_is_deterministic_across_reconstruction() {
        // Both verifier classes rebuild the identical preimage (REQ-701).
        assert_eq!(attestation_preimage(&header()), attestation_preimage(&header()));
    }

    /// TEST-708 adjunct: alias spellings of one identity reconstruct
    /// identical preimages, so canonicalisation cannot split signatures.
    #[test]
    fn alias_key_spellings_reconstruct_identical_preimage() {
        let mut explicit = header();
        explicit.from = key("@ed25519:alice");
        assert_eq!(attestation_preimage(&header()), attestation_preimage(&explicit));
    }

    #[test]
    fn caused_by_forms_encode_distinctly() {
        let mut begin = header();
        begin.caused_by = Some(CausedBy::Begin);
        let mut multi = header();
        multi.caused_by = Some(CausedBy::Multiple(alloc::vec![
            "sha256:b".to_string(),
            "sha256:c".to_string(),
        ]));
        let mut none = header();
        none.caused_by = None;
        let all = [
            attestation_preimage(&header()),
            attestation_preimage(&begin),
            attestation_preimage(&multi),
            attestation_preimage(&none),
        ];
        for i in 0..all.len() {
            for j in (i + 1)..all.len() {
                assert_ne!(all[i], all[j], "caused-by forms {i} and {j} collide");
            }
        }
    }

    // ---- TEST-701: verify from key + header + hash alone ----

    #[test]
    fn verify_succeeds_from_header_alone() {
        let h = header();
        let sig = sign_attestation_v2(&ALICE, &h).unwrap();
        // No payload exists anywhere in this test — header fields and the
        // content hash are the only verification inputs (REQ-701).
        assert_eq!(verify_attestation_v2(&ALICE, &key("@alice"), &h, &sig), Ok(()));
    }

    #[test]
    fn key_substitution_fails() {
        let h = header();
        let sig = sign_attestation_v2(&ALICE, &h).unwrap();
        // Presenting a different key than the attestation names: typed.
        assert_eq!(
            verify_attestation_v2(&ALICE, &key("@bob"), &h, &sig),
            Err(AttestError::KeyMismatch)
        );
        // Rewriting the from-key (and presenting Bob's matching identity
        // and verifier): the preimage changes, so the signature dies.
        let mut forged = h.clone();
        forged.from = key("@bob");
        assert_eq!(
            verify_attestation_v2(&BOB, &key("@bob"), &forged, &sig),
            Err(AttestError::InvalidSignature)
        );
    }

    #[test]
    fn hash_substitution_fails() {
        let h = header();
        let sig = sign_attestation_v2(&ALICE, &h).unwrap();
        let mut tampered = h.clone();
        tampered.content_hash = String::from(
            "sha256:cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc",
        );
        assert_eq!(
            verify_attestation_v2(&ALICE, &key("@alice"), &tampered, &sig),
            Err(AttestError::InvalidSignature)
        );
    }

    #[test]
    fn header_field_tampering_fails() {
        let h = header();
        let sig = sign_attestation_v2(&ALICE, &h).unwrap();

        let mut perf = h.clone();
        perf.performative = String::from("commit-bid");

        let mut to_widened = h.clone();
        to_widened.to.insert(key("@mallory"));

        let mut to_narrowed = h.clone();
        to_narrowed.to.remove(&key("@carol"));

        let mut thread = h.clone();
        thread.thread = String::from("conv-8");

        let mut caused = h.clone();
        caused.caused_by = Some(CausedBy::Single(String::from(
            "sha256:dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd",
        )));

        let mut caused_dropped = h.clone();
        caused_dropped.caused_by = None;

        for (label, tampered) in [
            ("performative", perf),
            ("to-set widened", to_widened),
            ("to-set narrowed", to_narrowed),
            ("thread", thread),
            ("caused-by rewritten", caused),
            ("caused-by dropped", caused_dropped),
        ] {
            assert_eq!(
                verify_attestation_v2(&ALICE, &key("@alice"), &tampered, &sig),
                Err(AttestError::InvalidSignature),
                "tampered field must fail closed: {label}"
            );
        }
    }

    // ---- REQ-701: discipline dispatch, v1 coexistence ----

    #[test]
    fn v1_path_still_verifies_full_bytes() {
        let bytes = b"(4:Stell4:Q@bob3:Qhi)";
        let sig = ALICE.sign(bytes);
        assert_eq!(
            verify_with_discipline(
                SignatureDiscipline::V1Full,
                &SigningInput::V1Full(bytes),
                &ALICE,
                &sig
            ),
            Ok(())
        );
        assert_eq!(
            verify_with_discipline(
                SignatureDiscipline::V1Full,
                &SigningInput::V1Full(b"(other)"),
                &ALICE,
                &sig
            ),
            Err(AttestError::InvalidSignature)
        );
    }

    #[test]
    fn v2_path_dispatches_through_discipline() {
        let h = header();
        let k = key("@alice");
        let sig = sign_attestation_v2(&ALICE, &h).unwrap();
        assert_eq!(
            verify_with_discipline(
                SignatureDiscipline::V2Attested,
                &SigningInput::V2Attested { key: &k, header: &h },
                &ALICE,
                &sig
            ),
            Ok(())
        );
    }

    /// REQ-701 fail-closed: a v1-marked signature presented to an envelope
    /// (v2) verification call is a typed mismatch — even if the bytes
    /// would verify under some interpretation, no guess is attempted.
    #[test]
    fn v1_signature_never_satisfies_v2_call() {
        let h = header();
        let k = key("@alice");
        // A genuine v1 signature over the full canonical message bytes.
        let v1_sig = ALICE.sign(b"(full-message-bytes)");
        assert_eq!(
            verify_with_discipline(
                SignatureDiscipline::V1Full,
                &SigningInput::V2Attested { key: &k, header: &h },
                &ALICE,
                &v1_sig
            ),
            Err(AttestError::DisciplineMismatch {
                marker: SignatureDiscipline::V1Full,
                input: SignatureDiscipline::V2Attested,
            })
        );
    }

    #[test]
    fn v2_signature_never_satisfies_v1_call() {
        let h = header();
        let sig = sign_attestation_v2(&ALICE, &h).unwrap();
        assert_eq!(
            verify_with_discipline(
                SignatureDiscipline::V2Attested,
                &SigningInput::V1Full(b"(full-message-bytes)"),
                &ALICE,
                &sig
            ),
            Err(AttestError::DisciplineMismatch {
                marker: SignatureDiscipline::V2Attested,
                input: SignatureDiscipline::V1Full,
            })
        );
    }

    #[test]
    fn discipline_marker_roundtrip_and_unknown_rejection() {
        for d in [SignatureDiscipline::V1Full, SignatureDiscipline::V2Attested] {
            assert_eq!(SignatureDiscipline::parse(d.as_str()), Ok(d));
        }
        assert_eq!(
            SignatureDiscipline::parse("v3-guess"),
            Err(AttestError::UnknownDiscipline("v3-guess".to_string()))
        );
    }

    // ---- TEST-708: suite dispatch ----

    #[test]
    fn unknown_suite_is_typed_rejection_not_pass_not_panic() {
        let mut h = header();
        h.from = key("@pq-frodo:alice");
        let err = AttestError::UnknownSuite("pq-frodo".to_string());
        assert_eq!(sign_attestation_v2(&ALICE, &h), Err(err.clone()));
        assert_eq!(
            verify_attestation_v2(&ALICE, &key("@pq-frodo:alice"), &h, b"sig"),
            Err(err)
        );
    }

    /// TEST-708: an ed25519 signature verifies only against an attestation
    /// naming `ed25519` — the same header under another suite is a typed
    /// rejection, and its preimage differs anyway (suite is committed).
    #[test]
    fn ed25519_sig_only_verifies_against_ed25519_attestation() {
        let h = header();
        let sig = sign_attestation_v2(&ALICE, &h).unwrap();
        let mut resuited = h.clone();
        resuited.from = key("@pq-frodo:alice");
        assert_ne!(
            attestation_preimage(&h),
            attestation_preimage(&resuited),
            "suite must be part of the committed bytes"
        );
        assert_eq!(
            verify_attestation_v2(&ALICE, &key("@pq-frodo:alice"), &resuited, &sig),
            Err(AttestError::UnknownSuite("pq-frodo".to_string()))
        );
    }
}
