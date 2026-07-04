//! Redacted envelopes (SPEC-015 REQ-700..703, NFR-700..702, CON-700,
//! ADR-702).
//!
//! A *redacted envelope* is the payload-free derivative of a signed
//! message: exactly its content hash, performative name, sender key,
//! recipient set, thread identifier, signature material, and `:caused-by`
//! list — and no payload fields (REQ-700). It widens the *evidence*, not
//! the message: a widened recipient's safety-level verification reads a
//! predecessor's hash, type, endpoints, and signature — never its payload —
//! so the envelope satisfies those needs at zero payload disclosure
//! (ADR-702, NFR-701) and constant size in the payload it redacts
//! (NFR-700).
//!
//! What an envelope *does* reveal is exactly its declared fields: content
//! hash, performative name, sender key, recipient set, thread, signature,
//! `:caused-by` references. That is metadata-only disclosure, never *none*
//! (NFR-702): type, speaker, audience, and causal position remain visible —
//! usually the knowledge-of-choice being delivered, occasionally the leak.
//!
//! Every field a verifier reads is authenticated: the envelope's signature
//! is the R4 v2 attestation signature (ADR-700), computed over the
//! canonical preimage of exactly these header fields, so [`RedactedEnvelope::verify`]
//! needs the envelope's own fields and nothing else (REQ-701). A v1
//! full-bytes signature can never satisfy an envelope path: the envelope
//! form *is* the v2 discipline, and a presented v1 marker is the typed
//! [`AttestError::DisciplineMismatch`] via [`RedactedEnvelope::verify_under_marker`]
//! (fail closed, review finding 6).
//!
//! Grammar (CON-700) — full recognition before any semantic action; an
//! envelope whose hash fails to parse, whose recipient set exceeds the
//! caller's R2-derived bound, or which carries any additional field is
//! rejected, never repaired:
//!
//! ```text
//! envelope    := "(" "envelope" hash perf-name "(" key ")" "(" key* ")"
//!                    thread sig [":caused-by" caused-ref] ")"
//! hash        := "sha256:" hex64
//! thread      := string | symbol
//! key         := "@" [suite ":"] symbol   ; omitted suite → ed25519 (REQ-708)
//! sig         := string                   ; lowercase hex of the v2 signature
//! caused-ref  := hash | "(" hash+ ")" | "begin"
//! ```
//!
//! The completion boundary (REQ-703) lives elsewhere by design: this module
//! makes envelopes *available* to the safety-level lookups of
//! `protocol::verify_causal` (via `store::MessageStore::envelope_in_thread`),
//! while the completion-level occupant fan-in of `projection.rs` (REQ-618)
//! never consults them — full validity includes payload grammaticality, so
//! fan-in deciders still require full messages.

#![forbid(unsafe_code)]

use crate::attest::{
    verify_attestation_v2, AttestError, AttestationHeader, SignatureDiscipline, SigningInput,
    verify_with_discipline,
};
use crate::equivocation::{attestation_header_for, MemberDefect};
use crate::keyid::{KeyId, KeyIdError};
use crate::message::{CausedBy, Message};
use crate::protocol::BEGIN_KEYWORD;
use crate::r4::Signer;
use crate::sexpr::{Atom, SExpr};
use alloc::collections::BTreeSet;
use alloc::string::String;
use alloc::vec::Vec;
use core::fmt;

/// Head symbol of the CON-700 envelope production.
pub const ENVELOPE_HEAD: &str = "envelope";

/// A redacted envelope (REQ-700): the authenticated header of a signed
/// message plus the R4 v2 signature over that header's attestation
/// preimage — and nothing else. Its size is bounded by role-set size and
/// `:caused-by` arity, independent of the redacted payload (NFR-700).
///
/// Field trustworthiness: the header fields are *claims* until
/// [`RedactedEnvelope::verify`] succeeds; after that, every field is
/// exactly what the sender's key vouched for (REQ-701). Store acceptance
/// goes through `ThreadedMessageStore::append_envelope`, which verifies
/// first and places the envelope in the thread its authenticated thread
/// field names (REQ-702).
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct RedactedEnvelope {
    /// The authenticated header: content hash, performative, sender key,
    /// recipient set, thread, `:caused-by` — the exact fields the v2
    /// attestation preimage commits to (ADR-700).
    pub header: AttestationHeader,
    /// R4 v2 signature over `attest::attestation_preimage(&header)`.
    pub signature: Vec<u8>,
}

impl RedactedEnvelope {
    /// Content hash of the message this envelope redacts (`sha256:<hex64>`).
    pub fn content_hash(&self) -> &str {
        &self.header.content_hash
    }

    /// Performative name of the redacted message.
    pub fn performative(&self) -> &str {
        &self.header.performative
    }

    /// Thread identifier — the envelope carries its thread, and store
    /// placement is by this authenticated field (REQ-702).
    pub fn thread(&self) -> &str {
        &self.header.thread
    }

    /// REQ-701: verify the envelope from its own fields alone — the payload
    /// is never an input. Reconstructs the identical attestation preimage a
    /// full-message holder would, and dispatches on the key's signature
    /// suite (typed rejection for unimplemented suites, REQ-708).
    pub fn verify(&self, signer: &dyn Signer) -> Result<(), AttestError> {
        verify_attestation_v2(signer, &self.header.from, &self.header, &self.signature)
    }

    /// Verify under an explicitly presented discipline marker (REQ-701).
    ///
    /// The envelope form *is* the v2 discipline, so a signature declaring
    /// `v1` is the typed [`AttestError::DisciplineMismatch`] — a v1
    /// full-bytes signature never satisfies an envelope path, and no guess
    /// is attempted (fail closed, review finding 6).
    pub fn verify_under_marker(
        &self,
        marker: SignatureDiscipline,
        signer: &dyn Signer,
    ) -> Result<(), AttestError> {
        verify_with_discipline(
            marker,
            &SigningInput::V2Attested {
                key: &self.header.from,
                header: &self.header,
            },
            signer,
            &self.signature,
        )
    }

    /// Serialise to the CON-700 `envelope` production.
    ///
    /// Canonical choices: keys in suite-explicit spelling, the recipient
    /// set in its canonical (suite, name) order, the thread as a string,
    /// the signature as lowercase hex — so serialise ∘ parse is identity
    /// and any holder re-derives identical bytes.
    pub fn to_sexpr(&self) -> SExpr {
        use alloc::vec;
        let h = &self.header;
        let mut items = vec![
            SExpr::Atom(Atom::Symbol(String::from(ENVELOPE_HEAD))),
            SExpr::Atom(Atom::Symbol(h.content_hash.clone())),
            SExpr::Atom(Atom::Symbol(h.performative.clone())),
            SExpr::List(vec![SExpr::Atom(Atom::Symbol(h.from.canonical_spelling()))]),
            SExpr::List(
                h.to
                    .iter()
                    .map(|k| SExpr::Atom(Atom::Symbol(k.canonical_spelling())))
                    .collect(),
            ),
            SExpr::Atom(Atom::Str(h.thread.clone())),
            SExpr::Atom(Atom::Str(hex_encode(&self.signature))),
        ];
        if let Some(cb) = &h.caused_by {
            items.push(SExpr::Atom(Atom::Keyword(String::from("caused-by"))));
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
}

/// REQ-700: redaction — the pure function from a signed message (message +
/// its detached R4 v2 attestation signature) to its redacted envelope.
///
/// The envelope identifies the message it redacts by content hash: the
/// header is `attestation_header_for(message)`, whose `content_hash` is
/// computed from the message's canonical bytes, so redaction and the
/// original message name the same hash by construction (TEST-700).
///
/// Rejects (typed) a message missing any committed header field — an
/// envelope that cannot carry its full authenticated header is never
/// produced partially (LangSec: reject, don't repair).
pub fn redact(message: &Message, signature: Vec<u8>) -> Result<RedactedEnvelope, MemberDefect> {
    Ok(RedactedEnvelope {
        header: attestation_header_for(message)?,
        signature,
    })
}

/// Typed rejection for the CON-700 envelope parser — full recognition
/// before any semantic action; nothing is repaired.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EnvelopeParseError {
    /// The input is not a list headed by the `envelope` symbol.
    NotAnEnvelopeForm,
    /// Wrong number of items: 7 (no `:caused-by`) or 9 (with it).
    WrongArity { found: usize },
    /// The `hash` position is not a well-formed `sha256:<hex64>` symbol.
    MalformedHash,
    /// The `perf-name` position is not a symbol.
    MalformedPerformative,
    /// The sender position is not a list of exactly one key.
    MalformedFromList,
    /// A key does not parse as `@[suite:]name` (REQ-708).
    MalformedKey(KeyIdError),
    /// The recipient position is not a list of keys.
    MalformedToList,
    /// The recipient set exceeds the caller's R2-derived bound (CON-700).
    RecipientBoundExceeded { count: usize, max: usize },
    /// The `thread` position is neither a string nor a symbol.
    MalformedThread,
    /// The `sig` position is not a non-empty lowercase-hex string.
    MalformedSignature,
    /// Item 7 of a 9-item form is not the `:caused-by` keyword — any other
    /// additional field is rejected, never repaired (CON-700).
    UnexpectedField,
    /// The `caused-ref` is not `begin`, a hash, or a non-empty hash list.
    MalformedCausedBy,
}

impl fmt::Display for EnvelopeParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NotAnEnvelopeForm => f.write_str("not an (envelope …) form"),
            Self::WrongArity { found } => {
                write!(f, "envelope must have 7 or 9 items, found {found}")
            }
            Self::MalformedHash => f.write_str("envelope hash is not sha256:<hex64>"),
            Self::MalformedPerformative => f.write_str("envelope performative is not a symbol"),
            Self::MalformedFromList => {
                f.write_str("envelope sender is not a list of exactly one key")
            }
            Self::MalformedKey(e) => write!(f, "envelope key is malformed: {e}"),
            Self::MalformedToList => f.write_str("envelope recipients are not a list of keys"),
            Self::RecipientBoundExceeded { count, max } => {
                write!(f, "envelope recipient set of {count} exceeds the bound {max}")
            }
            Self::MalformedThread => f.write_str("envelope thread is not a string or symbol"),
            Self::MalformedSignature => {
                f.write_str("envelope signature is not a non-empty lowercase-hex string")
            }
            Self::UnexpectedField => {
                f.write_str("envelope carries an additional field (only :caused-by is legal)")
            }
            Self::MalformedCausedBy => {
                f.write_str("envelope :caused-by is not begin, a hash, or a hash list")
            }
        }
    }
}

/// Whether `s` is a CON-700 `hash`: `sha256:` followed by exactly 64
/// lowercase hex digits.
pub fn is_content_hash(s: &str) -> bool {
    match s.strip_prefix("sha256:") {
        Some(hex) => hex.len() == 64 && hex.bytes().all(|b| b.is_ascii_hexdigit() && !b.is_ascii_uppercase()),
        None => false,
    }
}

fn hex_encode(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        out.push(HEX[(b >> 4) as usize] as char);
        out.push(HEX[(b & 0x0f) as usize] as char);
    }
    out
}

/// Strict lowercase-hex decode; anything else is `None` (reject, don't
/// repair — an uppercase or odd-length spelling is not normalised).
fn hex_decode(s: &str) -> Option<Vec<u8>> {
    if s.is_empty() || s.len() % 2 != 0 {
        return None;
    }
    let nibble = |b: u8| -> Option<u8> {
        match b {
            b'0'..=b'9' => Some(b - b'0'),
            b'a'..=b'f' => Some(b - b'a' + 10),
            _ => None,
        }
    };
    let bytes = s.as_bytes();
    let mut out = Vec::with_capacity(bytes.len() / 2);
    for pair in bytes.chunks_exact(2) {
        out.push(nibble(pair[0])? << 4 | nibble(pair[1])?);
    }
    Some(out)
}

fn parse_key(item: &SExpr) -> Result<KeyId, EnvelopeParseError> {
    match item {
        SExpr::Atom(Atom::Symbol(s)) => KeyId::parse(s).map_err(EnvelopeParseError::MalformedKey),
        _ => Err(EnvelopeParseError::MalformedKey(KeyIdError::MissingSigil)),
    }
}

fn parse_caused_ref(item: &SExpr) -> Result<CausedBy, EnvelopeParseError> {
    let as_hash = |s: &str| -> Result<String, EnvelopeParseError> {
        if is_content_hash(s) {
            Ok(String::from(s))
        } else {
            Err(EnvelopeParseError::MalformedCausedBy)
        }
    };
    match item {
        SExpr::Atom(Atom::Symbol(s)) if s == BEGIN_KEYWORD => Ok(CausedBy::Begin),
        SExpr::Atom(Atom::Symbol(s)) | SExpr::Atom(Atom::Str(s)) => {
            Ok(CausedBy::Single(as_hash(s)?))
        }
        SExpr::List(items) if !items.is_empty() => {
            let mut hashes = Vec::with_capacity(items.len());
            for it in items {
                match it {
                    SExpr::Atom(Atom::Symbol(s)) | SExpr::Atom(Atom::Str(s)) => {
                        hashes.push(as_hash(s)?);
                    }
                    _ => return Err(EnvelopeParseError::MalformedCausedBy),
                }
            }
            // Canonical ordering, mirroring the message layer's REQ-202
            // canonicalisation — both verifier classes rebuild identical
            // attestation preimages.
            hashes.sort();
            Ok(CausedBy::Multiple(hashes))
        }
        _ => Err(EnvelopeParseError::MalformedCausedBy),
    }
}

/// Parse the CON-700 `envelope` production — full recognition, reject-never
/// -repair. `max_recipients` is the caller's R2-derived bound on the
/// recipient set (role sets are already bounded by R2; an envelope claiming
/// more recipients than the deployment admits is rejected structurally,
/// before any signature work).
pub fn parse_envelope(
    sexpr: &SExpr,
    max_recipients: usize,
) -> Result<RedactedEnvelope, EnvelopeParseError> {
    let SExpr::List(items) = sexpr else {
        return Err(EnvelopeParseError::NotAnEnvelopeForm);
    };
    if items.first().map(|h| h.is_symbol(ENVELOPE_HEAD)) != Some(true) {
        return Err(EnvelopeParseError::NotAnEnvelopeForm);
    }
    if items.len() != 7 && items.len() != 9 {
        return Err(EnvelopeParseError::WrongArity { found: items.len() });
    }

    // hash
    let content_hash = match &items[1] {
        SExpr::Atom(Atom::Symbol(s)) if is_content_hash(s) => s.clone(),
        _ => return Err(EnvelopeParseError::MalformedHash),
    };
    // perf-name
    let performative = match &items[2] {
        SExpr::Atom(Atom::Symbol(s)) => s.clone(),
        _ => return Err(EnvelopeParseError::MalformedPerformative),
    };
    // "(" key ")" — exactly one sender key
    let from = match &items[3] {
        SExpr::List(ks) if ks.len() == 1 => parse_key(&ks[0])?,
        _ => return Err(EnvelopeParseError::MalformedFromList),
    };
    // "(" key* ")" — recipient set, bounded
    let to: BTreeSet<KeyId> = match &items[4] {
        SExpr::List(ks) => {
            if ks.len() > max_recipients {
                return Err(EnvelopeParseError::RecipientBoundExceeded {
                    count: ks.len(),
                    max: max_recipients,
                });
            }
            let mut set = BTreeSet::new();
            for k in ks {
                set.insert(parse_key(k)?);
            }
            set
        }
        _ => return Err(EnvelopeParseError::MalformedToList),
    };
    // thread := string | symbol
    let thread = match &items[5] {
        SExpr::Atom(Atom::Str(s)) | SExpr::Atom(Atom::Symbol(s)) => s.clone(),
        _ => return Err(EnvelopeParseError::MalformedThread),
    };
    // sig := string (lowercase hex of the v2 signature bytes)
    let signature = match &items[6] {
        SExpr::Atom(Atom::Str(s)) => {
            hex_decode(s).ok_or(EnvelopeParseError::MalformedSignature)?
        }
        _ => return Err(EnvelopeParseError::MalformedSignature),
    };
    // optional [":caused-by" caused-ref]; any other trailing field rejected
    let caused_by = if items.len() == 9 {
        match &items[7] {
            SExpr::Atom(Atom::Keyword(k)) if k == "caused-by" => {}
            _ => return Err(EnvelopeParseError::UnexpectedField),
        }
        Some(parse_caused_ref(&items[8])?)
    } else {
        None
    };

    Ok(RedactedEnvelope {
        header: AttestationHeader {
            content_hash,
            performative,
            from,
            to,
            thread,
            caused_by,
        },
        signature,
    })
}

// ---------------------------------------------------------------------------
// Tests (TEST-700; TEST-701 — envelope half; CON-700 recognition)
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::attest::sign_attestation_v2;
    use crate::equivocation::message_content_hash;
    use crate::message::{Performative, Recipients};
    use alloc::format;
    use alloc::string::ToString;
    use alloc::vec;

    /// Data-dependent test signer (same construction as `attest.rs` tests):
    /// sig = SHA-256(secret ‖ data), so any preimage change kills the
    /// signature and distinct secrets model distinct keys.
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

    fn hash64(c: char) -> String {
        format!("sha256:{}", c.to_string().repeat(64))
    }

    fn sample_message(caused_by: Option<CausedBy>) -> Message {
        let mut to = alloc::collections::BTreeSet::new();
        to.insert("@bob".to_string());
        to.insert("@carol".to_string());
        Message::Simple {
            performative: Performative::Custom("reveal-bid".to_string()),
            recipient: Some(Recipients::Set(to)),
            content: SExpr::Atom(Atom::Str("the secret payload".to_string())),
            params: Vec::new(),
            thread: Some("conv-7".to_string()),
            sender: Some("@alice".to_string()),
            caused_by,
        }
    }

    fn signed_envelope(msg: &Message, signer: &dyn Signer) -> RedactedEnvelope {
        let header = attestation_header_for(msg).unwrap();
        let sig = sign_attestation_v2(signer, &header).unwrap();
        redact(msg, sig).unwrap()
    }

    // ---- TEST-700: redaction round-trip ----

    #[test]
    fn redaction_names_the_same_content_hash() {
        let m = sample_message(Some(CausedBy::Single(hash64('b'))));
        let env = signed_envelope(&m, &ALICE);
        assert_eq!(env.content_hash(), message_content_hash(&m));
        assert_eq!(env.performative(), "reveal-bid");
        assert_eq!(env.thread(), "conv-7");
    }

    #[test]
    fn redaction_is_pure_and_deterministic() {
        let m = sample_message(Some(CausedBy::Begin));
        let sig = vec![1u8, 2, 3];
        assert_eq!(redact(&m, sig.clone()), redact(&m, sig));
    }

    #[test]
    fn redaction_rejects_a_message_missing_committed_fields() {
        let mut m = sample_message(None);
        if let Message::Simple { sender, .. } = &mut m {
            *sender = None;
        }
        assert_eq!(redact(&m, Vec::new()), Err(MemberDefect::MissingSender));
    }

    /// TEST-700 property: over generated messages, the envelope names the
    /// message's own content hash, verifies from its fields alone, and the
    /// CON-700 serialisation round-trips exactly.
    #[test]
    fn test_700_property_roundtrip_over_generated_messages() {
        use proptest::prelude::*;
        use proptest::test_runner::TestRunner;

        let strategy = (
            "[a-z][a-z0-9-]{0,12}",                       // performative
            "[a-z][a-z0-9]{0,8}",                         // sender name
            prop::collection::btree_set("[a-z][a-z0-9]{0,8}", 0..4), // recipients
            "[a-z0-9-]{1,12}",                            // thread
            "[ -~]{0,24}",                                // payload text
            prop_oneof![
                Just(None),
                Just(Some(CausedBy::Begin)),
                prop::collection::vec("[0-9a-f]{64}", 1..4).prop_map(|hs| {
                    let mut hashes: Vec<String> =
                        hs.into_iter().map(|h| format!("sha256:{h}")).collect();
                    hashes.sort();
                    Some(if hashes.len() == 1 {
                        CausedBy::Single(hashes.pop().unwrap())
                    } else {
                        CausedBy::Multiple(hashes)
                    })
                }),
            ],
        );

        let mut runner = TestRunner::default();
        runner
            .run(&strategy, |(perf, sender, to, thread, payload, caused_by)| {
                let recipient = if to.is_empty() {
                    None
                } else {
                    Some(Recipients::Set(
                        to.iter().map(|r| format!("@{r}")).collect(),
                    ))
                };
                let m = Message::Simple {
                    performative: Performative::Custom(perf),
                    recipient,
                    content: SExpr::Atom(Atom::Str(payload)),
                    params: Vec::new(),
                    thread: Some(thread),
                    sender: Some(format!("@{sender}")),
                    caused_by,
                };
                let env = signed_envelope(&m, &ALICE);
                // Same content hash as the message it redacts (REQ-700).
                let expected_hash = message_content_hash(&m);
                prop_assert_eq!(env.content_hash(), expected_hash.as_str());
                // Verifies from its own fields alone (REQ-701).
                prop_assert_eq!(env.verify(&ALICE), Ok(()));
                // CON-700 serialise ∘ parse is identity.
                let reparsed = parse_envelope(&env.to_sexpr(), 8).unwrap();
                prop_assert_eq!(&reparsed, &env);
                Ok(())
            })
            .unwrap();
    }

    // ---- TEST-701 (envelope half): verification without the payload ----

    #[test]
    fn envelope_verifies_without_the_payload() {
        let m = sample_message(Some(CausedBy::Single(hash64('b'))));
        let env = signed_envelope(&m, &ALICE);
        // The payload exists nowhere in the envelope: its serialisation
        // does not contain the message's content (NFR-701).
        let wire = env.to_sexpr().to_string();
        assert!(!wire.contains("the secret payload"), "payload leaked: {wire}");
        assert_eq!(env.verify(&ALICE), Ok(()));
    }

    #[test]
    fn envelope_field_tampering_fails_closed() {
        let m = sample_message(Some(CausedBy::Single(hash64('b'))));
        let env = signed_envelope(&m, &ALICE);

        let mut hash = env.clone();
        hash.header.content_hash = hash64('c');

        let mut perf = env.clone();
        perf.header.performative = "commit-bid".to_string();

        let mut thread = env.clone();
        thread.header.thread = "conv-8".to_string();

        let mut widened = env.clone();
        widened.header.to.insert(key("@mallory"));

        let mut caused = env.clone();
        caused.header.caused_by = Some(CausedBy::Begin);

        for (label, tampered) in [
            ("hash substitution", hash),
            ("performative", perf),
            ("thread relabelling", thread),
            ("recipient widening", widened),
            ("caused-by rewrite", caused),
        ] {
            assert_eq!(
                tampered.verify(&ALICE),
                Err(AttestError::InvalidSignature),
                "{label} must fail closed"
            );
        }
    }

    #[test]
    fn envelope_key_substitution_fails() {
        let m = sample_message(None);
        let mut env = signed_envelope(&m, &ALICE);
        env.header.from = key("@bob");
        // Bob's own verifier and identity: the preimage changed, so the
        // signature is dead — a genuine envelope cannot be re-attributed.
        assert_eq!(env.verify(&BOB), Err(AttestError::InvalidSignature));
    }

    /// REQ-701 fail-closed: a v1 marker on an envelope path is the typed
    /// discipline mismatch; a v1 full-bytes signature never verifies.
    #[test]
    fn v1_signature_never_satisfies_an_envelope() {
        let m = sample_message(None);
        let mut env = signed_envelope(&m, &ALICE);
        assert_eq!(
            env.verify_under_marker(SignatureDiscipline::V1Full, &ALICE),
            Err(AttestError::DisciplineMismatch {
                marker: SignatureDiscipline::V1Full,
                input: SignatureDiscipline::V2Attested,
            })
        );
        // Even smuggled under the v2 marker, a signature over the full
        // canonical message bytes is not a signature over the attestation.
        env.signature = ALICE.sign(&crate::canonical::canonical_encode(&SExpr::from(&m)));
        assert_eq!(
            env.verify_under_marker(SignatureDiscipline::V2Attested, &ALICE),
            Err(AttestError::InvalidSignature)
        );
    }

    #[test]
    fn unknown_suite_is_typed_rejection() {
        let m = sample_message(None);
        let mut env = signed_envelope(&m, &ALICE);
        env.header.from = key("@pq-frodo:alice");
        assert_eq!(
            env.verify(&ALICE),
            Err(AttestError::UnknownSuite("pq-frodo".to_string()))
        );
    }

    // ---- CON-700: grammar recognition ----

    #[test]
    fn serialised_envelope_matches_the_grammar_shape() {
        let m = sample_message(Some(CausedBy::Single(hash64('b'))));
        let env = signed_envelope(&m, &ALICE);
        let SExpr::List(items) = env.to_sexpr() else {
            panic!("envelope serialises to a list");
        };
        assert_eq!(items.len(), 9);
        assert!(items[0].is_symbol("envelope"));
        assert!(matches!(&items[3], SExpr::List(ks) if ks.len() == 1));
        assert!(matches!(&items[5], SExpr::Atom(Atom::Str(_))));
        assert!(matches!(&items[7], SExpr::Atom(Atom::Keyword(k)) if k == "caused-by"));
    }

    #[test]
    fn parse_roundtrips_all_caused_by_forms() {
        for cb in [
            None,
            Some(CausedBy::Begin),
            Some(CausedBy::Single(hash64('b'))),
            Some(CausedBy::Multiple(vec![hash64('b'), hash64('c')])),
        ] {
            let env = signed_envelope(&sample_message(cb), &ALICE);
            assert_eq!(parse_envelope(&env.to_sexpr(), 8), Ok(env));
        }
    }

    #[test]
    fn alias_key_spellings_parse_to_one_identity() {
        // `@bob` and `@ed25519:bob` are one canonical identity (REQ-708):
        // the parsed envelope equals the canonically-spelled one.
        let env = signed_envelope(&sample_message(None), &ALICE);
        let mut sexpr = env.to_sexpr();
        if let SExpr::List(items) = &mut sexpr {
            items[3] = SExpr::List(vec![SExpr::Atom(Atom::Symbol("@alice".to_string()))]);
        }
        let parsed = parse_envelope(&sexpr, 8).unwrap();
        assert_eq!(parsed, env);
        assert_eq!(parsed.verify(&ALICE), Ok(()));
    }

    fn valid_items() -> Vec<SExpr> {
        let env = signed_envelope(&sample_message(Some(CausedBy::Begin)), &ALICE);
        let SExpr::List(items) = env.to_sexpr() else {
            unreachable!()
        };
        items
    }

    #[test]
    fn malformed_hash_is_rejected_never_repaired() {
        for bad in [
            "sha256:abc",                                       // short
            "md5:0000",                                         // wrong algo
            &format!("sha256:{}", "A".repeat(64)),              // uppercase
            &format!("sha256:{}", "g".repeat(64)),              // non-hex
        ] {
            let mut items = valid_items();
            items[1] = SExpr::Atom(Atom::Symbol(bad.to_string()));
            assert_eq!(
                parse_envelope(&SExpr::List(items), 8),
                Err(EnvelopeParseError::MalformedHash),
                "hash '{bad}' must be rejected"
            );
        }
    }

    #[test]
    fn extra_fields_are_rejected() {
        // Trailing junk after the sig (8 items — neither legal arity).
        let mut items = valid_items();
        items.push(SExpr::Atom(Atom::Symbol("junk".to_string())));
        assert_eq!(
            parse_envelope(&SExpr::List(items), 8),
            Err(EnvelopeParseError::WrongArity { found: 10 })
        );
        // A 9-item form whose keyword is not :caused-by.
        let mut items = valid_items();
        items[7] = SExpr::Atom(Atom::Keyword("payload".to_string()));
        assert_eq!(
            parse_envelope(&SExpr::List(items), 8),
            Err(EnvelopeParseError::UnexpectedField)
        );
    }

    #[test]
    fn recipient_bound_is_enforced_structurally() {
        let items = valid_items();
        assert_eq!(
            parse_envelope(&SExpr::List(items), 1),
            Err(EnvelopeParseError::RecipientBoundExceeded { count: 2, max: 1 })
        );
    }

    #[test]
    fn malformed_positions_are_typed_rejections() {
        // Sender list of two keys.
        let mut items = valid_items();
        items[3] = SExpr::List(vec![
            SExpr::Atom(Atom::Symbol("@a".to_string())),
            SExpr::Atom(Atom::Symbol("@b".to_string())),
        ]);
        assert_eq!(
            parse_envelope(&SExpr::List(items), 8),
            Err(EnvelopeParseError::MalformedFromList)
        );
        // A recipient without the sigil.
        let mut items = valid_items();
        items[4] = SExpr::List(vec![SExpr::Atom(Atom::Symbol("bob".to_string()))]);
        assert_eq!(
            parse_envelope(&SExpr::List(items), 8),
            Err(EnvelopeParseError::MalformedKey(KeyIdError::MissingSigil))
        );
        // Thread as a number.
        let mut items = valid_items();
        items[5] = SExpr::Atom(Atom::Num(7));
        assert_eq!(
            parse_envelope(&SExpr::List(items), 8),
            Err(EnvelopeParseError::MalformedThread)
        );
        // Signature: empty, odd length, uppercase.
        for bad in ["", "abc", "AB"] {
            let mut items = valid_items();
            items[6] = SExpr::Atom(Atom::Str(bad.to_string()));
            assert_eq!(
                parse_envelope(&SExpr::List(items), 8),
                Err(EnvelopeParseError::MalformedSignature),
                "sig '{bad}' must be rejected"
            );
        }
        // caused-ref that is not a hash.
        let mut items = valid_items();
        items[8] = SExpr::Atom(Atom::Symbol("h0".to_string()));
        assert_eq!(
            parse_envelope(&SExpr::List(items), 8),
            Err(EnvelopeParseError::MalformedCausedBy)
        );
        // Not an envelope at all.
        assert_eq!(
            parse_envelope(&"(tell @bob \"hi\")".parse::<SExpr>().unwrap(), 8),
            Err(EnvelopeParseError::NotAnEnvelopeForm)
        );
    }

    /// NFR-700: envelope size is constant in the payload it redacts.
    #[test]
    fn envelope_size_is_independent_of_payload_size() {
        let mut small = sample_message(None);
        let mut large = sample_message(None);
        if let Message::Simple { content, .. } = &mut small {
            *content = SExpr::Atom(Atom::Str("x".to_string()));
        }
        if let Message::Simple { content, .. } = &mut large {
            *content = SExpr::Atom(Atom::Str("y".repeat(64 * 1024)));
        }
        let e_small = signed_envelope(&small, &ALICE);
        let e_large = signed_envelope(&large, &ALICE);
        assert_eq!(
            e_small.to_sexpr().byte_size(),
            e_large.to_sexpr().byte_size(),
            "envelope size must not scale with the payload"
        );
    }
}
