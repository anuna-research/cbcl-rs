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
    sign_attestation_v3, verify_attestation_v2, verify_attestation_v3, AttestError,
    AttestationHeader, SignatureDiscipline, SigningInput, verify_with_discipline,
};
use crate::equivocation::{attestation_header_for, MemberDefect};
use crate::keyid::{KeyId, KeyIdError, SignatureSuite};
use crate::message::{CausedBy, Message};
use crate::protocol::BEGIN_KEYWORD;
use crate::r4::Signer;
use crate::sexpr::{Atom, SExpr};
use crate::typed_addr::{self, FieldId, Opening};
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
                CausedBy::SingleQuoted(hash) => SExpr::Atom(Atom::Str(hash.clone())),
                CausedBy::Multiple(hashes) => SExpr::List(
                    hashes
                        .iter()
                        .map(|hash| SExpr::Atom(Atom::Symbol(hash.clone())))
                        .collect(),
                ),
                CausedBy::MultipleQuoted(hashes) => SExpr::List(
                    hashes
                        .iter()
                        .map(|hash| SExpr::Atom(Atom::Str(hash.clone())))
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
// SPEC-017 REQ-813 Stage 3: opened envelopes — native field-openings
// ---------------------------------------------------------------------------

/// The SPEC-015 envelope header fields (leaves 0–4), in canonical order.
///
/// Opening exactly these reproduces a redacted envelope's disclosure —
/// performative, from, to, `:caused-by`, thread — while leaf 5 (payload)
/// stays sealed (NFR-701). This is the field set redacted delivery opens.
pub const HEADER_FIELDS: [FieldId; 5] = [
    FieldId::Performative,
    FieldId::From,
    FieldId::To,
    FieldId::CausedBy,
    FieldId::Thread,
];

/// An **opened envelope** (SPEC-017 REQ-813): the typed content address
/// (`root`), a v3 root-signature over it, and a set of authenticated
/// field-openings against that root.
///
/// This is the Stage-3 successor to [`RedactedEnvelope`]. Where a redacted
/// envelope *reconstructs* a header and re-binds it with a v2 attestation,
/// an opened envelope carries each header field as a self-authenticating
/// [`Opening`] of the *same* Merkle root the single v3 signature vouches for
/// ([`crate::attest::sign_attestation_v3`]): the header authentication is
/// now the content address's own read-out, not a separate signed object.
///
/// Redacted delivery opens leaves 0–4 (the [`HEADER_FIELDS`]) and seals
/// leaf 5, so a widened recipient learns the predecessor's type, endpoints,
/// causal position and thread at zero payload disclosure (NFR-701). Opening
/// the payload leaf as well is the full-content path a completion decider
/// needs ([[SPEC-015 REQ-703]]); an opened envelope built for redacted
/// delivery deliberately omits it, preserving the safety/completion boundary.
///
/// Constant size: each opening is a fixed ≤3-sibling path (NFR-700), so the
/// envelope is bounded by the header-field count, independent of the
/// redacted payload.
///
/// Trust: `root`, `suite`, and the opening *values* are claims until
/// [`verify_opened`] succeeds; after that, the v3 signature vouches for the
/// root and every opening authenticates a field value against it. Any party
/// can forward a genuine opened envelope; only the signer can *produce* one
/// (the v3 signature needs the private key), and forging any field fails
/// [`verify_opened`].
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct OpenedEnvelope {
    /// The typed Merkle root — the message's content address
    /// (`sha256:<hex64>`), which the v3 signature commits to.
    pub root: String,
    /// Signature suite named in the v3 attestation preimage (REQ-708): a v3
    /// signature can never be re-read under a different suite.
    pub suite: SignatureSuite,
    /// v3 root-signature over `(cbcl-attest-v3 <suite> <root>)` (REQ-812).
    pub signature: Vec<u8>,
    /// Authenticated field-openings against `root`. For redacted delivery
    /// these are the [`HEADER_FIELDS`]; the payload leaf is absent.
    pub openings: Vec<Opening>,
}

impl OpenedEnvelope {
    /// The content address the v3 signature vouches for (`sha256:<hex64>`).
    pub fn content_hash(&self) -> &str {
        &self.root
    }

    /// The opening for `field`, if this envelope discloses it.
    pub fn opening(&self, field: FieldId) -> Option<&Opening> {
        self.openings.iter().find(|o| o.field == field)
    }

    /// Authenticated performative type, from the Performative opening
    /// (leaf 0). `None` if that leaf is not opened or is malformed.
    pub fn performative(&self) -> Option<&str> {
        match &self.opening(FieldId::Performative)?.value {
            SExpr::Atom(Atom::Symbol(s)) => Some(s.as_str()),
            _ => None,
        }
    }

    /// Authenticated thread identifier, from the Thread opening (leaf 4).
    pub fn thread(&self) -> Option<&str> {
        opt_leaf_str(&self.opening(FieldId::Thread)?.value)
    }

    /// Authenticated sender spelling, from the From opening (leaf 1).
    pub fn from_spelling(&self) -> Option<&str> {
        opt_leaf_str(&self.opening(FieldId::From)?.value)
    }

    /// Authenticated recipient spellings, from the To opening (leaf 2).
    pub fn to_spellings(&self) -> Option<Vec<&str>> {
        match &self.opening(FieldId::To)?.value {
            SExpr::List(items) => items
                .iter()
                .map(|i| match i {
                    SExpr::Atom(Atom::Symbol(s)) => Some(s.as_str()),
                    _ => None,
                })
                .collect(),
            _ => None,
        }
    }
}

/// Read an `opt`-wrapped leaf value (`typed_addr::field_sexpr`'s `Some(v) →
/// (v)`, `None → ()`): `(s)` → `Some(s)`, `()` → `None`.
fn opt_leaf_str(v: &SExpr) -> Option<&str> {
    match v {
        SExpr::List(items) if items.len() == 1 => match &items[0] {
            SExpr::Atom(Atom::Str(s)) | SExpr::Atom(Atom::Symbol(s)) => Some(s.as_str()),
            _ => None,
        },
        _ => None,
    }
}

/// Typed rejection for [`verify_opened`] — fail closed, LangSec discipline
/// (reject, never repair; never a skipped check).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OpenedError {
    /// The v3 root-signature did not verify: a tampered root, a wrong suite,
    /// an unimplemented suite, or a wrong signing key (fail closed).
    Attestation(AttestError),
    /// A field-opening did not authenticate against the signed root — a
    /// forged or corrupted field value, path, or side.
    OpeningFailed { field: FieldId },
    /// A required header field was not disclosed by this envelope.
    MissingField { field: FieldId },
}

impl fmt::Display for OpenedError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Attestation(e) => write!(f, "opened-envelope root-signature invalid: {e}"),
            Self::OpeningFailed { field } => {
                write!(f, "opened-envelope field {field:?} fails to open against the root")
            }
            Self::MissingField { field } => {
                write!(f, "opened-envelope does not disclose field {field:?}")
            }
        }
    }
}

/// Build an opened envelope for `msg` (REQ-813): sign its typed root under
/// the v3 discipline and open exactly `fields` against that root.
///
/// `fields` selects which leaves to disclose — redacted delivery passes
/// [`HEADER_FIELDS`] (payload sealed); a full-content path additionally
/// passes [`FieldId::Payload`]. Only the holder of the signing key can
/// produce one (the v3 signature); any relay can forward the result.
///
/// Suite dispatch is a typed rejection for unimplemented suites (REQ-708),
/// inherited from [`sign_attestation_v3`].
pub fn build_opened(
    msg: &Message,
    fields: &[FieldId],
    suite: &SignatureSuite,
    signer: &dyn Signer,
) -> Result<OpenedEnvelope, AttestError> {
    let root = typed_addr::typed_root(msg);
    let signature = sign_attestation_v3(suite, &root, signer)?;
    let openings = fields.iter().map(|&f| typed_addr::open(msg, f)).collect();
    Ok(OpenedEnvelope {
        root,
        suite: suite.clone(),
        signature,
        openings,
    })
}

/// Verify an opened envelope (REQ-813), in two steps and fail-closed:
///
/// 1. the v3 root-signature via [`verify_attestation_v3`] — this
///    authenticates `root` under the sender's key (`signer` embodies that
///    key's verification, the R4 convention);
/// 2. every field-opening against that now-signed root via
///    [`typed_addr::verify_opening`].
///
/// Order is load-bearing: the signature authenticates the root first, so a
/// passing opening then proves its value under a root the sender vouched
/// for. A relay that only forwards a genuine envelope passes; a forger who
/// edits any field (value, path, or side) fails at step 2, and one who
/// edits the root fails at step 1 — no payload is ever an input (NFR-701).
pub fn verify_opened(env: &OpenedEnvelope, signer: &dyn Signer) -> Result<(), OpenedError> {
    verify_attestation_v3(&env.suite, &env.root, &env.signature, signer)
        .map_err(OpenedError::Attestation)?;
    for op in &env.openings {
        if !typed_addr::verify_opening(&env.root, op.field, &op.value, op) {
            return Err(OpenedError::OpeningFailed { field: op.field });
        }
    }
    Ok(())
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

    // -----------------------------------------------------------------------
    // SPEC-017 REQ-813 Stage 3: opened envelopes (native field-openings)
    // -----------------------------------------------------------------------

    use crate::keyid::SignatureSuite;
    use crate::typed_addr::{self, FieldId};

    fn opened(m: &Message, signer: &dyn Signer) -> OpenedEnvelope {
        build_opened(m, &HEADER_FIELDS, &SignatureSuite::Ed25519, signer).unwrap()
    }

    /// REQ-813: the opened header set verifies — the v3 root-signature plus
    /// every header opening against that signed root — and the disclosed
    /// values read back as the message's authenticated fields.
    #[test]
    fn opened_header_verifies_and_reads_back() {
        let m = sample_message(Some(CausedBy::Single(hash64('b'))));
        let env = opened(&m, &ALICE);
        assert_eq!(verify_opened(&env, &ALICE), Ok(()));
        assert_eq!(env.performative(), Some("reveal-bid"));
        assert_eq!(env.thread(), Some("conv-7"));
        assert_eq!(env.from_spelling(), Some("@alice"));
        assert_eq!(env.content_hash(), message_content_hash(&m));
        let to = env.to_spellings().unwrap();
        assert!(to.contains(&"@bob") && to.contains(&"@carol"));
    }

    /// A relay that is not the signer can forward a genuine opened envelope:
    /// forwarding is a pure copy, and it still verifies under the sender's
    /// key. (Producing one needs the signing key; forwarding does not.)
    #[test]
    fn relay_can_forward_a_genuine_opened_envelope() {
        let m = sample_message(None);
        let env = opened(&m, &ALICE);
        // The relay (BOB) holds no signing key for alice; it merely relays.
        let forwarded = env.clone();
        // Any holder verifies against alice's public verification (ALICE).
        assert_eq!(verify_opened(&forwarded, &ALICE), Ok(()));
    }

    /// Relay-unforgeability (REQ-813): forging any opened field value fails
    /// `verify_opening` against the signed root — the forger cannot mint a
    /// matching opening without re-rooting, and the v3 signature is over the
    /// genuine root.
    #[test]
    fn forging_an_opened_field_fails_verification() {
        let m = sample_message(None);
        let genuine = opened(&m, &ALICE);

        // Forge the performative: swap in a different type's opening value.
        let mut forged = genuine.clone();
        for op in &mut forged.openings {
            if op.field == FieldId::Performative {
                op.value = SExpr::Atom(Atom::Symbol("commit-bid".to_string()));
            }
        }
        assert_eq!(
            verify_opened(&forged, &ALICE),
            Err(OpenedError::OpeningFailed {
                field: FieldId::Performative
            })
        );

        // Forge the To set by lifting a genuine opening from a *widened*
        // message: it reconstructs a different root, so it fails here.
        let mut widened_to = alloc::collections::BTreeSet::new();
        widened_to.insert("@bob".to_string());
        widened_to.insert("@carol".to_string());
        widened_to.insert("@mallory".to_string());
        let widened = Message::Simple {
            performative: Performative::Custom("reveal-bid".to_string()),
            recipient: Some(Recipients::Set(widened_to)),
            content: SExpr::Atom(Atom::Str("the secret payload".to_string())),
            params: Vec::new(),
            thread: Some("conv-7".to_string()),
            sender: Some("@alice".to_string()),
            caused_by: None,
        };
        let mut forged2 = genuine.clone();
        for op in &mut forged2.openings {
            if op.field == FieldId::To {
                *op = typed_addr::open(&widened, FieldId::To);
            }
        }
        assert_eq!(
            verify_opened(&forged2, &ALICE),
            Err(OpenedError::OpeningFailed { field: FieldId::To })
        );
    }

    /// A tampered root fails at the v3 signature (step 1), before any
    /// opening is even considered.
    #[test]
    fn tampered_root_fails_at_the_signature() {
        let m = sample_message(None);
        let mut env = opened(&m, &ALICE);
        env.root = "sha256:0000000000000000000000000000000000000000000000000000000000000000".to_string();
        assert_eq!(
            verify_opened(&env, &ALICE),
            Err(OpenedError::Attestation(AttestError::InvalidSignature))
        );
    }

    /// A different key's verifier cannot validate the v3 signature.
    #[test]
    fn wrong_signer_fails_the_opened_envelope() {
        let m = sample_message(None);
        let env = opened(&m, &ALICE);
        assert_eq!(
            verify_opened(&env, &BOB),
            Err(OpenedError::Attestation(AttestError::InvalidSignature))
        );
    }

    /// NFR-701: the redacted opened envelope carries no payload field — no
    /// opening is the Payload leaf, and no disclosed value carries the
    /// payload bytes. The performative (metadata) stays visible (NFR-702).
    #[test]
    fn opened_header_seals_the_payload() {
        let m = sample_message(None); // content: "the secret payload"
        let env = opened(&m, &ALICE);
        assert!(
            env.opening(FieldId::Payload).is_none(),
            "redacted delivery must not open the payload leaf"
        );
        for op in &env.openings {
            let bytes = crate::canonical::canonical_encode(&op.value);
            let s = core::str::from_utf8(&bytes).unwrap();
            assert!(
                !s.contains("the secret payload"),
                "payload leaked via {:?}",
                op.field
            );
        }
    }

    /// The full-content path opens the Payload leaf too — authenticated
    /// disclosure of the payload itself (the REQ-703 completion input),
    /// not a separate mechanism.
    #[test]
    fn opened_full_content_reveals_the_payload_leaf() {
        let m = sample_message(None);
        let mut fields = HEADER_FIELDS.to_vec();
        fields.push(FieldId::Payload);
        let env = build_opened(&m, &fields, &SignatureSuite::Ed25519, &ALICE).unwrap();
        assert_eq!(verify_opened(&env, &ALICE), Ok(()));
        let payload = env.opening(FieldId::Payload).expect("payload opened");
        assert!(format!("{}", payload.value).contains("the secret payload"));
    }

    /// REQ-708: an unimplemented suite is a typed rejection on build.
    #[test]
    fn opened_unknown_suite_is_typed_rejection() {
        let m = sample_message(None);
        let pq = SignatureSuite::parse("pq-frodo");
        assert_eq!(
            build_opened(&m, &HEADER_FIELDS, &pq, &ALICE),
            Err(AttestError::UnknownSuite("pq-frodo".to_string()))
        );
    }
}
