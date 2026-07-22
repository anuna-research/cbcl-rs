//! SPEC-024 `mls-ds/v1` crypto-boundary **PROOF ARTIFACT** (draft gate).
//!
//! This module demonstrates that the SPEC-024 crypto boundary — closed-world
//! recognition (CON-011), the role-verification boundary (CON-003), the
//! `mls-ds/v1` signature-tuple wire language (CON-002), and DS signing under
//! the pinned strict Ed25519 profile (REQ-141) — is *implementable* on the
//! repaired cbcl-rs role layer (`fix/mls-ds-quoted-hash-depth`). The draft
//! proof gate explicitly permits a native-only proof of this shape.
//!
//! It is a PROOF, not production wiring. Read the honest real-vs-stub
//! inventory before trusting any part of it:
//!
//! ## Fully real (exercised by vectors with real Ed25519 keys/signatures)
//! - **REQ-141 strict Ed25519** ([`verify_strict_ed25519`]): explicit
//!   canonical-`S` (`S ∈ [0,L)`) rejection **plus** `ed25519-dalek` v2
//!   `verify_strict` (small-order `R`/`A`, non-canonical `R`, cofactorless).
//!   The `S += L` malleation, low-order `R`, small-order `A`, and
//!   non-canonical point encodings are all rejected on real signatures.
//! - **Canonical signable bytes** ([`canonical_signable_bytes`],
//!   [`sign_tuple`]/[`verify_tuple`]): `canonical_encode` (RFC 9804 typed-atom)
//!   of the domain-tagged tuple — the CON-002 "single definition". All ~16
//!   CON-002 signature/hash tuples are typed ([`DomainTuple`]) and produce
//!   domain-separated preimages.
//! - **key-id / signature recognition** ([`recognize_key_id`],
//!   [`recognize_signature`]): 44-byte `@`+43-base64url keys and 86-char
//!   base64url signatures, decoded and re-encoded byte-identically
//!   (canonical-base64url recognition predicate).
//! - **Closed-world recognizer** ([`recognize_dispatch_verified_outer`]):
//!   request-bundle / response-bundle / reserved-control / NonMls over the two
//!   bundle tags + the 40 performative names, with the outer byte cap and
//!   request/response AST depth caps (8 / 10). No substring/regex scan — it is
//!   a total predicate over the parsed AST.
//! - **`verify_mls_ds_request` / `verify_mls_ds_response`** (CON-003): opener
//!   OPEN-SIG + quoted dialect pin, separately-signed REQUEST-SIG/RESPONSE-SIG,
//!   nested SOURCE-SIG/ADD-AUTH, role projection via the **real** role layer
//!   ([`crate::projection::verify_causal_for_role`]), `h0`/`h1` causality via
//!   the **real** typed Merkle root ([`crate::typed_addr::typed_root`]),
//!   authority-room projection (ordinary row), and the ROOT-WINDOW time bounds.
//! - **Sidecar ref-set / digest / length** ([`verify_sidecars`]): real
//!   base64url-decode → length → SHA-256 digest → descriptor-set matching.
//! - **THREAD-UNIQUE** ([`ThreadRegistry`]): one `(room,client,thread)` binds
//!   one `(h0,h1,kind)`.
//!
//! ## Simplified / stubbed (each marked `STUB:` inline)
//! - **Representative dialect** ([`mls_ds_dialect`]): the two roles + the
//!   `next-record` / `commit-submit` / `commit-add-submit` request paths and
//!   the `record-admitted` / `ds-rejected` / `at-head` response paths, not all
//!   40 performatives. Its `Dialect::hash` is this subset's real canonical
//!   hash — it does **not** reproduce the spec's pinned
//!   `sha256:922ba8bf…` (that is the full 40-performative fence, already
//!   reproduced by the gate-1 proof at HEAD `df16949`). The pin-binding logic
//!   (REQ-628) is exercised with this subset's real hash.
//! - **Authority-room projection**: only the "ordinary submit/read" row is
//!   wired; the six cross-room successor rows are present as a table
//!   ([`authority_rooms`]) but return `state_owner = authority = body-room`.
//! - **TypedRequest / TypedResponse**: real decoded fields for the
//!   representative kinds; the other performatives are `Other { .. }` shells.
//! - **Sidecar bytes**: carried as a base64url string that is really decoded
//!   and hashed; no MLS/ciphertext semantics.
//! - **Parser**: the recognizer parses via cbcl-core's in-crate
//!   [`SExpr`](crate::sexpr::SExpr) `FromStr` (cbcl-core cannot depend on
//!   `cbcl-parser` — that crate depends on cbcl-core). The pinned production
//!   recognizer is `cbcl_parser`; REQ-142 differential-fuzz equivalence of the
//!   two is a separate release gate, not attempted here.
//! - **WASM/NIF/JS parity** (TEST-018 cross-runtime): out of scope — native
//!   Rust only, per the task.
//!
//! Nothing here is wired into the hub, the client, or any effect path; it is
//! reachable only under the non-default `mls-ds-proof` feature.

#![allow(clippy::result_large_err)]

use crate::canonical::{canonical_encode, dialect_hash};
use crate::dialect::{Dialect, PerformativeDef, ResourceBounds};
use crate::message::Message;
use crate::projection::verify_causal_for_role;
use crate::protocol::{CausalProtocol, NodeRef, StepDecl, VerificationResult};
use crate::role::{
    parse_wrapper_cast, AgentKey, Cast, Endpoint, RoleAnnotation, RoleCardinality, RoleDecl,
};
use crate::sexpr::{Atom, SExpr};
use crate::store::{ContentHash, MessageStore, ThreadId, ThreadedMessageStore};
use crate::typed_addr::typed_root;
use alloc::collections::{BTreeMap, BTreeSet};
use alloc::string::{String, ToString};
use alloc::vec;
use alloc::vec::Vec;
use ed25519_dalek::{Signature, Signer as _, SigningKey, VerifyingKey};
use sha2::{Digest, Sha256};

// ===========================================================================
// REQ-141 — Pinned STRICT Ed25519 verification profile
// ===========================================================================

/// The Ed25519 group order `L = 2^252 + 27742317777372353535851937790883648493`
/// in little-endian bytes (RFC 8032). A signature scalar `S` is canonical iff
/// `S ∈ [0, L)`.
const ED25519_L_LE: [u8; 32] = [
    0xed, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58, 0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9, 0xde, 0x14,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x10,
];

/// REQ-141 canonical-scalar predicate: `true` iff the little-endian 32-byte
/// scalar `s` satisfies `s ∈ [0, L)`. This is the exact `S += L` malleation
/// defence the threat-model "verifier-differential fork" row names — a
/// non-canonical `S` that a lax verifier would accept forks the DS log.
///
/// Enforced explicitly in-module so the REQ-141 stance does not silently
/// depend on an `ed25519-dalek` feature flag; the default `ed25519-dalek`
/// build *also* enforces it (`Scalar::from_canonical_bytes`), so this is
/// defence-in-depth that pins the semantics regardless of the dependency's
/// configuration.
pub fn scalar_is_canonical(s_le: &[u8; 32]) -> bool {
    // Compare little-endian from the most-significant byte down.
    for i in (0..32).rev() {
        if s_le[i] < ED25519_L_LE[i] {
            return true;
        }
        if s_le[i] > ED25519_L_LE[i] {
            return false;
        }
    }
    false // s == L is non-canonical (must be strictly < L)
}

/// Verify a 64-byte Ed25519 signature under the REQ-141 pinned strict profile:
///
/// 1. explicit canonical-`S` rejection (`S ∈ [0, L)`) — [`scalar_is_canonical`];
/// 2. `ed25519-dalek` v2 `verify_strict`, which
///    - rejects a public key `A` that fails to decompress;
///    - rejects small-order `R` and small-order `A`;
///    - compares `expected_R == signature.R` on the *compressed bytes*,
///      rejecting a non-canonically re-encoded `R`;
///    - uses the cofactorless equation `[S]B = R + [k]A` (RFC 8032 §5.1.7),
///      not the cofactored batch equation.
///
/// Any conformant verifier agrees with this on every 64-byte signature, so no
/// verifier-differential fork exists (state-invariant 53).
pub fn verify_strict_ed25519(vk_bytes: &[u8; 32], msg: &[u8], sig_bytes: &[u8; 64]) -> bool {
    let mut s_le = [0u8; 32];
    s_le.copy_from_slice(&sig_bytes[32..64]);
    if !scalar_is_canonical(&s_le) {
        return false; // REQ-141: reject non-canonical S (the S += L malleation)
    }
    let Ok(vk) = VerifyingKey::from_bytes(vk_bytes) else {
        return false; // non-decodable / non-canonical public-key point encoding
    };
    let sig = Signature::from_bytes(sig_bytes);
    vk.verify_strict(msg, &sig).is_ok()
}

/// A real Ed25519 keypair for the proof (deterministic from a 32-byte seed —
/// no RNG, so vectors are reproducible). Real curve arithmetic, real signing.
pub struct Ed25519Keypair {
    signing: SigningKey,
}

impl Ed25519Keypair {
    /// Deterministic keypair from a 32-byte seed.
    pub fn from_seed(seed: &[u8; 32]) -> Self {
        Self {
            signing: SigningKey::from_bytes(seed),
        }
    }

    /// The 32-byte Ed25519 public key.
    pub fn public_bytes(&self) -> [u8; 32] {
        self.signing.verifying_key().to_bytes()
    }

    /// The `mls-ds/v1` key-id spelling: `@` + 43-char canonical base64url.
    pub fn key_id(&self) -> String {
        let mut s = String::from("@");
        s.push_str(&b64url_encode(&self.public_bytes()));
        s
    }

    /// Sign `msg` with real Ed25519 (RFC 8032), returning the 64-byte signature.
    pub fn sign(&self, msg: &[u8]) -> [u8; 64] {
        self.signing.sign(msg).to_bytes()
    }
}

// ===========================================================================
// CON-002 — canonical base64url key-id / signature recognition predicates
// ===========================================================================

const B64URL: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_";

fn b64url_val(c: u8) -> Option<u8> {
    match c {
        b'A'..=b'Z' => Some(c - b'A'),
        b'a'..=b'z' => Some(c - b'a' + 26),
        b'0'..=b'9' => Some(c - b'0' + 52),
        b'-' => Some(62),
        b'_' => Some(63),
        _ => None,
    }
}

/// Unpadded canonical base64url encode.
pub fn b64url_encode(bytes: &[u8]) -> String {
    let mut out = String::new();
    let mut i = 0;
    while i + 3 <= bytes.len() {
        let n = (bytes[i] as u32) << 16 | (bytes[i + 1] as u32) << 8 | bytes[i + 2] as u32;
        out.push(B64URL[((n >> 18) & 63) as usize] as char);
        out.push(B64URL[((n >> 12) & 63) as usize] as char);
        out.push(B64URL[((n >> 6) & 63) as usize] as char);
        out.push(B64URL[(n & 63) as usize] as char);
        i += 3;
    }
    match bytes.len() - i {
        1 => {
            let n = (bytes[i] as u32) << 16;
            out.push(B64URL[((n >> 18) & 63) as usize] as char);
            out.push(B64URL[((n >> 12) & 63) as usize] as char);
        }
        2 => {
            let n = (bytes[i] as u32) << 16 | (bytes[i + 1] as u32) << 8;
            out.push(B64URL[((n >> 18) & 63) as usize] as char);
            out.push(B64URL[((n >> 12) & 63) as usize] as char);
            out.push(B64URL[((n >> 6) & 63) as usize] as char);
        }
        _ => {}
    }
    out
}

/// Unpadded base64url decode. Returns `None` on any invalid character or an
/// impossible remainder length. Does **not** by itself reject non-canonical
/// trailing bits — the caller re-encodes and compares for canonicality.
pub fn b64url_decode(s: &str) -> Option<Vec<u8>> {
    let c = s.as_bytes();
    let mut out = Vec::new();
    let mut i = 0;
    while i + 4 <= c.len() {
        let a = b64url_val(c[i])?;
        let b = b64url_val(c[i + 1])?;
        let d = b64url_val(c[i + 2])?;
        let e = b64url_val(c[i + 3])?;
        let n = (a as u32) << 18 | (b as u32) << 12 | (d as u32) << 6 | e as u32;
        out.push((n >> 16) as u8);
        out.push((n >> 8) as u8);
        out.push(n as u8);
        i += 4;
    }
    match c.len() - i {
        0 => {}
        2 => {
            let a = b64url_val(c[i])?;
            let b = b64url_val(c[i + 1])?;
            let n = (a as u32) << 18 | (b as u32) << 12;
            out.push((n >> 16) as u8);
        }
        3 => {
            let a = b64url_val(c[i])?;
            let b = b64url_val(c[i + 1])?;
            let d = b64url_val(c[i + 2])?;
            let n = (a as u32) << 18 | (b as u32) << 12 | (d as u32) << 6;
            out.push((n >> 16) as u8);
            out.push((n >> 8) as u8);
        }
        _ => return None, // a length ≡ 1 (mod 4) is not a valid base64 tail
    }
    Some(out)
}

/// CON-002 key-id recognition: `@` + 43 base64url chars decoding to exactly
/// 32 bytes and re-encoding byte-identically (canonical spelling). Returns the
/// decoded 32-byte Ed25519 public key.
pub fn recognize_key_id(sym: &str) -> Option<[u8; 32]> {
    let body = sym.strip_prefix('@')?;
    if body.len() != 43 {
        return None;
    }
    let bytes = b64url_decode(body)?;
    if bytes.len() != 32 || b64url_encode(&bytes) != body {
        return None; // non-canonical base64url spelling is rejected at recognition
    }
    let mut out = [0u8; 32];
    out.copy_from_slice(&bytes);
    Some(out)
}

/// CON-002 signature recognition: 86 base64url chars decoding to exactly
/// 64 bytes and re-encoding byte-identically.
pub fn recognize_signature(s: &str) -> Option<[u8; 64]> {
    if s.len() != 86 {
        return None;
    }
    let bytes = b64url_decode(s)?;
    if bytes.len() != 64 || b64url_encode(&bytes) != s {
        return None;
    }
    let mut out = [0u8; 64];
    out.copy_from_slice(&bytes);
    Some(out)
}

// ===========================================================================
// CON-002 — canonical signable bytes + tuple sign/verify (single definition)
// ===========================================================================

/// The domain-tagged tuple as an S-expression: `(domain_tag field₀ field₁ …)`.
pub fn tuple_sexpr(domain_tag: &str, fields: &[SExpr]) -> SExpr {
    let mut items = Vec::with_capacity(1 + fields.len());
    items.push(SExpr::Atom(Atom::Symbol(String::from(domain_tag))));
    items.extend_from_slice(fields);
    SExpr::List(items)
}

/// CON-002 "Canonical signable bytes (single definition)": the RFC 9804
/// `canonical_encode` of the domain-tagged tuple. This is the sole
/// signed/hashed preimage for every CON-002 domain tuple.
pub fn canonical_signable_bytes(domain_tag: &str, fields: &[SExpr]) -> Vec<u8> {
    canonical_encode(&tuple_sexpr(domain_tag, fields))
}

/// `sign_tuple(domain_tag, fields) -> sig`: real Ed25519 over the canonical
/// signable bytes.
pub fn sign_tuple(kp: &Ed25519Keypair, domain_tag: &str, fields: &[SExpr]) -> [u8; 64] {
    kp.sign(&canonical_signable_bytes(domain_tag, fields))
}

/// `verify_tuple(...) -> bool`: strict-profile (REQ-141) verify over the
/// canonical signable bytes.
pub fn verify_tuple(vk: &[u8; 32], domain_tag: &str, fields: &[SExpr], sig: &[u8; 64]) -> bool {
    verify_strict_ed25519(vk, &canonical_signable_bytes(domain_tag, fields), sig)
}

/// `SHA-256(canonical_encode(("<tag>", …)))` rendered `sha256:<hex64>` — the
/// content-hash construction used by `record_hash`, `anchor_hash`,
/// `offer_hash`, and every `*-hash-v1` tuple (distinct from `h0`/`h1`, which
/// use the typed Merkle root).
pub fn tuple_content_hash(domain_tag: &str, fields: &[SExpr]) -> String {
    sha256_hex(&canonical_signable_bytes(domain_tag, fields))
}

fn sha256_hex(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    let mut out = String::from("sha256:");
    push_hex(&mut out, &digest);
    out
}

fn push_hex(out: &mut String, bytes: &[u8]) {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    for b in bytes {
        out.push(HEX[(b >> 4) as usize] as char);
        out.push(HEX[(b & 0x0f) as usize] as char);
    }
}

// ---------------------------------------------------------------------------
// The ~16 CON-002 signature/hash domain tuples, as typed structures.
// ---------------------------------------------------------------------------

/// Every CON-002 signature-tuple domain, with its exact domain tag. The field
/// list of each is built from typed inputs (helpers below), so the "canonical
/// signable bytes" of each is fixed by construction and domain-separated by the
/// leading tag.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DomainTuple {
    /// `("mls-ds-open-signature-v1", bindings, dialect_hash, opener-message)`
    Open {
        bindings: SExpr,
        dialect_hash: String,
        opener_message: SExpr,
    },
    /// `("mls-ds-request-signature-v1", bindings, dialect_hash, h0, request,
    ///   read-context-or-none)`
    Request {
        bindings: SExpr,
        dialect_hash: String,
        h0: String,
        request: SExpr,
        read_context: ReadContext,
    },
    /// `("mls-ds-response-signature-v1", bindings, dialect_hash,
    ///   request-content-hash, response-message, read-context-or-none)`
    Response {
        bindings: SExpr,
        dialect_hash: String,
        request_content_hash: String,
        response_message: SExpr,
        read_context: ReadContext,
    },
    /// `("mls-ds-source-signature-v1", source)`
    Source { source: SExpr },
    /// `("mls-add-authorization-v1", room, source-author-key, base-seq,
    ///   base-hash, ciphertext-digest, targets, welcome-digest,
    ///   genesis-anchor-hash)`
    AddAuth {
        room: String,
        source_author_key: String,
        base_seq: i64,
        base_hash: String,
        ciphertext_digest: String,
        targets: Vec<String>,
        welcome_digest: String,
        genesis_anchor_hash: String,
    },
    /// `("mls-ds-record-signature-v1", log-record)`
    Record { log_record: SExpr },
    /// `("mls-room-claim-signature-v1", room-claim-core)`
    Claim { room_claim_core: SExpr },
    /// `("mls-room-claim-ds-signature-v1", room-claim-core, creator-signature)`
    ClaimDs {
        room_claim_core: SExpr,
        creator_signature: String,
    },
    /// `("mls-genesis-signature-v1", room, genesis-blob-ref, creator-key)`
    Genesis {
        room: String,
        genesis_blob_ref: SExpr,
        creator_key: String,
    },
    /// `("mls-ds-successor-predecessor-offer-signature-v1", successor-offer-core)`
    PredecessorOffer { successor_offer_core: SExpr },
    /// `("mls-ds-successor-successor-consent-signature-v1", successor-offer)`
    SuccessorConsent { successor_offer: SExpr },
    /// `("mls-ds-successor-ds-signature-v1", successor-proposal)`
    SuccessorDs { successor_proposal: SExpr },
    /// `("mls-ds-successor-offer-hash-v1", successor-offer)` (hashed, not signed)
    OfferHash { successor_offer: SExpr },
    /// `("mls-ds-successor-hash-v1", successor-value)` (the bridge hash)
    BridgeHash { successor_value: SExpr },
    /// `("mls-ds-closure-package-hash-v1", closure-package)` (hashed)
    ClosurePackageHash { closure_package: SExpr },
}

/// A read request's authenticated session/frame replay tuple, or `none` for a
/// mutation. `("mls-ds-read-context-v1", session-id, frame-id)` when present.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ReadContext {
    /// Mutation roots cover the CBCL atom `none`.
    None,
    /// Read roots cover `(session-id, frame-id)`.
    Read { session_id: String, frame_id: i64 },
}

impl ReadContext {
    fn to_sexpr(&self) -> SExpr {
        match self {
            ReadContext::None => SExpr::Atom(Atom::Symbol(String::from("none"))),
            ReadContext::Read {
                session_id,
                frame_id,
            } => tuple_sexpr(
                "mls-ds-read-context-v1",
                &[
                    SExpr::Atom(Atom::Str(session_id.clone())),
                    SExpr::Atom(Atom::Num(*frame_id)),
                ],
            ),
        }
    }
}

fn qhash(h: &str) -> SExpr {
    SExpr::Atom(Atom::Str(String::from(h)))
}
fn qstr(s: &str) -> SExpr {
    SExpr::Atom(Atom::Str(String::from(s)))
}
fn sym(s: &str) -> SExpr {
    SExpr::Atom(Atom::Symbol(String::from(s)))
}
fn num(n: i64) -> SExpr {
    SExpr::Atom(Atom::Num(n))
}

impl DomainTuple {
    /// The exact CON-002 domain tag.
    pub fn domain_tag(&self) -> &'static str {
        match self {
            DomainTuple::Open { .. } => "mls-ds-open-signature-v1",
            DomainTuple::Request { .. } => "mls-ds-request-signature-v1",
            DomainTuple::Response { .. } => "mls-ds-response-signature-v1",
            DomainTuple::Source { .. } => "mls-ds-source-signature-v1",
            DomainTuple::AddAuth { .. } => "mls-add-authorization-v1",
            DomainTuple::Record { .. } => "mls-ds-record-signature-v1",
            DomainTuple::Claim { .. } => "mls-room-claim-signature-v1",
            DomainTuple::ClaimDs { .. } => "mls-room-claim-ds-signature-v1",
            DomainTuple::Genesis { .. } => "mls-genesis-signature-v1",
            DomainTuple::PredecessorOffer { .. } => {
                "mls-ds-successor-predecessor-offer-signature-v1"
            }
            DomainTuple::SuccessorConsent { .. } => {
                "mls-ds-successor-successor-consent-signature-v1"
            }
            DomainTuple::SuccessorDs { .. } => "mls-ds-successor-ds-signature-v1",
            DomainTuple::OfferHash { .. } => "mls-ds-successor-offer-hash-v1",
            DomainTuple::BridgeHash { .. } => "mls-ds-successor-hash-v1",
            DomainTuple::ClosurePackageHash { .. } => "mls-ds-closure-package-hash-v1",
        }
    }

    /// The tuple's ordered fields (after the domain tag).
    pub fn fields(&self) -> Vec<SExpr> {
        match self {
            DomainTuple::Open {
                bindings,
                dialect_hash,
                opener_message,
            } => vec![bindings.clone(), qhash(dialect_hash), opener_message.clone()],
            DomainTuple::Request {
                bindings,
                dialect_hash,
                h0,
                request,
                read_context,
            } => vec![
                bindings.clone(),
                qhash(dialect_hash),
                qhash(h0),
                request.clone(),
                read_context.to_sexpr(),
            ],
            DomainTuple::Response {
                bindings,
                dialect_hash,
                request_content_hash,
                response_message,
                read_context,
            } => vec![
                bindings.clone(),
                qhash(dialect_hash),
                qhash(request_content_hash),
                response_message.clone(),
                read_context.to_sexpr(),
            ],
            DomainTuple::Source { source } => vec![source.clone()],
            DomainTuple::AddAuth {
                room,
                source_author_key,
                base_seq,
                base_hash,
                ciphertext_digest,
                targets,
                welcome_digest,
                genesis_anchor_hash,
            } => vec![
                qstr(room),
                sym(source_author_key),
                num(*base_seq),
                qhash(base_hash),
                qhash(ciphertext_digest),
                SExpr::List(targets.iter().map(|k| sym(k)).collect()),
                qhash(welcome_digest),
                qhash(genesis_anchor_hash),
            ],
            DomainTuple::Record { log_record } => vec![log_record.clone()],
            DomainTuple::Claim { room_claim_core } => vec![room_claim_core.clone()],
            DomainTuple::ClaimDs {
                room_claim_core,
                creator_signature,
            } => vec![room_claim_core.clone(), qstr(creator_signature)],
            DomainTuple::Genesis {
                room,
                genesis_blob_ref,
                creator_key,
            } => vec![qstr(room), genesis_blob_ref.clone(), sym(creator_key)],
            DomainTuple::PredecessorOffer {
                successor_offer_core,
            } => vec![successor_offer_core.clone()],
            DomainTuple::SuccessorConsent { successor_offer } => vec![successor_offer.clone()],
            DomainTuple::SuccessorDs { successor_proposal } => vec![successor_proposal.clone()],
            DomainTuple::OfferHash { successor_offer } => vec![successor_offer.clone()],
            DomainTuple::BridgeHash { successor_value } => vec![successor_value.clone()],
            DomainTuple::ClosurePackageHash { closure_package } => vec![closure_package.clone()],
        }
    }

    /// Canonical signable bytes of this tuple.
    pub fn signable_bytes(&self) -> Vec<u8> {
        canonical_signable_bytes(self.domain_tag(), &self.fields())
    }

    /// Sign with real Ed25519 under the strict profile.
    pub fn sign(&self, kp: &Ed25519Keypair) -> [u8; 64] {
        kp.sign(&self.signable_bytes())
    }

    /// Verify under the REQ-141 strict profile.
    pub fn verify(&self, vk: &[u8; 32], sig: &[u8; 64]) -> bool {
        verify_strict_ed25519(vk, &self.signable_bytes(), sig)
    }

    /// `sha256:<hex64>` content hash (for the hash-tuple domains).
    pub fn content_hash(&self) -> String {
        sha256_hex(&self.signable_bytes())
    }
}

// ===========================================================================
// CON-011 — closed-world reserved names and outer classification
// ===========================================================================

/// Reserved bundle tags (closed-world).
pub const REQUEST_BUNDLE_TAG: &str = "mls-ds-request-bundle-v1";
pub const RESPONSE_BUNDLE_TAG: &str = "mls-ds-response-bundle-v1";

/// The 15 request performative names (CON-002 `request-name`).
pub const REQUEST_NAMES: [&str; 15] = [
    "next-record",
    "commit-submit",
    "commit-add-submit",
    "proposal-submit",
    "recovery-submit",
    "welcome-get",
    "welcome-ack",
    "genesis-get",
    "genesis-register",
    "successor-candidate-get",
    "successor-offer-submit",
    "successor-offer-get",
    "successor-offer-revoke",
    "successor-get",
    "successor-close",
];

/// The 25 response performative names (CON-002 `response-name`).
pub const RESPONSE_NAMES: [&str; 25] = [
    "commit-record",
    "commit-add-record",
    "proposal-record",
    "recovery-record",
    "record-tombstone",
    "at-head",
    "log-behind",
    "log-truncated",
    "record-admitted",
    "stale-head",
    "welcome-delivery",
    "welcome-missing",
    "welcome-acknowledged",
    "genesis-none",
    "genesis-anchor",
    "genesis-accepted",
    "genesis-exists",
    "successor-none",
    "successor-candidate",
    "successor-offer-stored",
    "successor-offer-delivery",
    "successor-offer-none",
    "successor-offer-revoked",
    "room-closed",
    "ds-rejected",
];

/// Whether `name` is one of the 40 reserved `mls-ds/v1` performative names.
pub fn is_reserved_performative(name: &str) -> bool {
    REQUEST_NAMES.contains(&name) || RESPONSE_NAMES.contains(&name)
}

/// The maximum outer payload (CON-011 / SPEC-012): 1 MiB.
pub const MAX_OUTER_BYTES: usize = 1_048_576;
/// Request-bundle AST depth cap (CON-011).
pub const REQUEST_DEPTH_CAP: usize = 8;
/// Response-bundle AST depth cap (CON-011).
pub const RESPONSE_DEPTH_CAP: usize = 10;

/// Effect-free violation / recognition codes. Where a code corresponds to a
/// CON-002 `error-code` or a spec verdict it is named accordingly; the rest
/// are recognition-boundary codes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Code {
    /// `Violation(malformed)` — any lexical/grammar/bound/body mismatch.
    Malformed,
    /// CON-011 `reserved-mls-control` — a reserved name via the generic route,
    /// a member-authored response bundle, or a request on the response path.
    ReservedMlsControl,
    /// Outer byte cap or AST depth cap exceeded.
    ResourceExcess,
    /// The opener/request/response dialect pin ≠ the installed dialect hash.
    WrongDialectPin,
    /// A portable signature verifies under the wrong key, or the signer is not
    /// the cast occupant / not admitted (covers wrong-DS-binding).
    WrongSigner,
    /// The recipient set ≠ the endpoint-projected singleton (`not-addressee`).
    NotAddressee,
    /// A nested durable source signature does not bind the cast client.
    BadSourceSignature,
    /// The Add authorization tuple is missing or does not verify.
    AddUnauthorized,
    /// A `:caused-by` link or the role-layer R5/R6 relation is violated.
    Causality,
    /// A ROOT-WINDOW predicate is false or its checked arithmetic overflows.
    RootWindow,
    /// THREAD-UNIQUE: a different root reuses a live `(room,client,thread)`.
    ThreadReuse,
    /// A residual `Unknown` became terminal (CON-003 singleton rule).
    MissingEvidence,
    /// Sidecar ref-set / digest / length / sort / purpose mismatch.
    Sidecar,
    /// The authenticated outer room ≠ the projected authority room.
    AuthorityRoom,
}

/// A recognized-but-unverified request bundle.
#[derive(Debug, Clone)]
pub struct RequestBundleAst {
    pub opener: SExpr,
    pub signed_request: SExpr,
    pub sidecars: Vec<SidecarAst>,
    pub bundle_depth: usize,
}

/// A recognized-but-unverified response bundle.
#[derive(Debug, Clone)]
pub struct ResponseBundleAst {
    pub response: SExpr,
    pub sidecars: Vec<SidecarAst>,
    pub bundle_depth: usize,
}

/// A recognized sidecar descriptor. STUB: `b64` carries opaque bytes; only the
/// purpose/digest/length are semantically checked.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SidecarAst {
    pub purpose: String,
    pub digest: String,
    pub length: i64,
    pub b64: String,
}

/// A verified decoded sidecar handle (bytes actually decoded and hashed).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VerifiedSidecarHandle {
    pub purpose: String,
    pub digest: String,
    pub bytes: Vec<u8>,
}

/// The outer classification (CON-011 total AST predicate).
#[derive(Debug, Clone)]
pub enum OuterClass {
    Request(RequestBundleAst),
    Response(ResponseBundleAst),
    /// Well-formed CBCL that is not an `mls-ds/v1` bundle or reserved name.
    NonMls(SExpr),
    Violation(Code),
}

/// AST depth: an atom is depth 1; a list is `1 + max child depth` (empty list
/// is depth 1).
pub fn sexpr_depth(s: &SExpr) -> usize {
    match s {
        SExpr::Atom(_) => 1,
        SExpr::List(items) => 1 + items.iter().map(sexpr_depth).max().unwrap_or(0),
    }
}

fn as_list(s: &SExpr) -> Option<&[SExpr]> {
    match s {
        SExpr::List(v) => Some(v),
        _ => None,
    }
}
fn as_sym(s: &SExpr) -> Option<&str> {
    match s {
        SExpr::Atom(Atom::Symbol(x)) => Some(x),
        _ => None,
    }
}
fn as_str(s: &SExpr) -> Option<&str> {
    match s {
        SExpr::Atom(Atom::Str(x)) => Some(x),
        _ => None,
    }
}
fn as_num(s: &SExpr) -> Option<i64> {
    match s {
        SExpr::Atom(Atom::Num(n)) => Some(*n),
        _ => None,
    }
}
fn head_sym(s: &SExpr) -> Option<&str> {
    as_list(s).and_then(|items| items.first()).and_then(as_sym)
}

/// CON-011 step 2 sidecar parse: each element is
/// `(blob-sidecar-v1 <purpose> <hash> <uint63-len> <cbcl-string>)`.
fn parse_sidecars(s: &SExpr) -> Option<Vec<SidecarAst>> {
    let items = as_list(s)?;
    let mut out = Vec::new();
    for it in items {
        let f = as_list(it)?;
        if f.len() != 5 || as_sym(&f[0])? != "blob-sidecar-v1" {
            return None;
        }
        let purpose = as_sym(&f[1])?.to_string();
        if !matches!(purpose.as_str(), "ciphertext" | "welcome" | "genesis") {
            return None;
        }
        let digest = as_str(&f[2])?.to_string();
        let length = as_num(&f[3])?;
        let b64 = as_str(&f[4])?.to_string();
        out.push(SidecarAst {
            purpose,
            digest,
            length,
            b64,
        });
    }
    Some(out)
}

/// `recognize_dispatch_verified_outer` (CON-011): the shared outer recognizer.
/// Consumes the complete length-delimited payload, then a total AST predicate
/// classifies it — an exact request bundle, exact response bundle, reserved
/// control, or ordinary publication. No byte/substring/regex scan.
pub fn recognize_dispatch_verified_outer(payload_bytes: &[u8]) -> OuterClass {
    // Step 1a — outer byte cap.
    if payload_bytes.len() > MAX_OUTER_BYTES {
        return OuterClass::Violation(Code::ResourceExcess);
    }
    let Ok(text) = core::str::from_utf8(payload_bytes) else {
        // Not canonical CBCL. A real deployment routes opaque bytes through the
        // SPEC-012 generic-publication grammar; here that is stubbed as NonMls.
        return OuterClass::NonMls(SExpr::List(Vec::new()));
    };
    let Ok(sexpr) = text.parse::<SExpr>() else {
        return OuterClass::NonMls(SExpr::List(Vec::new())); // STUB generic grammar
    };
    match head_sym(&sexpr) {
        Some(REQUEST_BUNDLE_TAG) => classify_request(&sexpr),
        Some(RESPONSE_BUNDLE_TAG) => classify_response(&sexpr),
        // A reserved performative routed through the generic publication path
        // (T12-06 / CON-011): never fanned out.
        Some(name) if is_reserved_performative(name) => {
            OuterClass::Violation(Code::ReservedMlsControl)
        }
        // Any other well-formed CBCL is ordinary publication.
        _ => OuterClass::NonMls(sexpr),
    }
}

fn classify_request(sexpr: &SExpr) -> OuterClass {
    // Step 1 — complete request-bundle shape + depth cap ≤ 8.
    let items = match as_list(sexpr) {
        Some(v) if v.len() == 4 => v,
        _ => return OuterClass::Violation(Code::Malformed),
    };
    let depth = sexpr_depth(sexpr);
    if depth > REQUEST_DEPTH_CAP {
        return OuterClass::Violation(Code::ResourceExcess);
    }
    let sidecars = match parse_sidecars(&items[3]) {
        Some(s) => s,
        None => return OuterClass::Violation(Code::Malformed),
    };
    // Opener and signed-request must at least be lists with the right heads.
    if head_sym(&items[1]) != Some("with-roles") || head_sym(&items[2]) != Some("signed") {
        return OuterClass::Violation(Code::Malformed);
    }
    OuterClass::Request(RequestBundleAst {
        opener: items[1].clone(),
        signed_request: items[2].clone(),
        sidecars,
        bundle_depth: depth,
    })
}

fn classify_response(sexpr: &SExpr) -> OuterClass {
    // Step 1 — complete response-bundle shape + depth cap ≤ 10. A response
    // bundle carries NO opener (CON-011 step 4).
    let items = match as_list(sexpr) {
        Some(v) if v.len() == 3 => v,
        _ => return OuterClass::Violation(Code::Malformed),
    };
    let depth = sexpr_depth(sexpr);
    if depth > RESPONSE_DEPTH_CAP {
        return OuterClass::Violation(Code::ResourceExcess);
    }
    let sidecars = match parse_sidecars(&items[2]) {
        Some(s) => s,
        None => return OuterClass::Violation(Code::Malformed),
    };
    if head_sym(&items[1]) != Some("signed") {
        return OuterClass::Violation(Code::Malformed);
    }
    OuterClass::Response(ResponseBundleAst {
        response: items[1].clone(),
        sidecars,
        bundle_depth: depth,
    })
}

// ===========================================================================
// The representative mls-ds/v1 dialect (STUB: subset of 40 performatives)
// ===========================================================================

fn ann(from: &str, to: &str) -> Option<RoleAnnotation> {
    let mut set = BTreeSet::new();
    set.insert(String::from(to));
    Some(RoleAnnotation {
        from: String::from(from),
        to: set,
    })
}

fn perf(name: &str, from: &str, to: &str) -> PerformativeDef {
    PerformativeDef {
        role: ann(from, to),
        name: String::from(name),
        params: Vec::new(),
        // STUB: the real dialect expands `:enc mls` etc.; verification only
        // reads the role annotation and the causal protocol, so a placeholder
        // template suffices and keeps this subset's canonical hash stable.
        template: sym("mls-ds-body"),
    }
}

fn step(name: &str, preds: &[NodeRef], succs: &[NodeRef]) -> (String, StepDecl) {
    (
        String::from(name),
        StepDecl {
            performative: String::from(name),
            predecessors: preds.to_vec(),
            successors: succs.to_vec(),
        },
    )
}

fn single(n: &str) -> NodeRef {
    NodeRef::Single(String::from(n))
}
fn any(ns: &[&str]) -> NodeRef {
    NodeRef::Any(ns.iter().map(|s| String::from(*s)).collect())
}

/// The representative `mls-ds/v1` dialect: the two roles plus the
/// `next-record` / `commit-submit` / `commit-add-submit` request paths and the
/// `record-admitted` / `ds-rejected` / `at-head` response paths. Its
/// `Dialect::hash` is this subset's real canonical hash (populated as
/// `DialectRegistry::install` would). STUB: not the full 40-performative fence.
pub fn mls_ds_dialect() -> Dialect {
    let roles = vec![
        RoleDecl {
            name: String::from("client"),
            cardinality: RoleCardinality::Singleton,
        },
        RoleDecl {
            name: String::from("ds"),
            cardinality: RoleCardinality::Singleton,
        },
    ];
    let performatives = vec![
        perf("next-record", "client", "ds"),
        perf("commit-submit", "client", "ds"),
        perf("commit-add-submit", "client", "ds"),
        perf("record-admitted", "ds", "client"),
        perf("ds-rejected", "ds", "client"),
        perf("at-head", "ds", "client"),
        perf("commit-record", "ds", "client"),
    ];
    let submits = ["commit-submit", "commit-add-submit"];
    let steps: BTreeMap<String, StepDecl> = [
        step(
            "begin",
            &[],
            &[any(&["next-record", "commit-submit", "commit-add-submit"])],
        ),
        step(
            "next-record",
            &[single("begin")],
            &[any(&["commit-record", "at-head", "ds-rejected"])],
        ),
        step(
            "commit-submit",
            &[single("begin")],
            &[any(&["record-admitted", "ds-rejected"])],
        ),
        step(
            "commit-add-submit",
            &[single("begin")],
            &[any(&["record-admitted", "ds-rejected"])],
        ),
        step("record-admitted", &[any(&submits)], &[]),
        step("at-head", &[single("next-record")], &[]),
        step(
            "ds-rejected",
            &[any(&["next-record", "commit-submit", "commit-add-submit"])],
            &[],
        ),
        step("commit-record", &[single("next-record")], &[]),
    ]
    .into_iter()
    .collect();

    let mut d = Dialect {
        roles,
        causal_locality: Default::default(),
        name: String::from("mls-ds/v1"),
        extends: vec![String::from("cbcl")],
        author: Some(String::from("@cbcl-chat")),
        performatives,
        resources: ResourceBounds {
            max_depth: 9,
            max_expansion_size: 8192,
            verification_time_ms: 10,
        },
        examples: Vec::new(),
        signature: None,
        hash: None,
        protocol: None,
        causal_protocol: Some(CausalProtocol { steps }),
        shapes: Vec::new(),
    };
    d.hash = Some(dialect_hash(&d));
    d
}

/// The `bindings` object `((client @c) (ds @d))` used verbatim in the OPEN/
/// REQUEST/RESPONSE signature tuples.
pub fn bindings_sexpr(client_key: &str, ds_key: &str) -> SExpr {
    SExpr::List(vec![
        SExpr::List(vec![sym("client"), sym(client_key)]),
        SExpr::List(vec![sym("ds"), sym(ds_key)]),
    ])
}

// ===========================================================================
// CON-003 — VerifiedThreadContext, verdicts, typed messages
// ===========================================================================

/// The authenticated outer-frame context an ingress supplies (from SPEC-012).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EnvelopeContext {
    pub session_id: String,
    pub frame_id: i64,
    /// The authenticated room the outer frame carries (`outer_room`).
    pub outer_room: String,
}

/// CON-003 `VerifiedThreadContext`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VerifiedThreadContext {
    pub bindings: SExpr,
    pub dialect_hash: String,
    pub canonical_signed_opener: Vec<u8>,
    pub opener_message_hash: String, // h0
    pub canonical_signed_request: Vec<u8>,
    /// The inner request descriptor SExpr, retained so response projection can
    /// re-store the request at `h1` and revalidate the cast/request chain
    /// (CON-003: "revalidates its cast/opener/request chain").
    pub request_descriptor: SExpr,
    pub request_message_hash: String, // h1
    pub thread_id: String,
    pub request_kind: String,
    pub outer_room: String,
    pub authority_room: String,
    pub state_owner_room: String,
    pub request_frame_context: ReadContext,
    pub expires_at: i64,
    /// The client/DS 32-byte keys, retained so response verification revalidates
    /// the same cast without re-deriving cross-room authority.
    pub client_key: [u8; 32],
    pub ds_key: [u8; 32],
    pub client_key_id: String,
    pub ds_key_id: String,
}

/// Decoded typed request (CON-002 body). Representative kinds carry real
/// fields; others are `Other` shells (STUB).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypedRequest {
    NextRecord {
        room: String,
        cursor_seq: i64,
        cursor_hash: String,
        wait_ms: i64,
    },
    CommitSubmit {
        room: String,
        base_seq: i64,
        base_hash: String,
        ciphertext: BlobRef,
    },
    CommitAddSubmit {
        room: String,
        base_seq: i64,
        base_hash: String,
        ciphertext: BlobRef,
        welcome: BlobRef,
        targets: Vec<String>,
    },
    /// STUB: a recognized request kind not decoded in this proof.
    Other {
        kind: String,
    },
}

/// Decoded typed response.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypedResponse {
    RecordAdmitted {
        room: String,
        seq: i64,
        record_hash: String,
        source_hash: String,
    },
    DsRejected {
        room: String,
        error_code: String,
    },
    AtHead {
        room: String,
        head_seq: i64,
        head_hash: String,
        floor_seq: i64,
        floor_prev_hash: String,
    },
    /// STUB: a recognized response kind not decoded in this proof.
    Other {
        kind: String,
    },
}

/// A `(blob-ref-v1 <purpose> <hash> <len>)` descriptor.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BlobRef {
    pub purpose: String,
    pub digest: String,
    pub length: i64,
}

/// `verify_mls_ds_request` verdict (CON-003).
#[derive(Debug, Clone)]
pub enum RequestVerdict {
    Valid(TypedRequest, ContentHash, VerifiedThreadContext),
    Unknown(BTreeSet<ContentHash>),
    Violation(Code),
}

/// `verify_mls_ds_response` verdict (CON-003).
#[derive(Debug, Clone)]
pub enum ResponseVerdict {
    Valid(TypedResponse, ContentHash),
    Unknown(BTreeSet<ContentHash>),
    Violation(Code),
}

// ---------------------------------------------------------------------------
// ROOT-WINDOW (CON-002)
// ---------------------------------------------------------------------------

/// Read-kind duration: 60 s.
const READ_DURATION_MS: i64 = 60_000;
/// Mutation-kind duration: 24 h.
const MUTATION_DURATION_MS: i64 = 86_400_000;
/// Admission clock-skew policy: 300 s.
const SKEW_MS: i64 = 300_000;

fn is_read_kind(kind: &str) -> bool {
    matches!(
        kind,
        "next-record"
            | "welcome-get"
            | "genesis-get"
            | "successor-candidate-get"
            | "successor-offer-get"
            | "successor-get"
    )
}

fn duration_ms(kind: &str) -> i64 {
    if is_read_kind(kind) {
        READ_DURATION_MS
    } else {
        MUTATION_DURATION_MS
    }
}

/// CON-002 `root_window_valid(kind, issued_at, expires_at, trusted_now)` under
/// checked `uint63` arithmetic. Overflow or a false predicate is terminal.
pub fn root_window_valid(kind: &str, issued_at: i64, expires_at: i64, trusted_now: i64) -> bool {
    if issued_at < 0 || expires_at < 0 || trusted_now < 0 {
        return false;
    }
    let Some(expected_expiry) = issued_at.checked_add(duration_ms(kind)) else {
        return false;
    };
    if expires_at != expected_expiry {
        return false;
    }
    let Some(issue_ceiling) = trusted_now.checked_add(SKEW_MS) else {
        return false;
    };
    if issued_at > issue_ceiling {
        return false;
    }
    let Some(expiry_ceiling) = expires_at.checked_add(SKEW_MS) else {
        return false;
    };
    trusted_now <= expiry_ceiling
}

// ---------------------------------------------------------------------------
// Authority-room projection table (CON-003)
// ---------------------------------------------------------------------------

/// The (authority_room, state_owner_room) projection for a request kind, given
/// the decoded body room. STUB: only the ordinary submit/read row is wired;
/// the six cross-room successor rows return `(body, body)` and are marked as a
/// follow-up. `outer_room` MUST equal `authority_room` (checked by the caller).
pub fn authority_rooms(kind: &str, body_room: &str) -> (String, String) {
    match kind {
        // Ordinary submit/read/Welcome/genesis: authority = state-owner = body.
        _ => (String::from(body_room), String::from(body_room)),
    }
}

// ===========================================================================
// CON-003 — verify_mls_ds_request
// ===========================================================================

/// Verify a recognized request bundle (CON-003 / CON-011 step 3).
///
/// `dialect` stands for the installed dialect (its canonical bytes ≡
/// `dialect_bytes`, its `hash` ≡ `expected_dialect_hash`). Real keys/signatures
/// throughout; the role projection is the real [`verify_causal_for_role`].
#[allow(clippy::too_many_arguments)]
pub fn verify_mls_ds_request(
    dialect: &Dialect,
    expected_dialect_hash: &str,
    expected_ds_key: &[u8; 32],
    admitted_client_key: &[u8; 32],
    verified_outer_signer: &[u8; 32],
    candidate_envelope_context: &EnvelopeContext,
    admission_wall_time_ms: i64,
    bundle: &RequestBundleAst,
) -> RequestVerdict {
    // --- Opener (inert `with-roles`): cast, dialect pin, OPEN-SIG ---
    let opener_items = match as_list(&bundle.opener) {
        Some(v) => v,
        None => return RequestVerdict::Violation(Code::Malformed),
    };
    // (with-roles <bindings> :dialect <hash> <signed-opener>)
    if opener_items.len() != 5 {
        return RequestVerdict::Violation(Code::Malformed);
    }
    let cast = match parse_wrapper_cast(&opener_items[1..4], &dialect.roles) {
        Ok(c) => c,
        Err(_) => return RequestVerdict::Violation(Code::Malformed),
    };
    // Dialect pin must equal the installed hash (REQ-628 / CON-003).
    match cast.dialect_pin.as_deref() {
        Some(pin) if pin == expected_dialect_hash => {}
        _ => return RequestVerdict::Violation(Code::WrongDialectPin),
    }
    let signed_opener = &opener_items[4];
    let (opener_signer_id, opener_sig, opener_message_sexpr) = match parse_signed(signed_opener) {
        Some(x) => x,
        None => return RequestVerdict::Violation(Code::Malformed),
    };

    // Cast occupants (decoded 32-byte keys).
    let client_key_id = match cast.singleton.get("client") {
        Some(k) => k.0.clone(),
        None => return RequestVerdict::Violation(Code::Malformed),
    };
    let ds_key_id = match cast.singleton.get("ds") {
        Some(k) => k.0.clone(),
        None => return RequestVerdict::Violation(Code::Malformed),
    };
    let (client_key, ds_key) = match (recognize_key_id(&client_key_id), recognize_key_id(&ds_key_id))
    {
        (Some(c), Some(d)) => (c, d),
        _ => return RequestVerdict::Violation(Code::Malformed),
    };
    // Bind the cast to the authenticated principals (CON-003): the ds occupant
    // is the pinned DS key; the client occupant is the admitted, outer-verified
    // signer.
    if &ds_key != expected_ds_key {
        return RequestVerdict::Violation(Code::WrongSigner);
    }
    if &client_key != admitted_client_key || &client_key != verified_outer_signer {
        return RequestVerdict::Violation(Code::WrongSigner);
    }
    // The opener's immediate signer is the client.
    if opener_signer_id != client_key_id {
        return RequestVerdict::Violation(Code::WrongSigner);
    }

    // Opener-message shape: (mls-ds-open-v1 <ds-recipient> (open-v1 <c> <d>) :thread t :caused-by begin)
    let bindings = bindings_sexpr(&client_key_id, &ds_key_id);
    if let Err(code) = check_opener_message(&opener_message_sexpr, &client_key_id, &ds_key_id) {
        return RequestVerdict::Violation(code);
    }
    // OPEN-SIG under the client key.
    let open_tuple = DomainTuple::Open {
        bindings: bindings.clone(),
        dialect_hash: expected_dialect_hash.to_string(),
        opener_message: opener_message_sexpr.clone(),
    };
    if !verify_tuple(
        &client_key,
        open_tuple.domain_tag(),
        &open_tuple.fields(),
        &opener_sig,
    ) {
        return RequestVerdict::Violation(Code::WrongSigner);
    }
    // h0 = typed Merkle root of the opener-message (NOT a flat/text hash).
    let opener_msg = match parse_message(&opener_message_sexpr) {
        Some(m) => m,
        None => return RequestVerdict::Violation(Code::Malformed),
    };
    let h0 = typed_root(&opener_msg);
    let thread_id = match opener_msg.thread() {
        Some(t) => t.to_string(),
        None => return RequestVerdict::Violation(Code::Malformed),
    };

    // --- Separately-signed request: REQUEST-SIG, recipient, causality ---
    let (req_signer_id, req_sig, request_sexpr) = match parse_signed(&bundle.signed_request) {
        Some(x) => x,
        None => return RequestVerdict::Violation(Code::Malformed),
    };
    if req_signer_id != client_key_id {
        return RequestVerdict::Violation(Code::WrongSigner);
    }
    let req = match decode_request_head(&request_sexpr) {
        Ok(r) => r,
        Err(code) => return RequestVerdict::Violation(code),
    };
    // Recipient must be the DS (endpoint-projected singleton).
    if req.recipient_id != ds_key_id {
        return RequestVerdict::Violation(Code::NotAddressee);
    }
    // Thread continuity + causality: request.:thread = opener thread, and
    // request.:caused-by = h0.
    if req.thread_id != thread_id {
        return RequestVerdict::Violation(Code::Malformed);
    }
    if req.caused_by != h0 {
        return RequestVerdict::Violation(Code::Causality);
    }
    // Read/mutation read-context: reads bind the outer (session, frame); a
    // mutation binds `none`.
    let read_context = if is_read_kind(&req.kind) {
        ReadContext::Read {
            session_id: candidate_envelope_context.session_id.clone(),
            frame_id: candidate_envelope_context.frame_id,
        }
    } else {
        ReadContext::None
    };
    // REQUEST-SIG under the client key.
    let request_tuple = DomainTuple::Request {
        bindings: bindings.clone(),
        dialect_hash: expected_dialect_hash.to_string(),
        h0: h0.clone(),
        request: request_sexpr.clone(),
        read_context: read_context.clone(),
    };
    if !verify_tuple(
        &client_key,
        request_tuple.domain_tag(),
        &request_tuple.fields(),
        &req_sig,
    ) {
        return RequestVerdict::Violation(Code::WrongSigner);
    }

    // --- ROOT-WINDOW ---
    if !root_window_valid(
        &req.kind,
        req.issued_at,
        req.expires_at,
        admission_wall_time_ms,
    ) {
        return RequestVerdict::Violation(Code::RootWindow);
    }

    // --- Decode the typed body + nested source/add signatures + sidecars ---
    let (typed, body_room, blob_refs) =
        match decode_request_body(&req, &request_sexpr, &client_key) {
            Ok(x) => x,
            Err(code) => return RequestVerdict::Violation(code),
        };

    // Sidecars: ref-set / digest / length (real).
    if let Err(code) = verify_sidecars(&blob_refs, &bundle.sidecars) {
        return RequestVerdict::Violation(code);
    }

    // --- Authority-room projection + outer==authority ---
    let (authority_room, state_owner_room) = authority_rooms(&req.kind, &body_room);
    if candidate_envelope_context.outer_room != authority_room {
        return RequestVerdict::Violation(Code::AuthorityRoom);
    }

    // --- Role projection via the REAL role layer ---
    // The request is a first step caused by the opener root h0; R5 rewrites the
    // root reference to `begin`, so an empty store suffices for the request.
    let store = ThreadedMessageStore::new();
    let tid = ThreadId(thread_id.clone());
    let root = ContentHash(h0.clone());
    let signed_req_msg = match parse_message(&bundle.signed_request) {
        Some(m) => m,
        None => return RequestVerdict::Violation(Code::Malformed),
    };
    let ds_endpoint = Endpoint {
        role: String::from("ds"),
        occupant: None,
    };
    match verify_causal_for_role(
        &signed_req_msg,
        &ds_endpoint,
        dialect,
        &cast,
        &store,
        &tid,
        &root,
    ) {
        VerificationResult::Valid => {}
        VerificationResult::Unknown => {
            // A v1 protocol is a singleton transaction: a residual Unknown on
            // the request is terminal missing-evidence (CON-003).
            return RequestVerdict::Violation(Code::MissingEvidence);
        }
        VerificationResult::Violation(_) => return RequestVerdict::Violation(Code::Causality),
    }

    // h1 = typed Merkle root of the request.
    let request_msg = match parse_message(&request_sexpr) {
        Some(m) => m,
        None => return RequestVerdict::Violation(Code::Malformed),
    };
    let h1 = typed_root(&request_msg);

    let vtc = VerifiedThreadContext {
        bindings,
        dialect_hash: expected_dialect_hash.to_string(),
        canonical_signed_opener: canonical_encode(signed_opener),
        opener_message_hash: h0,
        canonical_signed_request: canonical_encode(&bundle.signed_request),
        request_descriptor: request_sexpr.clone(),
        request_message_hash: h1.clone(),
        thread_id,
        request_kind: req.kind.clone(),
        outer_room: candidate_envelope_context.outer_room.clone(),
        authority_room,
        state_owner_room,
        request_frame_context: read_context,
        expires_at: req.expires_at,
        client_key,
        ds_key,
        client_key_id,
        ds_key_id,
    };
    RequestVerdict::Valid(typed, ContentHash(h1), vtc)
}

// ===========================================================================
// CON-003 — verify_mls_ds_response
// ===========================================================================

/// Verify a recognized response bundle against a persisted
/// `VerifiedThreadContext` (CON-003 / CON-011 step 4). A response bundle
/// carries no opener; it projects only after the retained request.
pub fn verify_mls_ds_response(
    dialect: &Dialect,
    expected_dialect_hash: &str,
    expected_ds_key: &[u8; 32],
    verified_outer_signer: &[u8; 32],
    candidate_envelope_context: &EnvelopeContext,
    vtc: &VerifiedThreadContext,
    bundle: &ResponseBundleAst,
) -> ResponseVerdict {
    // The response is DS-signed: (signed <ds> <sig> <response-message>).
    let (resp_signer_id, resp_sig, response_message_sexpr) = match parse_signed(&bundle.response) {
        Some(x) => x,
        None => return ResponseVerdict::Violation(Code::Malformed),
    };
    // Member-signed response (T12-03) or wrong DS binding: reject.
    if resp_signer_id != vtc.ds_key_id {
        return ResponseVerdict::Violation(Code::WrongSigner);
    }
    // The outer frame signer on the response path must also be the DS.
    if verified_outer_signer != expected_ds_key || &vtc.ds_key != expected_ds_key {
        return ResponseVerdict::Violation(Code::WrongSigner);
    }
    let resp = match decode_response_head(&response_message_sexpr) {
        Ok(r) => r,
        Err(code) => return ResponseVerdict::Violation(code),
    };
    // Recipient must be the client (T12-10).
    if resp.recipient_id != vtc.client_key_id {
        return ResponseVerdict::Violation(Code::NotAddressee);
    }
    // Same thread; caused-by = the persisted request hash h1 (T13-01 / T13-06).
    if resp.thread_id != vtc.thread_id {
        return ResponseVerdict::Violation(Code::Malformed);
    }
    if resp.caused_by != vtc.request_message_hash {
        return ResponseVerdict::Violation(Code::Causality);
    }
    // RESPONSE-SIG under the DS key, binding the persisted read-context.
    let response_tuple = DomainTuple::Response {
        bindings: vtc.bindings.clone(),
        dialect_hash: expected_dialect_hash.to_string(),
        request_content_hash: vtc.request_message_hash.clone(),
        response_message: response_message_sexpr.clone(),
        read_context: vtc.request_frame_context.clone(),
    };
    if !verify_tuple(
        &vtc.ds_key,
        response_tuple.domain_tag(),
        &response_tuple.fields(),
        &resp_sig,
    ) {
        return ResponseVerdict::Violation(Code::WrongSigner);
    }

    // Every response-room field equals the persisted state_owner_room (CON-003).
    let (typed, resp_room) = match decode_response_body(&resp, &response_message_sexpr) {
        Ok(x) => x,
        Err(code) => return ResponseVerdict::Violation(code),
    };
    if resp_room != vtc.state_owner_room {
        return ResponseVerdict::Violation(Code::AuthorityRoom);
    }
    // The response envelope's own room must match too (no cross-room transplant).
    if candidate_envelope_context.outer_room != vtc.state_owner_room {
        return ResponseVerdict::Violation(Code::AuthorityRoom);
    }

    // --- Role projection via the REAL role layer, after the retained request ---
    // Rebuild the cast from the persisted VTC and store the request at h1 so the
    // response's :caused-by resolves to it.
    let cast = rebuild_cast(vtc);
    let mut store = ThreadedMessageStore::new();
    let tid = ThreadId(vtc.thread_id.clone());
    if let Some(req_msg) = parse_message(&vtc.request_descriptor) {
        store.append(
            ContentHash(vtc.request_message_hash.clone()),
            tid.clone(),
            req_msg,
        );
    }
    let response_msg = match parse_message(&bundle.response) {
        Some(m) => m,
        None => return ResponseVerdict::Violation(Code::Malformed),
    };
    let client_endpoint = Endpoint {
        role: String::from("client"),
        occupant: None,
    };
    let root = ContentHash(vtc.opener_message_hash.clone());
    match verify_causal_for_role(
        &response_msg,
        &client_endpoint,
        dialect,
        &cast,
        &store,
        &tid,
        &root,
    ) {
        VerificationResult::Valid => {}
        VerificationResult::Unknown => return ResponseVerdict::Violation(Code::MissingEvidence),
        VerificationResult::Violation(_) => return ResponseVerdict::Violation(Code::Causality),
    }

    let response_msg2 = match parse_message(&response_message_sexpr) {
        Some(m) => m,
        None => return ResponseVerdict::Violation(Code::Malformed),
    };
    let resp_hash = typed_root(&response_msg2);
    ResponseVerdict::Valid(typed, ContentHash(resp_hash))
}

fn rebuild_cast(vtc: &VerifiedThreadContext) -> Cast {
    let mut singleton = BTreeMap::new();
    singleton.insert(String::from("client"), AgentKey(vtc.client_key_id.clone()));
    singleton.insert(String::from("ds"), AgentKey(vtc.ds_key_id.clone()));
    Cast {
        singleton,
        indexed: BTreeMap::new(),
        dialect_pin: Some(vtc.dialect_hash.clone()),
    }
}

// ===========================================================================
// Sidecars (CON-002 / CON-011 step 2) — real ref-set/digest/length checks
// ===========================================================================

/// Purpose byte-length bounds (CON-002).
fn length_ok(purpose: &str, len: i64) -> bool {
    match purpose {
        "ciphertext" => (1..=65_536).contains(&len),
        "welcome" => (1..=65_536).contains(&len),
        "genesis" => (1..=8_192).contains(&len),
        _ => false,
    }
}

/// Verify the sidecar list against the descriptor's declared blob refs:
/// exact set, sorted by `(purpose, digest)`, no duplicates, and each sidecar's
/// base64url string decodes to exactly its declared length and SHA-256 digest.
pub fn verify_sidecars(
    refs: &[BlobRef],
    sidecars: &[SidecarAst],
) -> Result<Vec<VerifiedSidecarHandle>, Code> {
    if sidecars.len() != refs.len() {
        return Err(Code::Sidecar);
    }
    // Sorted by (purpose, digest), strictly (no duplicates).
    for w in sidecars.windows(2) {
        let a = (&w[0].purpose, &w[0].digest);
        let b = (&w[1].purpose, &w[1].digest);
        if a >= b {
            return Err(Code::Sidecar);
        }
    }
    let mut handles = Vec::new();
    for sc in sidecars {
        // Real decode + length + digest.
        let bytes = b64url_decode(&sc.b64).ok_or(Code::Sidecar)?;
        if b64url_encode(&bytes) != sc.b64 {
            return Err(Code::Sidecar); // non-canonical base64url
        }
        if bytes.len() as i64 != sc.length || !length_ok(&sc.purpose, sc.length) {
            return Err(Code::Sidecar);
        }
        if sha256_hex(&bytes) != sc.digest {
            return Err(Code::Sidecar);
        }
        // Must be named by exactly one descriptor ref.
        let matched = refs
            .iter()
            .any(|r| r.purpose == sc.purpose && r.digest == sc.digest && r.length == sc.length);
        if !matched {
            return Err(Code::Sidecar);
        }
        handles.push(VerifiedSidecarHandle {
            purpose: sc.purpose.clone(),
            digest: sc.digest.clone(),
            bytes,
        });
    }
    Ok(handles)
}

// ===========================================================================
// THREAD-UNIQUE (CON-003 / CON-004 state) — one (room,client,thread) → root
// ===========================================================================

/// STUB (CON-004 stateful layer): the THREAD-UNIQUE binding table. One
/// `(room, client_key_id, thread_id)` binds exactly one `(h0, h1, kind)`
/// through request expiry; an exact replay reuses the binding, a different
/// root is a terminal violation.
#[derive(Debug, Default)]
pub struct ThreadRegistry {
    map: BTreeMap<(String, String, String), (String, String, String)>,
}

impl ThreadRegistry {
    pub fn new() -> Self {
        Self::default()
    }

    /// Bind, or accept an exact replay, or reject a different root (T13-02).
    pub fn bind(&mut self, vtc: &VerifiedThreadContext) -> Result<(), Code> {
        let key = (
            vtc.authority_room.clone(),
            vtc.client_key_id.clone(),
            vtc.thread_id.clone(),
        );
        let val = (
            vtc.opener_message_hash.clone(),
            vtc.request_message_hash.clone(),
            vtc.request_kind.clone(),
        );
        match self.map.get(&key) {
            Some(existing) if existing == &val => Ok(()), // exact replay
            Some(_) => Err(Code::ThreadReuse),            // different root on the thread
            None => {
                self.map.insert(key, val);
                Ok(())
            }
        }
    }
}

// ===========================================================================
// Small structural decoders (fail-closed → Violation(Malformed))
// ===========================================================================

/// `(signed <key-id> <sig-string> <inner>)` → (key-id, 64-byte sig, inner).
fn parse_signed(s: &SExpr) -> Option<(String, [u8; 64], SExpr)> {
    let items = as_list(s)?;
    if items.len() != 4 || as_sym(&items[0])? != "signed" {
        return None;
    }
    let key_id = as_sym(&items[1])?.to_string();
    recognize_key_id(&key_id)?; // must be a canonical key-id
    let sig = recognize_signature(as_str(&items[2])?)?;
    Some((key_id, sig, items[3].clone()))
}

/// opener-message = (mls-ds-open-v1 <ds> (open-v1 <c> <d>) :thread t :caused-by begin)
fn check_opener_message(s: &SExpr, client_id: &str, ds_id: &str) -> Result<(), Code> {
    let items = as_list(s).ok_or(Code::Malformed)?;
    // head, recipient(@ds), body, :thread, t, :caused-by, begin  → 7 items
    if items.len() != 7 || as_sym(&items[0]).ok_or(Code::Malformed)? != "mls-ds-open-v1" {
        return Err(Code::Malformed);
    }
    if as_sym(&items[1]).ok_or(Code::Malformed)? != ds_id {
        return Err(Code::NotAddressee); // opener recipient must be the DS
    }
    let body = as_list(&items[2]).ok_or(Code::Malformed)?;
    if body.len() != 3
        || as_sym(&body[0]).ok_or(Code::Malformed)? != "open-v1"
        || as_sym(&body[1]).ok_or(Code::Malformed)? != client_id
        || as_sym(&body[2]).ok_or(Code::Malformed)? != ds_id
    {
        return Err(Code::Malformed);
    }
    Ok(())
}

struct RequestHead {
    kind: String,
    recipient_id: String,
    thread_id: String,
    caused_by: String,
    issued_at: i64,
    expires_at: i64,
}

/// Decode the request envelope common fields (not the body).
/// request = (<name> <ds> <body> :issued-at N :expires-at N :thread t :caused-by h)
fn decode_request_head(s: &SExpr) -> Result<RequestHead, Code> {
    let items = as_list(s).ok_or(Code::Malformed)?;
    if items.len() != 11 {
        return Err(Code::Malformed);
    }
    let kind = as_sym(&items[0]).ok_or(Code::Malformed)?.to_string();
    if !REQUEST_NAMES.contains(&kind.as_str()) {
        return Err(Code::Malformed);
    }
    let recipient_id = as_sym(&items[1]).ok_or(Code::Malformed)?.to_string();
    // items[2] = body (decoded later)
    let kv = &items[3..];
    let issued_at = kw_num(kv, "issued-at")?;
    let expires_at = kw_num(kv, "expires-at")?;
    let thread_id = kw_str(kv, "thread")?;
    let caused_by = kw_qhash(kv, "caused-by")?;
    Ok(RequestHead {
        kind,
        recipient_id,
        thread_id,
        caused_by,
        issued_at,
        expires_at,
    })
}

struct ResponseHead {
    kind: String,
    recipient_id: String,
    thread_id: String,
    caused_by: String,
}

/// response-message = (<name> <client> <body> :thread t :caused-by h)
fn decode_response_head(s: &SExpr) -> Result<ResponseHead, Code> {
    let items = as_list(s).ok_or(Code::Malformed)?;
    if items.len() != 7 {
        return Err(Code::Malformed);
    }
    let kind = as_sym(&items[0]).ok_or(Code::Malformed)?.to_string();
    if !RESPONSE_NAMES.contains(&kind.as_str()) {
        return Err(Code::Malformed);
    }
    let recipient_id = as_sym(&items[1]).ok_or(Code::Malformed)?.to_string();
    let kv = &items[3..];
    let thread_id = kw_str(kv, "thread")?;
    let caused_by = kw_qhash(kv, "caused-by")?;
    Ok(ResponseHead {
        kind,
        recipient_id,
        thread_id,
        caused_by,
    })
}

/// Decode the request body + verify nested SOURCE-SIG / ADD-AUTH, returning the
/// typed request, the body room, and the declared blob refs (for sidecars).
fn decode_request_body(
    head: &RequestHead,
    request_sexpr: &SExpr,
    client_key: &[u8; 32],
) -> Result<(TypedRequest, String, Vec<BlobRef>), Code> {
    let items = as_list(request_sexpr).ok_or(Code::Malformed)?;
    let body = &items[2];
    let b = as_list(body).ok_or(Code::Malformed)?;
    match head.kind.as_str() {
        "next-record" => {
            // (next-v1 <room> <cursor_seq> <cursor_hash> <wait-ms>)
            if b.len() != 5 || as_sym(&b[0]).ok_or(Code::Malformed)? != "next-v1" {
                return Err(Code::Malformed);
            }
            let room = as_str(&b[1]).ok_or(Code::Malformed)?.to_string();
            let cursor_seq = as_num(&b[2]).ok_or(Code::Malformed)?;
            let cursor_hash = as_str(&b[3]).ok_or(Code::Malformed)?.to_string();
            let wait_ms = as_num(&b[4]).ok_or(Code::Malformed)?;
            if !(0..=25_000).contains(&wait_ms) {
                return Err(Code::Malformed);
            }
            Ok((
                TypedRequest::NextRecord {
                    room,
                    cursor_seq,
                    cursor_hash,
                    wait_ms,
                },
                as_str(&b[1]).unwrap().to_string(),
                Vec::new(),
            ))
        }
        "commit-submit" => {
            // (submit-v1 (source-signed <c> <sig> (commit-v1 <room> <seq> <hash> <ciphertext-ref>)))
            if b.len() != 2 || as_sym(&b[0]).ok_or(Code::Malformed)? != "submit-v1" {
                return Err(Code::Malformed);
            }
            let (src_key_id, src_sig, source) = parse_source_signed(&b[1])?;
            // Nested SOURCE-SIG must bind the cast client (T12-04).
            if recognize_key_id(&src_key_id) != Some(*client_key) {
                return Err(Code::BadSourceSignature);
            }
            let source_tuple = DomainTuple::Source {
                source: source.clone(),
            };
            if !verify_tuple(
                client_key,
                source_tuple.domain_tag(),
                &source_tuple.fields(),
                &src_sig,
            ) {
                return Err(Code::BadSourceSignature);
            }
            let sc = as_list(&source).ok_or(Code::Malformed)?;
            if sc.len() != 5 || as_sym(&sc[0]).ok_or(Code::Malformed)? != "commit-v1" {
                return Err(Code::Malformed);
            }
            let room = as_str(&sc[1]).ok_or(Code::Malformed)?.to_string();
            let base_seq = as_num(&sc[2]).ok_or(Code::Malformed)?;
            let base_hash = as_str(&sc[3]).ok_or(Code::Malformed)?.to_string();
            let ciphertext = parse_blob_ref(&sc[4], "ciphertext")?;
            let refs = vec![ciphertext.clone()];
            Ok((
                TypedRequest::CommitSubmit {
                    room: room.clone(),
                    base_seq,
                    base_hash,
                    ciphertext,
                },
                room,
                refs,
            ))
        }
        "commit-add-submit" => {
            // (submit-add-v1 (source-signed <c> <sig>
            //    (commit-add-v1 <room> <seq> <hash> <cref> <targets> <wref> <admission-proof>)))
            if b.len() != 2 || as_sym(&b[0]).ok_or(Code::Malformed)? != "submit-add-v1" {
                return Err(Code::Malformed);
            }
            let (src_key_id, src_sig, source) = parse_source_signed(&b[1])?;
            if recognize_key_id(&src_key_id) != Some(*client_key) {
                return Err(Code::BadSourceSignature);
            }
            let source_tuple = DomainTuple::Source {
                source: source.clone(),
            };
            if !verify_tuple(
                client_key,
                source_tuple.domain_tag(),
                &source_tuple.fields(),
                &src_sig,
            ) {
                return Err(Code::BadSourceSignature);
            }
            let sc = as_list(&source).ok_or(Code::Malformed)?;
            if sc.len() != 8 || as_sym(&sc[0]).ok_or(Code::Malformed)? != "commit-add-v1" {
                return Err(Code::Malformed);
            }
            let room = as_str(&sc[1]).ok_or(Code::Malformed)?.to_string();
            let base_seq = as_num(&sc[2]).ok_or(Code::Malformed)?;
            let base_hash = as_str(&sc[3]).ok_or(Code::Malformed)?.to_string();
            let ciphertext = parse_blob_ref(&sc[4], "ciphertext")?;
            let targets = parse_targets(&sc[5])?;
            let welcome = parse_blob_ref(&sc[6], "welcome")?;
            // ADD-AUTH (admission proof): `none` → add-unauthorized, else the
            // 9-field tuple must verify under the named creator key.
            verify_add_auth(&sc[7], &room, &sc[2], &base_hash, &ciphertext, &targets, &welcome)?;
            // Sidecar set for an Add submit: ciphertext + welcome, sorted.
            let mut refs = vec![ciphertext.clone(), welcome.clone()];
            refs.sort_by(|a, b| (&a.purpose, &a.digest).cmp(&(&b.purpose, &b.digest)));
            Ok((
                TypedRequest::CommitAddSubmit {
                    room: room.clone(),
                    base_seq,
                    base_hash,
                    ciphertext,
                    welcome,
                    targets,
                },
                room,
                refs,
            ))
        }
        // STUB: recognized-but-not-decoded request kinds.
        other => Ok((
            TypedRequest::Other {
                kind: other.to_string(),
            },
            String::new(),
            Vec::new(),
        )),
    }
}

fn decode_response_body(
    head: &ResponseHead,
    response_sexpr: &SExpr,
) -> Result<(TypedResponse, String), Code> {
    let items = as_list(response_sexpr).ok_or(Code::Malformed)?;
    let body = &items[2];
    let b = as_list(body).ok_or(Code::Malformed)?;
    match head.kind.as_str() {
        "record-admitted" => {
            // (admitted-v1 <room> <seq> <record_hash> <source_hash>)
            if b.len() != 5 || as_sym(&b[0]).ok_or(Code::Malformed)? != "admitted-v1" {
                return Err(Code::Malformed);
            }
            let room = as_str(&b[1]).ok_or(Code::Malformed)?.to_string();
            Ok((
                TypedResponse::RecordAdmitted {
                    room: room.clone(),
                    seq: as_num(&b[2]).ok_or(Code::Malformed)?,
                    record_hash: as_str(&b[3]).ok_or(Code::Malformed)?.to_string(),
                    source_hash: as_str(&b[4]).ok_or(Code::Malformed)?.to_string(),
                },
                room,
            ))
        }
        "ds-rejected" => {
            // (error-v1 <room> <error-code>)
            if b.len() != 3 || as_sym(&b[0]).ok_or(Code::Malformed)? != "error-v1" {
                return Err(Code::Malformed);
            }
            let room = as_str(&b[1]).ok_or(Code::Malformed)?.to_string();
            let error_code = as_sym(&b[2]).ok_or(Code::Malformed)?.to_string();
            Ok((
                TypedResponse::DsRejected {
                    room: room.clone(),
                    error_code,
                },
                room,
            ))
        }
        "at-head" => {
            // (head-v1 <room> <head_seq> <head_hash> <floor_seq> <floor_prev_hash>)
            if b.len() != 6 || as_sym(&b[0]).ok_or(Code::Malformed)? != "head-v1" {
                return Err(Code::Malformed);
            }
            let room = as_str(&b[1]).ok_or(Code::Malformed)?.to_string();
            Ok((
                TypedResponse::AtHead {
                    room: room.clone(),
                    head_seq: as_num(&b[2]).ok_or(Code::Malformed)?,
                    head_hash: as_str(&b[3]).ok_or(Code::Malformed)?.to_string(),
                    floor_seq: as_num(&b[4]).ok_or(Code::Malformed)?,
                    floor_prev_hash: as_str(&b[5]).ok_or(Code::Malformed)?.to_string(),
                },
                room,
            ))
        }
        other => Ok((
            TypedResponse::Other {
                kind: other.to_string(),
            },
            // STUB: undeclared response kinds report the outer room so the
            // state-owner equality still runs.
            String::new(),
        )),
    }
}

/// (source-signed <key-id> <sig> <source>) → (key-id, sig, source)
fn parse_source_signed(s: &SExpr) -> Result<(String, [u8; 64], SExpr), Code> {
    let items = as_list(s).ok_or(Code::Malformed)?;
    if items.len() != 4 || as_sym(&items[0]).ok_or(Code::Malformed)? != "source-signed" {
        return Err(Code::Malformed);
    }
    let key_id = as_sym(&items[1]).ok_or(Code::Malformed)?.to_string();
    recognize_key_id(&key_id).ok_or(Code::Malformed)?;
    let sig = recognize_signature(as_str(&items[2]).ok_or(Code::Malformed)?).ok_or(Code::Malformed)?;
    Ok((key_id, sig, items[3].clone()))
}

/// (blob-ref-v1 <purpose> <hash> <len>)
fn parse_blob_ref(s: &SExpr, expected_purpose: &str) -> Result<BlobRef, Code> {
    let items = as_list(s).ok_or(Code::Malformed)?;
    if items.len() != 4 || as_sym(&items[0]).ok_or(Code::Malformed)? != "blob-ref-v1" {
        return Err(Code::Malformed);
    }
    let purpose = as_sym(&items[1]).ok_or(Code::Malformed)?.to_string();
    if purpose != expected_purpose {
        return Err(Code::Malformed);
    }
    let digest = as_str(&items[2]).ok_or(Code::Malformed)?.to_string();
    let length = as_num(&items[3]).ok_or(Code::Malformed)?;
    Ok(BlobRef {
        purpose,
        digest,
        length,
    })
}

/// targets = (@k1 @k2 …), strictly increasing by decoded bytes, no duplicate.
fn parse_targets(s: &SExpr) -> Result<Vec<String>, Code> {
    let items = as_list(s).ok_or(Code::Malformed)?;
    let mut ids = Vec::new();
    let mut prev: Option<[u8; 32]> = None;
    for it in items {
        let id = as_sym(it).ok_or(Code::Malformed)?.to_string();
        let bytes = recognize_key_id(&id).ok_or(Code::Malformed)?;
        if let Some(p) = prev {
            if bytes <= p {
                return Err(Code::Malformed); // strictly increasing by decoded bytes
            }
        }
        prev = Some(bytes);
        ids.push(id);
    }
    Ok(ids)
}

/// admission-proof = "none" | (add-authorized-v1 <creator-key> <genesis-anchor-hash> <sig>)
/// The ADD-AUTH 9-field tuple is reconstructed and verified under the creator.
#[allow(clippy::too_many_arguments)]
fn verify_add_auth(
    proof: &SExpr,
    room: &str,
    base_seq: &SExpr,
    base_hash: &str,
    ciphertext: &BlobRef,
    targets: &[String],
    welcome: &BlobRef,
) -> Result<(), Code> {
    // `none` maps to add-unauthorized (CON-002 reducer mapping).
    if let Some("none") = as_sym(proof) {
        return Err(Code::AddUnauthorized);
    }
    let items = as_list(proof).ok_or(Code::Malformed)?;
    if items.len() != 4 || as_sym(&items[0]).ok_or(Code::Malformed)? != "add-authorized-v1" {
        return Err(Code::Malformed);
    }
    let creator_key_id = as_sym(&items[1]).ok_or(Code::Malformed)?.to_string();
    let creator_key = recognize_key_id(&creator_key_id).ok_or(Code::Malformed)?;
    let genesis_anchor_hash = as_str(&items[2]).ok_or(Code::Malformed)?.to_string();
    let sig = recognize_signature(as_str(&items[3]).ok_or(Code::Malformed)?).ok_or(Code::Malformed)?;
    let base_seq_n = as_num(base_seq).ok_or(Code::Malformed)?;
    // Reconstruct the 9-field ADD-AUTH preimage (CON-002) and verify.
    let add_auth = DomainTuple::AddAuth {
        room: room.to_string(),
        source_author_key: creator_key_id.clone(),
        base_seq: base_seq_n,
        base_hash: base_hash.to_string(),
        ciphertext_digest: ciphertext.digest.clone(),
        targets: targets.to_vec(),
        welcome_digest: welcome.digest.clone(),
        genesis_anchor_hash,
    };
    if !verify_tuple(&creator_key, add_auth.domain_tag(), &add_auth.fields(), &sig) {
        return Err(Code::AddUnauthorized);
    }
    Ok(())
}

// -- keyword-field extractors (exact position, no duplicates) --

fn kw_num(kv: &[SExpr], key: &str) -> Result<i64, Code> {
    let v = kw_value(kv, key)?;
    as_num(v).ok_or(Code::Malformed)
}
fn kw_str(kv: &[SExpr], key: &str) -> Result<String, Code> {
    let v = kw_value(kv, key)?;
    Ok(as_str(v).ok_or(Code::Malformed)?.to_string())
}
fn kw_qhash(kv: &[SExpr], key: &str) -> Result<String, Code> {
    // caused-by hash carried as a quoted string (mls-ds hash form).
    let v = kw_value(kv, key)?;
    Ok(as_str(v).ok_or(Code::Malformed)?.to_string())
}
fn kw_value<'a>(kv: &'a [SExpr], key: &str) -> Result<&'a SExpr, Code> {
    let mut found: Option<&SExpr> = None;
    let mut i = 0;
    while i + 1 < kv.len() {
        if let SExpr::Atom(Atom::Keyword(k)) = &kv[i] {
            if k == key {
                if found.is_some() {
                    return Err(Code::Malformed); // duplicate keyword
                }
                found = Some(&kv[i + 1]);
            }
        }
        i += 2;
    }
    found.ok_or(Code::Malformed)
}

fn parse_message(s: &SExpr) -> Option<Message> {
    Message::try_from(s).ok()
}

// ===========================================================================
// REQ-142 / CON-003 / TEST-018 — deterministic verdict SERIALIZATION and the
// cross-runtime VECTOR RUNNER
// ===========================================================================
//
// `run_verify_vector` is the single entry point the cross-target parity gate
// drives: a `&[u8]` in, canonical verdict bytes out. It decodes a
// self-describing vector, runs the CON-003 role-verification boundary
// (`verify_mls_ds_request` / `verify_mls_ds_response`, via the CON-011
// recognizer), and serializes the verdict to canonical RFC 9804 bytes with the
// crate's own `canonical_encode`. Because the ONLY sink is `canonical_encode`
// over a fixed S-expression shape — no floats, `usize` widths only ever
// stringified as small decimals, `i64` fields, portable SHA-256 / Ed25519 —
// the output is byte-identical on every compile target (native, the cbcl-erl
// NIF, and wasm32). That byte-identity is the REQ-142 / CON-003 "serialized
// verdict vector" the release gate requires.
//
// ## Vector wire format (self-describing, a canonical CBCL S-expression)
//
// Top:      `(mls-ds-verify-vector-v1 <clause>)`
//
// Request clause (recognize + `verify_mls_ds_request` + serialize):
//   `(request <exp-dialect-hash:str> <ds-key-id:str> <admitted-client-key-id:str>
//             <outer-signer-key-id:str> <session-id:str> <frame-id:num>
//             <outer-room:str> <wall-time-ms:num> <payload-b64:str>)`
//   where `<payload-b64>` is the unpadded base64url of the serialized request
//   bundle TEXT, and the three key-ids are canonical `@`+43-base64url spellings.
//
// Response clause (reproduce the VTC from the embedded request, then recognize
// + `verify_mls_ds_response` + serialize):
//   `(response <request-clause> <resp-session-id:str> <resp-frame-id:num>
//              <resp-outer-room:str> <resp-outer-signer-key-id:str>
//              <resp-payload-b64:str>)`
//
// Direct clause (serialize a literal verdict — the ONLY way to exercise the
// `Unknown` outcome, which the v1 boundary never returns from `verify_*`: it
// collapses a residual role-layer `Unknown` to `Violation(missing-evidence)`
// per CON-003's singleton-transaction rule, so `Unknown` is proven purely at
// the serialization boundary):
//   `(direct <side:sym request|response> unknown (<content-hash:str> …))`
//   `(direct <side:sym request|response> violation <code:sym>)`
//
// ## Verdict wire format (the serialized output, canonical_encode'd)
//
//   Valid:     `(mls-ds-verdict-v1 <side> valid <kind:sym> <content-hash:str>)`
//   Unknown:   `(mls-ds-verdict-v1 <side> unknown (<content-hash:str> …))`
//   Violation: `(mls-ds-verdict-v1 <side> violation <code:sym>)`
//   Recognizer short-circuit (payload is not the expected bundle):
//     `(mls-ds-verdict-v1 <side> recognize-violation <code:sym>)`  (a CON-011
//        recognizer `Violation`, e.g. reserved-mls-control / resource-excess)
//     `(mls-ds-verdict-v1 <side> recognize <non-mls|wrong-bundle>)`
//   Vector envelope error: `(mls-ds-verdict-v1 vector-error <reason:sym>)`
//   Response with no reproducible VTC: `(mls-ds-verdict-v1 response vtc-unavailable)`

/// Canonical, stable wire token for a violation / recognition [`Code`].
pub fn code_symbol(code: &Code) -> &'static str {
    match code {
        Code::Malformed => "malformed",
        Code::ReservedMlsControl => "reserved-mls-control",
        Code::ResourceExcess => "resource-excess",
        Code::WrongDialectPin => "wrong-dialect-pin",
        Code::WrongSigner => "wrong-signer",
        Code::NotAddressee => "not-addressee",
        Code::BadSourceSignature => "bad-source-signature",
        Code::AddUnauthorized => "add-unauthorized",
        Code::Causality => "causality",
        Code::RootWindow => "root-window",
        Code::ThreadReuse => "thread-reuse",
        Code::MissingEvidence => "missing-evidence",
        Code::Sidecar => "sidecar",
        Code::AuthorityRoom => "authority-room",
    }
}

fn typed_request_kind(t: &TypedRequest) -> &str {
    match t {
        TypedRequest::NextRecord { .. } => "next-record",
        TypedRequest::CommitSubmit { .. } => "commit-submit",
        TypedRequest::CommitAddSubmit { .. } => "commit-add-submit",
        TypedRequest::Other { kind } => kind,
    }
}

fn typed_response_kind(t: &TypedResponse) -> &str {
    match t {
        TypedResponse::RecordAdmitted { .. } => "record-admitted",
        TypedResponse::DsRejected { .. } => "ds-rejected",
        TypedResponse::AtHead { .. } => "at-head",
        TypedResponse::Other { kind } => kind,
    }
}

fn verdict_sexpr(side: &str, outcome: &str, tail: Vec<SExpr>) -> SExpr {
    let mut items = vec![sym("mls-ds-verdict-v1"), sym(side), sym(outcome)];
    items.extend(tail);
    SExpr::List(items)
}

fn hash_set_sexpr(set: &BTreeSet<ContentHash>) -> SExpr {
    // BTreeSet iterates in sorted order → deterministic on every target.
    SExpr::List(set.iter().map(|ContentHash(h)| qstr(h)).collect())
}

/// Serialize a [`RequestVerdict`] to canonical RFC 9804 bytes (REQ-142).
pub fn serialize_request_verdict(v: &RequestVerdict) -> Vec<u8> {
    let s = match v {
        RequestVerdict::Valid(t, ContentHash(h), _vtc) => {
            verdict_sexpr("request", "valid", vec![sym(typed_request_kind(t)), qstr(h)])
        }
        RequestVerdict::Unknown(set) => {
            verdict_sexpr("request", "unknown", vec![hash_set_sexpr(set)])
        }
        RequestVerdict::Violation(code) => {
            verdict_sexpr("request", "violation", vec![sym(code_symbol(code))])
        }
    };
    canonical_encode(&s)
}

/// Serialize a [`ResponseVerdict`] to canonical RFC 9804 bytes (REQ-142).
pub fn serialize_response_verdict(v: &ResponseVerdict) -> Vec<u8> {
    let s = match v {
        ResponseVerdict::Valid(t, ContentHash(h)) => verdict_sexpr(
            "response",
            "valid",
            vec![sym(typed_response_kind(t)), qstr(h)],
        ),
        ResponseVerdict::Unknown(set) => {
            verdict_sexpr("response", "unknown", vec![hash_set_sexpr(set)])
        }
        ResponseVerdict::Violation(code) => {
            verdict_sexpr("response", "violation", vec![sym(code_symbol(code))])
        }
    };
    canonical_encode(&s)
}

fn vector_error(reason: &str) -> Vec<u8> {
    canonical_encode(&SExpr::List(vec![
        sym("mls-ds-verdict-v1"),
        sym("vector-error"),
        sym(reason),
    ]))
}

/// Serialize a CON-011 recognizer short-circuit (the payload was not the
/// expected bundle, so the role-verification boundary was never entered).
fn recognizer_verdict(side: &str, class: &OuterClass) -> Vec<u8> {
    let s = match class {
        OuterClass::Violation(code) => {
            verdict_sexpr(side, "recognize-violation", vec![sym(code_symbol(code))])
        }
        OuterClass::NonMls(_) => verdict_sexpr(side, "recognize", vec![sym("non-mls")]),
        OuterClass::Request(_) => verdict_sexpr(side, "recognize", vec![sym("wrong-bundle")]),
        OuterClass::Response(_) => verdict_sexpr(side, "recognize", vec![sym("wrong-bundle")]),
    };
    canonical_encode(&s)
}

/// Fields decoded from a `(request …)` vector clause.
struct RequestVectorCtx {
    exp_dialect_hash: String,
    ds_key: [u8; 32],
    client_key: [u8; 32],
    outer_signer: [u8; 32],
    env: EnvelopeContext,
    wall_time_ms: i64,
    payload: Vec<u8>,
}

/// Decode a `(request …)` clause into its context + raw payload bytes.
fn decode_request_clause(items: &[SExpr]) -> Option<RequestVectorCtx> {
    // (request exp-hash ds client outer session frame room wall payload-b64)
    if items.len() != 10 || as_sym(&items[0])? != "request" {
        return None;
    }
    let exp_dialect_hash = as_str(&items[1])?.to_string();
    let ds_key = recognize_key_id(as_str(&items[2])?)?;
    let client_key = recognize_key_id(as_str(&items[3])?)?;
    let outer_signer = recognize_key_id(as_str(&items[4])?)?;
    let session_id = as_str(&items[5])?.to_string();
    let frame_id = as_num(&items[6])?;
    let outer_room = as_str(&items[7])?.to_string();
    let wall_time_ms = as_num(&items[8])?;
    let payload = b64url_decode(as_str(&items[9])?)?;
    Some(RequestVectorCtx {
        exp_dialect_hash,
        ds_key,
        client_key,
        outer_signer,
        env: EnvelopeContext {
            session_id,
            frame_id,
            outer_room,
        },
        wall_time_ms,
        payload,
    })
}

fn run_request_clause(clause: &SExpr) -> Vec<u8> {
    let items = match as_list(clause) {
        Some(v) => v,
        None => return vector_error("bad-request-clause"),
    };
    let ctx = match decode_request_clause(items) {
        Some(c) => c,
        None => return vector_error("bad-request-clause"),
    };
    let class = recognize_dispatch_verified_outer(&ctx.payload);
    let ast = match &class {
        OuterClass::Request(a) => a,
        other => return recognizer_verdict("request", other),
    };
    let dialect = mls_ds_dialect();
    let verdict = verify_mls_ds_request(
        &dialect,
        &ctx.exp_dialect_hash,
        &ctx.ds_key,
        &ctx.client_key,
        &ctx.outer_signer,
        &ctx.env,
        ctx.wall_time_ms,
        ast,
    );
    serialize_request_verdict(&verdict)
}

fn run_response_clause(clause: &SExpr) -> Vec<u8> {
    let items = match as_list(clause) {
        Some(v) if v.len() == 7 && as_sym(&v[0]) == Some("response") => v,
        _ => return vector_error("bad-response-clause"),
    };
    // 1. Reproduce the VTC by running the embedded request clause.
    let req_items = match as_list(&items[1]) {
        Some(v) => v,
        None => return vector_error("bad-response-request"),
    };
    let req_ctx = match decode_request_clause(req_items) {
        Some(c) => c,
        None => return vector_error("bad-response-request"),
    };
    let dialect = mls_ds_dialect();
    let req_ast = match recognize_dispatch_verified_outer(&req_ctx.payload) {
        OuterClass::Request(a) => a,
        _ => return vector_error("response-request-not-a-bundle"),
    };
    let vtc = match verify_mls_ds_request(
        &dialect,
        &req_ctx.exp_dialect_hash,
        &req_ctx.ds_key,
        &req_ctx.client_key,
        &req_ctx.outer_signer,
        &req_ctx.env,
        req_ctx.wall_time_ms,
        &req_ast,
    ) {
        RequestVerdict::Valid(_, _, vtc) => vtc,
        _ => {
            return canonical_encode(&SExpr::List(vec![
                sym("mls-ds-verdict-v1"),
                sym("response"),
                sym("vtc-unavailable"),
            ]))
        }
    };
    // 2. Decode the response context.
    let resp_session = match as_str(&items[2]) {
        Some(s) => s.to_string(),
        None => return vector_error("bad-response-clause"),
    };
    let resp_frame = match as_num(&items[3]) {
        Some(n) => n,
        None => return vector_error("bad-response-clause"),
    };
    let resp_room = match as_str(&items[4]) {
        Some(s) => s.to_string(),
        None => return vector_error("bad-response-clause"),
    };
    let resp_outer_signer = match as_str(&items[5]).and_then(recognize_key_id) {
        Some(k) => k,
        None => return vector_error("bad-response-clause"),
    };
    let resp_payload = match as_str(&items[6]).and_then(b64url_decode) {
        Some(p) => p,
        None => return vector_error("bad-response-clause"),
    };
    let resp_env = EnvelopeContext {
        session_id: resp_session,
        frame_id: resp_frame,
        outer_room: resp_room,
    };
    let class = recognize_dispatch_verified_outer(&resp_payload);
    let resp_ast = match &class {
        OuterClass::Response(a) => a,
        other => return recognizer_verdict("response", other),
    };
    // expected_ds_key is the VTC's DS key (the pinned DS for this thread).
    let verdict = verify_mls_ds_response(
        &dialect,
        &req_ctx.exp_dialect_hash,
        &vtc.ds_key,
        &resp_outer_signer,
        &resp_env,
        &vtc,
        resp_ast,
    );
    serialize_response_verdict(&verdict)
}

fn run_direct_clause(clause: &SExpr) -> Vec<u8> {
    let items = match as_list(clause) {
        Some(v) if v.len() >= 3 && as_sym(&v[0]) == Some("direct") => v,
        _ => return vector_error("bad-direct-clause"),
    };
    let side = match as_sym(&items[1]) {
        Some(s @ ("request" | "response")) => s,
        _ => return vector_error("bad-direct-side"),
    };
    match as_sym(&items[2]) {
        Some("unknown") => {
            let list = match items.get(3).and_then(as_list) {
                Some(l) => l,
                None => return vector_error("bad-direct-unknown"),
            };
            let mut set = BTreeSet::new();
            for h in list {
                match as_str(h) {
                    Some(s) => {
                        set.insert(ContentHash(s.to_string()));
                    }
                    None => return vector_error("bad-direct-unknown"),
                }
            }
            if side == "request" {
                serialize_request_verdict(&RequestVerdict::Unknown(set))
            } else {
                serialize_response_verdict(&ResponseVerdict::Unknown(set))
            }
        }
        Some("violation") => {
            let code = match items.get(3).and_then(as_sym).and_then(symbol_code) {
                Some(c) => c,
                None => return vector_error("bad-direct-violation"),
            };
            if side == "request" {
                serialize_request_verdict(&RequestVerdict::Violation(code))
            } else {
                serialize_response_verdict(&ResponseVerdict::Violation(code))
            }
        }
        _ => vector_error("bad-direct-outcome"),
    }
}

/// Inverse of [`code_symbol`] (for `direct` violation vectors).
fn symbol_code(s: &str) -> Option<Code> {
    Some(match s {
        "malformed" => Code::Malformed,
        "reserved-mls-control" => Code::ReservedMlsControl,
        "resource-excess" => Code::ResourceExcess,
        "wrong-dialect-pin" => Code::WrongDialectPin,
        "wrong-signer" => Code::WrongSigner,
        "not-addressee" => Code::NotAddressee,
        "bad-source-signature" => Code::BadSourceSignature,
        "add-unauthorized" => Code::AddUnauthorized,
        "causality" => Code::Causality,
        "root-window" => Code::RootWindow,
        "thread-reuse" => Code::ThreadReuse,
        "missing-evidence" => Code::MissingEvidence,
        "sidecar" => Code::Sidecar,
        "authority-room" => Code::AuthorityRoom,
        _ => return None,
    })
}

/// REQ-142 / CON-003 / TEST-018 cross-runtime VECTOR RUNNER.
///
/// Decodes a self-describing verify vector, runs the CON-003 role-verification
/// boundary, and serializes the verdict to canonical RFC 9804 bytes. The output
/// is byte-identical across native, NIF, and wasm32 compile targets — that is
/// the property the release gate proves. Total and deterministic: every
/// malformed input maps to a fixed `vector-error` verdict, never a panic.
pub fn run_verify_vector(input: &[u8]) -> Vec<u8> {
    let text = match core::str::from_utf8(input) {
        Ok(t) => t,
        Err(_) => return vector_error("bad-vector-utf8"),
    };
    let sexpr = match text.parse::<SExpr>() {
        Ok(s) => s,
        Err(_) => return vector_error("bad-vector-parse"),
    };
    let items = match as_list(&sexpr) {
        Some(v) if v.len() == 2 && as_sym(&v[0]) == Some("mls-ds-verify-vector-v1") => v,
        _ => return vector_error("bad-vector-envelope"),
    };
    match head_sym(&items[1]) {
        Some("request") => run_request_clause(&items[1]),
        Some("response") => run_response_clause(&items[1]),
        Some("direct") => run_direct_clause(&items[1]),
        _ => vector_error("bad-vector-clause"),
    }
}

/// SHA-256 fingerprint over a sequence of already-computed verdict outputs:
/// for each verdict, absorb its 8-byte little-endian length followed by its
/// bytes. A single differing byte in ANY verdict changes this digest, so a
/// matching digest across targets is proof of per-vector byte-identity
/// (REQ-142). Cross-target tests pass their OWN target-produced outputs here.
pub fn digest_verdicts(outputs: &[Vec<u8>]) -> [u8; 32] {
    let mut h = Sha256::new();
    for out in outputs {
        h.update((out.len() as u64).to_le_bytes());
        h.update(out);
    }
    let d = h.finalize();
    let mut out = [0u8; 32];
    out.copy_from_slice(&d);
    out
}

/// [`digest_verdicts`] rendered as lowercase hex (a compact cross-target token).
pub fn digest_verdicts_hex(outputs: &[Vec<u8>]) -> String {
    let mut s = String::new();
    push_hex(&mut s, &digest_verdicts(outputs));
    s
}

/// Run every input through [`run_verify_vector`], then fingerprint the outputs.
/// The convenience path for the native baseline.
pub fn corpus_digest(vectors: &[Vec<u8>]) -> [u8; 32] {
    let outputs: Vec<Vec<u8>> = vectors.iter().map(|v| run_verify_vector(v)).collect();
    digest_verdicts(&outputs)
}

/// `corpus_digest` rendered as lowercase hex.
pub fn corpus_digest_hex(vectors: &[Vec<u8>]) -> String {
    let mut s = String::new();
    push_hex(&mut s, &corpus_digest(vectors));
    s
}

/// The deterministic REQ-142 corpus (built with real Ed25519 keys/signatures).
/// Re-exported here so every compile target builds byte-identical inputs.
pub mod corpus;

// ===========================================================================
// Tests
// ===========================================================================

#[cfg(test)]
mod tests;
