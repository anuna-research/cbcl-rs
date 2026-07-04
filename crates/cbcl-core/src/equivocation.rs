//! Equivocation accountability (SPEC-015 REQ-705/REQ-706/REQ-707,
//! ADR-703, CON-702).
//!
//! The paper proves per-message *exclusion* of equivocation is non-monotone
//! (outside the CALM coordination-free envelope) while *detection* is
//! monotone and the offending signed pair is a transferable proof. This
//! module makes that literal, in three pieces:
//!
//! 1. [`equivocation`] (REQ-705) — a monotone predicate over a
//!    thread-scoped store: does `key` have two distinct messages in
//!    `thread` that are (a) messages of two distinct alternatives of one
//!    `(any …)` choice point of the dialect's protocol (*choice*
//!    equivocation), or (b) two distinct discharges of the same protocol
//!    obligation — same performative, different content hash (*obligation*
//!    equivocation)? Detection is read-only and verdict-neutral: both
//!    members of the pair keep whatever verdict they individually earned
//!    (detection, not exclusion — ADR-703).
//! 2. [`EquivocationProof`] / [`verify_equivocation_proof`] (REQ-706,
//!    CON-702) — the offending pair as a transferable proof object
//!    `(equivocation key thread dialect-hash member member)`, verifiable
//!    by any third party from the pair and the *pinned* dialect alone (the
//!    proof names the governing dialect's content hash and verification is
//!    against a dialect matching it, never a same-named substitute): no
//!    store, no testimony. Anything short of a fully-verifying pair is a
//!    typed rejection.
//! 3. [`choice_transparency_lint`] (REQ-707) — an opt-in, advisory R6-area
//!    lint: when a choice point's alternatives share no common recipient
//!    role other than the chooser, no single honest endpoint is guaranteed
//!    to witness a choice equivocation locally, and detection relies on
//!    proof gossip. A warning, never a violation — the corpus shows
//!    disjoint-branch addressing is legitimate.
//!
//! Key identity is canonical throughout ([`KeyId`], REQ-708): `@alice` and
//! `@ed25519:alice` are one identity, so spelling aliases can neither evade
//! the predicate nor split a proof.
//!
//! Choice-membership is read from the dialect as the `(any …)` node-refs of
//! its causal protocol: every [`NodeRef::Any`] set appearing in any step's
//! predecessor or successor position is one choice point, its members the
//! alternatives (`begin` excluded).
// SIMPLIFY: multi-entry predecessor lists ([Single(a), Single(b)]) are read
// as a ∨ b by the deployed verifier and by R6 chooser coherence (r6.rs),
// but are not yet treated as choice points here — REQ-705 names the
// `(any …)` form. Fold them in if the spec is amended to say so.

#![forbid(unsafe_code)]

use crate::attest::{verify_attestation_v2, AttestError, AttestationHeader};
use crate::canonical::canonical_encode;
use crate::dialect::Dialect;
use crate::keyid::{KeyId, KeyIdError};
use crate::message::Message;
use crate::protocol::{CausalProtocol, NodeRef, BEGIN_KEYWORD};
use crate::r4::Signer;
use crate::role::RoleAnnotation;
use crate::sexpr::SExpr;
use crate::store::{ContentHash, MessageStore, ThreadId};
use alloc::collections::{BTreeMap, BTreeSet};
use alloc::string::String;
use alloc::vec::Vec;
use core::fmt;

// ---------------------------------------------------------------------------
// Shared: content hashing and choice-point extraction
// ---------------------------------------------------------------------------

/// Canonical content hash of a message: `sha256:<lowercase-hex64>` over the
/// RFC 9804 canonical encoding of its S-expression form — the same
/// discipline as `:caused-by` references, dialect `:hash` fields
/// (`crate::canonical::dialect_hash`), and the wasm binding's message
/// hashing (SPEC-003 REQ-314).
pub fn message_content_hash(msg: &Message) -> String {
    use sha2::{Digest, Sha256};
    let sexpr: SExpr = msg.into();
    let digest = Sha256::digest(canonical_encode(&sexpr));
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(7 + 64);
    out.push_str("sha256:");
    for b in digest {
        out.push(HEX[(b >> 4) as usize] as char);
        out.push(HEX[(b & 0x0f) as usize] as char);
    }
    out
}

/// The `(any …)` choice points of a protocol: each distinct `NodeRef::Any`
/// member set (predecessor or successor position, `begin` excluded) with at
/// least two named alternatives.
fn any_choice_sets(cp: &CausalProtocol) -> Vec<BTreeSet<String>> {
    let mut sets: Vec<BTreeSet<String>> = Vec::new();
    for step in cp.steps.values() {
        for nr in step.predecessors.iter().chain(step.successors.iter()) {
            if let NodeRef::Any(set) = nr {
                let named: BTreeSet<String> = set
                    .iter()
                    .filter(|m| m.as_str() != BEGIN_KEYWORD)
                    .cloned()
                    .collect();
                if named.len() >= 2 && !sets.contains(&named) {
                    sets.push(named);
                }
            }
        }
    }
    sets
}

/// Every performative name the protocol constrains (step keys plus all
/// node-ref references, `begin` excluded) — the obligation schema the (b)
/// form quantifies over. The protocol is a finite DAG in which each name
/// occurs as one obligation (repeat expansion synthesises distinct copy
/// names, REQ-704), so the name identifies the obligation instance.
fn protocol_performatives(cp: &CausalProtocol) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    for (name, step) in &cp.steps {
        if name != BEGIN_KEYWORD {
            names.insert(name.clone());
        }
        for nr in step.predecessors.iter().chain(step.successors.iter()) {
            for p in nr.performatives() {
                if p != BEGIN_KEYWORD {
                    names.insert(String::from(p));
                }
            }
        }
    }
    names
}

// ---------------------------------------------------------------------------
// REQ-705: the store-level equivocation predicate
// ---------------------------------------------------------------------------

/// Which clause of REQ-705 the offending pair satisfies.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum EquivocationKind {
    /// (a) The two messages are messages of two distinct alternatives of
    /// one `(any …)` choice point.
    Choice {
        /// The choice point's alternative set, as declared in the dialect.
        alternatives: BTreeSet<String>,
    },
    /// (b) The two messages are two distinct discharges of the same
    /// obligation: same performative, different content hash.
    Obligation {
        /// The doubly-discharged performative.
        performative: String,
    },
}

/// Evidence returned by [`equivocation`]: the convicted key, the thread,
/// the clause satisfied, and the offending pair as stored (hash-sorted, so
/// evidence is deterministic for a given store state).
///
/// Evidence is *not* yet a transferable proof — the store holds messages,
/// not their detached signatures. Package the pair's signed forms into an
/// [`EquivocationProof`] to convince a third party (REQ-706).
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct EquivocationEvidence {
    pub key: KeyId,
    pub thread: ThreadId,
    pub kind: EquivocationKind,
    pub first: (ContentHash, Message),
    pub second: (ContentHash, Message),
}

/// All messages of a thread, in ascending content-hash order, read through
/// the store's existing public API only: every message is in the causal
/// closure of some frontier leaf (a non-leaf is referenced by a successor,
/// and reference chains are finite and acyclic by content addressing).
fn thread_messages<S: MessageStore>(store: &S, thread: &ThreadId) -> Vec<(ContentHash, Message)> {
    let mut hashes: BTreeSet<ContentHash> = BTreeSet::new();
    let leaves: Vec<ContentHash> = store.frontier(thread).into_iter().cloned().collect();
    for leaf in &leaves {
        for h in store.causal_closure(leaf, thread) {
            hashes.insert(h);
        }
    }
    hashes
        .into_iter()
        .filter_map(|h| {
            store
                .lookup_in_thread(&h, thread)
                .cloned()
                .map(|m| (h, m))
        })
        .collect()
}

/// REQ-705: the monotone, thread-scoped equivocation predicate.
///
/// Returns `Some` evidence iff the store contains two distinct messages in
/// `thread` whose (innermost) sender is canonically `key` and which satisfy
/// clause (a) *choice* or (b) *obligation* of REQ-705 against the dialect's
/// protocol. Message identity is store identity (content hash), so "same
/// performative, different content hash" is exactly "two distinct store
/// entries with the same performative".
///
/// Properties, by construction:
/// - **Monotone / upward-closed**: a pure function of the store's message
///   set; appending messages can only add candidate pairs, never remove
///   one, so `Some` can never revert to `None` (which pair is reported may
///   change, but existence cannot). Once true, forever true.
/// - **Read-only / verdict-neutral** (ADR-703): takes `&S`, calls only the
///   store's read API, and touches no verdict — both members keep the
///   individual verdicts they earned. What a deployment does with a
///   convicted key is action policy above the verdict lattice.
/// - **Canonical identity** (REQ-708): senders are compared as parsed
///   [`KeyId`]s, so `@alice` and `@ed25519:alice` cannot evade detection
///   by spelling. A message whose sender is absent or unparsable is not
///   attributed to anyone and never enters a pair.
pub fn equivocation<S: MessageStore>(
    key: &KeyId,
    thread: &ThreadId,
    store: &S,
    dialect: &Dialect,
) -> Option<EquivocationEvidence> {
    let cp = dialect.causal_protocol.as_ref()?;
    let choices = any_choice_sets(cp);
    let obligations = protocol_performatives(cp);

    // The key's messages in this thread: (hash, performative, message),
    // ascending hash order (deterministic evidence).
    let mut owned: Vec<(ContentHash, String, Message)> = Vec::new();
    for (h, m) in thread_messages(store, thread) {
        let Some(simple) = m.innermost_simple() else {
            continue;
        };
        let Some(sender) = simple.sender() else {
            continue;
        };
        let Ok(sender_id) = KeyId::parse(sender) else {
            continue;
        };
        if &sender_id != key {
            continue;
        }
        let Some(perf) = simple.performative() else {
            continue;
        };
        owned.push((h, String::from(perf.name()), m));
    }

    for i in 0..owned.len() {
        for j in (i + 1)..owned.len() {
            let (h1, p1, m1) = &owned[i];
            let (h2, p2, m2) = &owned[j];
            let kind = if p1 == p2 {
                // (b) obligation: distinct entries ⇒ distinct content
                // hashes (store dedup), same performative — provided the
                // protocol actually obliges that performative.
                if obligations.contains(p1) {
                    Some(EquivocationKind::Obligation {
                        performative: p1.clone(),
                    })
                } else {
                    None
                }
            } else {
                // (a) choice: two distinct alternatives of one choice set.
                choices
                    .iter()
                    .find(|set| set.contains(p1) && set.contains(p2))
                    .map(|set| EquivocationKind::Choice {
                        alternatives: set.clone(),
                    })
            };
            if let Some(kind) = kind {
                return Some(EquivocationEvidence {
                    key: key.clone(),
                    thread: thread.clone(),
                    kind,
                    first: (h1.clone(), m1.clone()),
                    second: (h2.clone(), m2.clone()),
                });
            }
        }
    }
    None
}

// ---------------------------------------------------------------------------
// REQ-706: the transferable proof object (CON-702)
// ---------------------------------------------------------------------------

/// One member of an equivocation proof (CON-702 `member`).
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ProofMember {
    /// A full signed message: the message plus its detached R4 v2
    /// attestation signature (ADR-700). Verification reconstructs the
    /// attestation preimage from the message and its computed content hash
    /// — the full-message-holder arm of REQ-701.
    SignedMessage {
        message: Message,
        signature: Vec<u8>,
    },
    /// A redacted envelope member (CON-702 `member := … | envelope`;
    /// REQ-706). The envelope carries its authenticated header and thread
    /// (REQ-701), so verification runs over exactly the same attestation
    /// preimage as the full-message arm — relabelling a genuine message
    /// into a fake conflict fails at the signature either way, and the
    /// proof discloses no payload for the envelope member (NFR-701).
    Envelope(crate::envelope::RedactedEnvelope),
}

/// The transferable proof object (REQ-706, CON-702):
/// `(equivocation key thread dialect-hash member member)`.
///
/// The proof pins the governing dialect by content hash (SPEC-014 REQ-628)
/// so it can never be verified against a same-named substitute dialect
/// (SPEC-015 review finding 2).
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct EquivocationProof {
    /// The accused key (canonical identity, REQ-708).
    pub key: KeyId,
    /// The thread both members must carry.
    pub thread: String,
    /// Content hash of the governing dialect (`sha256:<hex64>`).
    pub dialect_hash: String,
    /// The offending pair.
    pub first: ProofMember,
    pub second: ProofMember,
}

/// What is structurally wrong with a proof member (full recognition before
/// any semantic action: a member missing a committed header field is
/// rejected, never repaired).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MemberDefect {
    /// The member's message is not a `Simple` message carrying the header
    /// fields the attestation commits to.
    NotSimple,
    /// No `:from` sender field.
    MissingSender,
    /// The sender spelling is not a well-formed key (REQ-708).
    SenderSpelling(KeyIdError),
    /// No `:thread` field.
    MissingThread,
    /// A recipient spelling is not a well-formed key (REQ-708).
    RecipientSpelling(KeyIdError),
}

impl fmt::Display for MemberDefect {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            MemberDefect::NotSimple => f.write_str("member is not a simple message"),
            MemberDefect::MissingSender => f.write_str("member carries no sender"),
            MemberDefect::SenderSpelling(e) => write!(f, "member sender is malformed: {e}"),
            MemberDefect::MissingThread => f.write_str("member carries no thread"),
            MemberDefect::RecipientSpelling(e) => {
                write!(f, "member recipient is malformed: {e}")
            }
        }
    }
}

/// Typed rejection for [`verify_equivocation_proof`] — anything short of a
/// fully-verifying offending pair (LangSec discipline: reject, don't
/// repair). `member` is the 0-based index of the offending member.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EquivocationProofError {
    /// The verifier's dialect carries no content hash, so the pin cannot
    /// be checked (fail closed).
    DialectUnhashed,
    /// The proof pins a different dialect than the verifier holds
    /// (REQ-706: never a same-named substitute).
    DialectHashMismatch { pinned: String, installed: String },
    /// A member does not parse into the committed header shape.
    MalformedMember { member: usize, defect: MemberDefect },
    /// A member's sender is not the accused key (canonical comparison).
    KeyMismatch { member: usize },
    /// A member does not carry the proof's thread.
    ThreadMismatch { member: usize },
    /// The two members are the same message (identical content hash) —
    /// one message is never an equivocation.
    IdenticalMembers,
    /// A member's signature failed R4 v2 verification.
    Signature { member: usize, error: AttestError },
    /// Both members verify but the pair is compatible under the pinned
    /// dialect: neither two alternatives of one choice point nor a double
    /// discharge of one obligation.
    CompatiblePair { first: String, second: String },
}

impl fmt::Display for EquivocationProofError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::DialectUnhashed => {
                f.write_str("verifier's dialect carries no content hash; cannot check the pin")
            }
            Self::DialectHashMismatch { pinned, installed } => write!(
                f,
                "dialect hash mismatch: proof pins {pinned}, verifier holds {installed}"
            ),
            Self::MalformedMember { member, defect } => {
                write!(f, "member {member} malformed: {defect}")
            }
            Self::KeyMismatch { member } => {
                write!(f, "member {member} is not by the accused key")
            }
            Self::ThreadMismatch { member } => {
                write!(f, "member {member} does not carry the proof's thread")
            }
            Self::IdenticalMembers => f.write_str("members are the same message"),
            Self::Signature { member, error } => {
                write!(f, "member {member} signature invalid: {error}")
            }
            Self::CompatiblePair { first, second } => write!(
                f,
                "pair ({first}, {second}) is compatible under the pinned dialect"
            ),
        }
    }
}

/// Reconstruct the R4 v2 attestation header a full-message holder signs and
/// verifies (REQ-701's full-message arm): every committed field read from
/// the message, the content hash computed from its canonical bytes.
///
/// Pure. Rejects (typed) any message missing a committed field — a header
/// that cannot be reconstructed in full is never guessed at.
pub fn attestation_header_for(message: &Message) -> Result<AttestationHeader, MemberDefect> {
    let Message::Simple {
        performative,
        thread,
        sender,
        caused_by,
        ..
    } = message
    else {
        return Err(MemberDefect::NotSimple);
    };
    let sender = sender.as_deref().ok_or(MemberDefect::MissingSender)?;
    let from = KeyId::parse(sender).map_err(MemberDefect::SenderSpelling)?;
    let thread = thread.as_deref().ok_or(MemberDefect::MissingThread)?;
    let mut to = BTreeSet::new();
    for r in message.recipient_set() {
        to.insert(KeyId::parse(r).map_err(MemberDefect::RecipientSpelling)?);
    }
    Ok(AttestationHeader {
        content_hash: message_content_hash(message),
        performative: String::from(performative.name()),
        from,
        to,
        thread: String::from(thread),
        caused_by: caused_by.clone(),
    })
}

/// A member that passed structural + cryptographic checks.
struct CheckedMember {
    performative: String,
    content_hash: String,
}

fn check_member(
    member: &ProofMember,
    index: usize,
    proof: &EquivocationProof,
    signer: &dyn Signer,
) -> Result<CheckedMember, EquivocationProofError> {
    // Both member classes reconstruct the same attestation header shape
    // (REQ-701): a full message from its fields and computed content hash,
    // an envelope from its own authenticated header.
    let (header, signature): (AttestationHeader, &[u8]) = match member {
        ProofMember::SignedMessage { message, signature } => {
            let header = attestation_header_for(message).map_err(|defect| {
                EquivocationProofError::MalformedMember {
                    member: index,
                    defect,
                }
            })?;
            (header, signature)
        }
        ProofMember::Envelope(envelope) => (envelope.header.clone(), &envelope.signature),
    };
    // Canonical key identity (REQ-708): alias spellings of the accused key
    // are one identity; a different identity is a typed mismatch.
    if header.from != proof.key {
        return Err(EquivocationProofError::KeyMismatch { member: index });
    }
    if header.thread != proof.thread {
        return Err(EquivocationProofError::ThreadMismatch { member: index });
    }
    // R4 v2: the signature verifies under the canonical key over the
    // reconstructed attestation preimage — relabelling a genuine message
    // into a fake conflict (other thread, other recipients, other type)
    // changes the preimage and dies here (ADR-700).
    verify_attestation_v2(signer, &proof.key, &header, signature).map_err(|error| {
        EquivocationProofError::Signature {
            member: index,
            error,
        }
    })?;
    Ok(CheckedMember {
        performative: header.performative,
        content_hash: header.content_hash,
    })
}

/// REQ-706: verify an equivocation proof from the pair and the pinned
/// dialect alone — no store, no third-party testimony.
///
/// `signer` embodies signature verification for the accused key (the same
/// [`Signer`] convention as the rest of the R4 path).
///
/// Checks, in order (CON-702), each failure a typed rejection:
/// 1. the proof's dialect hash matches `dialect.hash` (the *pinned*
///    dialect, never a same-named substitute);
/// 2. both members parse into the committed header shape;
/// 3. both members are by the accused key (canonical identity) and carry
///    the proof's thread;
/// 4. both signatures verify under the key via the existing R4 v2
///    full-message path ([`verify_attestation_v2`]);
/// 5. the members are two *distinct* messages; and
/// 6. the pair satisfies clause (a) or (b) of REQ-705 against the pinned
///    dialect's protocol.
///
/// On success returns the convicted [`KeyId`].
pub fn verify_equivocation_proof(
    proof: &EquivocationProof,
    dialect: &Dialect,
    signer: &dyn Signer,
) -> Result<KeyId, EquivocationProofError> {
    // 1. Pinned dialect only (review finding 2). A hashless dialect cannot
    // witness the pin: fail closed.
    let installed = dialect
        .hash
        .as_deref()
        .ok_or(EquivocationProofError::DialectUnhashed)?;
    if installed != proof.dialect_hash {
        return Err(EquivocationProofError::DialectHashMismatch {
            pinned: proof.dialect_hash.clone(),
            installed: String::from(installed),
        });
    }

    // 2–4. Per-member structural and cryptographic checks.
    let a = check_member(&proof.first, 0, proof, signer)?;
    let b = check_member(&proof.second, 1, proof, signer)?;

    // 5. Two distinct messages (distinct canonical content).
    if a.content_hash == b.content_hash {
        return Err(EquivocationProofError::IdenticalMembers);
    }

    // 6. The pair conflicts under the pinned dialect (REQ-705 (a)/(b)).
    let conflicting = match dialect.causal_protocol.as_ref() {
        None => false, // no protocol ⇒ no choice points, no obligations
        Some(cp) => {
            if a.performative == b.performative {
                protocol_performatives(cp).contains(&a.performative)
            } else {
                any_choice_sets(cp)
                    .iter()
                    .any(|set| set.contains(&a.performative) && set.contains(&b.performative))
            }
        }
    };
    if !conflicting {
        return Err(EquivocationProofError::CompatiblePair {
            first: a.performative,
            second: b.performative,
        });
    }

    Ok(proof.key.clone())
}

// ---------------------------------------------------------------------------
// REQ-707: choice-transparency lint (opt-in, advisory)
// ---------------------------------------------------------------------------

/// Advisory warning: the alternatives of a choice point share no common
/// recipient role other than the chooser, so no single honest endpoint is
/// guaranteed to witness a choice equivocation locally — detection relies
/// on proof gossip. A warning, never an [`crate::role::R6Violation`].
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ChoiceTransparencyWarning {
    /// The choice point's alternatives.
    pub alternatives: BTreeSet<String>,
    /// The chooser role (the alternatives' common sender).
    pub chooser: String,
}

impl fmt::Display for ChoiceTransparencyWarning {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "choice-transparency: alternatives [{}] of chooser '{}' share no \
             common recipient role other than the chooser; a choice \
             equivocation has no guaranteed local witness",
            self.alternatives
                .iter()
                .map(String::as_str)
                .collect::<Vec<_>>()
                .join(", "),
            self.chooser
        )
    }
}

/// REQ-707: the opt-in choice-transparency lint, companion to the R6
/// dialect checks (`crate::r6::r6_violations`) but advisory by design.
///
/// With `enabled == false` (the default posture) the lint is silent.
/// When enabled, it warns for every `(any …)` choice point whose
/// alternatives share no common recipient role beyond the chooser.
/// Shared-recipient dialects (OAuth's branches both address `client`) are
/// lint-clean. Choice points with unannotated alternatives or incoherent
/// senders are skipped — those are R6's findings (REQ-601/REQ-603), not
/// this lint's.
pub fn choice_transparency_lint(d: &Dialect, enabled: bool) -> Vec<ChoiceTransparencyWarning> {
    if !enabled {
        return Vec::new();
    }
    let Some(cp) = &d.causal_protocol else {
        return Vec::new();
    };
    let annotations: BTreeMap<&str, &RoleAnnotation> = d
        .performatives
        .iter()
        .filter_map(|p| p.role.as_ref().map(|ann| (p.name.as_str(), ann)))
        .collect();

    let mut warnings = Vec::new();
    for alternatives in any_choice_sets(cp) {
        let anns: Option<Vec<&RoleAnnotation>> = alternatives
            .iter()
            .map(|a| annotations.get(a.as_str()).copied())
            .collect();
        let Some(anns) = anns else {
            continue; // unannotated alternative: REQ-601's finding
        };
        let senders: BTreeSet<&str> = anns.iter().map(|a| a.from.as_str()).collect();
        if senders.len() != 1 {
            continue; // incoherent chooser: REQ-603's finding
        }
        let chooser = *senders.first().expect("len checked");
        let mut common: BTreeSet<&str> = anns[0].to.iter().map(String::as_str).collect();
        for ann in &anns[1..] {
            let to: BTreeSet<&str> = ann.to.iter().map(String::as_str).collect();
            common = common.intersection(&to).copied().collect();
        }
        common.remove(chooser);
        if common.is_empty() {
            warnings.push(ChoiceTransparencyWarning {
                alternatives,
                chooser: String::from(chooser),
            });
        }
    }
    warnings
}

// ---------------------------------------------------------------------------
// Tests (TEST-705, TEST-706, TEST-707)
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::attest::sign_attestation_v2;
    use crate::dialect::{Dialect, PerformativeDef, ResourceBounds};
    use crate::message::{CausedBy, Performative, Recipients};
    use crate::protocol::{verify_causal, StepDecl, VerificationResult};
    use crate::role::{RoleCardinality, RoleDecl};
    use crate::sexpr::Atom;
    use crate::store::ThreadedMessageStore;
    use alloc::string::ToString;
    use alloc::vec;

    // ---- fixtures ----

    fn single(name: &str) -> NodeRef {
        NodeRef::Single(name.to_string())
    }

    fn any(names: &[&str]) -> NodeRef {
        NodeRef::Any(names.iter().map(|s| s.to_string()).collect())
    }

    fn step(name: &str, preds: Vec<NodeRef>, succs: Vec<NodeRef>) -> (String, StepDecl) {
        (
            name.to_string(),
            StepDecl {
                performative: name.to_string(),
                predecessors: preds,
                successors: succs,
            },
        )
    }

    fn perf_def(name: &str, role: Option<RoleAnnotation>) -> PerformativeDef {
        PerformativeDef {
            name: name.to_string(),
            params: Vec::new(),
            template: SExpr::Atom(Atom::Symbol("t".to_string())),
            role,
        }
    }

    fn ann(from: &str, to: &[&str]) -> RoleAnnotation {
        RoleAnnotation {
            from: from.to_string(),
            to: to.iter().map(|s| s.to_string()).collect(),
        }
    }

    fn dialect(
        roles: &[&str],
        perfs: Vec<PerformativeDef>,
        steps: Vec<(String, StepDecl)>,
    ) -> Dialect {
        let mut d = Dialect {
            roles: roles
                .iter()
                .map(|n| RoleDecl {
                    name: n.to_string(),
                    cardinality: RoleCardinality::Singleton,
                })
                .collect(),
            causal_locality: Default::default(),
            name: "equiv-test".to_string(),
            extends: Vec::new(),
            author: None,
            performatives: perfs,
            resources: ResourceBounds {
                max_depth: 8,
                max_expansion_size: 512,
                verification_time_ms: 10,
            },
            examples: Vec::new(),
            signature: None,
            hash: None,
            protocol: None,
            causal_protocol: Some(CausalProtocol {
                steps: steps.into_iter().collect(),
            }),
            shapes: Vec::new(),
        };
        d.hash = Some(crate::canonical::dialect_hash(&d));
        d
    }

    /// begin → (any offer refuse); offer → settle. `offer`/`refuse` are one
    /// choice point; `settle` is a compatible successor of `offer`.
    fn choice_dialect() -> Dialect {
        dialect(
            &["chooser", "peer"],
            vec![
                perf_def("offer", None),
                perf_def("refuse", None),
                perf_def("settle", None),
            ],
            vec![
                step("begin", vec![], vec![any(&["offer", "refuse"])]),
                step("offer", vec![single("begin")], vec![single("settle")]),
                step("refuse", vec![single("begin")], vec![]),
                step("settle", vec![single("offer")], vec![]),
            ],
        )
    }

    fn msg(perf: &str, sender: &str, thread: &str, content: &str) -> Message {
        Message::Simple {
            performative: Performative::Custom(perf.to_string()),
            recipient: Some(Recipients::One("@bob".to_string())),
            content: SExpr::Atom(Atom::Str(content.to_string())),
            params: Vec::new(),
            thread: Some(thread.to_string()),
            sender: Some(sender.to_string()),
            caused_by: Some(CausedBy::Begin),
        }
    }

    fn hash(s: &str) -> ContentHash {
        ContentHash(s.to_string())
    }

    fn thread(s: &str) -> ThreadId {
        ThreadId(s.to_string())
    }

    fn alice() -> KeyId {
        KeyId::parse("@alice").unwrap()
    }

    // ---- TEST-705: the predicate ----

    #[test]
    fn choice_equivocation_flips_the_predicate() {
        let d = choice_dialect();
        let mut store = ThreadedMessageStore::new();
        store.append(hash("h1"), thread("t1"), msg("offer", "@alice", "t1", "a"));
        store.append(hash("h2"), thread("t1"), msg("refuse", "@alice", "t1", "b"));

        let ev = equivocation(&alice(), &thread("t1"), &store, &d).expect("detected");
        assert_eq!(ev.key, alice());
        assert_eq!(ev.thread, thread("t1"));
        assert_eq!(
            ev.kind,
            EquivocationKind::Choice {
                alternatives: ["offer", "refuse"].iter().map(|s| s.to_string()).collect(),
            }
        );
        let pair: BTreeSet<&str> = [ev.first.0 .0.as_str(), ev.second.0 .0.as_str()]
            .into_iter()
            .collect();
        assert_eq!(pair, ["h1", "h2"].into_iter().collect());
    }

    #[test]
    fn obligation_equivocation_flips_the_predicate() {
        let d = choice_dialect();
        let mut store = ThreadedMessageStore::new();
        // Two distinct discharges of `offer`: same performative and
        // occupant, different content (hence different content hash).
        store.append(hash("h1"), thread("t1"), msg("offer", "@alice", "t1", "a"));
        store.append(hash("h2"), thread("t1"), msg("offer", "@alice", "t1", "b"));

        let ev = equivocation(&alice(), &thread("t1"), &store, &d).expect("detected");
        assert_eq!(
            ev.kind,
            EquivocationKind::Obligation {
                performative: "offer".to_string(),
            }
        );
    }

    /// REQ-708: spelling aliases cannot evade the predicate.
    #[test]
    fn alias_key_spellings_cannot_evade_detection() {
        let d = choice_dialect();
        let mut store = ThreadedMessageStore::new();
        store.append(hash("h1"), thread("t1"), msg("offer", "@alice", "t1", "a"));
        store.append(
            hash("h2"),
            thread("t1"),
            msg("refuse", "@ed25519:alice", "t1", "b"),
        );
        assert!(equivocation(&alice(), &thread("t1"), &store, &d).is_some());
    }

    /// TEST-705: adding messages never unflips the predicate (monotone).
    #[test]
    fn predicate_is_monotone_under_store_growth() {
        let d = choice_dialect();
        let mut store = ThreadedMessageStore::new();
        store.append(hash("h1"), thread("t1"), msg("offer", "@alice", "t1", "a"));
        assert!(equivocation(&alice(), &thread("t1"), &store, &d).is_none());

        store.append(hash("h2"), thread("t1"), msg("refuse", "@alice", "t1", "b"));
        assert!(equivocation(&alice(), &thread("t1"), &store, &d).is_some());

        // Grow the store every which way: other keys, other performatives,
        // even more equivocation. The predicate never reverts.
        let later = [
            ("h3", msg("settle", "@bob", "t1", "c")),
            ("h4", msg("offer", "@carol", "t1", "d")),
            ("h5", msg("offer", "@alice", "t1", "e")),
            ("h6", msg("refuse", "@alice", "t1", "f")),
        ];
        for (h, m) in later {
            store.append(hash(h), thread("t1"), m);
            assert!(
                equivocation(&alice(), &thread("t1"), &store, &d).is_some(),
                "predicate reverted after appending {h}"
            );
        }
    }

    /// TEST-705 / ADR-703: detection does not alter any verdict — both
    /// members of the pair stay individually Valid.
    #[test]
    fn members_verdicts_remain_valid() {
        let d = choice_dialect();
        let cp = d.causal_protocol.as_ref().unwrap();
        let mut store = ThreadedMessageStore::new();
        let m1 = msg("offer", "@alice", "t1", "a");
        let m2 = msg("refuse", "@alice", "t1", "b");
        store.append(hash("h1"), thread("t1"), m1.clone());
        store.append(hash("h2"), thread("t1"), m2.clone());

        let verdict = |m: &Message| {
            verify_causal(
                m.performative().unwrap().name(),
                m.caused_by(),
                &store,
                cp,
                &thread("t1"),
            )
        };
        assert_eq!(verdict(&m1), VerificationResult::Valid);
        assert_eq!(verdict(&m2), VerificationResult::Valid);

        assert!(equivocation(&alice(), &thread("t1"), &store, &d).is_some());

        // Read-only detection: the verdicts after are the verdicts before.
        assert_eq!(verdict(&m1), VerificationResult::Valid);
        assert_eq!(verdict(&m2), VerificationResult::Valid);
    }

    #[test]
    fn distinct_keys_are_not_an_equivocating_pair() {
        let d = choice_dialect();
        let mut store = ThreadedMessageStore::new();
        store.append(hash("h1"), thread("t1"), msg("offer", "@alice", "t1", "a"));
        store.append(hash("h2"), thread("t1"), msg("refuse", "@bob", "t1", "b"));
        assert!(equivocation(&alice(), &thread("t1"), &store, &d).is_none());
        assert!(
            equivocation(&KeyId::parse("@bob").unwrap(), &thread("t1"), &store, &d).is_none()
        );
    }

    #[test]
    fn predicate_is_thread_scoped() {
        let d = choice_dialect();
        let mut store = ThreadedMessageStore::new();
        store.append(hash("h1"), thread("t1"), msg("offer", "@alice", "t1", "a"));
        store.append(hash("h2"), thread("t2"), msg("refuse", "@alice", "t2", "b"));
        assert!(equivocation(&alice(), &thread("t1"), &store, &d).is_none());
        assert!(equivocation(&alice(), &thread("t2"), &store, &d).is_none());
    }

    #[test]
    fn sequential_steps_are_compatible_not_equivocation() {
        // offer then its declared successor settle, both by alice: fine.
        let d = choice_dialect();
        let mut store = ThreadedMessageStore::new();
        store.append(hash("h1"), thread("t1"), msg("offer", "@alice", "t1", "a"));
        store.append(hash("h2"), thread("t1"), msg("settle", "@alice", "t1", "b"));
        assert!(equivocation(&alice(), &thread("t1"), &store, &d).is_none());
    }

    #[test]
    fn same_key_suite_variant_is_a_distinct_identity() {
        // REQ-708: same bytes under another suite is a different identity;
        // its messages do not pair with the ed25519 identity's.
        let d = choice_dialect();
        let mut store = ThreadedMessageStore::new();
        store.append(hash("h1"), thread("t1"), msg("offer", "@alice", "t1", "a"));
        store.append(
            hash("h2"),
            thread("t1"),
            msg("refuse", "@pq-frodo:alice", "t1", "b"),
        );
        assert!(equivocation(&alice(), &thread("t1"), &store, &d).is_none());
    }

    #[test]
    fn dialect_without_protocol_never_detects() {
        let mut d = choice_dialect();
        d.causal_protocol = None;
        let mut store = ThreadedMessageStore::new();
        store.append(hash("h1"), thread("t1"), msg("offer", "@alice", "t1", "a"));
        store.append(hash("h2"), thread("t1"), msg("refuse", "@alice", "t1", "b"));
        assert!(equivocation(&alice(), &thread("t1"), &store, &d).is_none());
    }

    // ---- TEST-706: the proof object ----

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

    const ALICE_SIGNER: TestSigner = TestSigner { secret: b"alice" };
    const BOB_SIGNER: TestSigner = TestSigner { secret: b"bob" };

    fn signed_member(m: Message, signer: &dyn Signer) -> ProofMember {
        let header = attestation_header_for(&m).unwrap();
        let signature = sign_attestation_v2(signer, &header).unwrap();
        ProofMember::SignedMessage {
            message: m,
            signature,
        }
    }

    fn proof_over(d: &Dialect, m1: Message, m2: Message) -> EquivocationProof {
        EquivocationProof {
            key: alice(),
            thread: "t1".to_string(),
            dialect_hash: d.hash.clone().unwrap(),
            first: signed_member(m1, &ALICE_SIGNER),
            second: signed_member(m2, &ALICE_SIGNER),
        }
    }

    #[test]
    fn choice_proof_verifies_from_pair_and_dialect_alone() {
        // No store exists anywhere in this test (REQ-706).
        let d = choice_dialect();
        let proof = proof_over(
            &d,
            msg("offer", "@alice", "t1", "a"),
            msg("refuse", "@alice", "t1", "b"),
        );
        assert_eq!(
            verify_equivocation_proof(&proof, &d, &ALICE_SIGNER),
            Ok(alice())
        );
    }

    #[test]
    fn obligation_proof_verifies() {
        let d = choice_dialect();
        let proof = proof_over(
            &d,
            msg("offer", "@alice", "t1", "a"),
            msg("offer", "@alice", "t1", "b"),
        );
        assert_eq!(
            verify_equivocation_proof(&proof, &d, &ALICE_SIGNER),
            Ok(alice())
        );
    }

    /// REQ-708: an alias spelling in a member is the same canonical
    /// identity — the proof still convicts.
    #[test]
    fn alias_spelled_member_still_convicts() {
        let d = choice_dialect();
        let proof = proof_over(
            &d,
            msg("offer", "@alice", "t1", "a"),
            msg("refuse", "@ed25519:alice", "t1", "b"),
        );
        assert_eq!(
            verify_equivocation_proof(&proof, &d, &ALICE_SIGNER),
            Ok(alice())
        );
    }

    #[test]
    fn forged_pair_different_keys_rejected() {
        let d = choice_dialect();
        let mut proof = proof_over(
            &d,
            msg("offer", "@alice", "t1", "a"),
            msg("refuse", "@alice", "t1", "b"),
        );
        // Bob's genuine message swapped in as the second member.
        proof.second = signed_member(msg("refuse", "@bob", "t1", "b"), &BOB_SIGNER);
        assert_eq!(
            verify_equivocation_proof(&proof, &d, &ALICE_SIGNER),
            Err(EquivocationProofError::KeyMismatch { member: 1 })
        );
    }

    #[test]
    fn forged_pair_different_threads_rejected() {
        let d = choice_dialect();
        let mut proof = proof_over(
            &d,
            msg("offer", "@alice", "t1", "a"),
            msg("refuse", "@alice", "t1", "b"),
        );
        // A genuine message from another thread cannot be relabelled into
        // this conflict: its authenticated thread differs.
        proof.second = signed_member(msg("refuse", "@alice", "t2", "b"), &ALICE_SIGNER);
        assert_eq!(
            verify_equivocation_proof(&proof, &d, &ALICE_SIGNER),
            Err(EquivocationProofError::ThreadMismatch { member: 1 })
        );
    }

    #[test]
    fn wrong_dialect_hash_rejected() {
        let d = choice_dialect();
        let mut proof = proof_over(
            &d,
            msg("offer", "@alice", "t1", "a"),
            msg("refuse", "@alice", "t1", "b"),
        );
        proof.dialect_hash = "sha256:0000000000000000000000000000000000000000000000000000000000000000".to_string();
        assert!(matches!(
            verify_equivocation_proof(&proof, &d, &ALICE_SIGNER),
            Err(EquivocationProofError::DialectHashMismatch { .. })
        ));
    }

    #[test]
    fn unhashed_dialect_fails_closed() {
        let mut d = choice_dialect();
        let proof = proof_over(
            &d,
            msg("offer", "@alice", "t1", "a"),
            msg("refuse", "@alice", "t1", "b"),
        );
        d.hash = None;
        assert_eq!(
            verify_equivocation_proof(&proof, &d, &ALICE_SIGNER),
            Err(EquivocationProofError::DialectUnhashed)
        );
    }

    #[test]
    fn compatible_pair_rejected() {
        // offer → settle is the declared sequence, not an equivocation.
        let d = choice_dialect();
        let proof = proof_over(
            &d,
            msg("offer", "@alice", "t1", "a"),
            msg("settle", "@alice", "t1", "b"),
        );
        assert_eq!(
            verify_equivocation_proof(&proof, &d, &ALICE_SIGNER),
            Err(EquivocationProofError::CompatiblePair {
                first: "offer".to_string(),
                second: "settle".to_string(),
            })
        );
    }

    #[test]
    fn identical_members_rejected() {
        let d = choice_dialect();
        let proof = proof_over(
            &d,
            msg("offer", "@alice", "t1", "a"),
            msg("offer", "@alice", "t1", "a"),
        );
        assert_eq!(
            verify_equivocation_proof(&proof, &d, &ALICE_SIGNER),
            Err(EquivocationProofError::IdenticalMembers)
        );
    }

    #[test]
    fn tampered_member_signature_dies() {
        let d = choice_dialect();
        let mut proof = proof_over(
            &d,
            msg("offer", "@alice", "t1", "a"),
            msg("refuse", "@alice", "t1", "b"),
        );
        // Re-content the second member after signing: the recomputed
        // content hash changes the attestation preimage.
        if let ProofMember::SignedMessage { message, .. } = &mut proof.second {
            if let Message::Simple { content, .. } = message {
                *content = SExpr::Atom(Atom::Str("tampered".to_string()));
            }
        }
        assert_eq!(
            verify_equivocation_proof(&proof, &d, &ALICE_SIGNER),
            Err(EquivocationProofError::Signature {
                member: 1,
                error: AttestError::InvalidSignature,
            })
        );
    }

    // ---- REQ-706 + REQ-700..701: envelope proof members ----

    fn envelope_member(m: Message, signer: &dyn Signer) -> ProofMember {
        let header = attestation_header_for(&m).unwrap();
        let signature = sign_attestation_v2(signer, &header).unwrap();
        ProofMember::Envelope(crate::envelope::redact(&m, signature).unwrap())
    }

    #[test]
    fn envelope_member_convicts_without_payload() {
        // The second member travels as a redacted envelope: the proof
        // still verifies from the pair and the pinned dialect alone, and
        // the envelope member discloses no payload field.
        let d = choice_dialect();
        let mut proof = proof_over(
            &d,
            msg("offer", "@alice", "t1", "a"),
            msg("refuse", "@alice", "t1", "b"),
        );
        proof.second = envelope_member(msg("refuse", "@alice", "t1", "payload-b"), &ALICE_SIGNER);
        if let ProofMember::Envelope(env) = &proof.second {
            assert!(
                !env.to_sexpr().to_string().contains("payload-b"),
                "envelope member must disclose no payload field (NFR-701)"
            );
        }
        assert_eq!(
            verify_equivocation_proof(&proof, &d, &ALICE_SIGNER),
            Ok(alice())
        );
    }

    #[test]
    fn all_envelope_pair_convicts() {
        let d = choice_dialect();
        let mut proof = proof_over(
            &d,
            msg("offer", "@alice", "t1", "a"),
            msg("offer", "@alice", "t1", "b"),
        );
        proof.first = envelope_member(msg("offer", "@alice", "t1", "a"), &ALICE_SIGNER);
        proof.second = envelope_member(msg("offer", "@alice", "t1", "b"), &ALICE_SIGNER);
        assert_eq!(
            verify_equivocation_proof(&proof, &d, &ALICE_SIGNER),
            Ok(alice())
        );
    }

    #[test]
    fn relabelled_envelope_member_fails_at_the_signature() {
        // An envelope's thread is its authenticated field (REQ-701):
        // rewriting it to frame a cross-thread conflict changes the
        // attestation preimage, so the forgery dies at the signature —
        // never at a repairable policy check.
        let d = choice_dialect();
        let mut proof = proof_over(
            &d,
            msg("offer", "@alice", "t1", "a"),
            msg("refuse", "@alice", "t2", "b"), // genuinely from thread t2
        );
        let ProofMember::SignedMessage { message, .. } = proof.second.clone() else {
            unreachable!()
        };
        let mut env = match envelope_member(message, &ALICE_SIGNER) {
            ProofMember::Envelope(env) => env,
            _ => unreachable!(),
        };
        env.header.thread = "t1".to_string(); // relabel into the conflict
        proof.second = ProofMember::Envelope(env);
        assert_eq!(
            verify_equivocation_proof(&proof, &d, &ALICE_SIGNER),
            Err(EquivocationProofError::Signature {
                member: 1,
                error: AttestError::InvalidSignature,
            })
        );
    }

    #[test]
    fn envelope_member_by_another_key_is_a_key_mismatch() {
        let d = choice_dialect();
        let mut proof = proof_over(
            &d,
            msg("offer", "@alice", "t1", "a"),
            msg("refuse", "@alice", "t1", "b"),
        );
        proof.second = envelope_member(msg("refuse", "@bob", "t1", "b"), &BOB_SIGNER);
        assert_eq!(
            verify_equivocation_proof(&proof, &d, &ALICE_SIGNER),
            Err(EquivocationProofError::KeyMismatch { member: 1 })
        );
    }

    #[test]
    fn member_missing_committed_fields_rejected() {
        let d = choice_dialect();
        let mut senderless = msg("offer", "@alice", "t1", "a");
        if let Message::Simple { sender, .. } = &mut senderless {
            *sender = None;
        }
        let proof = EquivocationProof {
            key: alice(),
            thread: "t1".to_string(),
            dialect_hash: d.hash.clone().unwrap(),
            first: ProofMember::SignedMessage {
                message: senderless,
                signature: vec![0u8; 32],
            },
            second: signed_member(msg("refuse", "@alice", "t1", "b"), &ALICE_SIGNER),
        };
        assert_eq!(
            verify_equivocation_proof(&proof, &d, &ALICE_SIGNER),
            Err(EquivocationProofError::MalformedMember {
                member: 0,
                defect: MemberDefect::MissingSender,
            })
        );
    }

    // ---- TEST-707: the transparency lint ----

    /// The OAuth fragment of r6.rs, parameterised on the abort branch's
    /// recipient: branches `login`/`abort` are one `(any …)` choice by
    /// `server`; with `abort :to client` both branches share recipient
    /// `client` (the paper's shared-recipient shape).
    fn oauth_like(abort_to: &[&str]) -> Dialect {
        dialect(
            &["server", "client", "authoriser"],
            vec![
                perf_def("login", Some(ann("server", &["client"]))),
                perf_def("abort", Some(ann("server", abort_to))),
                perf_def("passwd", Some(ann("client", &["authoriser"]))),
                perf_def("auth", Some(ann("authoriser", &["server"]))),
                perf_def("quit", Some(ann("client", &["authoriser"]))),
            ],
            vec![
                step("begin", vec![], vec![any(&["login", "abort"])]),
                step("login", vec![single("begin")], vec![single("passwd")]),
                step("abort", vec![single("begin")], vec![single("quit")]),
                step("passwd", vec![single("login")], vec![single("auth")]),
                step("auth", vec![single("passwd")], vec![]),
                step("quit", vec![single("abort")], vec![]),
            ],
        )
    }

    #[test]
    fn shared_recipient_choice_is_lint_clean() {
        // OAuth-style: both branches address `client` — a common witness
        // exists, nothing to warn about.
        let warnings = choice_transparency_lint(&oauth_like(&["client"]), true);
        assert_eq!(warnings, Vec::new());
    }

    #[test]
    fn disjoint_recipient_choice_warns() {
        let warnings = choice_transparency_lint(&oauth_like(&["authoriser"]), true);
        assert_eq!(
            warnings,
            vec![ChoiceTransparencyWarning {
                alternatives: ["login", "abort"].iter().map(|s| s.to_string()).collect(),
                chooser: "server".to_string(),
            }]
        );
    }

    #[test]
    fn flag_off_suppresses_the_lint() {
        assert_eq!(
            choice_transparency_lint(&oauth_like(&["authoriser"]), false),
            Vec::new()
        );
    }

    #[test]
    fn chooser_as_only_common_recipient_still_warns() {
        // Both branches carry the chooser itself as the only shared
        // recipient: no *other* endpoint is a guaranteed witness.
        let d = dialect(
            &["server", "client", "authoriser"],
            vec![
                perf_def("login", Some(ann("server", &["server", "client"]))),
                perf_def("abort", Some(ann("server", &["server", "authoriser"]))),
            ],
            vec![
                step("begin", vec![], vec![any(&["login", "abort"])]),
                step("login", vec![single("begin")], vec![]),
                step("abort", vec![single("begin")], vec![]),
            ],
        );
        let warnings = choice_transparency_lint(&d, true);
        assert_eq!(warnings.len(), 1);
        assert_eq!(warnings[0].chooser, "server");
    }

    #[test]
    fn unannotated_or_incoherent_choices_are_not_this_lints_finding() {
        // One branch unannotated → skipped (REQ-601's finding).
        let mut d = oauth_like(&["authoriser"]);
        d.performatives[1].role = None; // abort
        assert_eq!(choice_transparency_lint(&d, true), Vec::new());

        // Incoherent senders → skipped (REQ-603's finding).
        let mut d = oauth_like(&["authoriser"]);
        d.performatives[1].role = Some(ann("client", &["authoriser"]));
        assert_eq!(choice_transparency_lint(&d, true), Vec::new());
    }

    // ---- shared helpers ----

    #[test]
    fn message_content_hash_is_canonical_and_content_sensitive() {
        let m1 = msg("offer", "@alice", "t1", "a");
        let m2 = msg("offer", "@alice", "t1", "b");
        let h1 = message_content_hash(&m1);
        assert_eq!(h1, message_content_hash(&m1), "deterministic");
        assert_ne!(h1, message_content_hash(&m2), "content-sensitive");
        assert!(h1.starts_with("sha256:") && h1.len() == 7 + 64);
    }
}
