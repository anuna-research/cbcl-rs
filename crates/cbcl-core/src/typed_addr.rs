//! SPEC-017 seed (architecture spike — NOT wired into any hash path).
//!
//! A standalone prototype validating that CBCL's content address can move
//! from a flat `sha256:H(canonical-bytes)` (see
//! `equivocation::message_content_hash`) to a **canonical Merkle commitment
//! over a message's fields**, enabling authenticated *selective disclosure*
//! (field-openings) and subsuming the SPEC-015 redacted-envelope header
//! binding.
//!
//! Nothing here is called by `message_content_hash`, `store.rs`, `envelope.rs`,
//! or `attest.rs`; the module is entirely additive so the existing flat-hash
//! wiring keeps its exact behaviour while this design is evaluated.
//!
//! # 1. Openable field schema (fixed canonical order)
//!
//! A `Message::Simple` decomposes into six leaves in a FIXED order. The order
//! is part of the construction (like `canonical.rs`'s child order) and must
//! not change once published:
//!
//! | id | [`FieldId`]     | source on `Message::Simple`      |
//! |----|-----------------|----------------------------------|
//! | 0  | `Performative`  | `performative` (the *type*)      |
//! | 1  | `From`          | `sender` (the signer/speaker)    |
//! | 2  | `To`            | `recipient_set()` (audience)     |
//! | 3  | `CausedBy`      | `caused_by`                      |
//! | 4  | `Thread`        | `thread`                         |
//! | 5  | `Payload`       | `content` + `params`             |
//!
//! These are exactly the SPEC-015 envelope header fields (performative, from,
//! to, caused-by, thread) plus the payload the envelope redacts — so opening
//! leaves 0–4 reproduces the redacted envelope, and leaf 5 is the payload a
//! completion decider (REQ-703) additionally needs.
//!
//! Non-`Simple` messages are handled totally (never panic): the whole
//! `SExpr::from(msg)` becomes the `Payload` leaf, other leaves empty, so a
//! root always exists. Refining the schema for `Wrapped`/`Dialect`/`Meta` is
//! future work; the safety-level fields the envelope reads only exist on the
//! innermost `Simple` anyway.
//!
//! # 2. Deterministic canonical Merkle tree
//!
//! **Leaf.** For field `i` with canonical field S-expression `field_i`:
//!
//! ```text
//! leaf_i = SHA256( 0x00 ‖ canonical_encode( ( <domain-tag-i> field_i ) ) )
//! ```
//!
//! The domain tag and the field value are wrapped in a *two-element list* and
//! run through the existing [`canonical_encode`]: RFC 9804's length-prefixed
//! framing makes `(tag field)` an unambiguous, injective encoding of the pair
//! — there is no concatenation-boundary ambiguity to exploit, and the fixed
//! per-field tag domain-separates leaf 0's bytes from leaf 5's even when the
//! field values coincide. This is the exact "compose with the existing
//! `canonical_encode` per field" property required: `field_i` is itself built
//! from the same atom/list encoding the message layer already uses.
//!
//! **Tree.** A fixed-arity (binary) tree over the fixed six leaves. Because
//! the leaf count is a protocol constant (6), the tree *shape* is constant and
//! identical for every message — so there is no Merkle second-preimage / arity
//! ambiguity (the classic duplicate-last-leaf forgery needs an attacker-chosen
//! leaf count; here it cannot vary):
//!
//! ```text
//! n0 = H(l0,l1)   n1 = H(l2,l3)   n2 = H(l4,l5)
//! m0 = H(n0,n1)
//! root = H(m0, n2)          where  H(a,b) = SHA256( 0x01 ‖ a ‖ b )
//! ```
//!
//! Leaves carry the `0x00` prefix, internal nodes `0x01`, so a 32-byte leaf
//! digest can never be reinterpreted as an internal node (leaf/node domain
//! separation).
//!
//! **Guarantees.**
//! - *Same message ⇒ same root*: every step is a deterministic function of the
//!   canonical field encodings; `canonical_encode` is itself deterministic and
//!   set-order-insensitive (recipient `BTreeSet`, sorted `:caused-by`).
//! - *Collision-safe*: distinct field-sets ⇒ distinct roots under SHA-256
//!   collision resistance. Two messages with the same root would require either
//!   a SHA-256 collision or equal canonical encodings of every leaf, i.e. equal
//!   messages. This is the *same* assumption the flat hash and the Lean
//!   development's `contentHash_injective` axiom already make — no new
//!   weakest link (SPEC-015 ADR-700 security accounting).
//!
//! The root is still rendered `sha256:<hex64>` on the wire ([`typed_root`]),
//! so it is a drop-in content address.
//!
//! # 3. Signature over the root
//!
//! Sign-the-digest, SPEC-015 ADR-700 style: the signer vouches for a
//! domain-tagged, suite-named commitment to the *root*, e.g.
//! `(cbcl-attest-v3 <suite> <root>)`, NOT the bare root (keeping ADR-700's
//! cross-protocol-substitution resistance). Because the root commits to every
//! leaf, one root-signature authenticates all fields at once — this is what
//! makes field-openings *authenticated* disclosure.
//!
//! # 4. Field-opening
//!
//! [`open`] returns an [`Opening`]: the field value plus the sibling hashes on
//! the path from its leaf to the root. [`verify_opening`] recomputes the leaf
//! from `(field_id, value)`, folds the path, and checks the reconstructed root
//! against the given root *alone* — no other field, and in particular not the
//! payload, is needed. Under collision resistance a passing opening proves the
//! value is the message's field-`i` value at that authenticated root.

#![forbid(unsafe_code)]

use crate::canonical::canonical_encode;
use crate::message::{CausedBy, Message};
use crate::protocol::BEGIN_KEYWORD;
use crate::sexpr::{Atom, SExpr};
use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;
use sha2::{Digest, Sha256};

/// Version of the typed-address construction. Bump on any change to the field
/// schema, leaf framing, or tree shape (mirrors `CANONICAL_FORM_VERSION`).
pub const TYPED_ADDR_VERSION: u32 = 1;

const LEAF_PREFIX: u8 = 0x00;
const NODE_PREFIX: u8 = 0x01;

/// The openable fields of a message, in fixed canonical order.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum FieldId {
    /// Performative / message type (leaf 0).
    Performative = 0,
    /// Sender / signer key (leaf 1).
    From = 1,
    /// Recipient set / audience (leaf 2).
    To = 2,
    /// `:caused-by` reference (leaf 3).
    CausedBy = 3,
    /// Thread identifier (leaf 4).
    Thread = 4,
    /// Payload: content plus params (leaf 5).
    Payload = 5,
}

/// The fixed leaf order. Length is the protocol-constant leaf count.
pub const FIELD_ORDER: [FieldId; 6] = [
    FieldId::Performative,
    FieldId::From,
    FieldId::To,
    FieldId::CausedBy,
    FieldId::Thread,
    FieldId::Payload,
];

impl FieldId {
    /// Stable per-field domain-tag symbol (part of the published construction).
    fn domain_tag(self) -> &'static str {
        match self {
            FieldId::Performative => "cbcl-taddr-v1/field-0-performative",
            FieldId::From => "cbcl-taddr-v1/field-1-from",
            FieldId::To => "cbcl-taddr-v1/field-2-to",
            FieldId::CausedBy => "cbcl-taddr-v1/field-3-caused-by",
            FieldId::Thread => "cbcl-taddr-v1/field-4-thread",
            FieldId::Payload => "cbcl-taddr-v1/field-5-payload",
        }
    }
}

/// Which side a sibling sits on when folding an opening path.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Side {
    /// Sibling is the left child: `parent = H(sibling, current)`.
    Left,
    /// Sibling is the right child: `parent = H(current, sibling)`.
    Right,
}

/// A Merkle opening for one field: the revealed value and the sibling path.
///
/// Size is O(number of leaves), a protocol constant (≤ 3 sibling hashes), so
/// an opening is constant-size in the payload — the SPEC-015 NFR-700 property,
/// preserved.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Opening {
    /// Which field this opens.
    pub field: FieldId,
    /// The revealed field value, as its canonical field S-expression.
    pub value: SExpr,
    /// Sibling hashes from leaf to root, each tagged with the sibling's side.
    pub path: Vec<([u8; 32], Side)>,
}

// ---------------------------------------------------------------------------
// Field extraction — the canonical S-expression for each leaf
// ---------------------------------------------------------------------------

/// The canonical S-expression of `msg`'s field `id`.
///
/// `Option` fields encode present/absent injectively as a one- vs zero-element
/// list (`(v)` vs `()`), so "absent thread" can never canonical-encode to the
/// same bytes as any present thread value.
pub fn field_sexpr(msg: &Message, id: FieldId) -> SExpr {
    match msg {
        Message::Simple {
            performative,
            content,
            params,
            thread,
            sender,
            caused_by,
            ..
        } => match id {
            FieldId::Performative => SExpr::Atom(Atom::Symbol(String::from(performative.name()))),
            FieldId::From => opt(sender
                .as_deref()
                .map(|s| SExpr::Atom(Atom::Str(String::from(s))))),
            FieldId::To => {
                // recipient_set() is a BTreeSet<&str>: canonical sorted order,
                // so insertion order cannot change the leaf (order-insensitive).
                let items = msg
                    .recipient_set()
                    .into_iter()
                    .map(|r| SExpr::Atom(Atom::Symbol(String::from(r))))
                    .collect();
                SExpr::List(items)
            }
            FieldId::CausedBy => opt(caused_by.as_ref().map(caused_by_sexpr)),
            FieldId::Thread => opt(thread
                .as_deref()
                .map(|t| SExpr::Atom(Atom::Str(String::from(t))))),
            FieldId::Payload => {
                let mut items = vec![content.clone()];
                items.extend(params.clone());
                SExpr::List(items)
            }
        },
        // Non-Simple: total fallback — whole message rides in the payload leaf.
        other => match id {
            FieldId::Payload => SExpr::List(vec![SExpr::from(other)]),
            FieldId::Performative => match other {
                Message::Meta { .. } => SExpr::Atom(Atom::Symbol(String::from("meta"))),
                Message::Dialect { .. } => SExpr::Atom(Atom::Symbol(String::from("lang"))),
                Message::Wrapped { wrapper, .. } => {
                    SExpr::Atom(Atom::Symbol(String::from(wrapper.as_str())))
                }
                Message::Simple { .. } => unreachable!("handled above"),
            },
            _ => SExpr::List(Vec::new()),
        },
    }
}

/// Wrap an optional field value: `Some(v) → (v)`, `None → ()`.
fn opt(v: Option<SExpr>) -> SExpr {
    match v {
        Some(v) => SExpr::List(vec![v]),
        None => SExpr::List(Vec::new()),
    }
}

/// Canonical `:caused-by` value encoding — mirrors `From<Message> for SExpr`
/// (message.rs) and `attest::attestation_sexpr`, so all three agree.
fn caused_by_sexpr(cb: &CausedBy) -> SExpr {
    match cb {
        CausedBy::Begin => SExpr::Atom(Atom::Symbol(String::from(BEGIN_KEYWORD))),
        CausedBy::Single(h) => SExpr::Atom(Atom::Symbol(h.clone())),
        CausedBy::Multiple(hs) => SExpr::List(
            hs.iter()
                .map(|h| SExpr::Atom(Atom::Symbol(h.clone())))
                .collect(),
        ),
    }
}

// ---------------------------------------------------------------------------
// Leaf and node hashing
// ---------------------------------------------------------------------------

/// The leaf digest for a field value: `SHA256(0x00 ‖ enc((tag, value)))`.
fn leaf_hash(id: FieldId, value: &SExpr) -> [u8; 32] {
    let framed = SExpr::List(vec![
        SExpr::Atom(Atom::Symbol(String::from(id.domain_tag()))),
        value.clone(),
    ]);
    let mut h = Sha256::new();
    h.update([LEAF_PREFIX]);
    h.update(canonical_encode(&framed));
    h.finalize().into()
}

/// Internal node: `SHA256(0x01 ‖ left ‖ right)`.
fn node_hash(left: &[u8; 32], right: &[u8; 32]) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update([NODE_PREFIX]);
    h.update(left);
    h.update(right);
    h.finalize().into()
}

/// The six leaves in fixed order.
fn leaves(msg: &Message) -> [[u8; 32]; 6] {
    let mut out = [[0u8; 32]; 6];
    for (slot, id) in FIELD_ORDER.iter().enumerate() {
        out[slot] = leaf_hash(*id, &field_sexpr(msg, *id));
    }
    out
}

/// All intermediate node hashes of the fixed tree.
struct Tree {
    l: [[u8; 32]; 6],
    n0: [u8; 32],
    n1: [u8; 32],
    n2: [u8; 32],
    m0: [u8; 32],
    root: [u8; 32],
}

fn build_tree(msg: &Message) -> Tree {
    let l = leaves(msg);
    let n0 = node_hash(&l[0], &l[1]);
    let n1 = node_hash(&l[2], &l[3]);
    let n2 = node_hash(&l[4], &l[5]);
    let m0 = node_hash(&n0, &n1);
    let root = node_hash(&m0, &n2);
    Tree {
        l,
        n0,
        n1,
        n2,
        m0,
        root,
    }
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

fn hex32(bytes: &[u8; 32]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(64);
    for b in bytes {
        out.push(HEX[(b >> 4) as usize] as char);
        out.push(HEX[(b & 0x0f) as usize] as char);
    }
    out
}

/// The typed content address of `msg`: the Merkle root, rendered
/// `sha256:<hex64>` — a drop-in replacement for the flat content hash.
pub fn typed_root(msg: &Message) -> String {
    let mut out = String::with_capacity(7 + 64);
    out.push_str("sha256:");
    out.push_str(&hex32(&build_tree(msg).root));
    out
}

/// Produce an authenticated-disclosure [`Opening`] for one field of `msg`.
///
/// The opening reveals only that field's value plus sibling *hashes*; sibling
/// subtrees (in particular the payload leaf, when opening a header field) are
/// never revealed.
pub fn open(msg: &Message, field: FieldId) -> Opening {
    let t = build_tree(msg);
    // Fixed tree shape ⇒ hard-coded, auditable paths. Each entry is the
    // sibling hash and the side the *sibling* sits on.
    let path: Vec<([u8; 32], Side)> = match field {
        FieldId::Performative => vec![
            (t.l[1], Side::Right),
            (t.n1, Side::Right),
            (t.n2, Side::Right),
        ],
        FieldId::From => vec![
            (t.l[0], Side::Left),
            (t.n1, Side::Right),
            (t.n2, Side::Right),
        ],
        FieldId::To => vec![
            (t.l[3], Side::Right),
            (t.n0, Side::Left),
            (t.n2, Side::Right),
        ],
        FieldId::CausedBy => vec![
            (t.l[2], Side::Left),
            (t.n0, Side::Left),
            (t.n2, Side::Right),
        ],
        FieldId::Thread => vec![(t.l[5], Side::Right), (t.m0, Side::Left)],
        FieldId::Payload => vec![(t.l[4], Side::Left), (t.m0, Side::Left)],
    };
    Opening {
        field,
        value: field_sexpr(msg, field),
        path,
    }
}

/// Verify a field-opening against a root alone.
///
/// Recomputes the leaf from `(field_id, value)`, folds the sibling path, and
/// checks the reconstructed root equals `root` (`sha256:<hex64>`). Returns
/// `false` on any mismatch — tampered value, wrong path, or wrong root.
pub fn verify_opening(root: &str, field_id: FieldId, value: &SExpr, opening: &Opening) -> bool {
    if opening.field != field_id {
        return false;
    }
    let mut cur = leaf_hash(field_id, value);
    for (sibling, side) in &opening.path {
        cur = match side {
            Side::Left => node_hash(sibling, &cur),
            Side::Right => node_hash(&cur, sibling),
        };
    }
    let expected = match root.strip_prefix("sha256:") {
        Some(hex) => hex,
        None => return false,
    };
    hex32(&cur) == expected
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::message::{Performative, Recipients};
    use alloc::collections::BTreeSet;
    use alloc::string::ToString;

    fn sample(payload: &str) -> Message {
        let mut to = BTreeSet::new();
        to.insert("@bob".to_string());
        to.insert("@carol".to_string());
        Message::Simple {
            performative: Performative::Custom("reveal-bid".to_string()),
            recipient: Some(Recipients::Set(to)),
            content: SExpr::Atom(Atom::Str(payload.to_string())),
            params: Vec::new(),
            thread: Some("conv-7".to_string()),
            sender: Some("@alice".to_string()),
            caused_by: Some(CausedBy::Single("sha256:beef".to_string())),
        }
    }

    // ---- determinism ----

    #[test]
    fn same_message_two_builds_equal_root() {
        let m = sample("secret");
        assert_eq!(typed_root(&m), typed_root(&sample("secret")));
        // Two independent builds of the identical value.
        assert_eq!(typed_root(&m), typed_root(&m));
    }

    #[test]
    fn root_has_sha256_hex64_form() {
        let r = typed_root(&sample("x"));
        let hex = r.strip_prefix("sha256:").expect("prefix");
        assert_eq!(hex.len(), 64);
        assert!(hex
            .chars()
            .all(|c| c.is_ascii_digit() || ('a'..='f').contains(&c)));
    }

    #[test]
    fn reordered_but_equal_encodings_equal_root() {
        // Recipient set built in two different insertion orders; the To leaf
        // composes with canonical_encode over a BTreeSet, so order is
        // irrelevant and the roots coincide.
        let mk = |order: &[&str]| {
            let mut to = BTreeSet::new();
            for r in order {
                to.insert(r.to_string());
            }
            Message::Simple {
                performative: Performative::Custom("reveal-bid".to_string()),
                recipient: Some(Recipients::Set(to)),
                content: SExpr::Atom(Atom::Str("p".to_string())),
                params: Vec::new(),
                thread: Some("conv-7".to_string()),
                sender: Some("@alice".to_string()),
                caused_by: Some(CausedBy::Multiple(vec![
                    "sha256:aaa".to_string(),
                    "sha256:bbb".to_string(),
                ])),
            }
        };
        assert_eq!(
            typed_root(&mk(&["@carol", "@bob"])),
            typed_root(&mk(&["@bob", "@carol"]))
        );
    }

    #[test]
    fn distinct_field_sets_give_distinct_roots() {
        let base = sample("p");
        // Vary each header field in turn; every change must move the root.
        let mut perf = base.clone();
        if let Message::Simple { performative, .. } = &mut perf {
            *performative = Performative::Custom("commit-bid".to_string());
        }
        let mut from = base.clone();
        if let Message::Simple { sender, .. } = &mut from {
            *sender = Some("@mallory".to_string());
        }
        let mut thread = base.clone();
        if let Message::Simple { thread: t, .. } = &mut thread {
            *t = Some("conv-8".to_string());
        }
        let payload = sample("different-payload");
        let r = typed_root(&base);
        for other in [&perf, &from, &thread, &payload] {
            assert_ne!(r, typed_root(other));
        }
    }

    // ---- opening soundness ----

    #[test]
    fn valid_openings_verify_for_every_field() {
        let m = sample("secret");
        let root = typed_root(&m);
        for id in FIELD_ORDER {
            let op = open(&m, id);
            assert!(
                verify_opening(&root, id, &field_sexpr(&m, id), &op),
                "field {id:?} opening must verify"
            );
        }
    }

    #[test]
    fn tampered_value_fails() {
        let m = sample("secret");
        let root = typed_root(&m);
        let op = open(&m, FieldId::Performative);
        // Claim a different performative than the opening's leaf commits to.
        let forged = SExpr::Atom(Atom::Symbol("commit-bid".to_string()));
        assert!(!verify_opening(&root, FieldId::Performative, &forged, &op));
    }

    #[test]
    fn wrong_path_fails() {
        let m = sample("secret");
        let root = typed_root(&m);
        let mut op = open(&m, FieldId::Performative);
        // Corrupt one sibling hash.
        op.path[0].0[0] ^= 0xff;
        assert!(!verify_opening(
            &root,
            FieldId::Performative,
            &field_sexpr(&m, FieldId::Performative),
            &op
        ));
        // Flip a side.
        let mut op2 = open(&m, FieldId::Performative);
        op2.path[0].1 = Side::Left;
        assert!(!verify_opening(
            &root,
            FieldId::Performative,
            &field_sexpr(&m, FieldId::Performative),
            &op2
        ));
    }

    #[test]
    fn wrong_root_fails() {
        let m = sample("secret");
        let other_root = typed_root(&sample("other"));
        let op = open(&m, FieldId::From);
        assert!(!verify_opening(
            &other_root,
            FieldId::From,
            &field_sexpr(&m, FieldId::From),
            &op
        ));
    }

    #[test]
    fn opening_for_wrong_field_id_fails() {
        let m = sample("secret");
        let root = typed_root(&m);
        let op = open(&m, FieldId::From);
        // Present a From-opening under the Performative id.
        assert!(!verify_opening(
            &root,
            FieldId::Performative,
            &field_sexpr(&m, FieldId::From),
            &op
        ));
    }

    // ---- payload not revealed ----

    #[test]
    fn type_opening_reveals_type_not_payload() {
        let m = sample("TOP-SECRET-BID-4200");
        let root = typed_root(&m);
        let op = open(&m, FieldId::Performative);
        assert!(verify_opening(&root, FieldId::Performative, &op.value, &op));

        // The revealed value's bytes carry the performative...
        let value_bytes = canonical_encode(&op.value);
        let value_str = core::str::from_utf8(&value_bytes).unwrap();
        assert!(value_str.contains("reveal-bid"), "type must be revealed");
        assert!(
            !value_str.contains("TOP-SECRET-BID-4200"),
            "payload leaked into value"
        );

        // ...and the sibling path carries only 32-byte hashes, never the
        // payload bytes.
        for (sibling, _) in &op.path {
            assert_eq!(sibling.len(), 32);
            assert!(
                !sibling.windows(4).any(|w| w == b"4200"),
                "payload must not appear in a sibling hash"
            );
        }
    }

    // ---- SUBSUMPTION (deliverable 3): the SPEC-015 envelope's REQ-702
    // safety-level checks are all expressible as authenticated openings. ----

    /// A "redacted envelope" reconstructed purely as typed-root openings:
    /// the root, a (mock) signature over the root, and openings for exactly
    /// the SPEC-015 header fields — no payload.
    struct OpenedEnvelope {
        root: String,
        root_sig: [u8; 32],
        performative: Opening,
        from: Opening,
        to: Opening,
        caused_by: Opening,
        thread: Opening,
    }

    /// Sign-the-digest, ADR-700 style: a domain-tagged, suite-named
    /// commitment to the root (mock signer = SHA256(secret ‖ preimage)).
    fn sign_root(secret: &[u8], root: &str) -> [u8; 32] {
        let preimage = alloc::format!("(cbcl-attest-v3 ed25519 {root})");
        let mut h = Sha256::new();
        h.update(secret);
        h.update(preimage.as_bytes());
        h.finalize().into()
    }

    fn redact_to_openings(m: &Message, secret: &[u8]) -> OpenedEnvelope {
        let root = typed_root(m);
        OpenedEnvelope {
            root_sig: sign_root(secret, &root),
            performative: open(m, FieldId::Performative),
            from: open(m, FieldId::From),
            to: open(m, FieldId::To),
            caused_by: open(m, FieldId::CausedBy),
            thread: open(m, FieldId::Thread),
            root: root,
        }
    }

    #[test]
    fn envelope_safety_checks_are_authenticated_openings() {
        let m = sample("the secret payload");
        let env = redact_to_openings(&m, b"alice");

        // (0) The single root-signature authenticates every field at once —
        // the envelope holder verifies it exactly as a v2 attestation, over
        // a domain-tagged commitment to the root (ADR-700 preserved).
        assert_eq!(env.root_sig, sign_root(b"alice", &env.root));

        // (a) predecessor TYPE (REQ-702 / REQ-616): open the performative.
        assert!(verify_opening(
            &env.root,
            FieldId::Performative,
            &env.performative.value,
            &env.performative
        ));
        // (b) role conformance of the citing message (from / to): open both.
        assert!(verify_opening(
            &env.root,
            FieldId::From,
            &env.from.value,
            &env.from
        ));
        assert!(verify_opening(
            &env.root,
            FieldId::To,
            &env.to.value,
            &env.to
        ));
        // (c) resolution of the :caused-by reference: open caused-by.
        assert!(verify_opening(
            &env.root,
            FieldId::CausedBy,
            &env.caused_by.value,
            &env.caused_by
        ));
        // (d) thread placement (REQ-702: authenticated thread field): open thread.
        assert!(verify_opening(
            &env.root,
            FieldId::Thread,
            &env.thread.value,
            &env.thread
        ));

        // NFR-701: no payload disclosure — nothing in the opened envelope
        // carries the payload bytes.
        for op in [
            &env.performative,
            &env.from,
            &env.to,
            &env.caused_by,
            &env.thread,
        ] {
            let bytes = canonical_encode(&op.value);
            let s = core::str::from_utf8(&bytes).unwrap();
            assert!(
                !s.contains("the secret payload"),
                "payload leaked via {:?}",
                op.field
            );
        }
    }

    #[test]
    fn tampering_a_field_after_signing_breaks_the_check() {
        // The envelope's authenticated-header property (REQ-701 / review
        // finding 1): a relay holding a genuine (root, signature) pair cannot
        // forge a header field, because each field is bound into the root and
        // the signature is over the root.
        let genuine = sample("payload");
        let env = redact_to_openings(&genuine, b"alice");

        // Attacker fabricates a different `to` set and a matching opening from
        // a *different* message — but its opening reconstructs a different
        // root, so it fails against the signed root.
        let mut widened = BTreeSet::new();
        widened.insert("@bob".to_string());
        widened.insert("@carol".to_string());
        widened.insert("@mallory".to_string());
        let forged_msg = Message::Simple {
            performative: Performative::Custom("reveal-bid".to_string()),
            recipient: Some(Recipients::Set(widened)),
            content: SExpr::Atom(Atom::Str("payload".to_string())),
            params: Vec::new(),
            thread: Some("conv-7".to_string()),
            sender: Some("@alice".to_string()),
            caused_by: Some(CausedBy::Single("sha256:beef".to_string())),
        };
        let forged_to = open(&forged_msg, FieldId::To);
        // Presented against the genuine signed root, the forged opening fails.
        assert!(!verify_opening(
            &env.root,
            FieldId::To,
            &forged_to.value,
            &forged_to
        ));
        // And the forged message's own root is not the signed one, so the
        // signature does not carry over.
        assert_ne!(typed_root(&forged_msg), env.root);
    }

    #[test]
    fn completion_needs_the_payload_leaf() {
        // REQ-703: a fan-in decider needs payload grammaticality, which the
        // header openings above deliberately do NOT provide. It is recovered
        // by opening the Payload leaf — authenticated disclosure of the
        // payload itself, not a separate mechanism.
        let m = sample("the actual content");
        let root = typed_root(&m);
        let payload = open(&m, FieldId::Payload);
        assert!(verify_opening(
            &root,
            FieldId::Payload,
            &payload.value,
            &payload
        ));
        let s = alloc::format!("{}", payload.value);
        assert!(
            s.contains("the actual content"),
            "payload opening reveals content"
        );
    }
}
