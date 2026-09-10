---
id: SPEC-017
title: Typed Content Addresses — Merkle-over-Fields and Authenticated Selective Disclosure
status: draft
version: 0.1.1
date: 2026-09-10
author: Anuna Research (https://anuna.io)
depends-on:
  - SPEC-016 (abstract splicing boundary and concrete refinement obligations)
  - SPEC-015 (redacted envelopes — the header-authentication this re-expresses)
  - SPEC-014 (role layer — R6(vi), safety-level checks, redacted evidence)
  - SPEC-003 (verification lattice — three-valued result, resolution)
  - SPEC-002 (structural contracts — canonical encoding, LangSec recognition, R2 bounds)
supersedes: SPEC-015 (PARTIAL — the envelope's header-authentication re-expressed as a field-opening; the attestation discipline is retained, not superseded)
prior-art:
  - crates/cbcl-core/src/typed_addr.rs (the normative construction — Stage 0, standalone, 13 tests green)
  - af75648 (IMPL-017 spike — GO verdict; determinism + collision-safety, envelope subsumption, bounded blast radius)
  - crates/cbcl-core/src/canonical.rs (RFC 9804 canonical_encode — the per-field encoder composed here)
  - crates/cbcl-core/src/equivocation.rs (message_content_hash — the flat H(canonical-bytes) this replaces at the hub)
repository: https://codeberg.org/anuna/cbcl-rs
---

# SPEC-017: Typed Content Addresses

The key words MUST, MUST NOT, REQUIRED, SHALL, SHALL NOT, SHOULD, SHOULD NOT,
RECOMMENDED, MAY, and OPTIONAL in this document are to be interpreted as
described in BCP 14 (RFC 2119, RFC 8174) when, and only when, they appear in
all capitals.

## Orientation

CBCL's content address is today a flat digest: `sha256:H(canonical-bytes)`
over a whole message
([[crates/cbcl-core/src/equivocation.rs|message_content_hash]]). The supported verifier does not resolve a bare citation without predecessor
evidence ([[SPEC-016-splicing-boundary#REQ-800]]). The abstract observation theorem
does not establish cryptographic impossibility of recovering information from a
hash. The flat digest commits to the message as a whole; it has no field-opening
format in this construction.

This spec moves the content address from that flat digest to a **canonical
Merkle commitment over the message's fields**. The address becomes the root
of a fixed-shape tree whose leaves are the message's performative type,
sender, recipients, `:caused-by`, thread, and payload. Any single field then
*opens*: its holder produces the field value plus a constant-size sibling
path that verifies against the address **alone**, revealing that one field
and nothing else. This is authenticated selective disclosure — *verifiable
hearsay*: a relay that never authored the message, holding only the root and
an opening, can prove to a third party "this address is a message of *this
type*, from *this sender*" while the payload stays sealed.

This subsumes — partially, and the boundary is stated honestly in
[[#ADR-811]] — the SPEC-015 redacted envelope's header-authentication
([[SPEC-015-evidence-widening-v2#REQ-701]]). Where SPEC-015 signs a
domain-tagged attestation that *names* the header fields so a redacted
verifier can trust them, SPEC-017 makes each field a leaf of the address
itself: the header is authenticated by the content address's own structure,
and a single signature over the root vouches for every field at once. It
operationalises the paper's *form/content split* as a substrate primitive —
the performative (form) opens; the payload (content) seals — rather than as
an envelope derivative.

A field-opening delivers a type-tagged form of predecessor evidence. It is
verifiable against a trusted root, can omit the payload, and can be produced by a
holder of the message. These are construction goals, not a Lean optimality theorem
over all possible evidence schemes. [[SPEC-016-splicing-boundary#REQ-802]] sets the
scope of the abstract observation and resolution results.

The Lean semantic factoring result assumes equal predecessor types and resolution
in the compared stores. A separate refinement proof must connect authenticated
concrete openings to those assumptions. Keeping an abstract `contentHash` interface
unchanged does not prove this connection. Collision resistance is a computational
assumption, not mathematical injectivity of a fixed-size digest on all messages.
The migration contract remains in [[SPEC-017-typed-content-addresses#REQ-813]].

## Context

| Layer | Address today | Address here |
|---|---|---|
| Content address | flat `sha256:H(canonical-bytes)`, type-opaque | Merkle root over six fields; any field opens against the root |
| Header authentication (SPEC-015 envelope) | attestation names header fields ([[SPEC-015-evidence-widening-v2#REQ-701]]) | header fields are leaves of the address; a field-opening authenticates against the root |
| Selective disclosure | envelope redacts payload, discloses header ([[SPEC-015-evidence-widening-v2#NFR-701]]) | open header leaves 0–4, seal payload leaf 5 — same disclosure, self-authenticating |
| Splicing remedy ([[SPEC-016-splicing-boundary#REQ-801]]) | deliver type-tagged envelope | deliver a field-opening — concrete refinement remains required |

The construction is validated and standalone in
[[crates/cbcl-core/src/typed_addr.rs]] (Stage 0 of the migration below,
13 tests green, wired into no hash path). This spec is its normative
transcription.

## Requirements

### Address construction

**REQ-810: Merkle-over-fields content address.**
The content address of a `Message::Simple` SHALL be the root of a
deterministic canonical Merkle tree over its fields in a FIXED canonical
order — `(performative/type, from, to, caused-by, thread, payload)`, leaves
0–5 respectively. The construction SHALL be:

- **Leaf.** For field `i` with canonical field S-expression `field_i` and a
  stable per-field domain tag `tag_i`,
  `leaf_i = SHA256( 0x00 ‖ canonical_encode( ( tag_i field_i ) ) )`. The tag
  and value are wrapped in a two-element list and run through the existing
  RFC 9804 [[crates/cbcl-core/src/canonical.rs|canonical_encode]], whose
  length-prefixed framing makes `(tag field)` an injective encoding of the
  pair (no concatenation-boundary ambiguity) and domain-separates each
  field's bytes from every other's.
- **Tree.** A fixed-arity binary tree over the six leaves. Because the leaf
  count is a protocol constant (6), the tree *shape* is constant and
  identical for every message, so the classic duplicate-last-leaf
  second-preimage forgery — which needs an attacker-chosen leaf count —
  cannot arise. Internal nodes SHALL be
  `node = SHA256( 0x01 ‖ a ‖ b )`. Leaf prefix `0x00` and node prefix `0x01`
  domain-separate leaves from internal nodes (a leaf digest can never be
  reinterpreted as a node).
- **Root.** Rendered on the wire as `sha256:<hex64>`, a drop-in replacement
  for the flat content address.

The construction SHALL be **deterministic** (every step a function of the
canonical field encodings; `canonical_encode` is deterministic and
set-order-insensitive — recipients a `BTreeSet`, `:caused-by` sorted) and
**collision-safe**: two messages sharing a root require either a [[SHA-256]]
collision or equal canonical encodings of every leaf, i.e. equal messages.
The abstract `contentHash_injective` axiom idealizes collision avoidance;
computational collision resistance does not establish literal injectivity.
The concrete construction requires separate security and refinement arguments
([[SPEC-015-evidence-widening-v2#ADR-700]]).
Non-`Simple` messages SHALL be handled totally (never panic): the whole
message rides in the payload leaf, other leaves empty, so a root always
exists (schema refinement for `Wrapped`/`Dialect`/`Meta` is future work).
Trace: [[#TEST-810]], [[#TEST-811]], [[#TEST-812]], decision [[#ADR-810]].

### Field-opening

**REQ-811: Field-opening and verify-against-root.**
The layer SHALL provide `open(msg, field) → Opening` and
`verify_opening(root, field_id, value, opening) → bool`. An `Opening` SHALL
carry the field id, the revealed field value (its canonical field
S-expression), and the sibling path — each entry a `(hash, side)` pair —
from the field's leaf to the root. `verify_opening` SHALL recompute the leaf
from `(field_id, value)`, fold the sibling path, and check the reconstructed
root equals the given `root` **alone** — no other field, and in particular
not the payload, is consulted. Under [[SHA-256]] collision resistance a
passing opening proves `value` is the message's field-`i` value at that
authenticated root.
An opening SHALL be **constant-size** in the payload it does not reveal:
the path length is `O(number of leaves)`, a protocol constant (≤ 3 sibling
hashes for the six-leaf tree) — the SPEC-015 [[SPEC-015-evidence-widening-v2#NFR-700]]
envelope-size property, preserved. Opening a header field (leaves 0–4) SHALL
reveal only that field's value and sibling *hashes*; the payload leaf's
subtree is never revealed — the payload is **sealed**.
Trace: [[#TEST-813]], [[#TEST-814]], [[#TEST-815]], grammar [[#CON-810]],
decision [[#ADR-810]].

### Signature over the root

**REQ-812: Sign-the-root.**
A signature SHALL be computed over a domain-tagged, suite-named commitment to
the *root*, not the bare root:
`(cbcl-attest-v3 <suite> <root>)`. Because the root already commits to every
leaf, one root-signature authenticates all six fields at once — this is what
makes every field-opening *authenticated* disclosure without a per-field
signature. This retains, unchanged, the SPEC-015 attestation discipline:
the [[SPEC-015-evidence-widening-v2#ADR-700]] domain tag (cross-protocol
substitution resistance — a signed 32-byte string never re-interpretable
under another protocol), the [[SPEC-015-evidence-widening-v2#REQ-708]]
suite-naming (the attestation names its signature suite, verification
dispatches on it, an unimplemented suite is a typed rejection never a
skipped check), and the v1/v2/v3 discipline marker: the `-v3` tag governs
*what is signed* (a Merkle root, versus v2's header-attestation, versus v1's
full bytes) and SHALL fail closed — a v1 or v2 signature SHALL NOT satisfy a
v3 root-signature path, and a discipline mismatch SHALL be a typed rejection,
never a failed guess.
Trace: [[#TEST-816]], grammar [[#CON-811]], decision [[#ADR-811]].

### Envelope subsumption

**REQ-813: Openings satisfy the safety-level checks; completion opens the payload.**
The SPEC-015 [[SPEC-015-evidence-widening-v2#REQ-702]] safety-level checks —
predecessor type ([[SPEC-014-role-layer-endpoint-projection#REQ-616]]), the
citing message's `from`/`to` role conformance, `:caused-by` resolution, and
authenticated `thread` placement — SHALL all be satisfiable as field-openings
against the root, with **zero payload disclosure** (the
[[SPEC-015-evidence-widening-v2#NFR-701]] property): open leaves 0–4, seal
leaf 5. Leaves 0–4 are exactly the SPEC-015 envelope header fields, so an
opened set of them *is* a redacted envelope, self-authenticating against the
address. The SPEC-015 [[SPEC-015-evidence-widening-v2#REQ-703]]
completion-level check (a fan-in member "present and Valid", requiring
payload grammaticality) SHALL be satisfied by opening the **payload leaf**
(leaf 5) — authenticated disclosure of the payload itself, not a separate
mechanism; the two-tier reading (headers for safety, full content for fan-in
deciders) is preserved.
The abstract Lean model SHALL retain its existing `contentHash` interface.
Its injectivity is an abstract assumption. Preserving that interface preserves
the abstract theorem statements, but does not prove that a concrete Merkle root
or authenticated opening satisfies them; that refinement remains outstanding.
Trace: [[#TEST-816]], decision [[#ADR-811]].

## Architecture Decisions

**ADR-810: Merkle-over-fields as the content address.**
*Decision*: the content address becomes a canonical Merkle root over the
message's fields ([[#REQ-810]]), replacing the flat `H(canonical-bytes)`.
*Rationale*: native selective disclosure. A flat digest forces all-or-nothing
holding; a Merkle root lets any single field open against the address with a
constant-size proof, so authenticated header disclosure ceases to need a
separate envelope object and a separate header-binding attestation — it falls
out of the address's own structure. *Security accounting*: collision-safety
of the root reduces to [[SHA-256]] collision resistance, the *same*
assumption content addressing, every `:caused-by` link, and the Lean
`contentHash_injective` axiom already make — a collision forger can already
rewrite causal history without forging a signature, so the tree adds **no new
weakest link** ([[SPEC-015-evidence-widening-v2#ADR-700]]). The fixed six-leaf
shape and the leaf/node prefix domain separation close the standard Merkle
forgery surfaces (variable arity, leaf-as-node reinterpretation) by
construction. *Alternatives rejected*: (a) keep the flat hash and layer
selective disclosure as a side-channel — re-introduces the SPEC-015 envelope
as a distinct signed object, the very duplication this removes; (b) a
variable-arity or sorted-leaf tree — surrenders the constant-shape argument
that makes the paths hard-coded and auditable.

**ADR-811: PARTIAL subsumption of the envelope — the honest boundary.**
*Decision*: SPEC-017 subsumes the SPEC-015 envelope's **header
authentication**, and *retains* the SPEC-015 **attestation discipline**. The
boundary is stated exactly:

- **Subsumed** (the tree provides it): *what* the message is. Each header
  field (performative, from, to, caused-by, thread) is a leaf of the content
  address, authenticated against the root by its opening — no separate
  attestation naming the header, no forgeable `(hash, signature)` gossip
  surface ([[SPEC-015-evidence-widening-v2#REQ-701]] review finding 1 is
  answered structurally: a relay cannot forge a header field because the field
  is bound into the root). The redacted envelope's raison d'être — a
  payload-free, header-authenticated, constant-size derivative — is now the
  default readout of the address itself.
- **Retained** (the tree does *not* provide it): the *signing* discipline.
  The tree commits fields; it does not sign anything. The
  [[SPEC-015-evidence-widening-v2#ADR-700]] domain tag, the
  [[SPEC-015-evidence-widening-v2#REQ-708]] suite-naming, and the v1/v2/v3
  fail-closed marker live in the **root-signature** ([[#REQ-812]]), not in the
  tree. A bare root proves internal consistency of the fields to each other;
  it does not prove *who* vouches for them. Authentication of authorship
  remains a signature over `(cbcl-attest-v3 <suite> <root>)`.

*Rationale*: conflating these would over-claim. The tree is a commitment
scheme, not an authentication scheme; selective disclosure of *committed*
fields is not the same as attribution to a signer. Stating the split keeps
SPEC-015's attestation reasoning load-bearing rather than silently dropped.
*Consequence on SPEC-015*: the envelope's header-authentication is superseded
(re-expressed as a field-opening); the attestation discipline is carried
forward verbatim into the root-signature. Hence the frontmatter's PARTIAL
supersession.

## Contracts

### CON-810: Field-opening wire object

```
opening   := "(" "opening" field-id value path ")"
field-id  := "performative" | "from" | "to" | "caused-by" | "thread" | "payload"
value     := sexpr                 ; the canonical field S-expression of the leaf
path      := "(" step* ")"         ; leaf→root sibling path, length ≤ 3
step      := "(" hash side ")"
hash      := hex64                 ; a 32-byte sibling digest, raw (no sha256: prefix)
side      := "left" | "right"      ; the side the SIBLING sits on
```

Full recognition before any semantic action ([[SPEC-002-structural-contracts|LangSec discipline]]):
a malformed opening — a `field-id` outside the six, a `hash` that is not
exactly 64 hex, a `path` exceeding the tree's fixed depth, an unknown `side`,
or any extra field — SHALL be **rejected, never repaired**. `verify_opening`
against a root that lacks the `sha256:` prefix, or whose reconstructed root
does not match, SHALL return failure (never a partial or guessed accept).

### CON-811: Attestation over the root

```
attestation := "(" "cbcl-attest-v3" suite root ")"
suite       := symbol              ; registered signature-suite name (REQ-708)
root        := "sha256:" hex64     ; the Merkle root of REQ-810
```

The signing preimage (never transmitted; reconstructed by any holder of the
root). `-v3` is the discipline marker: it governs *what is signed* (a Merkle
root), independent of the `suite` field, which governs *how*. A verifier
presented a v1 (full-bytes) or v2 (header-attestation) signature on a v3 path
SHALL yield a typed rejection (fail closed), never a fallback attempt.

## Test Specifications

The 13 tests of [[crates/cbcl-core/src/typed_addr.rs]] are the normative test
corpus; they group as follows.

**TEST-810: Determinism.** The same message built twice yields an equal root
(`same_message_two_builds_equal_root`); the root has the `sha256:<hex64>`
form (`root_has_sha256_hex64_form`).

**TEST-811: Order-insensitivity.** A recipient set built in two different
insertion orders yields one root — the `To` leaf composes with
`canonical_encode` over a `BTreeSet`, so order is irrelevant
(`reordered_but_equal_encodings_equal_root`).

**TEST-812: Collision-safety.** Varying any header field in turn (performative,
from, thread) or the payload moves the root; every distinct field-set gives a
distinct root (`distinct_field_sets_give_distinct_roots`).

**TEST-813: Opening soundness.** For every one of the six fields, a valid
opening verifies against the root
(`valid_openings_verify_for_every_field`).

**TEST-814: Opening rejection (tamper / wrong-path / wrong-root / wrong-id).**
A tampered value fails (`tampered_value_fails`); a corrupted sibling hash or a
flipped side fails (`wrong_path_fails`); an opening presented against another
message's root fails (`wrong_root_fails`); a `From`-opening presented under
the `Performative` id fails (`opening_for_wrong_field_id_fails`).

**TEST-815: Payload sealed.** Opening the performative reveals the type but
never the payload — neither the revealed value nor any sibling hash carries
the payload bytes (`type_opening_reveals_type_not_payload`).

**TEST-816: Envelope subsumption demo.** The SPEC-015 [[SPEC-015-evidence-widening-v2#REQ-702]]
safety-level checks (type, from, to, caused-by, thread) are all satisfied as
authenticated openings against one root-signature, with zero payload
disclosure ([[#REQ-813]], `envelope_safety_checks_are_authenticated_openings`);
a relay holding a genuine `(root, signature)` pair cannot forge a header
field, because a forged opening reconstructs a different root
(`tampering_a_field_after_signing_breaks_the_check`); and completion
([[SPEC-015-evidence-widening-v2#REQ-703]]) is recovered by opening the
payload leaf (`completion_needs_the_payload_leaf`).

## Migration

Staged, blast radius bounded to one hub function (spike verdict GO,
commit af75648):

- **Stage 0 — done.** `typed_addr` standalone: `typed_root` / `open` /
  `verify_opening`, 13 tests green, wired into no hash path
  ([[crates/cbcl-core/src/typed_addr.rs]]). The existing flat-hash wiring
  keeps its exact behaviour while the design is evaluated.
- **Stage 1 — hub flip.** Replace `message_content_hash` (the flat
  `H(canonical-bytes)`) with `typed_root` at the single hub, with an atomic
  fixture update (every recorded address changes exactly once).
- **Stage 2 — attest → sign-the-root v3.** Move R4 signing from the SPEC-015
  header-attestation (`cbcl-attest-v2`) to the root-attestation
  (`cbcl-attest-v3 <suite> <root>`, [[#REQ-812]]), retaining domain-tag,
  suite-naming, and the fail-closed marker.
- **Stage 3 — native openings.** Replace the `RedactedEnvelope` object with
  native field-openings ([[#REQ-811]], [[#REQ-813]]); the envelope's
  header-authentication is now the address's own readout.

Throughout, the abstract Lean interface remains unchanged. The concrete
Merkle implementation still needs a refinement argument; its fixed-size root
is not a mathematically injective function on all messages.

## Traceability

| Requirement | Tests | Decision |
|---|---|---|
| [[#REQ-810]] | [[#TEST-810]], [[#TEST-811]], [[#TEST-812]] | [[#ADR-810]] |
| [[#REQ-811]] | [[#TEST-813]], [[#TEST-814]], [[#TEST-815]] | [[#ADR-810]] |
| [[#REQ-812]] | [[#TEST-816]] | [[#ADR-811]] |
| [[#REQ-813]] | [[#TEST-816]] | [[#ADR-811]] |

## Changelog

- 0.1.1 (2026-09-10) — qualify references to the abstract splicing results
  under [[SPEC-016-splicing-boundary#REQ-802]]; concrete authenticated-opening
  refinement remains unproved. Runtime construction requirements are unchanged.

- 0.1.0 (2026-07-09) — initial draft, transcribed from the validated IMPL-017
  spike ([[crates/cbcl-core/src/typed_addr.rs]], commit af75648, GO verdict).
  Content address moves from flat `H(canonical-bytes)` to a canonical
  six-leaf Merkle root over a message's fields, enabling authenticated
  selective disclosure (field-openings verifiable against the address alone,
  payload sealed). Subsumes the SPEC-015 envelope's header-authentication
  (PARTIAL — [[#ADR-811]]: the tree commits *what*, the attestation discipline
  is retained in the root-signature). The original revision described openings as the *optimal* tag under the
  [[SPEC-016-splicing-boundary#REQ-800]] necessity result — self-authenticating,
  minimal-disclosure, relay-producible — not an escape from it. Staged
  migration: Stage 0 done; Stages 1–3 (hub flip, sign-the-root v3, native
  openings) pending. Abstract Lean model untouched.
