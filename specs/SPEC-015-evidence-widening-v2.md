---
id: SPEC-015
title: Role Layer v2 — Redacted Delivery, Bounded Repetition, Equivocation Accountability
status: approved
version: 0.1.3
date: 2026-07-04
author: Anuna Research (https://anuna.io)
depends-on:
  - SPEC-014 (role layer — R6, projection, casts; the v1 this revises)
  - SPEC-002 (structural contracts — R1/R2 bounds, dialect install)
  - SPEC-003 (verification lattice — three-valued result, policy layer)
prior-art:
  - crates/cbcl-parser/tests/paper_corpus.rs (TEST-640 — the corpus verdicts motivating this spec)
  - anuna-papers/papers/2026-cbcl-endpoint-projection (EPP paper — corpus table, adversary and equivocation sections)
repository: https://codeberg.org/anuna/cbcl-rs
---

# SPEC-015: Role Layer v2 — Redacted Delivery, Bounded Repetition, Equivocation Accountability

The key words MUST, MUST NOT, REQUIRED, SHALL, SHALL NOT, SHOULD, SHOULD NOT,
RECOMMENDED, MAY, and OPTIONAL in this document are to be interpreted as
described in BCP 14 (RFC 2119, RFC 8174) when, and only when, they appear in
all capitals.

## Orientation

The corpus study
([[SPEC-014-role-layer-endpoint-projection#TEST-640]]; the EPP paper's
Table 1) measured what v1's causal locality actually costs: three of ten
literature protocols pass R6(vi) as written; every failure repairs by
recipient widening; and the repair's price is paid in two currencies —
extra *deliveries* (typically $+1$–$2$ per run, $O(n^2)$ for indexed
fan-ins) and structural *disclosure* (the seller learns the buyers' split,
participants see each other's votes, every widened payload reaches parties
who only needed evidence of it). The study also confirmed the corpus's
ceiling: recursive protocols are excluded outright by v1's finite DAGs.

This spec revises the role layer along the three axes those findings expose,
changing **none** of the abstract model's theorems:

1. **Redacted delivery** ([[#REQ-700]]–[[#REQ-703]]): widen the *evidence*,
   not the message. Role-local verification reads a predecessor's hash,
   performative type, endpoints, and signature — never its payload
   ([[SPEC-014-role-layer-endpoint-projection#REQ-615]]–[[SPEC-014-role-layer-endpoint-projection#REQ-617]]).
   A payload-free **redacted envelope** (its size independent of the payload
   it redacts) satisfies a widened recipient's verification needs at safety
   level, collapsing the disclosure column of the corpus table and shrinking
   $O(n^2)$ payload fan-out to $O(n^2)$ payload-free headers. This is also the concrete realisation
   path for the deferred splicing regime: "verify a dependency never
   received" becomes "received in redacted form".
2. **Bounded repetition** ([[#REQ-704]]): a `(repeat k …)` protocol form,
   macro-expanded to `k` copies at install, lifts the recursion exclusion
   for retries, rounds, and bounded heartbeats while keeping every protocol
   a finite DAG — [[SPEC-002-structural-contracts|R1]] untouched (expansion
   happens once at install), [[DCFL]] preservation untouched (the obligation
   schema stays finite), in the declared-bounds idiom R2 already uses.
3. **Equivocation accountability** ([[#REQ-705]]–[[#REQ-707]]): the paper
   proves per-message *exclusion* of equivocation is non-monotone (outside
   the [[CALM]] coordination-free envelope) while *detection* is monotone
   and the offending signed pair is a transferable proof. v2 makes that
   literal: a store-level equivocation predicate, a proof object any
   third party verifies from the pair and the dialect alone, and an
   optional choice-transparency lint.

What does not change: the verdict lattice
([[SPEC-003-verification-lattice#REQ-302]]), per-message verdict stability,
R6's clause structure, cast sealing, and the mechanised EPP correspondence —
redacted delivery and bounded repetition are engineered to leave the
abstract model of the Lean development untouched.

## Context

Corpus verdicts this spec responds to (machine-checked by
[[SPEC-014-role-layer-endpoint-projection#TEST-640]]):

| Finding | Consequence here |
|---|---|
| 5 of 7 R6(vi) failures are classically-unremarkable protocols (two-buyer, pipeline, ring, 2PC, announcing auction) | Widening is the routine repair, so its cost dominates the layer's usability |
| Widening cost = deliveries + disclosure; disclosure is the dominant objection (votes, bids, credential digests) | [[#REQ-700]]: pay in evidence, not payloads |
| Recursive protocols excluded entirely | [[#REQ-704]]: bounded repetition within finite DAGs |
| Equivocation individually-Valid pairs (choice and obligation forms) are detectable but not excludable | [[#REQ-705]]–[[#REQ-707]]: make detection first-class |
| Checker gap: [[SPEC-014-role-layer-endpoint-projection#BUG-640]] (instantiated check misses non-fan-in references) | Fix under SPEC-014; redacted delivery makes the then-correctly-rejected repairs cheap to satisfy |

## Requirements

### Redacted delivery

**REQ-700: Redacted envelope.**
The message layer SHALL define a *redacted envelope*: a derivative of a
signed message carrying exactly its content hash, performative name, sender
key, recipient set, thread identifier, signature material, and `:caused-by`
list — and no payload fields. Producing an envelope from a message SHALL be a pure
function; the envelope SHALL identify (by content hash) the same message it
redacts.
Trace: [[#TEST-700]], grammar [[#CON-700]].

**REQ-701: Envelope verifiability without payload.**
An envelope SHALL be verifiable from its own fields alone, and every field
the verifier reads SHALL be authenticated: R4 v2 SHALL sign the canonical
bytes of a domain-tagged attestation committing to the signature suite, the
content hash, **and the header** — performative name, sender key, recipient
set, thread, `:caused-by` list ([[#ADR-700]]; review finding 1: binding the
hash alone leaves the header forgeable from gossiped (hash, signature)
pairs).
Both verifier classes reconstruct the identical preimage: an envelope holder
from the envelope's fields, a full-message holder from the message and its
computed hash.
Messages and envelopes SHALL carry an explicit discipline marker
distinguishing v2-attested from legacy v1 full-bytes signatures; a v1
signature SHALL NOT satisfy any envelope path (fail closed), and a
discipline mismatch SHALL be a typed rejection, never a failed guess
(review finding 6).
Trace: [[#TEST-701]].

**REQ-702: Safety-level verification over envelopes.**
`verify_causal_for_role` SHALL accept a redacted envelope as a store entry
satisfying a `:caused-by` reference for all safety-level checks: presence,
predecessor type ([[SPEC-014-role-layer-endpoint-projection#REQ-616]]), role
conformance of the *citing* message, and resolution. A message whose
predecessors are present only as envelopes SHALL resolve to the same
safety verdict it would with full predecessors.
The verifier SHALL read an envelope's header fields only as authenticated by
its attestation ([[#REQ-701]]), and the store SHALL place an envelope in the
thread its authenticated thread field names — cross-thread injection of a
genuine envelope is thereby a signature failure, not a policy question
(review findings 1, 7).
Trace: [[#TEST-702]].

**REQ-703: Completion requires content.**
Completion-level checks (a fan-in member "present and Valid",
[[SPEC-014-role-layer-endpoint-projection#REQ-618]]) SHALL NOT be satisfied
by an envelope alone: full validity includes grammaticality of the payload,
so the role that decides a fan-in (the hub) still requires full messages.
A deployment MAY therefore widen with envelopes for safety and deliver full
content only to fan-in deciders — the two-tier reading the corpus table's
disclosure column motivates.
Trace: [[#TEST-703]].

**NFR-700: Envelope size.**
A redacted envelope SHALL be constant-size in the payload it redacts
(bounded by role-set size and `:caused-by` arity, both already bounded by
R2), so that the $O(n^2)$ widenings of the corpus (2PC votes, auction
prefix) cost $O(n^2)$ *headers*, not payloads.

**NFR-701: No payload disclosure.**
An envelope SHALL reveal no payload field of the message it redacts; in
particular the corpus repairs for two-buyer (share), 2PC (votes), OAuth
(passwd), and the announcing auction (bids) SHALL be expressible with zero
payload disclosure to the widened recipients.

**NFR-702: Metadata exposure bounded and stated.**
An envelope SHALL reveal exactly its declared fields — content hash,
performative name, sender key, recipient set, signature, `:caused-by`
references — and nothing else; and every consumer-facing statement of this
layer's guarantees (docs, the EPP paper's table) SHALL describe envelope
disclosure as *metadata-only*, never as *none*: performative type, speaker,
audience, and causal position are traffic-analysis-grade information (the
warehouse learning the branch is the knowledge-of-choice being delivered —
usually the point, occasionally the leak). Conversation-shape
confidentiality is a transport concern, explicitly out of scope here.

**REQ-709: Derived envelope routing (causal locality as compilation).**
A dialect MAY declare `(:causal-locality derive)` (default: `reject`, the
v1 behaviour). Under `derive`, an R6(vi) failure at either level SHALL NOT
reject the dialect; instead the installer SHALL compute the
\emph{envelope-widening closure} — for every violation
`NotCausallyLocal {t, pred, r}` (or per-occupant equivalent), add `r` as an
*envelope recipient* of `pred`, iterated to a fixpoint up the causal chain
(the paper's ``fails one level up'' rule), terminating because the protocol
DAG and role set are finite — and install the dialect with the resulting
per-performative envelope-routing table. Payload recipient sets
(`:to`) SHALL be unchanged.
Per review finding 3, derivation is two-level, mirroring R6 itself: the
installer derives the dialect-level closure at install, and the
per-occupant closure for an indexed role is derived at thread open as a
pure function of dialect and sealed cast (it cannot exist earlier — those
routes are $O(n^2)$ in a cast fixed only then); each level is deterministic,
so every agent derives identical routes — the replicated-choreographer
property extended from projection to repair.
The widened reading is made precise: an envelope recipient counts as an
endpoint role of the predecessor *for R6(vi) observability*, and projection
SHALL emit for each derived route an \emph{ExpectEnvelope} step (a
Recv-analogue carrying no payload obligation), so a widened role's local
protocol tells its verifier to await the envelope; Send/Recv steps and
payload delivery are untouched.
Corpus consequence: the seven R6(vi)-failing protocols of
[[SPEC-014-role-layer-endpoint-projection#TEST-640]] install under `derive`
with exactly the table's delivery counts as derived header routes and
metadata-only disclosure ([[#NFR-702]]).
Trace: [[#TEST-709]], decision [[#ADR-704]].

### Bounded repetition

**REQ-704: `(repeat k …)` protocol form.**
The protocol grammar SHALL admit `(repeat <k> <step>…)` with `<k>` a
positive integer literal; at dialect install the form SHALL macro-expand to
`k` sequential copies of its body (indexed performative instances chained
by `:caused-by` type references), after which R1–R3, R5, and R6 run over
the *expanded* protocol exactly as today. The expanded size SHALL count
against R2's declared bounds
([[SPEC-002-structural-contracts|SPEC-002]]), which is what keeps `k`
honest; no runtime construct is added, every protocol remains a finite DAG,
and [[SPEC-003-verification-lattice#REQ-308]] (DCFL preservation) is
unaffected.
Per review finding 5, expansion mechanics are normative: synthesised
per-copy names SHALL live in a namespace the parser cannot produce for user
symbols (index separator outside the legal symbol alphabet), so collision
with declared performatives is impossible by construction — the hazard
[[SPEC-014-role-layer-endpoint-projection#ADR-604]] avoided; each copy
inherits the base performative's role annotation, R3 protection applying to
the base name; and iteration seams are structural — a body ending in a
choice seams as `(any …)` over the alternatives' copy-instances, one ending
in a fan-in seams on the fan-in's copy-instance, chooser coherence holding
per copy.
Trace: [[#TEST-704]], grammar [[#CON-701]], decision [[#ADR-701]].

### Equivocation accountability

**REQ-705: Equivocation predicate.**
The store SHALL expose a monotone predicate `equivocation(key, thread)`
holding iff the store contains two distinct messages, both signed by `key`
(canonical identity, [[#REQ-708]] — spelling aliases MUST NOT evade the
predicate) in `thread`, that are (a) messages of two distinct alternatives of one
choice point whose chooser role `key` occupies (*choice* equivocation), or
(b) two distinct discharges of the same obligation instance — same
performative and occupant slot, different content hash (*obligation*
equivocation). Once true the predicate SHALL never revert (upward-closed in
the store), and it SHALL NOT alter any message's verdict: detection, not
exclusion ([[#ADR-703]]).
Trace: [[#TEST-705]].

**REQ-706: Transferable proof object.**
The layer SHALL define an equivocation *proof*: the pair of offending
signed messages (or their envelopes, per [[#REQ-701]]). Verifying a proof
SHALL require only the pair and the *pinned* dialect — the proof object
names the governing dialect's content hash
([[SPEC-014-role-layer-endpoint-projection#REQ-628]]) and verification
SHALL be against a dialect matching it, never a same-named substitute
(review finding 2) — with no store and no third-party testimony, exposed
as a pure function returning the convicted key or a typed rejection.
Envelope members carry their authenticated header and thread
([[#REQ-701]]), so relabelling a genuine message into a fake conflict fails
at the signature.
Trace: [[#TEST-706]].

**REQ-708: Signature-suite agility.**
Key material SHALL carry an algorithm identifier as part of key identity
(with [[Ed25519]] the v2 default and the unmarked legacy reading), the
attestation preimage SHALL name the suite ([[#ADR-700]]), and verification
SHALL dispatch on the identified suite. A signature, envelope, or cast
binding naming a suite the verifier does not implement SHALL yield a typed
rejection — never a skipped check, never a fallback guess
([[SPEC-002-structural-contracts|LangSec discipline]]: reject, don't
repair). Two keys identical in bytes but differing in suite are distinct
identities. This is the affordance for post-quantum or deployment-specific
schemes and for [[did:crdt]]-style typed identifiers; adding a suite is a
registry entry plus a dispatch arm, not a discipline version bump.
Key identity SHALL be canonical before any equality: an omitted suite
marker normalises to `ed25519` at parse, and equality is over the
(suite, key bytes) pair, never the surface spelling — `@alice` and
`@ed25519:alice` are one identity, so spelling aliases can neither evade
the equivocation predicate ([[#REQ-705]]) nor spuriously fail cast
conformance (review finding 4).
Trace: [[#TEST-708]].

**REQ-707: Choice-transparency lint (optional).**
The R6 checker MAY, behind an opt-in flag, warn when the alternatives of a
choice point share no common recipient role other than the chooser: under
such addressing no single honest endpoint is guaranteed to witness a choice
equivocation locally, and detection relies on proof gossip. The lint SHALL
be advisory (a warning, not a violation) — the corpus shows disjoint-branch
addressing is legitimate.
Trace: [[#TEST-707]].

## Architecture Decisions

**ADR-700: Sign a canonical attestation binding the header to the hash.**
*Decision (amended at adversarial review; human sign-off 2026-07-04)*:
R4 v2 signatures are computed over the RFC 9804 canonical bytes of a
domain-tagged attestation committing to the suite, the content hash, and
the message header:
`(cbcl-attest-v2 <suite> sha256:H <perf> <from> (<to>…) <thread> [<caused-by>])`
— rather than over the full canonical message bytes.
The original preimage named only suite and hash; the review showed that
leaves every header field a redacted verifier reads unauthenticated,
forgeable by any gossip relay holding a genuine (hash, signature) pair.
The attestation now says not ``I vouch for this content hash'' but ``I
vouch for this message: this type, from me, to these roles, in this
thread, citing these hashes, with this content hash.''
*Why not sign the full canonical message*: [[Ed25519]] verification takes
the message itself as input (its internal hash runs over the signed bytes),
so a signature over full canonical bytes is unverifiable from a redacted
envelope, defeating [[#REQ-701]] — the envelope holder would hold hearsay.
*Why not sign a bare digest*: signing unstructured 32-byte strings invites
cross-protocol substitution; the domain-tagged canonical attestation gives
the signature a single unambiguous meaning ("this key vouches for the
CBCL message with this content hash") and remains reconstructible by any
holder of the hash alone.
*Security accounting*: signing an attestation over the hash forfeits
Ed25519's collision resilience — signature security now reduces to
[[SHA-256]] collision resistance. In CBCL this introduces **no new
assumption**: content addressing, every `:caused-by` link, cast
tamper-evidence, and the Lean development's hash-injectivity axiom already
rest on exactly that; a collision forger can already rewrite causal history
without forging a signature. The signature becomes as strong as, and no
stronger than, everything else — no new weakest link.
*Alternatives rejected*: (a) sign full bytes and accept unverifiable
envelopes — hearsay, re-opens the spoofing surface; (b) countersigned
attestations by prior recipients — introduces a trust topology and message
growth. *Consequence*: one audited change in the R4 path.
*Algorithm agility*: the attestation names its signature suite —
`(cbcl-attest-v2 ed25519 sha256:…)` — mirroring the hash's existing
self-describing `sha256:` prefix, so the signed statement binds scheme,
hash algorithm, and content in one place and a signature can never be
re-interpreted under a different suite ([[#REQ-708]]). The `-v2` version
tag governs the *discipline* (what is signed); the suite field governs the
*algorithm* (how); they vary independently.

**ADR-701: Unrolling over μ-types.**
*Decision*: repetition enters as install-time macro-expansion
([[#REQ-704]]), not as recursive types. *Rationale*: μ-types would
surrender the finite obligation schema on which both DCFL-preservation
results and the finite-state verifier argument rest; unrolling keeps every
theorem and prices repetition in R2's existing declared-bounds currency.
*Ceiling*: unbounded interaction (true heartbeats, long-lived sessions)
remains out of scope; the upgrade path is thread chaining (a terminal act
opening a successor thread), which composes with sealed casts and is future
work beyond this spec.

**ADR-702: Widen evidence, not messages.**
*Decision*: the routine R6(vi) repair becomes envelope widening
([[#REQ-702]]) with full content reserved for fan-in deciders
([[#REQ-703]]). *Rationale*: the corpus shows the objection to widening is
disclosure, and role-local verification never reads the fields being
disclosed. *Relation to splicing*: this realises the deferred
splicing regime's goal (verify a dependency never received in full) without
rewritten predecessor views — raw hashes still verify, so
[[SPEC-014-role-layer-endpoint-projection#REQ-610]] stands.

**ADR-704: Derive, don't reject — but opt in.**
*Decision*: under `(:causal-locality derive)` ([[#REQ-709]]), R6(vi) stops
being a rejection condition and becomes a compilation step deriving
envelope routes; the default remains `reject`.
*Rationale*: with envelope widening costing constant-size headers and
metadata-only disclosure, rejection's remaining justification is thin —
five classically-unremarkable corpus protocols fail v1's check for want of
routing the substrate can now derive itself, purely and identically at
every endpoint.
*Why opt-in*: derivation silently enlarges delivery obligations and
metadata audiences; a dialect author should accept that consciously, and
`reject` preserves v1 semantics bit-for-bit. *Ceiling*: `derive` MAY become
the default in a later version after field experience; recorded here so
the flip is a documented decision, not drift.

**ADR-703: Detection, not exclusion.**
*Decision*: equivocation is detected and attributed, never excluded by
verdict. *Rationale*: exclusion requires reading arrival order or revoking
committed Valids — non-monotone either way, hence coordination-requiring by
[[CALM]]; the EPP paper's discussion section carries the argument. What a
deployment does with a convicted key is action policy above the verdict
lattice.

## Contracts

### CON-700: Redacted envelope grammar

```
envelope    := "(" "envelope" hash perf-name "(" key ")" "(" key* ")"
                   thread sig [":caused-by" caused-ref] ")"
attestation := "(" "cbcl-attest-v2" suite hash perf-name key
                   "(" key* ")" thread [caused-ref] ")"
                                 ; the signing preimage (ADR-700) — never
                                 ; transmitted; reconstructed by verifiers
hash        := "sha256:" hex64
perf-name   := symbol
thread      := string | symbol
key         := "@" [suite ":"] symbol  ; omitted suite normalises to ed25519
suite       := symbol                  ; registered signature-suite name
sig         := string         ; R4 v2 signature over the attestation
caused-ref  := hash | "(" hash+ ")" | "begin"
```

Full recognition before any semantic action; an envelope whose `hash` fails
to parse, whose role sets exceed R2 bounds, or which carries any additional
field SHALL be rejected, never repaired
([[SPEC-002-structural-contracts|LangSec discipline]]).

### CON-701: Repeat form grammar

```
repeat-form := "(" "repeat" nat protocol-step+ ")"
nat         := integer atom, positive, no leading zero
                 ; a post-parse predicate on the recognised atom, per the
                 ; CON-600 convention — not a lexical rule
```

`repeat` nests inside `(protocol …)` only; nested `repeat` multiplies
bounds and SHALL be counted multiplicatively against R2's expansion budget
at install.

### CON-702: Equivocation proof object

```
equiv-proof := "(" "equivocation" key thread dialect-hash member member ")"
dialect-hash := hash
member      := signed-message | envelope
```

Verification: both members parse; both signatures verify under `key`
(canonical identity); both carry `thread` (an envelope member's thread is
its authenticated field, CON-700); the named dialect hash matches the
verifier's installed dialect; and the pair satisfies clause (a) or (b) of
[[#REQ-705]] against that pinned dialect. Anything else is a typed
rejection.

## Test Specifications

**TEST-700: Envelope round-trip.** Redacting a parsed message yields an
envelope naming the same content hash; property-tested over generated
messages.

**TEST-701: Envelope verifiability.** An envelope's signature check
succeeds without the payload and fails under key substitution, hash
substitution, or field tampering.

**TEST-702: Corpus re-run under envelope widening.** Re-encode the corpus
repairs of [[SPEC-014-role-layer-endpoint-projection#TEST-640]] with
envelope deliveries in place of payload widenings: every R6 verdict is
unchanged, and no widened recipient receives a payload field
([[#NFR-701]]).

**TEST-703: Completion still requires content.** A fan-in decider whose
member reveals are present only as envelopes reports the fan-in
not-yet-complete; supplying full members completes it.

**TEST-704: Repeat expansion.** `(repeat 3 x y)` expands to the 6-step
chain; R1 accepts (no template recursion); an expansion exceeding declared
R2 bounds is rejected at install; R5/R6 verdicts over the expanded protocol
match a hand-unrolled equivalent; a user dialect declaring a symbol
lexically resembling a synthesised copy name still installs (no collision,
by namespace construction); bodies ending in `(any …)` and `(all …)`
expand with the specified seam edges and stay chooser-coherent per copy.

**TEST-705: Equivocation predicate.** Both forms (choice, obligation)
flip the predicate; adding messages never unflips it; verdicts of both
members remain Valid.

**TEST-706: Proof object.** A proof verifies from the pair alone; a forged
pair (different keys, different threads, compatible messages) is rejected
with the typed error.

**TEST-707: Transparency lint.** The OAuth dialect (branches share
recipient `client`) is lint-clean; a variant with disjoint branch
recipients warns; the flag off suppresses the lint.

**TEST-708: Suite agility.** An envelope naming an unimplemented suite
yields the typed rejection (not a pass, not a panic); the same key bytes
under two suites are distinct identities (cast conformance fails across
them); an ed25519 signature verifies only against an attestation naming
`ed25519`, never one naming another suite over the same hash.

**TEST-709: Derivation closure.** Under `(:causal-locality derive)`, every
R6(vi)-failing corpus dialect installs; its derived envelope routes equal
the hand-widened repair of
[[SPEC-014-role-layer-endpoint-projection#TEST-640]] read as envelope
recipients (transitive closure included: warehouse derivation covers
`track-shipment`, not just the deciding branch; announcing-auction
derivation covers `commit`, not just `reveal`); derivation is idempotent
and identical across independent installs; payload `:to` sets are
byte-identical before and after; under the default `reject` the v1
verdicts of TEST-640 are unchanged; indexed-role routes appear only in the
thread-open derivation (never the install-time table); and projection of a
derived dialect emits an ExpectEnvelope step for every route.

## Traceability

| Requirement | Tests | Decision |
|---|---|---|
| [[#REQ-700]] | [[#TEST-700]] | [[#ADR-702]] |
| [[#REQ-701]] | [[#TEST-701]] | [[#ADR-700]] |
| [[#REQ-702]] | [[#TEST-702]] | [[#ADR-702]] |
| [[#REQ-703]] | [[#TEST-703]] | [[#ADR-702]] |
| [[#REQ-704]] | [[#TEST-704]] | [[#ADR-701]] |
| [[#REQ-705]] | [[#TEST-705]] | [[#ADR-703]] |
| [[#REQ-706]] | [[#TEST-706]] | [[#ADR-703]] |
| [[#REQ-707]] | [[#TEST-707]] | [[#ADR-703]] |
| [[#REQ-708]] | [[#TEST-708]] | [[#ADR-700]] |
| [[#REQ-709]] | [[#TEST-709]] | [[#ADR-704]] |

## Changelog

- 0.1.3 (2026-07-04) — adversarial review (fresh context, PROTO-001
  principles 11–12) returned two blockers, four majors, two minors, two
  editorial; all accepted, amendments applied; ADR-700 amended and signed
  off by the author; status → approved. Load-bearing change: the
  attestation preimage now commits to the envelope header (performative,
  sender, recipients, thread, `:caused-by`) alongside suite and hash —
  binding the hash alone left every header field forgeable from gossiped
  (hash, signature) pairs and made equivocation proofs a framing tool.
  Also: explicit v1/v2 discipline marker (fail closed on envelope paths);
  proof objects pin the dialect hash; derivation split into install-time
  (dialect-level) and thread-open (per-occupant) with ExpectEnvelope
  projection steps; repeat-expansion naming confined to a non-user
  namespace with structural seams; canonical key identity over
  (suite, bytes); envelope grammar gains thread + attestation productions;
  `nat` restated as a post-parse predicate. Deferred with rationale:
  finding 9 (move REQ-708 out of the equivocation section) — placement
  churn deferred to the next structural edit.
- 0.1.2 (2026-07-04) — projected-table review before implementation.
  REQ-709/ADR-704: `(:causal-locality derive)` turns R6(vi) from rejection
  into compilation — the installer derives the envelope-widening closure as
  a pure function, so the corpus's seven failures install with the table's
  delivery counts as derived header routes (opt-in; `reject` stays the
  default). NFR-702: envelope disclosure is stated as metadata-only, never
  ``none'' — type, speaker, audience, and causal position remain visible,
  which is usually the knowledge-of-choice being delivered and occasionally
  the leak. TEST-709 pins the closure (transitive: warehouse ⇒
  track-shipment; announcing auction ⇒ commit).
- 0.1.1 (2026-07-04) — ADR-700 refined per review dialogue: the signing
  preimage is a canonical, domain-tagged attestation naming the content
  hash (not the full message bytes, which envelopes cannot verify; not a
  bare digest, which invites cross-protocol substitution), with the
  no-new-assumption security accounting recorded. REQ-708 added: signature
  -suite agility — suite named in key identity and attestation preimage,
  unknown suites a typed rejection, Ed25519 the unmarked default.
- 0.1.0 (2026-07-04) — initial draft from the corpus-study findings
  ([[SPEC-014-role-layer-endpoint-projection#TEST-640]]) and the EPP paper's
  adversary/equivocation analysis. Three features: redacted delivery,
  bounded repetition, equivocation accountability. Status draft pending
  human review of [[#ADR-700]] (signing-discipline change) and Phase 2
  planning.
