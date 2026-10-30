---
id: SPEC-026
title: Rust Quorum-Budget Certification Runtime
version: 0.1.0
status: implemented
last-updated: 2026-10-31
---

# Rust Quorum-Budget Certification Runtime

## Orientation

Implement [[SPEC-025-consensus-free-refinement]] in the Rust library without a
consensus service or shared reservation authority. Dialect business messages remain
mint/burn/pay. `(certification quorum-budget)` selects independent validator budgets;
validators default to a host-supplied authenticated instance roster, never invented
keys. Fault tolerance defaults to (n-1)/3 with exact n=3f+1 validation. An omitted
certification clause preserves legacy host-gate dialect semantics. Explicit quorum
selection never falls back to that gate. Reclamation always requires cancellation
quorums; it is not a tunable safety option.

```text
CBCL intend --> complete unsigned transaction --> owner signing layer
                                                      |
                                               authenticated act
                                                      |
                                           independent validator
                                                      |
                                     durable local decision journal
                                                      |
                                           unsigned vote preimage
                                                      |
                                             validator signer
                                                      |
                                       verified quorum certificate
```

Crypto and storage remain host layers. The core defines typed preimages, verifies
received votes through a host key verifier, and validates every certificate's
context/kind/payload/distinct-member quorum. It persists complete local decisions
before returning unsigned votes. Hosts supply atomic durable compare-and-append
journals per validator identity, not per account across validators. Restart replays
those records through validation. No private key or signing implementation enters
the core engine.

Epoch manifests preserve full sealed signing journals, cumulative charges/refunds
and finalized credits. Honest operation/effects/fence/checkpoint decisions follow
the model. Cancellation requests additionally require the account owner's signature.
Local release never erases signatures or fence evidence. Buffers and accepted
objects are bounded; hitting a limit refuses new work rather than discarding safety
journals. No timeout unlock or voting reset exists.

A finalized transaction is not a complete balance read. The new observation reports
verified known-final operations and a local evidence snapshot, with completeness
explicitly unknown. It never labels that numeric view as a quorum-certified or
latest account balance. Plain fold without certificate runtime state fails closed
for quorum rules. A host-backed fold/authoring API receives the engine explicitly.

Controls: no consensus fallback; immutable pinned instance/committee/domain;
positive integer amounts; owner/issuer/cast/role/shape checks; distinct authenticated
quorums; durable decisions before signatures; permanent effects/fence exclusion;
sealed full journals; one successor vote; exact manifest books; no fresh budget on
replay; bounded inputs; honest explicit observation scope; separate signing layer.

[[SPEC-026-rust-quorum-certification#CON-2600]] defines declaration/defaults;
[[SPEC-026-rust-quorum-certification#CON-2601]] defines the engine and journal;
[[SPEC-026-rust-quorum-certification#CON-2602]] defines binding and balance queries.
Formal Rust extraction, physical networking, real key implementations and durable
storage providers remain separate integration boundaries.

## Amendment Channels

The user authorizes Rust wiring, defaults, balance queries and separate transaction
signing. No channel can add consensus, silently downgrade quorum certification or
present local cached balance as a complete latest read. Independent cross-model
adversarial review and Orientation comprehension apply. Human security review remains
a production-release requirement; this work enables library integration, not deployment.
BCP 14 keywords describe testable obligations.

## REQ-2600: Explicit safe defaults

The parser MUST recognize host-gate and quorum-budget profiles. Missing profile
MUST preserve legacy behavior. Quorum defaults MUST require a pinned instance roster
and derive faults only from a valid 3f+1 committee. Duplicate members, malformed
options, mismatched bounds and forged roster substitutions MUST reject. Semantic
defaults and member order MUST canonicalize consistently.
Validates: [[SPEC-026-rust-quorum-certification#TEST-2600]].

## REQ-2601: Actual certificate and journal enforcement

Every vote MUST commit domain, instance, payload, kind and signer. Verification
MUST reject nonmembers, duplicate identities, forged signatures and cross-context
replays. Honest decisions MUST persist before a signing preimage becomes available.
CAS failure MUST leave local state and returned signing capability unchanged.
Replay MUST preserve choices, seals, effects, fences and release history. Local
budgets MUST govern concurrent signatures; no shared available balance is permitted.
Validates: [[SPEC-026-rust-quorum-certification#TEST-2601]].

## REQ-2602: Finality, reclamation and query truth

Operation certificates MUST NOT imply effects finality. Effects/fence signatures
MUST exclude each other. Owner-authorized cancellation and actual fence quorums
MUST precede release. Manifests MUST include complete signed report candidates,
including released candidates, and refund each ID once. Observations MUST include
only verified effects-final operations and expose local-view completeness limits.
Legacy ready observations MUST NOT be relabeled Byzantine-final balances.
Validates: [[SPEC-026-rust-quorum-certification#TEST-2601]],
[[SPEC-026-rust-quorum-certification#TEST-2602]].

## CON-2600: Declaration and normalization

Add certification configuration to CounterRule. Grammar:

```lisp
(certification host-gate)
(certification quorum-budget)
(certification quorum-budget (validators @v0 @v1 @v2 @v3))
(certification quorum-budget (validators @v0 @v1 @v2 @v3) (faults 1))
```

Omitted validators resolve from the authenticated deployment/instance context.
Omitted faults derive from roster size; empty rosters and sizes outside 3f+1 reject.
Explicit rosters normalize to sorted unique symbols; duplicates reject. Static
committee/fault pairs validate at parse/install time; deferred pairs validate at
instance binding. No committee derives from payment recipients or holder balances.
Canonical omission of default host-gate preserves existing dialect hashes.

## CON-2601: Pure engine and effectful host boundary

Implement a no_std/alloc-compatible module for context, owner-authenticated acts,
operation/effects/cancellation/checkpoint certificates, signed seal reports and
local validator state. Use existing canonical encoding and SHA-256 domains.
Signature verification is a host trait; signing remains external. Initialization
verifies authenticated/admitted genesis and pins dialect/thread/opener/field/roster.

The core accepts typed values rather than parsing another byte language. Its
external proof grammar is:

```text
Vote = { context: ContextId, kind: VoteKind, payload: EvidenceId,
         signer: Key, signature: Bytes }
VoteKind = Operation | Effects | Cancel | Seal | Checkpoint
         | CancelRequest | CheckpointRequest
Certificate = { kind: Operation|Effects|Cancel|Checkpoint,
                payload: EvidenceId, votes: Vec<Vote> }
SealReport = { epoch: EpochId, signed: Set<OperationId>, vote: Vote }
Resources = { rights: i128, headroom: i128 }
Manifest = { account: Key, parent: EpochId, depth: u64,
             held: Set<OperationId>, refunded: Set<OperationId>,
             credited: Set<OperationId>, allocation: Resources }
Proposal = { manifest: Manifest, reports: Vec<SealReport>, authorization: Vote }
Checkpoint = { proposal: Proposal, certificate: Certificate }
Event = Initialize | Candidate(Act) | Certificate(Certificate)
      | Proposal(Proposal) | Sign(OperationId) | Effect(OperationId)
      | Fence(Vote) | Seal(EpochId) | Endorse(EvidenceId)
      | Checkpoint(Checkpoint) | Release(OperationId) | Install(EpochId)
```

The IDs bind canonical typed encodings under versioned domains. Receipt recognizes
all semantic fields and complete proofs before journal mutation. Proof structs,
including nested resource allocations, reject unknown serde fields. Hosts recognize
normal CBCL acts with existing message parsers and bound decoding allocations before
constructing typed inputs. The runtime preflights candidate tree depth and size
before recursive identity rebuilding and authentication. Default limits and the
per-method contract are in docs/reference/quorum-runtime.md.

The JSON contract adapter accepts bounded nested arrays for certification options.
It delegates option names, arity and semantics to the existing state-rule recognizer.
Compiler nonce fields remain reserved in both authoring languages.

Placement follows composition first: retain existing canonical encoding, SHA-256,
role/shape checking, and the shared intent binder. A separate local state machine
is necessary because the existing owner-chain verifier assumes nonforking issuance;
it cannot implement the selected concurrent validator-budget model.

Methods register candidates, prepare local votes, receive verified certificates,
seal journals, draft/endorse/receive/install checkpoints, and release cancelled
charges. All mutations pass through a per-validator append journal with expected
sequence. Its complete typed events support deterministic checked recovery. No
constructor can silently start an empty journal for a previously active identity.
Do not claim physical durability from an in-memory test provider.

Cancellation is stricter than the safety model: a valid owner cancellation request
is required before emitting an honest fence. Quorum proofs remain independently
verified. Alternate seal-report bundles proving the same semantic manifest do not
change its ID. Conflicting genuine certificates fault instead of selecting a winner.
Limits prevent unbounded unauthenticated proof/cache admission; safety evidence is
never pruned to make room.

## CON-2602: Authoring and observation

Add a Rust authoring entry point that completes ordinary CBCL fields using a pinned
engine view. Compiler-owned previous/epoch evidence, dependencies and nonce are
filled before external owner signing. Caller-forged bookkeeping rejects. The
shared binder retains protocol/role/shape checks and validates the engine context.
Legacy authoring and observation reject quorum rules without the explicit engine.

A finalized view contains context ID, known effects-final operation IDs, rights,
optional headroom and total value. Its evidence-set digest is not a quorum-signed
balance snapshot. Label freshness/completeness as local/unknown. Include pending
certified operations separately. Expose this through Rust balance/fold methods;
stateless existing bindings never invent certificate evidence. Document that a final
view is not guaranteed latest, complete or equal to immediately signable capacity.

## TEST-2600: Parser, default and canonicalization checks

Test omitted and explicit host-gate compatibility and empty quorum shorthand.
Check default fault derivation, deferred roster rejection until binding and sorted
committee identity. Check invalid sizes/faults, duplicate/unknown options,
compile/parse roundtrips and serde/programmatic declaration validation.
Validates: [[SPEC-026-rust-quorum-certification#REQ-2600]].

## TEST-2601: End-to-end quorum runtime adversaries

Port the original triangle and cross-epoch cancellation/refund cases.
Exercise forged votes/owner acts/reports, missing payloads/proofs, wrong contexts,
stale epochs and same-parent splits. Check duplicate finality/refunds, cap and issuer
enforcement, storage failure, concurrent local CAS, crash recovery and alternate report bundles. Test
nonce identity, field forgery and no early effects/certified-balance claims.
Use deterministic host test signers; no production crypto claim follows.
Validates: [[SPEC-026-rust-quorum-certification#REQ-2601]],
[[SPEC-026-rust-quorum-certification#REQ-2602]].

## TEST-2602: Integration and literature review

Check the balance API's local evidence scope, legacy fold refusal for quorum rules,
actual language authoring path and separate signing layer. Run workspace, no_std
and serde builds. Mutate critical quorum/budget/fence guards and require failures.
Independent review MUST search for implicit consensus, unsafe restore, signature
confusion and read-completeness overclaims. Review the user-supplied bibliography
against primary sources, recording limitations and architectural implications.
Validates: [[SPEC-026-rust-quorum-certification#REQ-2602]].

## Evidence and integration scope

The implementation is in `crates/cbcl-core/src/quorum/` and `certification.rs`.
[[rust-quorum-implementation]] links executed workspace/no_std checks, runtime tests,
behavioral guard mutations, Orientation comprehension and independent security review.
[[consensusless-literature-review]] records the primary-source comparison requested
by the user. These records distinguish tested Rust/model correspondence from a
formal extraction proof.

Reading paths: reviewers follow the engine contract to adversarial tests and the
implementation evidence. Implementers follow each contract to its validating tests
and requirement. Stakeholders follow requirements to the bounded-counter concept
page and its worked allocation trace.

## Open work

CBCL maintainer owns formal Rust/Lean extraction, physical transport, concrete key
providers, production durable journals and complete-history/freshness read protocols.
This library does not start network services or deploy validators.
