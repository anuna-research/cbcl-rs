---
id: SPEC-030
title: Rust multi-parent counter refinement
version: 0.1.0
status: superseded
last-updated: 2026-10-31
---

# Rust multi-parent counter refinement

Runtime selection and collective-only implementation restrictions in this document
are superseded by [[SPEC-031-unified-quorum-dag]]. The dated implementation evidence
remains a record of that delivery, not the current host API contract.

## Orientation

Implement the collective numeric DAG protocol from
[[SPEC-029-multi-parent-counter-model]] in the Rust quorum runtime. That specification
governs the abstract protocol; this specification governs its Rust implementation
and correspondence layer. A host explicitly
selects multi-parent context construction. Its context identity separates signatures
and journals from the existing single-parent protocol. Existing construction keeps
its current behavior. Multi-parent contexts reject account ownership.

A version contains unique parent IDs, held/refunded/credited transaction sets,
a rank and exact genesis-based allocation. Allocation is genesis plus unique final credits minus held costs plus
cancellation-backed refunds. Verified versions become known metadata
without a checkpoint quorum. A validator adopts only when its current active version belongs to the target's
parent set and the target contains its complete immutable signature history. Adoption preserves
all signatures, fences and releases. No consensus or timeout recovery is added.

Real signed CBCL acts, owner-authorized versions, operation/effects/cancellation
certificates and per-validator durable replay reuse the existing implementation.
Signing stays external. Rust enforces every local guard without knowing which
validators are Byzantine. Lean's unrestricted Byzantine actions are an adversarial
overapproximation, not executable validator behavior.

Shared Lean-generated execution traces compare Rust admission and projected state
step by step. Lean proves the reference interpreter generates valid abstract runs;
the differential suite checks the actual Rust runtime against those runs.
This establishes tested transition correspondence, not universal Rust source-code
equivalence or a cryptographic/network proof. Fixed machine-integer limits and
bounded catalogue admission fail closed. Infinite fresh-ID refinement remains open.

[[SPEC-030-rust-multi-parent-refinement#CON-3000]] defines protocol isolation and
handoff guards. [[SPEC-030-rust-multi-parent-refinement#CON-3001]] defines projection
and shared traces. [[SPEC-030-rust-multi-parent-refinement#TEST-3000]] defines acceptance.

## Amendment Channels

The user authorizes Rust implementation matching the Lean model. This is Tier 1
financial safety code. Fresh comprehension and independent cross-model adversarial
review apply. Human domain review precedes production deployment; no deployment is
requested here. The coordinator owns implementation, evidence and remaining proof
limitations. Wire decoding remains the bounded host boundary from
[[SPEC-026-rust-quorum-certification]].

## REQ-3000: Durable consensus-free DAG execution

Collective multi-parent contexts MUST validate and locally adopt covering DAG
versions without checkpoint votes or successor selection. They MUST preserve all
historical evidence across adoption, retry and recovery. Signed request identities
MUST bind complete context and immutable payloads.
Validates: [[SPEC-030-rust-multi-parent-refinement#TEST-3000]].

## REQ-3001: Model correspondence and rejection evidence

Rust transitions MUST match the documented honest-validator projection of the Lean
reference on shared executable traces. Rejections MUST leave state and journal
sequence unchanged. Arithmetic overflow and missing prerequisites MUST reject.
Acceptance MUST distinguish differential evidence from formal source equivalence.
Validates: [[SPEC-030-rust-multi-parent-refinement#TEST-3000]].

## CON-3000: Context, typed inputs and local transitions

The host selects `Context::from_instance_multi_parent`; existing `from_instance`
continues the single-parent protocol. Multi-parent context hashing uses a distinct
domain. Opposite-mode version/checkpoint/seal/install events MUST reject, including
on journal recovery. Existing CBCL dialect syntax and transaction signing remain.
No in-place journal migration or quorum change is supplied.

Typed input grammar, recognized fully before committing semantic state:

```text
VersionManifest := { account: PinnedPool, parents: Set<KnownVersionId>, rank: u64,
                     held: Set<KnownTxId>, refunded: Set<KnownTxId>,
                     credited: Set<KnownTxId>, allocation: Resources<i128> }
Version := { manifest: VersionManifest, authorization: SignedVersionRequest }
DagEvent := Version(Version) | AdoptVersion(KnownVersionId)
```

The version ID hashes all manifest fields under a distinct semantic domain.
Version authorization MUST authenticate an eligible actual actor, never the pool.
Parent sets MUST be nonempty, bounded, known and have lower rank. Held operation
source versions MUST also have lower rank. Rank is a well-founded graph label,
not a globally agreed transaction sequence; siblings can share rank. Sorting finite
known nodes by `(rank, id)` gives the Lean topological naming representation.

Each parent held/refund/credit set MUST be included. Refunds MUST belong to held
and carry cancellation QCs; credits MUST carry effects QCs. Every allocation MUST
be nonnegative and equal genesis plus unique credits minus unique held costs plus
unique refunds. No parent allowances are added. Local adoption MUST require the
active version in the parent set and the entire signed-ID set in held. Cached
same-version adoption and previously durable signing retries are stuttering.

Per-version local charge, effects/fence exclusion and cancellation-backed release
reuse the existing guards. Every new event MUST use tentative apply, atomic append,
then exposure; failure restores state. Recovery MUST re-run those same guards.
Evidence is never garbage-collected to regain capacity. Resource-vector disjointness
holds for collective mint/burn; account transfers are outside this new mode.

## CON-3001: Projection and execution oracle

Rust content hashes map to fixed Lean version/transaction IDs in each finite test
catalogue. Each validator's journal gives active version, visited versions, signed,
released, effects and fences. Verified version reception maps to Lean `record`;
adoption maps to `adopt`. Registration, evidence delivery and idempotent retries
map to abstract stuttering. Externally emitted votes map to honest sign/effect/fence
steps. Certificate availability maps to authenticated quorum evidence with arbitrary
message delay. Complete signature validity and durable append are host assumptions.

The shared oracle MUST execute the existing Lean `perform` guards through a
checked API adapter. For honest transaction commands the adapter MUST require known
source metadata, matching candidate registration. For version receipt it MUST
require known source metadata for every held or credited input. Non-core Byzantine
transaction commands remain unrestricted. Release MUST require an own signature.
Already signed requests and adoption of the current version MUST stutter as retries.
The adapter MUST prove every accepted command generates an abstract `Step`; it
MUST NOT change the abstract `perform` guards to fit Rust.

The shared oracle MUST emit admission results plus projected state after each
command. Shared traces synchronize validated version metadata and deliver QCs at
quorum formation. Separate Rust boundary tests MUST delay operation/finality
certificates and version metadata to check local prerequisites. These synchronized
traces do not model every possible network delivery schedule. Rust conformance tests MUST invoke
production APIs and compare those results, including rejected events. The fixture
checker MUST regenerate and compare oracle output. Evidence MUST cover the gap
between global certificate availability and locally received certificates; it MUST
NOT claim bidirectional wire or universal source equivalence.

## TEST-3000: Runtime and correspondence acceptance

Core acceptance MUST execute genuine A/B-to-M adoption, shared debit/credit
deduplication, late old certificates, cancellation-assisted crowded joins and
safe releases. It MUST reject omitted history even after release, missing parents, wrong ranks,
incorrect books, uncertified funding and sibling/backward adoption. Forged authority,
budget overflow, wrong protocol mode and unsafe replay MUST also reject.
Atomic-append failure, stale-process CAS, retries and recovery MUST retain evidence.

Shared Lean/Rust traces MUST check admission and projected states at each step.
An unmodified control MUST pass. Deliberately weakened adoption, books,
cancellation and budget guards MUST produce real failures. Workspace tests, no-std check and scoped
Clippy MUST pass. New Lean oracle code MUST kernel-check without sorry/custom
axioms/native_decide. Independent review MUST examine the actual runtime and shared
trace coverage, including specification/implementation gaps.
Validates: [[SPEC-030-rust-multi-parent-refinement#REQ-3000]],
[[SPEC-030-rust-multi-parent-refinement#REQ-3001]].

## Implementation and evidence

The opt-in runtime is implemented in `cbcl_core::quorum`, with shared oracle
`lean-cbcl/MultiParentRustOracle.lean` and fixture
`test-vectors/quorum/multi-parent-lean.json`. The fixture has a dedicated directory
because the state-fold corpus uses a different schema. Candidate source metadata,
own-charge release and durable retries are explicit adapter boundaries.

The reference adapter and oracle-run safety kernel-check. Workspace tests,
no-std, fixture regeneration, runtime boundary tests and production guard mutations
pass. Scoped Clippy reports no diagnostics in the changed runtime/test files;
strict global lint reports unrelated findings in unchanged modules. Independent
cross-model review accepted the documented scope. Recorded commands, outcomes and
limitations are [[rust-multi-parent-evidence]], with review details in
[[rust-multi-parent-review]]. These output-page links sit outside the specs-only
vault scan; the coordinator owns their vault-integration backlog.

Universal Rust source equivalence, packet/crypto verification, physical durability,
account DAGs and growing-catalogue refinement remain open work owned by the
coordinator. This implementation supplies no production deployment or migration.
