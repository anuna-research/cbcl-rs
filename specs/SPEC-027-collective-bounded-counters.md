---
id: SPEC-027
title: Collective bounded counters
version: 0.1.0
status: implemented
last-updated: 2026-10-31
---

# Collective bounded counters

Current runtime handoff rules are [[SPEC-031-unified-quorum-dag]]. Its DAG protocol
replaces this document's single-parent checkpoint APIs and compatibility assumptions;
the business declaration, authentication and resource-policy contracts remain
background for the current implementation.

## Orientation

A ticket pool must allow distinct authorized sellers to consume one shared capacity.
Account ownership currently selects a different budget for each signer, so it cannot
express this pool. Collective ownership separates the actor who authorizes an act
from the resource account charged by that act. Every actor uses the same pool epoch
and validator budgets. Business roles remain in extend declarations.

```text
Alice / seller -- signed sell --\
                               +--> one pool --> independent validator budgets
Bob / seller ---- signed sell -/                       |
                                              effects quorum
                                                      |
                                           known-final shared balance
```

`(ownership account)` is the default and preserves existing canonical hashes.
`(ownership collective)` requires quorum-budget certification, scalar initialization
and explicit role annotations. Collective counters support increment and decrement;
account transfers are absent. Optional ceiling derives pool headroom from genesis.
Transactions retain their real signer. Cancellation requires that transaction's
signer; another seller cannot cancel it. Any cast participant admitted by an operation
role can propose a pool checkpoint, subject to the existing full-journal and quorum
checks. Observation renders scalar rights/headroom with completeness unknown.

This reuses the single-parent checkpoint protocol in
[[SPEC-026-rust-quorum-certification]]. It does not implement Stingray multi-parent
version merges or consensus recovery. Contention can stall. Existing account-mode
behavior and separate signing/storage host contracts remain binding.
Controls: pinned ownership and pool identity; role and issuer checks; shared charges;
actual-signer cancellation; full sealed histories; one successor; no budget reset;
explicit final-view limits. [[SPEC-027-collective-bounded-counters#CON-2700]] governs
syntax, [[SPEC-027-collective-bounded-counters#CON-2701]] governs actor/pool separation,
and [[SPEC-027-collective-bounded-counters#TEST-2700]] governs acceptance evidence.

## Amendment Channels

The user authorizes collective pools and the proposed language syntax. No amendment
can silently add consensus or weaken journal, quorum, cancellation or checkpoint
safety. This Tier 1 library extension requires independent adversarial review.
Human security review remains a production deployment obligation. BCP 14 keywords
state measurable requirements. No deployment occurs in this change.

## REQ-2700: One shared budget with separate actors

A collective counter MUST charge all authorized actors to one shared resource scope.
The runtime MUST verify the actual actor's role and issuer authority independently
of that resource scope. Operation and effects certificates MUST remain separate.
Validates: [[SPEC-027-collective-bounded-counters#TEST-2700]].

## REQ-2701: Safe lifecycle and compatibility

Cancellation MUST require the original transaction actor. Pool checkpoints MUST
preserve cumulative accounting, seals, choices and durable recovery. Account-mode
hashes and runtime behavior MUST remain compatible. Unsupported declarations MUST
reject before installation or signing.
Validates: [[SPEC-027-collective-bounded-counters#TEST-2700]].

## CON-2700: Declaration grammar

```text
ownership := (ownership account) | (ownership collective)
initial-account := (initial-rights Verb :Field)
initial-collective := (initial Verb :Field)
certification := existing quorum-budget declaration
```

Omitted ownership means account. Account mode retains allocation-map initialization
and required transfer mappings. Collective mode requires scalar nonnegative integer
initial rights, increment/decrement mappings, issuers and explicit from roles on
all bound verbs. Its floor and optional ceiling use existing numeric bounds.
Initial collective headroom equals ceiling minus floor minus initial rights.
Collective initial-rights, initial-headroom, transfer and transfer-headroom options
reject. Account scalar initial rejects. Collective host-gate rejects.
Text and JSON authoring share recognition. Serialized rules default missing
ownership to account. Explicit account ownership has canonical omission.

## CON-2701: Resource scope and actor authorization

Each collective context has exactly one reserved resource scope, disjoint from key
identifiers, bound into context/epoch identities. The reserved `$collective` identity
MUST NOT appear in the authenticated cast, including typed or serde inputs. The signed act's original signer
remains unchanged. Every cost, credit, active epoch, charge, seal and manifest uses
that shared scope. Every business authorization uses the authenticated signer and
cast reconstructed from genesis. Caller Instance caches confer no authority.

Cancellation requests bind the operation and require its signer. A checkpoint
request additionally names an actual signing actor: that actor belongs to the cast
and occupies an operation's from role. Read-only cast members cannot choose pool
successors. Existing quorum, report inclusion and one-successor guards apply.
No multi-parent merge or timeout reclamation is introduced.

The public Rust view retains a resource map internally but renders collective rights
and optional headroom as scalar values, labelled ownership collective. Unknown
completeness remains explicit. Plain folds reject collective counters without the
certificate runtime. The collective specialization uses `ResourceScope = $collective`
for `Manifest.account`; signing identities remain actual actor keys. Other runtime
input types inherit the closed grammar in
[[SPEC-026-rust-quorum-certification#CON-2601]]. Configuration selects collective
ownership in a newly pinned dialect; changing it requires a new instance. Existing
instances remain pinned and cannot be downgraded or silently migrated.

Composition first: reuse the existing generic resource protocol and shared binder.
Add only an ownership distinction and actor-to-resource mapping. The Lean extension
models actor authorization separately and specializes existing resource safety;
it does not claim Rust extraction or multi-parent safety. Actual-signer cancellation
and checkpoint-proposer roles are tested Rust restrictions of the generic model;
the actor adapter does not add explicit theorems for those restrictions.

## TEST-2700: Core acceptance and adversaries

Core tests cover textual and JSON declarations, default/account hash equivalence,
serde compatibility, invalid combinations and role-less declarations. Concurrent
sellers share one budget and cannot obtain independent capacity by changing signers.
Test finality timing, ceiling/headroom, issuer checks, unauthorized casts, correct
signer cancellation, cross-actor refund checkpoints, late certificates, durable
recovery, CAS failure and successor splits. Existing account tests remain required.

Run workspace and no_std/serde checks. Mutate shared charging and cancellation/
checkpoint authorization and require real executed failures. Obtain independent
Orientation comprehension and adversarial review. Build the actor/resource Lean
model and preserve its existing safety assumptions. Evidence goes in outputs.
Validates: [[SPEC-027-collective-bounded-counters#REQ-2700]],
[[SPEC-027-collective-bounded-counters#REQ-2701]].

## Evidence and reading paths

[collective-implementation](https://git.anuna.io/anuna-research/cbcl-rs/src/commit/96d5858d427fb1e371e0a8f13ddf0b23c6c6c8f2/outputs/collective-implementation.md) records executed Rust and Lean checks, behavioral
mutations and independent review. Reviewers follow contracts to adversarial tests
and evidence. Implementers follow contracts to their validating tests and linked
requirements. Dialect authors read the collective section of the bounded-counter
concept page and the complete ticket example.

## Open scope

The maintainer owns multi-parent version merges, concrete networking/crypto/storage,
complete-history reads and formal Rust correspondence. The implemented lifecycle
continues to permit permanent stalls under contention.
