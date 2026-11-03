---
id: SPEC-033
title: Consensus-free owned counter completion
version: 0.3.0
status: implemented (abstract model and scoped runtime validation)
last-updated: 2026-11-02
---

# Owned counter completion

## Orientation

Intent: a correct logical owner must be able to spend its whole funded balance,
including the final base unit, without consensus or timeout refunds. The existing
fractional signing guard cannot do this. Execution/cancellation races can also
split votes permanently. Evidence: [counter-availability-investigation](https://git.anuna.io/anuna-research/cbcl-rs/src/commit/96d5858d427fb1e371e0a8f13ddf0b23c6c6c8f2/outputs/counter-availability-investigation.md).

One protocol has two internal phases:

```text
concurrent owner batch -> freeze new client issuance -> drain submitted work
                                                       |
                         owner-authorized drained manifest
                                                       |
               validators persist scope-wide seal before voting
                                                       |
                    seal QC -> owned continuation root
                                                       |
              one certified operation per version, full capacity
```

The seal is permanent for the account, carries complete historical signatures,
and requires actual effects/cancellation certificates for every held obligation.
Quorum intersection covers even old certificates assembled after sealing. A
continuation descendant uses one vote-once operation slot per version and the
full resource vector. New versions retain exact genesis-based books. No journal,
fence or old certificate is cleared. Accounts remain independent.

The durable owner driver admits requests FIFO, reserves their actual resource
cost, freezes before draining a finite submitted batch, and retries the identical
issued act. It never races an issued operation against cancellation. Large requests
and the final unit trigger the same handoff. Later small requests cannot bypass
that handoff. After conversion, one operation is completed before advancing the
owner's next version. Self credits and incoming credits require actual effects QCs.

Scope: account ownership only. Collective pools retain [[SPEC-031-unified-quorum-dag]]
semantics and receive no new arbitrary-contention liveness claim. No distributed
lock among independent devices is assumed; one coherent durable logical owner is
an explicit liveness condition. Byzantine owners retain safety but may stall their
own accounts. Existing language syntax and host signature separation remain.

Controls: [[SPEC-033-owned-counter-lifecycle#REQ-3300]] permanent authenticated seal;
[[SPEC-033-owned-counter-lifecycle#REQ-3301]] full-capacity vote-once continuation;
[[SPEC-033-owned-counter-lifecycle#REQ-3302]] durable nonstarving owner driver;
[[SPEC-033-owned-counter-lifecycle#REQ-3303]] conditional model safety/liveness;
[[SPEC-033-owned-counter-lifecycle#REQ-3304]] rejection/replay and integration.

## Amendment Channels

User explicitly requests proof and implementation. This Tier 1 protocol work
requires independent adversarial review and an Orientation comprehension check.
User no-consensus constraint cannot be waived. Human domain review is required
before production deployment, not before authorized local development. No changes
to collective ownership, money semantics or external signing authority are implicit.

## Requirements

### REQ-3300

An account-owned continuation seal MUST bind one owner-authorized DAG manifest,
context and resource scope. Owner seal intent MUST have a distinct OwnedSealRequest
signature domain; an ordinary VersionRequest signature MUST NOT authorize sealing.
Every held obligation MUST have an effects or
cancellation certificate; every local historical signature in that scope MUST be
held, including released and zero-cost signatures. The active version MUST be a
parent. A validator MUST persist its unique scope-wide seal before releasing its
seal signing request, MUST never vote for a different seal in that scope, and MUST
stop new concurrent signatures and ordinary concurrent adoption after sealing.
After a verified owned-root QC, forward adoption along that root's verified
pre-root ancestry MAY be used solely for catch-up; no fresh spending outside the
owned root is enabled. [[SPEC-034-owned-progress-closure#REQ-3401]] governs that
catch-up path. Retry of an identical old
signature MAY return the same vote. Manifest phase MUST be hash-bound. Owned roots MUST reject provisional adoption/signing
before a verified seal QC; an Owned parent MUST force Owned descendants.
A verified seal quorum activates the root;
local partial seal votes alone MUST NOT enable full-capacity signatures.
Trace: [[SPEC-033-owned-counter-lifecycle#CON-3300]], [[SPEC-033-owned-counter-lifecycle#TEST-3300]].

### REQ-3301

An owned root and its descendants MUST permit at most one distinct operation
signature per consumed version at each validator. Cost MUST fit the entire version
allocation in every coordinate, with no fractional multiplier. Existing authority,
exact books, thread/context binding, parent/rank checks, cumulative history coverage
and effects evidence MUST remain enforced. Operations outside the certified owned
root's descendants MUST NOT obtain fresh signatures. Owned signing MUST reject historical fences/cancellation QCs, including preactivation
fences. Owned operations MUST NOT
be cancellable; finalization is driven to completion. Another account's handoff
MUST NOT restrict this account. No root balance may be copied into a second live
continuation.
Trace: [[SPEC-033-owned-counter-lifecycle#CON-3300]], [[SPEC-033-owned-counter-lifecycle#TEST-3301]].

### REQ-3302

The owner driver MUST durably enqueue immutable requests, reject nonce reuse with
changed contents, reserve funded queued costs, and select FIFO. It MUST journal
the exact issued act before exposing it for signing/publication. Retries MUST reuse
that act. When a head request does not fit the concurrent envelope, it MUST freeze
new issuance, drain the finite already-issued set, select one complete manifest,
and await its actual seal QC before proceeding. It MUST not issue cancellation
for an issued request. No timeout MUST release resources. In owned mode it MUST
finish each request and advance a funded version before issuing the next. Recovery
MUST reconstruct decisions from the durable log rather than accept serialized
capacity caches.
Trace: [[SPEC-033-owned-counter-lifecycle#CON-3301]], [[SPEC-033-owned-counter-lifecycle#TEST-3302]].

### REQ-3303

Lean MUST prove seal coverage of every possible old certificate using honest
quorum intersection and permanent local closure. It MUST prove one certified
continuation choice per version and derive funded continuation safety from exact
books. Conditional liveness MUST derive honest quorum formation from enabled
honest actions and fair service, without Byzantine cooperation, a selected-winner
oracle or an assumed final/handoff certificate. The contract MUST state eventual
delivery, correct coherent owner, finite draining, stable metadata, authenticated
prerequisite availability and bounded-catalogue assumptions explicitly. Configured operation/version/journal
capacity MUST remain available for required honest steps; no protection against
unbounded storage-exhaustion attacks is claimed. Account independence is protocol
scope isolation under that service-capacity premise. The unit
balance and real spend-down examples MUST be nonvacuous. Rust correspondence
traces MUST compare actual outputs against the executable Lean model; no universal
source/network/crypto equivalence may be claimed.
Trace: [[SPEC-033-owned-counter-lifecycle#CON-3302]], [[SPEC-033-owned-counter-lifecycle#TEST-3303]].

### REQ-3304

Rejected or failed-journal transitions MUST expose no new vote and leave state
unchanged. Recovery MUST replay all new authorization, certificate, seal and slot
guards. Tests MUST exercise malicious owners, missing/wrong-scope evidence, late
old votes, divergent seals, full-balance spend, dual-resource replenishment,
FIFO/retries, failed writes and restarts. Existing collective tests MUST retain
semantics. Language-owned counter construction MUST expose the lifecycle without
a host protocol selector. Documentation MUST distinguish raw replica APIs from
the correct-owner driver and its liveness assumptions.
Trace: [[SPEC-033-owned-counter-lifecycle#TEST-3304]].

## Contracts

### CON-3300

New typed messages/events are `OwnedSealRequest { version: DagVersion, authorization: Vote }`
and
validator `OwnedSeal` votes/certificates. Owner authorization uses the distinct
`OwnedSealRequest` vote kind over exact manifest identity and context; normal
version authorization is insufficient. They use the existing bounded manifest
and authenticated vote grammar, with a distinct signature-domain tag. New local
`SealOwned` events persist the entire authorized manifest and seal decision.
Unknown fields/variants reject under existing serde policy. Operation grammar is
unchanged: `:escrow-prev` names an immutable version, dependency lists match its
certified credits, and nonce is stable. The Owned manifest phase is included in DAG identity v2 and inherited by descendants.
Activation is derived from a verified owned-root certificate and its ancestry, never
from the phase tag alone. Concurrent and Owned manifests cannot share an identity. Collective scope rejects.

### CON-3301

A typed append-only owner journal binds context, owner and sequence, with atomic
compare-and-append and signing after durable issuance. Requests contain immutable
business fields and nonce; a caller cannot supply a resource-cost cache as authority.
Owner actions expose pending evidence, an issued act, or a stable manifest to sign.
Host provides keys, reliable relay, validator journal and owner journal durability.
The driver is deterministic, no_std-capable and independent of clocks/network IO.

### CON-3302

The Lean boundary has fixed immutable transaction/version catalogues and ideal
authenticated signatures. Honest old-sign and seal transitions share the same
permanent journal; owned slot choices persist. A certificate is derived from votes,
not inserted as an unexplained balance update. Per-resource safety and fairness
arguments apply to a vector, including rights and headroom. Finite shared traces
exercise the actual Rust transitions and Lean executable guards.

## Tests

### TEST-3300

Positive: drained owner manifest seals with honest votes only. Negative-input:
collective/other account, wrong actor, missing historical signature and unsettled
held operation reject. Negative-output: late old votes cannot certify an uncovered
operation; seal/cert arrival and restart never reopen old issuance.
Validates: [[SPEC-033-owned-counter-lifecycle#REQ-3300]].

### TEST-3301

Positive: initial unit and full-balance debit sign/finalize in owned mode. Negative:
distinct same-version candidates, conflicting roots, fresh old-mode signing and
canceling an owned operation reject. Weakened guards MUST fail targeted tests.
Validates: [[SPEC-033-owned-counter-lifecycle#REQ-3301]].

### TEST-3302

Positive: FIFO queue crosses the envelope, freezes, drains and resumes; restart
reissues exactly the recorded act. Negative: changed nonce contents, unaffordable
queues, forged acknowledgements and failed append reject without lost reservation.
Later arrivals MUST NOT move ahead of a selected handoff request.
Validates: [[SPEC-033-owned-counter-lifecycle#REQ-3302]].

### TEST-3303

Kernel-check theorem suite with standard axioms only; no sorry/native_decide.
Executable witnesses include full unit spend, multiple spend-down steps, silent
Byzantine validator and a late old-certificate schedule. Perturb closure or
vote-once guards and observe regression failure. Independent review examines the
actual enabling premises and refined resource accounting.
Validates: [[SPEC-033-owned-counter-lifecycle#REQ-3303]].

### TEST-3304

Run account/collective runtime, real-crypto harness, no_std, Lean build/axiom audit,
changed-file formatting and journal-failure tests. Confirm signing remains separate
and no global winner/consensus service enters the implementation.
Validates: [[SPEC-033-owned-counter-lifecycle#REQ-3304]].


## Implementation and proof scope

[owned-lifecycle-evidence](https://git.anuna.io/anuna-research/cbcl-rs/src/commit/96d5858d427fb1e371e0a8f13ddf0b23c6c6c8f2/outputs/owned-lifecycle-evidence.md) records the implementation, independent adversarial
review, executable Lean/Rust traces and validation. Lean proves an abstract finite
catalogue model with ideal authentication, complete exact books, coherent owner
issuance/history conditions, and fair honest service. It includes authenticated
incoming-credit receipts, prior-fence exclusion and separate client observation.
It does not universally prove every Rust owner-driver/host schedule establishes
those premises, nor extract the Rust source from Lean. Concrete versions, external
receipt identity deduplication and wire/storage/crypto remain refinement boundaries;
selected traces and adversarial, recovery and real-crypto tests exercise them.
A universal owner-driver refinement is future proof work, not an implemented claim.


[[SPEC-034-owned-progress-closure]] extends the receiver/relay enable path and works
towards deriving the remaining owner readiness premises. Its independent retry and
financial-invariant proofs do not supersede the open universal product/refinement
obligation. Honest peers relay any operation certificate enabling their effects
response; completion responses carry the retained proof chain for owner verification.
