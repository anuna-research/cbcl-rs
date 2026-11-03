---
id: SPEC-025
title: Consensus-Free Bounded Counter Refinement
version: 0.1.0
status: implemented-model-safety-proof
last-updated: 2026-10-31
---

# Consensus-Free Bounded Counter Refinement

## Orientation

Intent: derive funded asynchronous business execution from independent validator
budgets, sealed epoch manifests and permanent cancellation certificates. There is
no consensus service, serialized reservation authority or global balance oracle.
[[SPEC-024-asynchronous-reservation-refinement]] records the rejected shortcut.

```text
 owner operation --> independent local budget signatures --> operation certificate
                                                                  |
                                                          effects signatures
                                                                  |
                                                          final certificate

 sealed old journals --> complete manifest --> vote-once checkpoint certificate
         |                                        |
  preserve late operations                  local epoch installation

 no-effects fence quorum --> release own charge --> cumulative manifest refund
```

Each honest validator charges its fixed conservative epoch allocation before
signing. It seals that journal before supporting a successor. A checkpoint carries
every disclosed candidate, including unfinished operations. Honest validators vote
for at most one successor statement per parent. Quorum intersection prevents two
conflicting certificates; it does not guarantee a certificate will form.
Conflicting owner proposals can stall without any recovery oracle choosing a winner.

An honest validator never signs both effects and a cancellation fence for the same
operation. Only a cancellation quorum can release an existing local charge. The
charge remains in immutable signature history; release is idempotent. Checkpoints
carry cumulative charged/released/credited ID sets, deriving fresh allocations
from genesis and authenticated final/cancellation evidence. Delayed old operation
certificates remain usable unless cancellation excludes their effects finality.

The proof archive records certificates that actually exist. Its account/depth slots
and maximum known depth are ghost bookkeeping for the proof, not an authority that
orders requests or grants capacity. Registration unconditionally records a valid
certificate, and nonforking must be proved from witness vote-once. Validators install
locally and may lag. All numeric admission guards use local signing journals or
immutable manifest arithmetic, never the business observation or ghost frontier.

Controls: no consensus assumptions; pinned immutable typed operations/manifests;
fixed n=3f+1, q=2f+1 and at most f Byzantine witnesses; signature authentication;
local budget guards; sealing before reports; complete honest frozen reports;
vote-once successors; monotonic certificate history; authenticated final credits;
permanent effects/fence exclusion; no timeout release; cancellation-backed refunds;
replay-safe local epoch installation; funded trace simulation derived from genesis.

[[SPEC-025-consensus-free-refinement#CON-2500]] defines executable transitions;
[[SPEC-025-consensus-free-refinement#CON-2501]] defines the proof obligations.
Progress is conditional. Byzantine withholding, split checkpoint votes, split
execution/fence votes and overloaded manifests can stall. Production storage,
cryptography and wire decoding remain explicit implementation boundaries.

## Amendment Channels

The user explicitly requires no consensus. No reviewer, previous design or proof
convenience can waive this constraint. The anuna-dev independent adversarial review
and Orientation comprehension gates apply. BCP 14 keywords name testable obligations.

## ADR-2500: Consistent certification without agreement termination

A checkpoint certificate proves one complete manifest has enough signatures. It
is not an agreement oracle: competing proposals cannot be forcibly resolved, and
correct parties are not required to decide during arbitrary contention. There is
no prepare/activation recovery decision or global ordering of operations.
The account/depth archive stores discovered certificates only. Witness local state,
not that archive's frontier, controls operation signing and epoch installation.

This extends [[SPEC-022-sealed-budget-checkpoints]] with cancellation-backed release.
The [[SPEC-023-abortable-budget-handoff]] consensus-based recovery branch is not used.
The original unsafe partial-renewal counterexample remains a regression subject.

## REQ-2500: Independent issuance and no ordering oracle

Operation signatures MUST depend only on immutable authentication, the signer's
installed epoch, seal state and local charged journal. No command or assumption
can authorize reservations by consensus or consult a shared available-balance ledger.
Checkpoint uniqueness MUST follow from actual vote-once journals and quorum
intersection. Registration MUST NOT select a winner with a first-writer guard.
Validates: [[SPEC-025-consensus-free-refinement#TEST-2500]].

## REQ-2501: Safe cancellation-backed reclamation

Honest effects and fence votes MUST exclude each other permanently per operation.
A local charge release MUST require a cancellation quorum and an existing signature.
Released signatures MUST remain in history. Cumulative refunds MUST remain subsets
of charged obligations and require cancellation evidence. Refunds and local release
MUST be idempotent. No released operation can finalize in a future trace.
Validates: [[SPEC-025-consensus-free-refinement#TEST-2500]].

## REQ-2502: Cross-epoch funded refinement

The protocol MUST derive local capacity, certificate uniqueness, past-certificate
coverage, final/cancel exclusion and authenticated credit provenance from genesis.
Every final business label MUST satisfy an independent source-funding condition.
All other transitions MUST stutter. No theorem can assume endpoint nonnegativity,
frontier completeness or a global consumption bound as a per-step oracle.
Validates: [[SPEC-025-consensus-free-refinement#TEST-2501]].

## CON-2500: Canonical executable model

Use immutable finite operation, checkpoint, account and resource IDs. Each resource
belongs to one account; operation costs belong to its epoch owner. Cost and credit
vectors are disjoint per resource, covering mint, burn, pay and headroom transfer.
Root epochs allocate genesis resources. A checkpoint names an owner, parent, depth,
cumulative charged/released/credited sets and proposed nonnegative allocations.

The archive and journal predicates represent supplied authenticated certificate
proofs. They are not runtime shared-state or honesty lookups. The finite-state
executor knows the arbitrary fault partition to overapproximate Byzantine actions;
real validators do not identify other honest validators. Honest journal completeness
follows from durable sealing, not an omniscient report checker.

State tracks local installed epochs, immutable signing journals, seal state,
checkpoint votes and per-parent choices. It also tracks effects/fences, local release
flags, received operation/finality proofs and the certificate archive with a ghost frontier.
Commands sign, seal, endorse, receive checkpoint, install, receive operation/finality
certificate, emit effects/fence, release a charge, relay and wait. Replays do not reset
journals. Invalid commands reject without changing state.

A fresh honest signature requires an installed matching epoch, no seal, authority,
and resulting per-resource net charges <= (f+1)*epoch allocation. Each signature
charges (2f+1)*operation cost. Local net charges exclude only locally released
signatures backed by cancellation quorums. Byzantine witness emissions are unrestricted
within the fixed roster; an arbitrary honest core models correct actor discipline.

Checkpoint validation verifies parent certificate and depth, cumulative sets and
source/context of held operations. It verifies final-credit and cancellation
certificates, nonnegative exact allocations and a sealing quorum whose honest
journals fit the manifest. Byzantine seal reports overapproximate arbitrary authenticated reports;
they impose no honest completeness obligation. Endorsement also requires an honest
voter's own seal/report and one choice per parent. Valid certificate registration
has no first-writer selection guard; prove overwrites agree with existing certificates.
Local installation follows the parent's epoch and requires the credited final proofs.

Fencing is a validator-internal action, not a new permissionless dialect message.
The safety model permits preemptive fencing; it proves no owner-cancellation
permission policy or liveness. A runtime can strengthen the fence guard with an
authenticated owner request. That authorization policy requires separate host tests.

## CON-2501: Full protocol-model safety refinement

Prove invariant preservation for every executable command. Derive a hole-free
nonforking archive from parent certificates and vote-once quorum exclusion. Derive
sealed journal stability and manifest coverage for every old certifiable operation.
Derive local capacity under sign and release. Use double counting to bound active
finalized consumption within each epoch, excluding cancelled signatures.

For each resource, select its owner's maximal known certified epoch only in the
proof. Past finalized costs are covered by that epoch's non-refunded obligations;
present finalized costs fit its allocation; manifested credits are a subset of
actual finalized credits. Derive nonnegative observations. Combine the post-step
bound with disjoint cost/credit vectors to derive funded independent business steps.
Lift the simulation to arbitrary finite executable schedules and infinite stepwise
executions. State typed-model and cryptographic/storage boundaries explicitly.

## TEST-2500: Executable counterexamples and mutations

Reproduce the 30-rights A/B/C schedule with delayed certificates. Test complete cuts
and rejected partial cuts. Exercise cancellation before/after finality, local capacity
release and refunds in later descendant manifests. Check stale installation, split
votes, late source certificates and lagging witnesses. Check duplicate credits/refunds,
zero-cost operations, issuer authority, rights/headroom transfers and uncapped issuance.
Mutate budget, seal, vote-once, cancellation or manifest guards. Require executed
assertion or kernel-proof failures. Explicitly exercise stalls without any oracle.
Validates: [[SPEC-025-consensus-free-refinement#REQ-2500]],
[[SPEC-025-consensus-free-refinement#REQ-2501]].

## TEST-2501: Derived refinement and independent proof review

Build the canonical executable function, all invariant and coverage lemmas, funded
one-step simulation and all-traces theorem without custom axioms or proof holes.
Run central axiom audit. Independent review MUST search for implicit ordering
oracles, assumed cross-epoch accounting, vacuity and the original counterexample.
Validates: [[SPEC-025-consensus-free-refinement#REQ-2502]].

## Evidence and typed business scope

`ConsensusFree/Core.lean` defines independent signing and certificate verification.
`Archive.lean` derives consistent, hole-free certificate recording without selection.
`Evidence.lean` and `Capacity.lean` derive honest journals and local budget bounds.
`Coverage.lean` derives old-certificate coverage and resource nonnegativity.
`Execution.lean` proves canonical command and finite/infinite trace refinement.
`Currency.lean` constructs mint/burn/pay/headroom vectors, derives their disjointness,
enforces owner and issuer authorization and proves capped conservation and bounds.

The proved currency ceiling is floor plus genesis rights plus genesis headroom.
Binding an external dialect ceiling to that allocation remains an initialization
and Rust correspondence obligation. Uncapped issuance has no upper-bound claim.
The proof quantifies over arbitrary finite typed operation/checkpoint/account/resource
universes; dynamic wire ID allocation is not mechanized.

The executable regressions are `ConsensusFree/Tests.lean` and `ConsensusFreeAudit.lean`.
The independent review checks are `proofs/validator-budget/consensus-free-independent-review.lean`.
`proofs/validator-budget/check_consensus_free.py` runs these checks and recompiles
isolated guard mutants through all affected proof modules. It also checks the
absence of balance/frontier/ledger signing inputs and a registration selection guard.
Those structural checks supplement independent review; they are not a general
static-analysis proof. Recorded outcomes are [archived consensus-free-checks.json](https://git.anuna.io/anuna-research/cbcl-rs/src/commit/96d5858d427fb1e371e0a8f13ddf0b23c6c6c8f2/outputs/consensus-free-checks.json).

Fresh-context cross-model review by `/root/consensus_free_design_review`
(gpt-6-astra) found no blocking safety defect or hidden ordering oracle. It checked
that invariant preservation uses pre-state facts, archive overwrite equality is
derived from certified parents and vote-once, and numeric safety precedes fundedness.
It independently checked typed capped conservation, issuer policy and regressions.
The Orientation reader distinguished consistent certification from agreement
termination and recognized the archive as proof bookkeeping.

## Open work

CBCL maintainer owns physical networking, durable honest journals, cryptographic
recognition and Rust correspondence. Liveness under arbitrary Byzantine contention
is not promised. No future optimization can silently introduce consensus.
