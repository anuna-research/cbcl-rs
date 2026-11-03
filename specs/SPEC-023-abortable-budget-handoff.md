---
id: SPEC-023
title: Abortable Handoff for Concurrent Resource Checkpoints
version: 0.2.0
status: historical-consensus-research
last-updated: 2026-10-31
---

# Abortable Handoff for Concurrent Resource Checkpoints

## Orientation

Historical experiment: its abstract consensus fallback is not selected for the
user's consensus-free design. [[SPEC-025-consensus-free-refinement]] implements the
current independent-budget profile. This document preserves the earlier research.

Intent: recover from split checkpoint votes without forgetting finalized effects or
old payments that can still obtain certificates. Metaphor: hand the next protocol
a sealed manifest before letting it take over the account. This separate symbolic
profile builds on [[SPEC-022-sealed-budget-checkpoints]]; it implements neither
production BFT consensus nor the published Abstract ordered-history interface.

```text
 concurrent operation signing
              |
       sealed checkpoint
              |
     prepare quorum --> activation quorum --> install successor
              |
          stall / abort
              |
    freeze + quorum handoff reports
              |
    abstract one-shot consensus --> install recovered successor
```

A prepared checkpoint alone cannot activate the next epoch. Honest validators
record its complete prepare certificate before issuing activation votes. Aborting
freezes operation signing, checkpoint preparation and activation for that parent,
then exports the signed-operation journal and any known prepare certificate.
A handoff contains authenticated reports from a quorum. If any report carries a
valid prepare certificate, recovery MUST choose that exact checkpoint; otherwise
it can choose a valid complete checkpoint containing all reported candidates.
A hidden activation certificate necessarily intersects the abort quorum at an
honest validator whose report preserves its prepared checkpoint. Split prepare
votes without a certificate can be superseded by the recovery decision.

The recovery decision is supplied by an explicitly abstract unique consensus
service keyed by profile/genesis/account/parent. Delivery is asynchronous. Its
agreement, external validity, authentication and persistence are assumptions,
not implemented or proved BFT. Liveness requires an appropriate eventual-synchrony
or randomized-consensus implementation, honest availability and payload delivery.
No cancellation occurs. Overloaded candidate unions can still block recovery.
Old operation certificates remain valid and their costs stay reserved. A late
activation certificate names the same successor as recovery; installing it after
that successor is already active is an idempotent replay, and it cannot roll back
a later epoch. Replaying
either installation path never renews an already-spent journal.

Controls: fixed n=3f+1 and q=2f+1; at most f Byzantine witnesses; pinned profile and
parent; authenticated complete frozen reports; prepare before activate; recorded
prepare evidence before activation; abort before publication; no fresh old votes
after abort; quorum evidence recognition; pinned recovery choice when evidence
exists; one abstract consensus decision per parent; cumulative obligations and
finalized credits; no timeout release, cancellation or bare checkpoint install.

[[SPEC-023-abortable-budget-handoff#ADR-2300]] decides the extra activation phase;
[[SPEC-023-abortable-budget-handoff#CON-2300]] defines the executable boundary;
[[SPEC-023-abortable-budget-handoff#TEST-2300]] owns schedules and mutations;
[[SPEC-023-abortable-budget-handoff#CON-2301]] owns the scoped Lean proof.

## Amendment Channels

The user authorized this experiment. The anuna-dev workflow requires independent
cross-model adversarial review and an Orientation-only comprehension gate. Human
security review is a production gate; this prototype does not enable runtime use.
No review can waive preserving irreversible effects and possible old certificates.

## ADR-2300: Activation evidence makes switching safe

Abstract's Abort Order preserves every commit history across abort histories, and
Init Order preserves their common prefix in the next instance. Its abort is a
protocol handoff, not proof that a request never executed. Source: [The Next 700
BFT Protocols, section 3](https://www.iijlab.net/en/members/pierrelouis/tocs-700.pdf).
An accessible [EPFL copy](https://infoscience.epfl.ch/bitstreams/2dbb180b-39dd-46ae-b2a0-03061a1f75f7/download)
also states these ordered-history rules. Our commutative operation sets require a new preservation contract; the paper's
ordered-history composition theorem does not directly apply.

Simply clearing vote-once choices on recovery is unsafe: a withheld old checkpoint
certificate permits installing a competing successor. A second phase ensures that
any potentially activated checkpoint leaves prepare-certificate evidence at an
honest member of every abort quorum. Prepare vote-once also means two distinct
valid prepare certificates cannot coexist. Recovery can honor that evidence even
if no full activation certificate has yet been assembled.

This is composition of existing sealed accounting and an abstract agreement
service, rather than a new production consensus protocol. The extra phase costs
latency. It resolves split votes only when a valid non-overloaded checkpoint can
be selected. It intentionally does not reclaim abandoned reservations.

## REQ-2300: Preserve effects and potentially active successors

When recovery decides a successor, every previously or subsequently valid fast
activation certificate for the parent MUST name that same semantic successor.
Every certified old operation MUST remain reserved in the successor. Switching
MUST NOT erase operation votes, effects, finalized receipts or old budgets.
Trace: [[SPEC-023-abortable-budget-handoff#TEST-2300]].

## REQ-2301: Freeze before exporting handoff evidence

An honest abort action MUST seal its operation journal and stop fresh checkpoint
prepare and activation votes before publishing its immutable authenticated report.
The report MUST include any prepare certificate known through activation or fast
installation. Retries MUST return the same report; cached old signatures remain
relayable. Source identities and numeric fields MUST be canonical, rejecting
Python bool/integer and float/integer aliases.
Trace: [[SPEC-023-abortable-budget-handoff#TEST-2300]].

## REQ-2302: Explicit agreement boundary and replay safety

Recovery MUST require an authenticated decision from the abstract unique agreement
instance for this parent. Local timers, a mere report quorum or a proposer cannot
create that decision. Recovery MAY supersede split prepare votes only under that
decision. Installing fast or recovered successors MUST extend the active parent;
replaying the same successor MUST preserve its spent journal. Ancestors cannot
roll back current state. No cancellation or direct use of the old install API.
Trace: [[SPEC-023-abortable-budget-handoff#TEST-2300]].

## CON-2300: Symbolic handoff implementation

Implement a separate `HandoffModel(SealedModel)` in
`proofs/validator-budget/handoff_model.py`, with a distinct genesis profile.
Maintain monotonic prepared evidence, activation signatures, stopped witnesses,
immutable authenticated abort reports and abstract decisions. Ordinary operation
certification and effects delivery retain the sealed model's rules.

The fast certificate has q actual prepare votes on the semantic checkpoint.
Activation has q actual activation votes. Each honest activation vote follows
validation and recording of prepare evidence. Both bundles reject duplicates, nonmembers and
forgery. Honest preparation and activation stop once that witness aborts. A fast
installation requires both certificates and records prepare evidence locally.

A handoff report binds genesis, account, parent, witness, signed candidate set and
optional prepare-certificate ID. It is authenticated symbolically by a monotonic
issuance registry. Its complete certificate/payload remains available in the
model. Quorum handoff validation checks canonical fields, distinct members,
authentication and common context. Reports with prepare evidence pin the same
unique checkpoint; reject inconsistent evidence. Without such evidence, choose a
complete checkpoint containing the union of all handoff candidate sets, preserving
prior cumulative books and accepting only finalized credits. A pinned checkpoint
MAY omit uncertified partial candidates outside its original seal quorum: those
cannot obtain an old operation certificate. Every possibly certifiable operation MUST
remain reserved.

`decide_recovery` represents external-validity checking followed by an abstract
one-shot agreement oracle. It is NOT a validator vote, implemented consensus, or
a global finalized-balance admission guard. Its immutable authenticated decision
is scoped by genesis/account/parent; repeating the same outcome is idempotent,
while another outcome is rejected by the oracle's assumed agreement. Tests MUST
label this boundary and MUST NOT count that rejection as a proof of consensus.
Each witness separately receives and installs the decision, so lagging witnesses
can still relay cached old certificates and catch up sequentially.

## CON-2301: Scoped handoff proof

Add a Lean local transition model with operation identity sets, activation choice,
frozen abort snapshots and a reachability invariant. Prove that an honest aborted
witness cannot grow its signed set or change its exported activation knowledge.
Combine that invariant with honest quorum intersection to show that a valid
activation quorum leaves matching evidence in any valid handoff quorum. State
prepare-certificate uniqueness and abstract agreement as explicit boundaries unless
derived. Do not claim the complete Python lifecycle or Abstract composition theorem
is verified. Existing full async refinement obligations remain open.
Trace: [[SPEC-023-abortable-budget-handoff#TEST-2301]].

## TEST-2300: Executable schedules and falsification

Test split prepare votes followed by successful recovery. Hide an activation quorum
until after abort. Disclose a prepare certificate before an activation quorum exists.
Certify an old operation after handoff. Replay the A/B/C 30-rights regression.
Check abort blocking fresh prepares, activations and operations, with immutable
reports and cached retries. Reject forged, cross-context, duplicate, nonmember and
ill-typed proofs. Check successor replay preserving spent budgets, async sequential
catch-up, unchanged finalized effects, ceiling headroom and uncapped operation.
Refuse overloaded manifests, one-phase installation and cancellation. Inject isolated mutations
that omit prepare evidence, allow activation after abort, ignore the pinned choice,
or reset an installed journal. Require executed assertion failures.

## TEST-2301: Lean proof checks

Build local transition invariants and quorum-preservation theorem without custom
axioms or proof holes; include main import and central axiom audit. Mutate a
load-bearing freeze guard and require proof failure. Independent review MUST name
remaining transition correspondence and agreement assumptions.

## Plan and evidence

CBCL maintainer owns the Elephant tasks `abortable-handoff-model`
([[SPEC-023-abortable-budget-handoff#CON-2300]] /
[[SPEC-023-abortable-budget-handoff#TEST-2300]]) and `abortable-handoff-lean`
([[SPEC-023-abortable-budget-handoff#CON-2301]] /
[[SPEC-023-abortable-budget-handoff#TEST-2301]]) in theory
`spec-020-resource-agreement`. Both require this design; acceptance is isolated
executable evidence plus independent review, not production release.

The executable model and test runner are `proofs/validator-budget/handoff_model.py`
and `check_handoff.py`. Recorded outcomes are [archived abortable-handoff-checks.json](https://git.anuna.io/anuna-research/cbcl-rs/src/commit/96d5858d427fb1e371e0a8f13ddf0b23c6c6c8f2/outputs/abortable-handoff-checks.json)
and [archived abortable-handoff-quorum-audit.json](https://git.anuna.io/anuna-research/cbcl-rs/src/commit/96d5858d427fb1e371e0a8f13ddf0b23c6c6c8f2/outputs/abortable-handoff-quorum-audit.json); the latter is reproduced by
`proofs/validator-budget/handoff-independent-quorum-audit.py`. The runner's `--lean-mutation`
option checks the weakened activation freeze guard.

Independent fresh-context review by `/root/handoff_adversarial_review`
(gpt-6-astra) found no blocking defect within this scope. The Orientation-only
reader correctly predicted hidden-certificate preservation and the consensus
boundary. Its late-installation question is resolved explicitly in the Orientation.

The Lean module `LeanCbcl/AbortableHandoff.lean` proves frozen identity sets and
activation votes by local transition induction. It composes reachable snapshot
validity with a selected handoff quorum. It derives preservation under a recovery
selection that honors exported evidence. `prepare_unique` still takes honest prepare
vote-once as a premise; the recovery theorem takes honoring evidence as a premise.
External consensus agreement is assumed. The Lean `activated` field denotes an
issued activation vote. Python can learn extra `known_prepared` evidence on late
fast delivery after abort. Its already-issued report remains immutable;
that stronger knowledge is outside this minimal Lean projection. The projection,
Python correspondence, installation/accounting composition and full asynchronous
refinement remain unmechanized. The existing [[SPEC-022-sealed-budget-checkpoints#Evidence and remaining proof obligations]] are not closed by
these new local lemmas.

Synthesis trajectory: partial-epoch renewal was refuted. Sealed cuts repaired the
known schedule but stalled on split votes. Direct recovery overrides
risk hidden fast certificates. Prepare-before-activation adds evidence at every
potential handoff intersection. We retained conservative obligations and an
explicit agreement oracle, rather than claim cancellation or implemented BFT.

## Open work

CBCL maintainer owns these tasks:

- Implement a real BFT recovery service and its durable adapters.
- Prove full asynchronous resource refinement and ordered/generalized composition.
- Provide Byzantine payload retention.
- Design safe cancellation and reclaiming.
- Handle arbitrary overloaded manifests.
- Quantify fallback cost and progress under contention.
 No Abstract compatibility or production deployment claim is made.
