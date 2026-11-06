---
id: SPEC-037
title: Strong eventual consistency of the typed state kernel
status: implemented
version: 0.1.0
last-updated: 2026-11-06
---

# Strong eventual consistency of the typed state kernel

## Orientation

Intent: compose [[SPEC-036-state-kernel-correctness]] with delivery and fair
admission to prove strong eventual consistency. The named failure is **replicas
agree only after assuming their convergence**. Equal accepted sets must imply equal
observations independently of delivery order. Eventual acceptance must follow from
receipt, dependency availability and scheduling fairness, not be assumed.

For example, a child act may arrive before its required causal predecessor. It
remains pending until that evidence arrives. Replacement references alone do not
create admission dependencies. Delivery order can change intermediate observations,
but replicas with the same accepted acts agree. After the complete finite valid
history has arrived and been processed, their observations remain equal.
An infinite stream may keep changing forever; each valid act must
still eventually be incorporated.

The proof uses typed acts, immutable dialect context and unique content addresses.
Fairness schedules continuously enabled pending acts. Delivery eventually supplies
every act in the valid history; finite ranked dependencies eventually enable each
act. No false rejection of those valid acts is permitted. These are explicit
protocol/admission premises, not consequences of state arithmetic.

Replicas share one immutable interpretation context and the same evidence
providers. Progress evidence and delegated resource-verifier outcomes must be
set-extensional functions of accepted acts. Their classification and finalization
liveness remain separate obligations. No Rust, transport, cryptographic, clock
honesty, renderer or universal business-progress theorem is claimed.

Controls: REQ-3700 strong convergence, REQ-3701 eventual acceptance,
REQ-3702 finite-history convergence, REQ-3703 boundary/falsification.
Next actor: CBCL maintainer reviews the premises and verification evidence.
Reviewer path: Orientation then theorem contracts. Implementer path: contracts,
proofs and tests. Paper-author path: evidence and exclusions.

## Amendment Channels

The user authorizes proofs of strong eventual consistency on the existing branch.
No runtime semantics, admission rules or wire format changes are authorized by this
proof task. An external verifier law cannot be described as a proved classifier.

## REQ-3700: Strong convergence

For arbitrary supported compiled clauses and unique-address accepted histories,
set equality MUST imply extensional observation equality. This MUST include
replacement/domain selections, HLC/address arbitration, exact sums, maps, events,
histograms, progress and the delegated resource port. Ordered field names MUST be
preserved; map enumeration order and unsupported reads are unobservable.
Trace: [[SPEC-037-state-kernel-sec#TEST-3700]].

## REQ-3701: Eventual acceptance from execution

The proof MUST use StateRefinement's receive/pending/accept/reject/wait/idle steps.
Given eventual receipt, fair processing, finite ranked dependencies and valid
admission obligations, every valid act MUST eventually be accepted and remain accepted.
Fairness MUST concern scheduling transitions, not assume eventual acceptance.
Trace: [[SPEC-037-state-kernel-sec#TEST-3701]].

## REQ-3702: Eventual convergence

For a complete finite valid history without extraneous acts, replicas MUST
eventually maintain accepted-set equality and stable observation agreement. Infinite histories need not have a
final value: per-act eventual acceptance and equal-set agreement still apply.
Trace: [[SPEC-037-state-kernel-sec#TEST-3702]].

## REQ-3703: Explicit assumptions and falsification

The model MUST expose immutable context and set-extensional evidence ports.
Admission enabling, no false rejection, delivery and fairness MUST be inspectable
premises. The proof MUST introduce no sorry or custom axioms. Mutations MUST
invalidate the corresponding proofs. Independent review MUST inspect vacuity,
fairness and extension boundaries. Trace: [[SPEC-037-state-kernel-sec#TEST-3703]].

## CON-3700: Typed SEC interface

Strong convergence compares evaluateFields observations modulo extensional map,
set and histogram equality. The compiled clause and static context are fixed.
Causal/resource evidence ports can vary with the accepted set, but MUST respect
its set equality; this law does not establish resource validity or finality.

The execution uses an arbitrary Admission satisfying a valid-history contract:
All receipts belong to a common history. Address consistency follows from a
compliant Replica existing. Its receive discipline and eventual delivery cannot
realize conflicting bodies at one address. Each valid act has a finite dependency list in that history, strictly lower in
a natural rank. Once those dependencies are accepted the act is admitted.
It is never rejected while waiting. Eventual delivery is eventual membership in received. Weak fairness
requires an acceptance-labelled scheduling transition when a candidate remains
pending and admitted continuously. Acceptance follows from Step, not the premise.

A finite target list is needed only to extract one stabilization time for the
whole history. No uniform bound, throughput, fairness of arbitration, application
termination or protection from absent/malicious senders follows.

## TEST-3700: Set-extensional interpretation

Prove all expression constructors and arbitrary finite compiled field lists
preserve observation under set equality. Check permutations and duplicate insertion
through unique-address store semantics. Validates REQ-3700.

## TEST-3701: Fair delivery

Prove received/accepted persistence, pending-or-accepted for valid receipts,
eventual dependency closure, and eventual acceptance by well-founded rank
induction. Exhibit permanent stuttering without fairness. Validates REQ-3701.

## TEST-3702: Finite stabilization

Prove finite-history completion and pairwise stable convergence. Demonstrate why
infinite ongoing writes do not imply one final observation. Validates REQ-3702.

## TEST-3703: Verification

Build, lint, audit axioms and run semantic mutants against SEC and scheduling
lemmas. Record independent review and Orientation-only comprehension.
Validates REQ-3703.

## Proof inventory and evidence

`StateKernelSEC.strong_convergence` covers every expression constructor;
`clause_strong_convergence` lifts it to arbitrary ordered compiled clauses.
`merge_setEq` and its algebraic consequences specify accepted-store union, and
`duplicate_observation` covers replay. These are set laws, not conflicting-address
reconciliation or permission to bypass admission during runtime delivery.

`StateKernelDelivery.eventual_acceptance` derives eventual permanent incorporation
by natural-rank induction, using finite dependency completion and transition
fairness. `eventual_dissemination` applies it across replicas.
`finite_history_stabilizes` extracts a common completion time only for finite
complete histories. `strong_eventual_consistency` compares any sufficiently late
times of two compliant replicas using the same fixed Context and Compiled clause.

`StateKernelSECTests.replica` instantiates a nonempty child-before-parent execution
and all fairness/admission/delivery obligations. `starved_not_fair` excludes an
execution that delivers both acts but accepts neither. The increasing tick count
example is a sequence of valid snapshots, not a fully instantiated infinite Replica.

Implementation plan: [[IMPL-024-state-kernel-sec]]. Executed checks, mutation
failures and independent reviews: [[state-kernel-sec-verification]].

Open, owner CBCL maintainer: discharge these admission and shared-evidence laws for
the deployed driver; transport/scheduler and Rust equivalence; resource verifier
classification and certification finalization. No deadline or throughput bound is
established by eventual delivery or weak fairness.
