---
id: BUG-016
title: Reported conflict evidence lacks a replay-sufficiency certificate
severity: S3
priority: P1
status: new
reported-date: 2026-11-09
assigned-to: SPEC-038 implementer
component: lean-cbcl/LeanCbcl/StateObservation.lean
---

# BUG-016: Accepted evidence support does not establish witness replay

[[SPEC-038-lvar-state-kernel#REQ-3806]] and
[[SPEC-038-lvar-state-kernel#TEST-3806]] require a replica accepting the
conflicting witness to fault with evidence containing it. The resolved
[[BUG-015-certified-error-guards-lack-accepted-evidence-support]] establishes
finite accepted provenance. Support, extensionality and growth still do not
establish replay from only reported witness acts.

A kernel-checked probe constructs an `ErrorSpec` whose reader is
`if trigger ∈ A then some ∅ else none`. Membership is set-extensional,
faults grow with accepted histories, and empty evidence satisfies support.
Nevertheless the guard faults on `[trigger]` and is clear on `[]`. Both
claims compile without sorry or a custom axiom. The trigger is act
`⟨7,"write","@a",[],[],[]⟩`.

`StateQuasiDeterminism.finite_fault_dissemination` correctly transfers the
whole finite earlier accepted history, including context. It does not prove
the stronger reported-witness-only property. This is a normative model gap,
not an additional demand for literal Rust source extraction.

## Required implementation

Establish a replay-sufficiency certificate over the intended admissible
histories. Identity matching must use explicit immutable-address/world
premises; causal and immutable context prerequisites must be stated and
proved. Compose the certificate through observation paths and tie it to
installed concrete guards before closing the model capstone.

For example, context opener faults require `hasRoot`, but their reported
identities are opener identities. Prove root availability from the actual
admission premises rather than assuming arbitrary list restriction preserves
it. Domain selection can likewise depend on successful contextual reads.
Do not silently replace reported evidence with every accepted act, weaken
REQ-3806, or label whole-history delivery as witness-only replay.

## Acceptance

The trigger-with-empty-evidence counterexample cannot qualify as a replayable
certified guard. Actual installed guard paths have sufficient replay
certificates under their explicit admission/context assumptions. Accepting
the reported witness then reproduces a fault retaining its evidence. Build,
Batteries lint, axiom audit, semantic mutations and independent review pass.

## Current proof progress

`StateWitnessReplay.Accepts` transfers the original accepted acts selected by
reported identities; it does not infer act equality from an address string.
`union_replays` composes independent replay certificates. Both
`freeze_evidence_replays` and `freeze_replays` transfer actual conflict pairs
under the source causal-closure premise, without whole-history inclusion.
Raw guards still have to supply their replay law. Independent review found no
defect in these laws; concrete guard and admission bindings remain open.

`StateWitnessReplayTests` constructs the supported trigger guard and proves
that it is not replayable. A temporary semantic mutant replaced it with a
constant empty-evidence fault, whose guard definition independently compiled;
the unchanged regression then failed at its `False` proof obligation. Thus
the regression distinguishes a trigger-dependent fault from an unconditional,
replayable fault, rather than merely checking elaboration or a missing import.

The next checkpoint proves `threshold_replays`, `domain_replays` and
`context_replays`, including malformed roots, from the actual reported acts.
`errors_replay` composes all closed paths with the remaining certified/resource
obligations exposed by `PrimitiveReplay`. The typed
`fault_of_accepting_witness` and replica `witness_only_dissemination` now transfer
only the source acts whose identities occur in evidence; they do not substitute
the full source history. The latter retains explicit primitive replay premises
for receiving states. These premises still need concrete installed proofs.

`accepts_only_named_act` proves acceptance can omit an unrelated source act.
Its standalone baseline passes; replacing the extracted acceptance condition
with unconditional whole-history inclusion makes the same proof fail. Independent
review found no defect in the new primitive, path and delivery proofs.
