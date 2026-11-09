---
id: BUG-016
title: Reported conflict evidence lacks a replay-sufficiency certificate
severity: S2
priority: P1
status: new
reported-date: 2026-11-09
assigned-to: SPEC-038 implementer
component: crates/cbcl-core/src/lattice.rs and lean-cbcl/LeanCbcl/StateObservation.lean
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

`StateResourceReplay.resource_replays` now proves the actual resource
`faultRead` sufficient from its reported witness. `cause_replays` transfers
every constructor of the concrete certificate grammar, including funding
cones, cited roots and foreign dependencies. Unsupported profiles retain
history-independent faults with empty evidence. `paths_replay` discharges
built-in resource readers, leaving only certified extension guards as caller
obligations. Independent review found no defect in this transfer.

`StateResourceReplayTests` proves a malformed binding-free root and a foreign
non-resource dependency are named only by citations, not direct relevance.
Removing all cited context fails both assertions; retaining only protocol
predecessor citations fails the funding-dependency assertion while the root
case still passes. The unmodified extracted-definition baseline passes.

`StateContextReplay` proves replay for the actual root, mixed-thread, opener
and combined context guards. A reported opener's causal ancestry restores the
receiver's root. `root_ancestor` derives that ancestry from `ValidHistory` rank
and dependency closure plus `CausalDependencies`, the explicit coverage of cited
predecessors by the dependency certificate. Replica validity and causal admission
supply the remaining history premises. Coverage is not inferred from rank alone;
native cast/address binding remains the separate BUG-011 boundary.

The context regression observes the actual opener guard: a root plus two
openers faults with both opener identities; a receiver retaining both named
openers but omitting the root is pending and fails causal closure. Bypassing the
root gate makes the unchanged pending assertion fail, while the original source
fault still passes. Independent review found no defect or masking in these
proofs and tests. Remaining installed finite/domain guard certificates and
structural caller bindings still prevent closing BUG-016.

## Native finite-domain defect and repair

Further review found that domain-support ancestry cannot be assumed: BUG-007's
admitted graph permits a writer whose initializer is concurrent. A temporary
conditional finite replay proof and local ancestry checker were therefore
replaced, rather than used to narrow the admitted histories covered by replay.

The durable regression
`finite_fault_witness_retains_domain_initializer_for_replay` reproduced a native
fault whose evidence named only a writer. Folding exactly its named acts removed
the initializer, lost domain eligibility and returned bottom (`e0`) instead of a
fault. The failing assertion was captured in
`/tmp/spec038-finite-witness-red.log`. A parallel roster regression checks the
sealed root required by a finite writer.

Finite-top evidence now includes applicable domain initializer and roster-root
identities, in addition to selected non-bottom writers. Finite domain-fault
evidence likewise retains all applicable domain support with its raw writers.
The factored native reader and independent reference reader agree on the added
context. Successful values, wire forms and addresses are unchanged.

The Lean `domainEvidence` factory follows the same support rule and proves
accepted provenance, growth and set equality. `StateFiniteReplay` restores
eligibility directly from reported supporting contributions; its finite-guard
replay theorem is unconditional on causal-domain dominance. The checker and
ancestry premise were removed. Mixed initializer/roster tests explicitly cover
a selected writer concurrent with its initializer. Independent review found no
defect in the revised native/model alignment or unconditional proof.

The new native regressions verify fault reproduction, containing evidence and
reverse/duplicate receipt. Mutation checks remove finite initializer context,
roster context and raw writers under initializer-fault precedence; each fails
its executed semantic test. This repairs the concrete finite-domain witness
gap. Installed guard provenance/composition and the remaining structural caller
premises still need the top-level audit before closing this overall issue.

## Installed factory and clause composition

`StateInstalledReplay` now carries the concrete finite, resource, context and
resolved-domain certificates into the source plans emitted by their factories.
Term guard folding and the authored resource factory's appended domain guards
retain their actual certificates. An exact `guard_errors` equation separately
asserts retention of the complete attached error channel; it detects guard
omission independently of the replay predicate. A temporary semantic mutant
removing a certified guard from the extracted attachment function fails that
unchanged equation, while the baseline compiles.

Successful `compileRule`, clause-wide freeze attachment and ordered
`compileFields` now preserve the certificates for every emitted plan, including
references, maps, both product dependencies, raw/checked thresholds and freezes.
The proof maintains the actual extended-prefix lookup invariant. Independent
review found no defect in the factory or compilation proofs. These results
still require the concrete source certificates at authored binding and do not
yet claim full authored-output coverage or close this issue.
