---
title: Validator-budget model evidence
mode: explanation
---

# Validator-budget model evidence

Subsequent result: [[SPEC-021-validator-budget-model#BUG-2100]] refutes the
asynchronous resource-safety claim. This page records the earlier scoped checks;
[[validator-budget-async-refutation]] records the counterexample and Lean disproof.
The existing tests and fixed-checkpoint proofs did not establish global safety.

[[SPEC-021-validator-budget-model]] records the executable reference and Lean
safety-core contracts. The comparison gate in
[[SPEC-020-resource-certification#TEST-2006]] remains incomplete. No certification
runtime or dialect grammar changes in this work.

## Executable evidence

Run `python3 proofs/validator-budget/check.py --output outputs/validator-budget --lean-mutation`.
The generated `checks.json` records actual test execution and mutation outcomes.
`lifecycle.json` names the cases. The suite exercises real reference transitions, including small exhaustive
signature assignments and selected delivery orders. It checks exact input types,
capped and uncapped operations, finality and replay. Other cases cover negative
reconciled exposure, divergent version merging and no-commit recovery.

The mutation runs separately disable omitted-reservation retention, charge replay
again, lower finality to one effect vote and allow execution through a fence. Each
run must execute its named test and fail a behavioral assertion. The Lean mutation
weakens the witness capacity premise to permit full rather than conservative
budgets; the intended consumption-bound theorem becomes unprovable. A concrete
Lean example supplies the corresponding overspending signature assignment.

The constructor's exact integer and canonical identity checks address a finding
from independent review. The model accepts neither floating-point allocations nor
Python booleans as identity slots or amounts. The negative-exposure regression
checks an actual reconciliation producing a negative budget, then verifies that
an empty update retains it and cannot authorize another spend.

## Formal evidence

`lean-cbcl/LeanCbcl/ValidatorBudget.lean` is imported by the main library and central
axiom audit. `lean-build.log`, `axiom-audit.log` and `proof-label-lint.log` record the
build and repository checks. The new audited theorems use only standard Lean axioms;
no custom axiom or proof hole is introduced.

The main formal claims are:

| Claim | Theorem |
|---|---|
| A certificate has enough honest-core votes | `quorum_coverage` |
| Certified consumption fits one checkpoint | `certified_consumption_bound` |
| Both dimensions share the same certificates | `both_consumption_bounds` |
| Certificate charges imply fixed-checkpoint bounds | `certified_batch_bounds` |
| Replay does not reserve twice | `reservation_replay` |
| Reconciliation retains omitted exposure | `reconciliation_preserves_exposure` |
| Final effects exclude a no-commit quorum | `finality_excludes_no_commit` |
| Local execute/fence steps preserve discipline | `execute_preserves_discipline`, `fence_preserves_discipline` |
| Final receipt bookkeeping is monotonic and idempotent | `receipt_monotone`, `receipt_replay` |

The committee core is an arbitrary distinct honest subset; the other slots can
include additional honest witnesses. Cryptographic key binding, persistence and
concrete certificate-to-mask authenticity are external assumptions. Fixed-checkpoint
capacity does not prove capacity across arbitrary version updates. The finality
lemma excludes conflicting quorums; it does not implement the consensus engine.

## Remaining scope

The model uses a fixed fault set and symbolic authenticated identities. Copying
journals in the restart test is not a production crash-durability proof. Recovery
models only no-commit plus an abstract unique consensus result; all-outcome delivery
is one reference action. There is no asynchronous network liveness proof, full
FastUnlock implementation, Rust correspondence or proof of arbitrary author effects.
The executable and Lean models are separately checked artefacts, without an
extraction or refinement theorem connecting their transition systems.

The maintainer owns `budget-async-refinement` and later transport/storage work.
Human security review remains a production release requirement. Independent review
and final tool results follow.

## Independent verification

Fresh-context reader `validator_orientation` received only the Orientation text.
It correctly predicted retained omitted reservations, the absence of a deployed or
fully proved asynchronous coin, and the distinction between
[[SPEC-021-validator-budget-model#CON-2100]] and
[[SPEC-021-validator-budget-model#CON-2101]]. The cross-model adversarial reviewer
disclosed reading beyond Orientation initially; that reading is not used as a
blinded comprehension gate.

Cross-model reviewer `validator_model_review` compiled the Lean module, inspected
the proof premises and lifecycle implementation, ran the tests and deliberate
mutations, and checked the evidence scope. It found fractional-genesis acceptance;
exact-type guards and regressions resolve that finding. It suggested the explicit
negative-budget regression, which is included. Final review found no model-safety
blocker. Its report-output reproducibility finding is fixed: `check.py --output`
now saves the same combined report it prints.

The main library build and central axiom audit pass, as does the repository's
proof-label linter. The tests and mutation results are in `checks.json`; a replay
compares that printed report with the saved file. No production Rust code changes.
Elephant records completion only for the lifecycle and Lean-core tasks;
`budget-async-refinement` and the broader agreement model remain unfinished.

The vault checker passes its error threshold with unresolved cross-vault concept
links still reported. `traceability-check.json` independently checks repository
targets and named anchors for the new model artefacts. Neither result is presented
as a link-clean vault.
