---
id: BUG-015
title: Certified error guards lack accepted-evidence support
severity: S3
priority: P1
status: resolved
reported-date: 2026-11-09
assigned-to: SPEC-038 implementer
component: lean-cbcl/LeanCbcl/StateObservation.lean
---

# BUG-015: ErrorSpec does not guarantee finite accepted evidence

[[SPEC-038-lvar-state-kernel#REQ-3806]] requires finite conflict witnesses.
The model's former `ErrorSpec` required a reader, set extensionality and
error growth. Those laws permitted an error that reports every natural-number
address even on empty accepted history. Consequently a capstone quantified over
generic certified guards cannot derive finite, accepted-act evidence from this
interface alone. This is a proof-contract gap; no concrete native factory has
been shown to emit this evidence.

## Kernel-checked counterexample

The following temporary probe compiled with the repository's Lean toolchain,
without adding an axiom or sorry:

```lean
import LeanCbcl.StateObservation
namespace Spec038ErrorSupportProbe
open CBCL.State CBCL.StateObservation

def allAddresses : Evidence := fun _ => True

def guard : ErrorSpec := {
  read := fun _ => some allAddresses
  equiv := fun _ => rfl
  grow := by
    intro A B growth evidence observed
    cases Option.some.inj observed
    exact ⟨allAddresses,rfl,fun _ member => member⟩ }

theorem accepted_by_current_interface :
    guard.read [] = some allAddresses ∧ allAddresses 0 ∧
      ¬∃ act ∈ ([] : List Act), act.addr = 0 := by
  simp [guard,allAddresses]
end Spec038ErrorSupportProbe
```

## Required implementation

Require certified guards to prove that every reported identity belongs to an
accepted source act. Prove this law for existing concrete factories and through
the closed error-path constructors. A finite accepted history then supplies an
exact finite enumeration of the returned evidence. The counterexample above
must cease to be constructible as a certified guard. Preserve every existing
native output and all successful factory definitions.

This support law is not, by itself, a witness-only replay theorem. A guard can
report empty evidence while depending on a trigger act; support and growth
alone do not prove that accepting only reported identities recreates its fault.
The final capstone must state its delivery/context premises accurately rather
than claim that stronger implication without a sufficiency proof.

## Acceptance

The abstract counterexample is rejected for the missing support obligation;
concrete guards and composed paths prove accepted-address support; every model
fault has finite exact evidence. Build, Batteries lint and axiom audit pass,
with semantic proof mutants and independent review. This closes a normative
model obligation of [[SPEC-038-lvar-state-kernel#TEST-3806]], not a newly inferred
requirement for literal Rust source extraction.

## Resolution and verification

`ErrorSpec.support` now requires every reported identity to belong to the
accepted history. All root, mixed-thread, opener, domain and finite-lattice
factories prove this property without changing their readers. Joins retain
both channels. `StateEvidenceSupport.errors_supported` covers every closed
path constructor, including resource certificates, thresholds and freeze
witnesses. `observation_supported` transfers that result to the fault returned
by the complete typed `Plan.observe`; `observation_finite` constructs an exact
finite enumeration from the accepted address list.

`StateEvidenceSupportTests` checks that the former universal guard is rejected
for its missing support proof. An interface-weakening mutant, made by removing
the support field from the extracted guard structure, admits that same guard
and fails the expected-error test. Independent proof review found no defect.
The full Lean build and Batteries env-linter pass; all 2,140 audited theorems
use only allowlisted axioms. No new axiom or sorry was introduced.

These results establish finite accepted support. They do not establish
witness-only replay sufficiency or close the remaining top-level capstone,
root identity and authored product-read contract work.
