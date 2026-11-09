import LeanCbcl.StateAuthoredConditionOutputs
import LeanCbcl.StateOutputConvergence

/-! Equal accepted sets preserve freshly compiled complete v0.4 programs, including
condition trees, source-owned cuts, frozen metadata and all fault evidence. -/
set_option autoImplicit false
namespace CBCL.StateAuthoredConditionConvergence
open State StateLift StateLVar StateObservation StateObservationPlan StateInstalledCompiler
open StateInstalledLegacy StateInstalledLowering StateAuthoredBindings StateOutputCompiler
open StateScopePool StateExecutableFreeze StateOutputConvergence

/-- Actual complete authored programs agree on every output under accepted-set
equality; no condition-program correspondence is assumed by the caller. -/
theorem authored_observations_setEq (environment : Environment) (entries : List Entry)
    {A B : List Act} (rankedA : Ranked A) (rankedB : Ranked B)
    (consistentA : ∀ a ∈ A, ∀ b ∈ A, a.addr = b.addr → a = b)
    (consistentB : ∀ a ∈ B, ∀ b ∈ B, a.addr = b.addr → a = b)
    (same : SetEq A B) (left right : CompiledObservation)
    (leftCompiled : StateAuthoredConditionOutputs.compileAuthored environment entries A = some left)
    (rightCompiled : StateAuthoredConditionOutputs.compileAuthored environment entries B = some right) :
    left.observe = right.observe := by
  obtain ⟨prepared,sources,base,outputs,installed,plansA,baseA,emittedA,leftEq⟩ :=
    StateAuthoredConditionOutputs.compiled_parts environment entries A left leftCompiled
  obtain ⟨other,rightSources,rightBase,rightOutputs,otherInstalled,plansB,baseB,emittedB,rightEq⟩ :=
    StateAuthoredConditionOutputs.compiled_parts environment entries B right rightCompiled
  have preparedEq : prepared = other := Option.some.inj (installed.symm.trans otherInstalled)
  subst other
  have clauses : clauseAt prepared A = clauseAt prepared B := by
    simp only [clauseAt,materialize,contributes_setEq _ same]
  have sourceEq : sources = rightSources :=
    Option.some.inj (plansA.symm.trans ((congrArg StateInstalledLowering.compile clauses).trans plansB))
  subst rightSources
  have baseEq : base = rightBase := Option.some.inj (baseA.symm.trans baseB)
  subst rightBase
  have outputsEq : outputs = rightOutputs := Option.some.inj (emittedA.symm.trans emittedB)
  subst rightOutputs
  subst left
  subst right
  have freezesEq := congrArg Clause.freezes clauses
  change materialize prepared.domains A prepared.freezes = materialize prepared.domains B prepared.freezes at freezesEq
  change Program.observe ⟨materialize prepared.domains A prepared.freezes,outputs⟩ A =
    Program.observe ⟨materialize prepared.domains B prepared.freezes,outputs⟩ B
  rw [freezesEq]
  exact program_observe_setEq _ rankedA rankedB consistentA consistentB same

end CBCL.StateAuthoredConditionConvergence
