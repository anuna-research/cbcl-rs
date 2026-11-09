import LeanCbcl.StateOutputCompiler

/-! Complete v0.4 output assembly over the actual authored Entry inventory.
The existing source/threshold compiler remains the base stage; this final walk
reinserts Boolean conditions using the completed original source dictionary and
the exact earlier-definition prefix. Preparation, witness replay, projection and convergence refinements for this
expanded vector are composed by StateAuthoredConditionQuasiDeterminism. -/
set_option autoImplicit false
namespace CBCL.StateAuthoredConditionOutputs
open State StateLift StateLVar StateObservation StateObservationPlan StateInstalledCompiler
open StateInstalledLegacy StateInstalledLowering StateAuthoredBindings StateOutputCompiler

/-- Compile the full authored inventory with source-owned condition observations. -/
noncomputable def compileAuthored (environment : Environment) (entries : List Entry) (whole : List Act) :
    Option CompiledObservation := do
  let clause ← StateAuthoredBindings.prepare environment entries whole
  let sources ← StateInstalledLowering.compile clause
  let base ← compileDeclarations sources [] clause.declarations
  let outputs ← emitAuthored environment.profile.definition.bounds.maxList sources entries clause.declarations base []
  return ⟨whole,⟨clause.freezes,outputs⟩⟩

/-- Successful full compilation exposes the actual static preparation, completed
source dictionary, base instructions and final condition interleaving. -/
theorem compiled_parts (environment : Environment) (entries : List Entry) (whole : List Act)
    (observation : CompiledObservation) (compiled : compileAuthored environment entries whole = some observation) :
    ∃ prepared sources base outputs,
      prepareStatic environment entries = some prepared ∧
      StateInstalledLowering.compile (clauseAt prepared whole) = some sources ∧
      compileDeclarations sources [] prepared.declarations = some base ∧
      emitAuthored environment.profile.definition.bounds.maxList sources entries prepared.declarations base [] = some outputs ∧
      (⟨whole,⟨materialize prepared.domains whole prepared.freezes,outputs⟩⟩ : CompiledObservation) = observation := by
  unfold compileAuthored at compiled
  obtain ⟨clause,preparedAt,afterPrepare⟩ := Option.bind_eq_some_iff.mp compiled
  change (prepareStatic environment entries).map (fun prepared => clauseAt prepared whole) = some clause at preparedAt
  obtain ⟨prepared,installed,clauseEq⟩ := Option.map_eq_some_iff.mp preparedAt
  subst clause
  obtain ⟨sources,plans,afterPlans⟩ := Option.bind_eq_some_iff.mp afterPrepare
  obtain ⟨base,built,afterBase⟩ := Option.bind_eq_some_iff.mp afterPlans
  obtain ⟨outputs,emitted,final⟩ := Option.bind_eq_some_iff.mp afterBase
  exact ⟨prepared,sources,base,outputs,installed,plans,built,emitted,Option.some.inj final⟩

end CBCL.StateAuthoredConditionOutputs
