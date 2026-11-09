import LeanCbcl.StateAuthoredConditionOutputs
import LeanCbcl.StateOutputConvergence
import LeanCbcl.StateAuthoredConditionReplay

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

open StateKernelDelivery AdmissionStratification StateRefinement

/-- Fair replicas eventually agree exactly on the complete corrected emitted
vector for a finite valid history, including fault evidence and exclusions.
Compilation existence is derived from successful static installation. -/
theorem finite_history_output_convergence {adm : Admission} {auth : Act → Prop} {H : ValidHistory adm}
    (left right : Replica adm auth H) (admission : PredecessorAdmission adm H.contains)
    (causal : StateContextReplay.CausalDependencies H) (environment : StateAuthoredBindings.Environment)
    (entries : List StateAuthoredBindings.Entry) (prepared : StateAuthoredBindings.Prepared)
    (installed : StateAuthoredBindings.prepareStatic environment entries = some prepared)
    (history : List Act) (complete : ∀ act, H.contains act ↔ act ∈ history) :
    ∃ time, ∀ n m, time ≤ n → time ≤ m → ∃ first second,
      StateAuthoredConditionOutputs.compileAuthored environment entries (left.run n).accepted = some first ∧
      StateAuthoredConditionOutputs.compileAuthored environment entries (right.run m).accepted = some second ∧ first.observe = second.observe := by
  obtain ⟨tl,leftComplete⟩ := finite_history_stabilizes left history complete
  obtain ⟨tr,rightComplete⟩ := finite_history_stabilizes right history complete
  refine ⟨max tl tr,fun n m hn hm => ?_⟩
  have leftUnique := (reachable_wellFormed (behavior_reachable left.behavior n)).accepted_unique
  have rightUnique := (reachable_wellFormed (behavior_reachable right.behavior m)).accepted_unique
  have leftConsistent : ∀ a ∈ (left.run n).accepted, ∀ b ∈ (left.run n).accepted, a.addr = b.addr → a = b :=
    fun a ma b mb same => leftUnique.eq_of_addr ma mb same
  have rightConsistent : ∀ a ∈ (right.run m).accepted, ∀ b ∈ (right.run m).accepted, a.addr = b.addr → a = b :=
    fun a ma b mb same => rightUnique.eq_of_addr ma mb same
  have rankedA := StateAuthoredOutputReplay.replica_ranked left admission causal n
  have rankedB := StateAuthoredOutputReplay.replica_ranked right admission causal m
  obtain ⟨first,compiledA⟩ := StateAuthoredConditionPreparation.prepared_output_exists environment entries prepared installed _ rankedA leftConsistent
  obtain ⟨second,compiledB⟩ := StateAuthoredConditionPreparation.prepared_output_exists environment entries prepared installed _ rankedB rightConsistent
  have same : SetEq (left.run n).accepted (right.run m).accepted := fun act =>
    (leftComplete n (by omega) act).trans (rightComplete m (by omega) act).symm
  exact ⟨first,second,compiledA,compiledB,authored_observations_setEq environment entries rankedA rankedB
    leftConsistent rightConsistent same first second compiledA compiledB⟩

/-- Conditional SEC is the no-top specialization of complete emitted-output
convergence, with a shared full data vector and no discarded fault members. -/
theorem conflict_free_output_SEC {adm : Admission} {auth : Act → Prop} {H : ValidHistory adm}
    (left right : Replica adm auth H) (admission : PredecessorAdmission adm H.contains)
    (causal : StateContextReplay.CausalDependencies H) (environment : StateAuthoredBindings.Environment)
    (entries : List StateAuthoredBindings.Entry) (prepared : StateAuthoredBindings.Prepared)
    (installed : StateAuthoredBindings.prepareStatic environment entries = some prepared)
    (history : List Act) (complete : ∀ act, H.contains act ↔ act ∈ history)
    (clear : ∀ n observation, StateAuthoredConditionOutputs.compileAuthored environment entries (left.run n).accepted = some observation → NoFault observation.observe) :
    ∃ time, ∀ n m, time ≤ n → time ≤ m → ∃ (first second : CompiledObservation) (values : List (String × Data StateInstalledLegacy.Value)),
      StateAuthoredConditionOutputs.compileAuthored environment entries (left.run n).accepted = some first ∧
      StateAuthoredConditionOutputs.compileAuthored environment entries (right.run m).accepted = some second ∧
      first.observe = values.map (fun (name,value) => (name,Observation.data value)) ∧
      second.observe = values.map (fun (name,value) => (name,Observation.data value)) := by
  obtain ⟨time,converges⟩ := finite_history_output_convergence left right admission causal environment entries prepared installed history complete
  refine ⟨time,fun n m hn hm => ?_⟩
  obtain ⟨first,second,compiledA,compiledB,equal⟩ := converges n m hn hm
  have exactData := data_vector_complete first.observe (clear n first compiledA)
  exact ⟨first,second,dataVector first.observe,compiledA,compiledB,exactData.symm,equal.symm.trans exactData.symm⟩


end CBCL.StateAuthoredConditionConvergence
