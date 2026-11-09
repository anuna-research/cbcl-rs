import LeanCbcl.StateAuthoredConditionProjection
import LeanCbcl.StateAuthoredConditionConvergence

/-! SPEC-038 REQ-3806 / TEST-3806: the complete typed authored observation
agreement guarantee. All components concern actual compiled output vectors;
replica delivery, causal admission and immutable-content premises stay explicit.
Condition observations retain Boolean results and source-owned dependency faults.
Native extraction and authentication remain explicit model boundaries. -/
set_option autoImplicit false
namespace CBCL.StateAuthoredConditionQuasiDeterminism
open State StateLift StateLVar StateObservation StateObservationPlan StateOutputCompiler
open StateInstalledLegacy StateAuthoredBindings StateScopePool StateExecutableFreeze StateThresholdDispatch
open StateKernelDelivery AdmissionStratification StateRefinement StateOutputConvergence

/-- The complete authored observation guarantee, retaining each component's
structural premises rather than assuming its final observation conclusion. -/
structure Guarantees : Prop where
  /-- Successful condition observations agree on the authored Boolean result. -/
  condition (environment : Environment) (entries : List Entry) (name : String)
      (expression : StateCondition.Condition Value) (present : Entry.condition name expression ∈ entries)
      (A B : List Act) (left right : CompiledObservation)
      (compiledA : StateAuthoredConditionOutputs.compileAuthored environment entries A = some left)
      (compiledB : StateAuthoredConditionOutputs.compileAuthored environment entries B = some right)
      (x y : Value) (first : (name,.data (.reached x)) ∈ left.observe)
      (second : (name,.data (.reached y)) ∈ right.observe) : x = y
  /-- Successful thresholds agree or expose a same-named joint conflict. -/
  threshold (environment : Environment) (entries : List Entry) (prepared : Prepared)
      (accepted : prepareStatic environment entries = some prepared)
      (outputName sourceName : String) (elements : List Value)
      (threshold : Entry.threshold outputName sourceName elements ∈ entries)
      (A B C : List Act) (growthA : ∀ act ∈ A, act ∈ C) (growthB : ∀ act ∈ B, act ∈ C)
      (rankedA : StateExecutableFreeze.Ranked A) (rankedB : StateExecutableFreeze.Ranked B)
      (rankedC : StateExecutableFreeze.Ranked C)
      (consistentA : ∀ a ∈ A, ∀ b ∈ A, a.addr = b.addr → a = b)
      (consistentB : ∀ a ∈ B, ∀ b ∈ B, a.addr = b.addr → a = b)
      (consistentC : ∀ a ∈ C, ∀ b ∈ C, a.addr = b.addr → a = b)
      (left right joint : CompiledObservation)
      (compiledA : StateAuthoredConditionOutputs.compileAuthored environment entries A = some left)
      (compiledB : StateAuthoredConditionOutputs.compileAuthored environment entries B = some right)
      (compiledC : StateAuthoredConditionOutputs.compileAuthored environment entries C = some joint)
      (leftResult rightResult : Value)
      (reachedA : (outputName,.data (.reached leftResult)) ∈ left.observe)
      (reachedB : (outputName,.data (.reached rightResult)) ∈ right.observe) :
      leftResult = rightResult ∨ ∃ evidence, (outputName,.fault evidence) ∈ joint.observe
  /-- Successful frozen observations share the underlying value at the same actual freezer. -/
  frozen (world : Act → Prop) (environment : Environment) (entries : List Entry)
      (prepared : Prepared) (installed : prepareStatic environment entries = some prepared)
      (A B : List Act) (validA : ∀ act ∈ A, world act) (validB : ∀ act ∈ B, world act)
      (closedA : CausallyClosed world A) (closedB : CausallyClosed world B)
      (consistentA : ∀ a ∈ A, ∀ b ∈ A, a.addr = b.addr → a = b)
      (consistentB : ∀ a ∈ B, ∀ b ∈ B, a.addr = b.addr → a = b)
      (left right : CompiledObservation)
      (leftCompiled : StateAuthoredConditionOutputs.compileAuthored environment entries A = some left)
      (rightCompiled : StateAuthoredConditionOutputs.compileAuthored environment entries B = some right)
      (name : String) (freezer : Act) (presentA : freezer ∈ A) (presentB : freezer ∈ B)
      (leftValue rightValue : StateInstalledLegacy.Value) (leftExcluded rightExcluded : FinSet Act)
      (leftFrozen : (name,.data (.frozen freezer.addr leftValue leftExcluded)) ∈ left.observe)
      (rightFrozen : (name,.data (.frozen freezer.addr rightValue rightExcluded)) ∈ right.observe) :
      leftValue = rightValue
  /-- Equal accepted sets yield equal complete observations, including evidence. -/
  equalAccepted (environment : StateAuthoredBindings.Environment)
      (entries : List StateAuthoredBindings.Entry) {A B : List Act}
      (rankedA : Ranked A) (rankedB : Ranked B)
      (consistentA : ∀ a ∈ A, ∀ b ∈ A, a.addr = b.addr → a = b)
      (consistentB : ∀ a ∈ B, ∀ b ∈ B, a.addr = b.addr → a = b) (same : SetEq A B)
      (left right : CompiledObservation)
      (first : StateAuthoredConditionOutputs.compileAuthored environment entries A = some left)
      (second : StateAuthoredConditionOutputs.compileAuthored environment entries B = some right) : left.observe = right.observe
  /-- Accepting the actual named witness immediately reproduces a containing fault. -/
  acceptedWitness (world : Act → Prop) (environment : Environment) (entries : List Entry)
      (A B : List Act) (unique : NodupAddr A) (validA : ∀ act ∈ A, world act) (validB : ∀ act ∈ B, world act)
      (closedA : CausallyClosed world A) (closedB : CausallyClosed world B)
      (rooted : StateContextReplay.RootedOpeners world (StateInstalledContext.evidenceInput environment.profile))
      (left right : CompiledObservation)
      (leftCompiled : StateAuthoredConditionOutputs.compileAuthored environment entries A = some left)
      (rightCompiled : StateAuthoredConditionOutputs.compileAuthored environment entries B = some right)
      (name : String) (e : Evidence) (fault : (name,.fault e) ∈ left.observe)
      (accepted : StateWitnessReplay.Accepts A e B) :
      ∃ enlarged, (name,.fault enlarged) ∈ right.observe ∧ ∀ id ∈ e, id ∈ enlarged
  /-- The exact finite reported witness eventually reproduces a containing named fault. -/
  witness {adm : Admission} {auth : Act → Prop} {H : ValidHistory adm}
      (left right : Replica adm auth H) (admission : PredecessorAdmission adm H.contains)
      (causal : StateContextReplay.CausalDependencies H) (environment : Environment) (entries : List Entry)
      (atTime : Nat) (observation : CompiledObservation)
      (compiled : StateAuthoredConditionOutputs.compileAuthored environment entries (left.run atTime).accepted = some observation)
      (name : String) (e : Evidence) (fault : (name,.fault e) ∈ observation.observe) :
      ∃ witness : List Act,
        (∀ act, act ∈ witness ↔ act ∈ (left.run atTime).accepted ∧ act.addr ∈ e) ∧
        (∀ id, id ∈ witness.map Act.addr ↔ id ∈ e) ∧
        ∃ time, ∀ n, time ≤ n → ∃ current enlarged,
          StateAuthoredConditionOutputs.compileAuthored environment entries (right.run n).accepted = some current ∧
          (name,.fault enlarged) ∈ current.observe ∧ ∀ id ∈ e, id ∈ enlarged
  /-- Complete finite-history delivery yields eventual equality of the full output vector. -/
  finiteHistory {adm : Admission} {auth : Act → Prop} {H : ValidHistory adm}
      (left right : Replica adm auth H) (admission : PredecessorAdmission adm H.contains)
      (causal : StateContextReplay.CausalDependencies H) (environment : StateAuthoredBindings.Environment)
      (entries : List StateAuthoredBindings.Entry) (prepared : StateAuthoredBindings.Prepared)
      (installed : StateAuthoredBindings.prepareStatic environment entries = some prepared)
      (history : List Act) (complete : ∀ act, H.contains act ↔ act ∈ history) :
      ∃ time, ∀ n m, time ≤ n → time ≤ m → ∃ first second,
        StateAuthoredConditionOutputs.compileAuthored environment entries (left.run n).accepted = some first ∧
        StateAuthoredConditionOutputs.compileAuthored environment entries (right.run m).accepted = some second ∧ first.observe = second.observe
  /-- The no-top specialization yields a shared complete data vector without losing fields. -/
  noTop {adm : Admission} {auth : Act → Prop} {H : ValidHistory adm}
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
        second.observe = values.map (fun (name,value) => (name,Observation.data value))

/-- Complete v0.4 authored guarantee, composing original source agreement with
condition-aware exact witness replay and complete-vector convergence. -/
theorem authored_quasi_determinism : Guarantees := by
  refine {
    condition := ?_
    threshold := ?_
    frozen := ?_
    equalAccepted := @StateAuthoredConditionConvergence.authored_observations_setEq
    acceptedWitness := @StateAuthoredConditionReplay.authored_output_fault_replays
    witness := @StateAuthoredConditionReplay.eventual_authored_output_witness_fault
    finiteHistory := @StateAuthoredConditionConvergence.finite_history_output_convergence
    noTop := @StateAuthoredConditionConvergence.conflict_free_output_SEC
  }
  · intro environment entries name expression present A B left right ca cb x y first second
    exact (StateAuthoredConditionProjection.condition_success environment entries A left ca name expression present x first).trans
      (StateAuthoredConditionProjection.condition_success environment entries B right cb name expression present y second).symm
  · intro environment entries prepared installed name source elements threshold A B C growthA growthB
      rankedA rankedB rankedC consistentA consistentB consistentC left right joint ca cb cc x y ra rb
    obtain ⟨baseA,ba,_,_,_,_,_⟩ := StateAuthoredConditionProjection.base_projection environment entries A left ca
    obtain ⟨baseB,bb,_,_,_,_,_⟩ := StateAuthoredConditionProjection.base_projection environment entries B right cb
    obtain ⟨baseC,bc,sub,_,_,_,_⟩ := StateAuthoredConditionProjection.base_projection environment entries C joint cc
    have first := StateAuthoredConditionProjection.threshold_in_base environment entries prepared installed
      name source elements threshold A left baseA ba ca _ ra
    have second := StateAuthoredConditionProjection.threshold_in_base environment entries prepared installed
      name source elements threshold B right baseB bb cb _ rb
    rcases StateAuthoredThresholdOrigin.quasi_determinism environment entries prepared installed name source elements threshold
      A B C growthA growthB rankedA rankedB rankedC consistentA consistentB consistentC baseA baseB baseC ba bb bc x y first second
      with same | ⟨e,fault⟩
    · exact Or.inl same
    · exact Or.inr ⟨e,sub.subset fault⟩
  · intro world environment entries prepared installed A B validA validB closedA closedB consistentA consistentB
      left right ca cb name freezer presentA presentB x y excludedA excludedB frozenA frozenB
    obtain ⟨baseA,ba,_,_,_,_,_⟩ := StateAuthoredConditionProjection.base_projection environment entries A left ca
    obtain ⟨baseB,bb,_,_,_,_,_⟩ := StateAuthoredConditionProjection.base_projection environment entries B right cb
    exact StateAuthoredFrozenAgreement.authored_frozen_agreement world environment entries prepared installed A B
      validA validB closedA closedB consistentA consistentB baseA baseB ba bb name freezer presentA presentB x y excludedA excludedB
      (StateAuthoredConditionProjection.frozen_in_base environment entries A left baseA ba ca _ _ _ _ frozenA)
      (StateAuthoredConditionProjection.frozen_in_base environment entries B right baseB bb cb _ _ _ _ frozenB)

end CBCL.StateAuthoredConditionQuasiDeterminism
