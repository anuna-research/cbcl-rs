import LeanCbcl.StateAuthoredFrozenAgreement

/-! SPEC-038 REQ-3806 / TEST-3806: the complete typed authored observation
agreement guarantee. All components concern actual compiled output vectors;
replica delivery, causal admission and immutable-content premises stay explicit.
Native root identity and authored product-read syntax are separate contracts. -/
set_option autoImplicit false
namespace CBCL.StateAuthoredQuasiDeterminism
open State StateLift StateLVar StateObservation StateObservationPlan StateOutputCompiler
open StateInstalledLegacy StateAuthoredBindings StateScopePool StateExecutableFreeze StateThresholdDispatch
open StateKernelDelivery AdmissionStratification StateRefinement StateOutputConvergence

/-- The complete authored observation guarantee, retaining each component's
structural premises rather than assuming its final observation conclusion. -/
structure Guarantees : Prop where
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
      (compiledA : compileAuthored environment entries A = some left)
      (compiledB : compileAuthored environment entries B = some right)
      (compiledC : compileAuthored environment entries C = some joint)
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
      (leftCompiled : compileAuthored environment entries A = some left)
      (rightCompiled : compileAuthored environment entries B = some right)
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
      (first : compileAuthored environment entries A = some left)
      (second : compileAuthored environment entries B = some right) : left.observe = right.observe
  /-- Accepting the actual named witness immediately reproduces a containing fault. -/
  acceptedWitness (world : Act → Prop) (environment : Environment) (entries : List Entry)
      (A B : List Act) (unique : NodupAddr A) (validA : ∀ act ∈ A, world act) (validB : ∀ act ∈ B, world act)
      (closedA : CausallyClosed world A) (closedB : CausallyClosed world B)
      (rooted : StateContextReplay.RootedOpeners world (StateInstalledContext.evidenceInput environment.profile))
      (left right : CompiledObservation)
      (leftCompiled : compileAuthored environment entries A = some left)
      (rightCompiled : compileAuthored environment entries B = some right)
      (name : String) (e : Evidence) (fault : (name,.fault e) ∈ left.observe)
      (accepted : StateWitnessReplay.Accepts A e B) :
      ∃ enlarged, (name,.fault enlarged) ∈ right.observe ∧ ∀ id ∈ e, id ∈ enlarged
  /-- The exact finite reported witness eventually reproduces a containing named fault. -/
  witness {adm : Admission} {auth : Act → Prop} {H : ValidHistory adm}
      (left right : Replica adm auth H) (admission : PredecessorAdmission adm H.contains)
      (causal : StateContextReplay.CausalDependencies H) (environment : Environment) (entries : List Entry)
      (atTime : Nat) (observation : CompiledObservation)
      (compiled : compileAuthored environment entries (left.run atTime).accepted = some observation)
      (name : String) (e : Evidence) (fault : (name,.fault e) ∈ observation.observe) :
      ∃ witness : List Act,
        (∀ act, act ∈ witness ↔ act ∈ (left.run atTime).accepted ∧ act.addr ∈ e) ∧
        (∀ id, id ∈ witness.map Act.addr ↔ id ∈ e) ∧
        ∃ time, ∀ n, time ≤ n → ∃ current enlarged,
          compileAuthored environment entries (right.run n).accepted = some current ∧
          (name,.fault enlarged) ∈ current.observe ∧ ∀ id ∈ e, id ∈ enlarged
  /-- Complete finite-history delivery yields eventual equality of the full output vector. -/
  finiteHistory {adm : Admission} {auth : Act → Prop} {H : ValidHistory adm}
      (left right : Replica adm auth H) (admission : PredecessorAdmission adm H.contains)
      (causal : StateContextReplay.CausalDependencies H) (environment : StateAuthoredBindings.Environment)
      (entries : List StateAuthoredBindings.Entry) (prepared : StateAuthoredBindings.Prepared)
      (installed : StateAuthoredBindings.prepareStatic environment entries = some prepared)
      (history : List Act) (complete : ∀ act, H.contains act ↔ act ∈ history) :
      ∃ time, ∀ n m, time ≤ n → time ≤ m → ∃ first second,
        compileAuthored environment entries (left.run n).accepted = some first ∧
        compileAuthored environment entries (right.run m).accepted = some second ∧ first.observe = second.observe
  /-- The no-top specialization yields a shared complete data vector without losing fields. -/
  noTop {adm : Admission} {auth : Act → Prop} {H : ValidHistory adm}
      (left right : Replica adm auth H) (admission : PredecessorAdmission adm H.contains)
      (causal : StateContextReplay.CausalDependencies H) (environment : StateAuthoredBindings.Environment)
      (entries : List StateAuthoredBindings.Entry) (prepared : StateAuthoredBindings.Prepared)
      (installed : StateAuthoredBindings.prepareStatic environment entries = some prepared)
      (history : List Act) (complete : ∀ act, H.contains act ↔ act ∈ history)
      (clear : ∀ n observation, compileAuthored environment entries (left.run n).accepted = some observation → NoFault observation.observe) :
      ∃ time, ∀ n m, time ≤ n → time ≤ m → ∃ (first second : CompiledObservation) (values : List (String × Data StateInstalledLegacy.Value)),
        compileAuthored environment entries (left.run n).accepted = some first ∧
        compileAuthored environment entries (right.run m).accepted = some second ∧
        first.observe = values.map (fun (name,value) => (name,Observation.data value)) ∧
        second.observe = values.map (fun (name,value) => (name,Observation.data value))

/-- All typed authored agreement obligations hold together. The no-top field is
the conditional strong eventual consistency specialization of the same complete
output convergence result, and the fault field delivers the exact finite witness. -/
theorem authored_quasi_determinism : Guarantees := {
  threshold := @StateAuthoredThresholdOrigin.quasi_determinism
  frozen := @StateAuthoredFrozenAgreement.authored_frozen_agreement
  equalAccepted := @StateOutputConvergence.authored_observations_setEq
  acceptedWitness := @StateAuthoredOutputReplay.authored_output_fault_replays
  witness := @StateAuthoredOutputReplay.eventual_authored_output_witness_fault
  finiteHistory := @StateOutputConvergence.finite_history_output_convergence
  noTop := @StateOutputConvergence.conflict_free_output_SEC
}

end CBCL.StateAuthoredQuasiDeterminism
