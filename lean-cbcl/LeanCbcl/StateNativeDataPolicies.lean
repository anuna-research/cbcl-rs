import LeanCbcl.StateAuthoredFinitePreservation

/-! Native count and existence policies are tied to their actual domain-aware
kernel term. Cardinalities are over retained selected acts, so repeated delivery
cannot increase a count and domain-source support is included in freeze locality. -/
namespace CBCL.StateNativeDataPolicies
open State StateLift StateLVar StateObservation StateObservationPlan StateInstalledCompiler
open StateInstalledLegacy StateInstalledDomains StateDomainSupportLocality

/-- Exact membership equality for the domain-aware selected source history. -/
theorem selected_setEq (domains : List Domain) (names : List String) {A B : List Act} (same : SetEq A B) :
    SetEq (selected domains names A) (selected domains names B) := by
  have inside := StateInstalledDomains.selected_setEq domains same
  intro act
  simp only [selected,List.mem_filter,inside act]

/-- Native distinct cardinalities grow under accepted growth, including duplicate
and reordered histories. No duplicate-free delivery-list premise is required. -/
theorem count_grows (domains : List Domain) (names : List String) {A B : List Act}
    (growth : ∀ act ∈ A, act ∈ B) :
    FinSet.card (FinSet.mk (selected domains names A)) ≤ FinSet.card (FinSet.mk (selected domains names B)) := by
  have inside : ∀ act ∈ FinSet.dedup (selected domains names A), act ∈ FinSet.dedup (selected domains names B) := by
    intro act member
    exact FinSet.mem_dedup.mpr (StateDomainSupportLocality.selected_grows domains names growth act (FinSet.mem_dedup.mp member))
  obtain ⟨chosen,perm,subset⟩ := List.subperm_of_subset (FinSet.nodup_dedup (selected domains names A)) inside
  change (FinSet.dedup (selected domains names A)).length ≤ (FinSet.dedup (selected domains names B)).length
  have equal := perm.length_eq
  have bounded := subset.length_le
  omega

/-- Canonical retained history selects exactly the same finite set of source
acts; its selected list has no duplicates and therefore computes cardinality. -/
theorem canonical_count (domains : List Domain) (names : List String) (A : List Act) :
    (selected domains names (history (rawHistory A))).length = FinSet.card (FinSet.mk (selected domains names A)) := by
  have unique : (selected domains names (history (rawHistory A))).Nodup :=
    ((FinSet.nodup_dedup _).filter _).filter _
  have same : FinSet.mk (selected domains names (history (rawHistory A))) = FinSet.mk (selected domains names A) :=
    FinSet.ext (selected_setEq domains names (history_setEq A))
  rw [← same,FinSet.card_mk_of_nodup unique]

/-- An empty extra kernel-domain pass leaves the already selected acts intact. -/
theorem admitted_nil (A : List Act) : StateKernelSemantics.admitted [] A = A := by
  simp [StateKernelSemantics.admitted]

/-- Actual native count projection agrees with distinct selected cardinality,
including order changes and duplicate delivery of raw accepted history. -/
theorem count_value (context : StateKernelSEC.Context) (domains : List Domain) (verb : String) (A : List Act) :
    StateInstalledDomains.evaluate context domains (.count (.verb verb)) (rawHistory A) =
      .integer (FinSet.card (FinSet.mk (selected domains [verb] A))) := by
  have count := canonical_count domains [verb] A
  simpa [StateInstalledDomains.evaluate,rawExpression,StateKernel.evaluate,StateKernelSEC.Context.input,
    admitted_nil,StateKernelSemantics.select,acts,size,selected] using congrArg StateKernel.Observation.integer (congrArg Int.ofNat count)

/-- Actual native existence projection uses the same selected history. -/
theorem exists_value (context : StateKernelSEC.Context) (domains : List Domain) (verb : String) (A : List Act) :
    StateInstalledDomains.evaluate context domains (.existsRule (.verb verb)) (rawHistory A) =
      .boolean (!(selected domains [verb] A).isEmpty) := by
  have empty := State.isEmpty_setEq (selected_setEq domains [verb] (history_setEq A))
  simpa [StateInstalledDomains.evaluate,rawExpression,StateKernel.evaluate,StateKernelSEC.Context.input,
    admitted_nil,StateKernelSemantics.select,acts,selected] using congrArg StateKernel.Observation.boolean (congrArg Bool.not empty)

/-- Native count query code is emitted from the actual source-owned policy;
its predicate reads distinct selected cardinality, not a displayed payload. -/
theorem compiled_count (environment : StateAuthoredBindings.Environment) (domains : List Domain) (verb : String)
    (bound : Nat) (admitted : bound < 2^63) :
    ∃ code, StateOutputCompiler.compileQuery [.element (.count bound)]
      (StateAuthoredBindings.primitive environment domains (.count (.verb verb)) (.count verb)) = some code ∧
      ∀ (A : List Act) (payload : Data Value), code.run A (.data payload) =
        if bound ≤ FinSet.card (FinSet.mk (selected domains [verb] A)) then
          .data (.reached (.element (.count bound))) else .data .pending := by
  let term := StateInstalledDomains.term environment.context domains (.count (.verb verb)) (StateAuthoredBindings.resourceVerbs environment)
  let test := fun query state => readTest query (term.project state)
  refine ⟨.raw [.element (.count bound)] test term.state,?_,?_⟩
  · simp [StateOutputCompiler.compileQuery,StateAuthoredBindings.primitive,queryPolicy,readCheck,StateInstalledLegacy.allowed,admitted,term,test]
  · intro A payload
    have native : test (.element (.count bound)) (rawHistory A) = decide (bound ≤ FinSet.card (FinSet.mk (selected domains [verb] A))) := by
      simp only [test,term,StateInstalledDomains.term,count_value,readTest]
      simp
    simp only [StateOutputCompiler.Query.run,term,StateInstalledDomains.term,id_eq,nativeRawThreshold,List.find?_cons,native]
    by_cases enough : bound ≤ FinSet.card (FinSet.mk (selected domains [verb] A)) <;> simp [enough]

/-- Native existence query code also comes from the actual kernel source term. -/
theorem compiled_exists (environment : StateAuthoredBindings.Environment) (domains : List Domain) (verb : String) :
    ∃ code, StateOutputCompiler.compileQuery [.element (.scalar (.bool true))]
      (StateAuthoredBindings.primitive environment domains (.existsRule (.verb verb)) (.existsRule verb)) = some code ∧
      ∀ (A : List Act) (payload : Data Value), code.run A (.data payload) =
        if (selected domains [verb] A).isEmpty then .data .pending
          else .data (.reached (.element (.scalar (.bool true)))) := by
  let term := StateInstalledDomains.term environment.context domains (.existsRule (.verb verb)) (StateAuthoredBindings.resourceVerbs environment)
  let test := fun query state => readTest query (term.project state)
  refine ⟨.raw [.element (.scalar (.bool true))] test term.state,?_,?_⟩
  · simp [StateOutputCompiler.compileQuery,StateAuthoredBindings.primitive,queryPolicy,readCheck,StateInstalledLegacy.allowed,term,test]
  · intro A payload
    have native : test (.element (.scalar (.bool true))) (rawHistory A) = !(selected domains [verb] A).isEmpty := by
      simp only [test,term,StateInstalledDomains.term,exists_value,readTest]
    simp only [StateOutputCompiler.Query.run,term,StateInstalledDomains.term,id_eq,nativeRawThreshold,List.find?_cons,native]
    cases (selected domains [verb] A).isEmpty <;> rfl

end CBCL.StateNativeDataPolicies
