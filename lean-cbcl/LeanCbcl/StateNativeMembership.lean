import LeanCbcl.StateAuthoredDataPreservation

/-! Set-union membership is tied to the actual domain-aware distinct-value
kernel projection and source-owned query policy, then composed through all
fault-freeze scope outcomes. Structured membership queries remain rejected. -/
set_option autoImplicit false
namespace CBCL.StateNativeMembership
open State StateLift StateLVar StateObservation StateObservationPlan StateInstalledCompiler
open StateInstalledLegacy StateInstalledDomains StateDomainSupportLocality StateOutputCompiler

/-- The native distinct projection is membership in the exact selected history. -/
theorem member_value (context : StateKernelSEC.Context) (domains : List Domain) (verb field : String) (A : List Act) :
    StateInstalledDomains.evaluate context domains (.distinct (.verb verb) field) (rawHistory A) =
      .values (has field (selected domains [verb] A)) := by
  have equal := funext (fun value => State.has_setEq
    (StateNativeDataPolicies.selected_setEq domains [verb] (history_setEq A)) field value)
  simpa [StateInstalledDomains.evaluate,rawExpression,StateKernel.evaluate,StateKernelSEC.Context.input,
    StateNativeDataPolicies.admitted_nil,StateKernelSemantics.select,acts,selected] using congrArg StateKernel.Observation.values equal

/-- A selected field witness remains selected as accepted domain evidence grows. -/
theorem member_grows (domains : List Domain) (verb field : String) (value : Val) {A B : List Act}
    (growth : ∀ act ∈ A, act ∈ B) (reached : has field (selected domains [verb] A) value = true) :
    has field (selected domains [verb] B) value = true := by
  obtain ⟨act,member,matching⟩ := List.any_eq_true.mp reached
  exact List.any_eq_true.mpr ⟨act,StateDomainSupportLocality.selected_grows domains [verb] growth act member,matching⟩

/-- Actual emitted membership code tests the source's kernel carrier, not its
possibly frozen or pending displayed payload. -/
theorem compiled_member (environment : StateAuthoredBindings.Environment) (domains : List Domain) (verb field : String)
    (value : Val) (admitted : scalar value = true) :
    ∃ code, compileQuery [.element (.member value)]
      (StateAuthoredBindings.primitive environment domains (.distinct (.verb verb) field) (.setUnion verb field)) = some code ∧
      ∀ (A : List Act) (payload : Data Value), code.run A (.data payload) =
        if has field (selected domains [verb] A) value then .data (.reached (.element (.member value))) else .data .pending := by
  let term := StateInstalledDomains.term environment.context domains (.distinct (.verb verb) field) (StateAuthoredBindings.resourceVerbs environment)
  let test := fun query state => readTest query (term.project state)
  refine ⟨.raw [.element (.member value)] test term.state,?_,?_⟩
  · simp [compileQuery,StateAuthoredBindings.primitive,queryPolicy,readCheck,StateInstalledLegacy.allowed,admitted,term,test]
  · intro A payload
    have native : test (.element (.member value)) (rawHistory A) = has field (selected domains [verb] A) value := by
      simp only [test,term,StateInstalledDomains.term,member_value,readTest]
    simp only [Query.run,term,StateInstalledDomains.term,id_eq,nativeRawThreshold,List.find?_cons,native]
    cases has field (selected domains [verb] A) value <;> rfl

/-- Set-union membership success survives accepted growth and optional fault
freezes, or the actual guarded source observation reports terminal evidence. -/
theorem member_success_or_fault (environment : StateAuthoredBindings.Environment) (domains : List Domain)
    (verb field : String) (value : Val) (admitted : scalar value = true) (A B : List Act)
    (growth : ∀ act ∈ A, act ∈ B) (reached : has field (selected domains [verb] A) value = true)
    (sourceName outputName : String) (declaration : Option String)
    (ranked : StateExecutableFreeze.Ranked (StateScopePool.normalize B)) :
    let bare := sourcePlan (StateInstalledTerm.source (StateInstalledDomains.term environment.context domains
      (.distinct (.verb verb) field) (StateAuthoredBindings.resourceVerbs environment)))
    ∃ code, compileQuery [.element (.member value)]
      (StateAuthoredBindings.primitive environment domains (.distinct (.verb verb) field) (.setUnion verb field)) = some code ∧
      let output := (Output.threshold outputName sourceName code
        (StateNativeDataFreeze.decorate domains [verb] (StateScopePool.normalize B) declaration bare)).observe B
          (StateNativeDataFreeze.metadata domains [verb] (StateScopePool.normalize B) sourceName declaration)
      output = (outputName,.data (.reached (.element (.member value)))) ∨ ∃ evidence, output = (outputName,.fault evidence) := by
  intro bare
  obtain ⟨code,compiled,run⟩ := compiled_member environment domains verb field value admitted
  refine ⟨code,compiled,?_⟩
  cases fault : errors (fun act => act ∈ StateScopePool.normalize B)
      (path (StateNativeDataFreeze.decorate domains [verb] (StateScopePool.normalize B) declaration bare)) (StateScopePool.normalize B) with
  | some evidence =>
    right; refine ⟨evidence,?_⟩
    simp only [Output.observe,sourceValue,observe,fault,StateNativeDataFreeze.query_fault]
  | none =>
    left
    have inside : ∀ act ∈ A, act ∈ StateScopePool.normalize B := fun act member =>
      (StateScopePool.normalize_setEq B act).mpr (growth act member)
    have later := member_grows domains verb field value inside reached
    have rawReached : has field (selected domains [verb] (StateThresholdDispatch.referenceScope B
        (StateNativeDataFreeze.metadata domains [verb] (StateScopePool.normalize B) sourceName declaration) sourceName)) value = true := by
      rw [StateNativeDataFreeze.selected_scope domains [verb] B sourceName declaration bare ranked fault]
      exact later
    simp only [Output.observe,sourceValue,observe,fault]
    exact congrArg (outputName, ·) ((run _ _).trans (by simp only [rawReached,if_true]))

end CBCL.StateNativeMembership
