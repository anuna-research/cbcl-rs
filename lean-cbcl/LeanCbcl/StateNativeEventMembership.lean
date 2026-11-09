import LeanCbcl.StateEventMapKernel

/-! Actual event membership query code and fault-freeze composition. Address
content consistency is explicit: equal addresses must denote the same writer.
No map-cell result or native membership equivalence is supplied as a premise. -/
set_option autoImplicit false
namespace CBCL.StateNativeEventMembership
open State StateLift StateLVar StateObservation StateObservationPlan StateInstalledCompiler
open StateInstalledLegacy StateInstalledDomains StateDomainSupportLocality StateOutputCompiler
open StateEventMapKernel

/-- Event member code comes from the source's actual raw-kernel query policy. -/
theorem compiled_member (environment : StateAuthoredBindings.Environment) (domains : List Domain) (verb field : String)
    (value : Val) (admitted : scalar value = true) :
    ∃ code, compileQuery [.element (.member value)]
      (StateAuthoredBindings.primitive environment domains (.mapped (plan verb field)) (.events verb field)) = some code ∧
      ∀ (A : List Act), (∀ a ∈ A, ∀ b ∈ A, a.addr = b.addr → a = b) →
        ∀ payload : Data Value, code.run A (.data payload) =
          if has field (selected domains [verb] A) value then .data (.reached (.element (.member value))) else .data .pending := by
  let term := StateInstalledDomains.term environment.context domains (.mapped (plan verb field)) (StateAuthoredBindings.resourceVerbs environment)
  let test := fun query state => readTest query (term.project state)
  refine ⟨.raw [.element (.member value)] test term.state,?_,?_⟩
  · simp [compileQuery,StateAuthoredBindings.primitive,queryPolicy,readCheck,StateInstalledLegacy.allowed,admitted,term,test]
  · intro A consistent payload
    have native : test (.element (.member value)) (rawHistory A) = has field (selected domains [verb] A) value :=
      StateEventMapKernel.native_member environment.context domains verb field value A consistent
    simp only [Query.run,term,StateInstalledDomains.term,id_eq,nativeRawThreshold,List.find?_cons,native]
    cases has field (selected domains [verb] A) value <;> rfl

/-- Earlier event membership persists under growth or exposes the actual
source fault, for every outcome of the source's fault-freeze root selector. -/
theorem member_success_or_fault (environment : StateAuthoredBindings.Environment) (domains : List Domain)
    (verb field : String) (value : Val) (admitted : scalar value = true) (A B : List Act)
    (growth : ∀ act ∈ A, act ∈ B) (reached : has field (selected domains [verb] A) value = true)
    (sourceName outputName : String) (declaration : Option String)
    (ranked : StateExecutableFreeze.Ranked (StateScopePool.normalize B))
    (consistent : ∀ a ∈ B, ∀ b ∈ B, a.addr = b.addr → a = b) :
    let bare := sourcePlan (StateInstalledTerm.source (StateInstalledDomains.term environment.context domains
      (.mapped (plan verb field)) (StateAuthoredBindings.resourceVerbs environment)))
    ∃ code, compileQuery [.element (.member value)]
      (StateAuthoredBindings.primitive environment domains (.mapped (plan verb field)) (.events verb field)) = some code ∧
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
    have later := StateNativeMembership.member_grows domains verb field value inside reached
    let raw := StateThresholdDispatch.referenceScope B
      (StateNativeDataFreeze.metadata domains [verb] (StateScopePool.normalize B) sourceName declaration) sourceName
    have rawConsistent : ∀ a ∈ raw, ∀ b ∈ raw, a.addr = b.addr → a = b := by
      intro a ma b mb same
      exact consistent a (StateAuthoredDataPreservation.raw_inside B _ sourceName a ma)
        b (StateAuthoredDataPreservation.raw_inside B _ sourceName b mb) same
    have rawReached : has field (selected domains [verb] raw) value = true := by
      rw [StateNativeDataFreeze.selected_scope domains [verb] B sourceName declaration bare ranked fault]
      exact later
    simp only [Output.observe,sourceValue,observe,fault]
    exact congrArg (outputName, ·) ((run raw rawConsistent _).trans (by simp only [rawReached,if_true]))

end CBCL.StateNativeEventMembership
