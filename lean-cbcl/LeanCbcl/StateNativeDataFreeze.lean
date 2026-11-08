import LeanCbcl.StateNativeDataPolicies

/-! Native count/existence query stability through actual fault-freeze source
observations. Existing plan decoration and source factories are reused; healthy
cut locality is derived from observed errors for every root-selection outcome. -/
namespace CBCL.StateNativeDataFreeze
open State StateLift StateLVar StateObservation StateObservationPlan StateInstalledCompiler
open StateInstalledLegacy StateInstalledDomains StateDomainSupportLocality StateOutputCompiler

/-- Fault-freeze metadata retains selected writers and their domain sources. -/
def spec (domains : List Domain) (names : List String) (whole : List Act) (verb : String) : FreezeSpec :=
  ⟨verb,StateAuthoredBindings.contributes domains whole (.verbs names),true⟩

/-- Source-name dispatch metadata matches the optional source decoration. -/
def metadata (domains : List Domain) (names : List String) (whole : List Act) (name : String) (declaration : Option String) :
    List (String × FreezeSpec) := declaration.toList.map (fun verb => (name,spec domains names whole verb))

/-- Reuse the installed field compiler's decoration operation. -/
def decorate {V : Type} (domains : List Domain) (names : List String) (whole : List Act)
    (declaration : Option String) (bare : Plan V) : Plan V :=
  StateCompiledFieldEquations.decorate (declaration.map (spec domains names whole)) bare

/-- Any completed source fault is preserved by all emitted query strategies. -/
theorem query_fault {V : Type} (code : Query V) (raw : List Act) (evidence : Evidence) :
    code.run raw (.fault evidence) = .fault evidence := by
  cases code <;> rfl

/-- A healthy observed decorated source preserves its selected source history
in the actual dispatch scope. No selected-root or cut-locality premise is supplied. -/
theorem selected_scope {V : Type} (domains : List Domain) (names : List String) (whole : List Act)
    (sourceName : String) (declaration : Option String) (bare : Plan V)
    (ranked : StateExecutableFreeze.Ranked (StateScopePool.normalize whole))
    (clear : errors (fun act => act ∈ StateScopePool.normalize whole)
      (path (decorate domains names (StateScopePool.normalize whole) declaration bare)) (StateScopePool.normalize whole) = none) :
    selected domains names (StateThresholdDispatch.referenceScope whole
      (metadata domains names (StateScopePool.normalize whole) sourceName declaration) sourceName) =
      selected domains names (StateScopePool.normalize whole) := by
  cases declaration with
  | none => rfl
  | some verb =>
    cases chosen : StateScopePool.uniqueRoot (StateScopePool.normalize whole) verb with
    | none => simp [metadata,StateThresholdDispatch.referenceScope,spec,chosen]
    | some root =>
      have combined : freezeFault (fun act => act ∈ StateScopePool.normalize whole) verb
          (spec domains names (StateScopePool.normalize whole) verb).contributes true
          (errors (fun act => act ∈ StateScopePool.normalize whole) (path bare) (StateScopePool.normalize whole))
          (StateScopePool.normalize whole) = none := clear
      have parts := (StateNativeReader.freeze_clear _ (spec domains names (StateScopePool.normalize whole) verb) _ _).mp combined
      have healthy : freezeFault (fun act => act ∈ StateScopePool.normalize whole) verb
          (spec domains names (StateScopePool.normalize whole) verb).contributes true none (StateScopePool.normalize whole) = none :=
        (StateNativeReader.freeze_clear _ (spec domains names (StateScopePool.normalize whole) verb) none _).mpr ⟨rfl,parts.2⟩
      have first := StateScopePool.uniqueRoot_earliest (StateScopePool.normalize whole) ranked verb root chosen
      have equal := StateDomainSupportLocality.selected_cut domains names (StateScopePool.normalize whole) verb root first healthy
      simpa [metadata,StateThresholdDispatch.referenceScope,spec,chosen] using equal

/-- Native count queries preserve earlier success or expose an actual source
fault under growth and optional fault-freezes, including absent/concurrent roots. -/
theorem count_success_or_fault (environment : StateAuthoredBindings.Environment) (domains : List Domain)
    (verb : String) (bound : Nat) (admitted : bound < 2^63) (A B : List Act)
    (growth : ∀ act ∈ A, act ∈ B)
    (reached : bound ≤ FinSet.card (FinSet.mk (selected domains [verb] A)))
    (sourceName outputName : String) (declaration : Option String)
    (ranked : StateExecutableFreeze.Ranked (StateScopePool.normalize B)) :
    let bare := sourcePlan (StateInstalledTerm.source (StateInstalledDomains.term environment.context domains
      (.count (.verb verb)) (StateAuthoredBindings.resourceVerbs environment)))
    ∃ code, compileQuery [.element (.count bound)]
      (StateAuthoredBindings.primitive environment domains (.count (.verb verb)) (.count verb)) = some code ∧
      let output := (Output.threshold outputName sourceName code
        (decorate domains [verb] (StateScopePool.normalize B) declaration bare)).observe B
          (metadata domains [verb] (StateScopePool.normalize B) sourceName declaration)
      output = (outputName,.data (.reached (.element (.count bound)))) ∨
        ∃ evidence, output = (outputName,.fault evidence) := by
  intro bare
  obtain ⟨code,compiled,run⟩ := StateNativeDataPolicies.compiled_count environment domains verb bound admitted
  refine ⟨code,compiled,?_⟩
  cases fault : errors (fun act => act ∈ StateScopePool.normalize B)
      (path (decorate domains [verb] (StateScopePool.normalize B) declaration bare)) (StateScopePool.normalize B) with
  | some evidence =>
    right; refine ⟨evidence,?_⟩
    simp only [Output.observe,sourceValue,observe,fault,query_fault]
  | none =>
    left
    have inside : ∀ act ∈ A, act ∈ StateScopePool.normalize B := fun act present =>
      (StateScopePool.normalize_setEq B act).mpr (growth act present)
    have enough : bound ≤ FinSet.card (FinSet.mk (selected domains [verb]
        (StateThresholdDispatch.referenceScope B (metadata domains [verb] (StateScopePool.normalize B) sourceName declaration) sourceName))) := by
      rw [selected_scope domains [verb] B sourceName declaration bare ranked fault]
      exact Nat.le_trans reached (StateNativeDataPolicies.count_grows domains [verb] inside)
    simp only [Output.observe,sourceValue,observe,fault]
    exact congrArg (outputName, ·) ((run _ _).trans (if_pos enough))

/-- Native existence queries use the same real source term and error pass. -/
theorem exists_success_or_fault (environment : StateAuthoredBindings.Environment) (domains : List Domain)
    (verb : String) (A B : List Act) (growth : ∀ act ∈ A, act ∈ B)
    (reached : (selected domains [verb] A).isEmpty = false)
    (sourceName outputName : String) (declaration : Option String)
    (ranked : StateExecutableFreeze.Ranked (StateScopePool.normalize B)) :
    let bare := sourcePlan (StateInstalledTerm.source (StateInstalledDomains.term environment.context domains
      (.existsRule (.verb verb)) (StateAuthoredBindings.resourceVerbs environment)))
    ∃ code, compileQuery [.element (.scalar (.bool true))]
      (StateAuthoredBindings.primitive environment domains (.existsRule (.verb verb)) (.existsRule verb)) = some code ∧
      let output := (Output.threshold outputName sourceName code
        (decorate domains [verb] (StateScopePool.normalize B) declaration bare)).observe B
          (metadata domains [verb] (StateScopePool.normalize B) sourceName declaration)
      output = (outputName,.data (.reached (.element (.scalar (.bool true))))) ∨
        ∃ evidence, output = (outputName,.fault evidence) := by
  intro bare
  obtain ⟨code,compiled,run⟩ := StateNativeDataPolicies.compiled_exists environment domains verb
  refine ⟨code,compiled,?_⟩
  cases fault : errors (fun act => act ∈ StateScopePool.normalize B)
      (path (decorate domains [verb] (StateScopePool.normalize B) declaration bare)) (StateScopePool.normalize B) with
  | some evidence =>
    right; refine ⟨evidence,?_⟩
    simp only [Output.observe,sourceValue,observe,fault,query_fault]
  | none =>
    left
    have inside : ∀ act ∈ A, act ∈ StateScopePool.normalize B := fun act present =>
      (StateScopePool.normalize_setEq B act).mpr (growth act present)
    obtain ⟨act,member⟩ := List.isEmpty_eq_false_iff_exists_mem.mp reached
    have later := StateDomainSupportLocality.selected_grows domains [verb] inside act member
    have nonempty : (selected domains [verb] (StateThresholdDispatch.referenceScope B
        (metadata domains [verb] (StateScopePool.normalize B) sourceName declaration) sourceName)).isEmpty = false := by
      rw [selected_scope domains [verb] B sourceName declaration bare ranked fault]
      exact List.isEmpty_eq_false_iff_exists_mem.mpr ⟨act,later⟩
    simp only [Output.observe,sourceValue,observe,fault]
    exact congrArg (outputName, ·) ((run _ _).trans (by simp only [nonempty,Bool.false_eq_true,if_false]))

end CBCL.StateNativeDataFreeze
