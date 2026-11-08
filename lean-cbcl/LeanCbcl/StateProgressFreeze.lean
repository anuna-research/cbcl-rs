import LeanCbcl.StateProgressLocality

/-! Actual closure-progress data under optional authored fault freezes.
Healthy cut retention is derived from observed freeze errors, not a chosen-root
or assumed progress-locality premise. -/
set_option autoImplicit false
namespace CBCL.StateProgressFreeze
open State StateLift StateLVar StateObservation StateObservationPlan StateInstalledCompiler
open StateInstalledLegacy StateProgressStore StateProgressLocality

/-- The actual raw-verb footprint used by the authored progress binding. -/
def spec (domains : List StateInstalledDomains.Domain) (whole : List Act) (verb freezeVerb : String) : FreezeSpec :=
  ⟨freezeVerb,StateAuthoredBindings.contributes domains whole (.rawVerbs [verb]),true⟩

/-- Optional source decoration uses the existing installed field compiler. -/
def decorate (domains : List StateInstalledDomains.Domain) (whole : List Act) (verb : String)
    (declaration : Option String) (bare : Plan Value) : Plan Value :=
  StateCompiledFieldEquations.decorate (declaration.map (spec domains whole verb)) bare

/-- The actual progress source's data is its kernel projection, independently of
which installed terminal-error guards accompany the source. -/
theorem bare_data (environment : StateAuthoredBindings.Environment) (domains : List StateInstalledDomains.Domain)
    (verb : String) (world : Act → Prop) (A : List Act) :
    data world (sourcePlan (StateInstalledTerm.source (StateInstalledDomains.term environment.context domains
      (.progress verb) (StateAuthoredBindings.resourceVerbs environment)))) A =
      .snapshot (.kernel (StateInstalledDomains.evaluate environment.context domains (.progress verb) (rawHistory A))) :=
  StateInstalledTerm.source_state_coherence world _ A

/-- A healthy decorated source displays the actual kernel value from a scope
containing every contributing-verb act. No particular earliest root is assumed. -/
theorem healthy_payload (environment : StateAuthoredBindings.Environment) (domains : List StateInstalledDomains.Domain)
    (whole : List Act) (verb : String) (declaration : Option String)
    (clear : errors (fun act => act ∈ whole) (path (decorate domains whole verb declaration
      (sourcePlan (StateInstalledTerm.source (StateInstalledDomains.term environment.context domains
        (.progress verb) (StateAuthoredBindings.resourceVerbs environment)))))) whole = none) :
    ∃ scope, (∀ act ∈ scope, act ∈ whole) ∧ (∀ act ∈ whole, act.verb = verb → act ∈ scope) ∧
      (data (fun act => act ∈ whole) (decorate domains whole verb declaration
        (sourcePlan (StateInstalledTerm.source (StateInstalledDomains.term environment.context domains
          (.progress verb) (StateAuthoredBindings.resourceVerbs environment))))) whole).payload =
        some (.kernel (StateInstalledDomains.evaluate environment.context domains (.progress verb) (rawHistory scope))) := by
  classical
  let bare := sourcePlan (StateInstalledTerm.source (StateInstalledDomains.term environment.context domains
    (.progress verb) (StateAuthoredBindings.resourceVerbs environment)))
  cases declaration with
  | none =>
    refine ⟨whole,fun _ member => member,fun _ member _ => member,?_⟩
    exact congrArg Data.payload (bare_data environment domains verb _ whole)
  | some freezeVerb =>
    have combined : freezeFault (fun act => act ∈ whole) freezeVerb (spec domains whole verb freezeVerb).contributes true
        (errors (fun act => act ∈ whole) (path bare) whole) whole = none := clear
    have parts := (StateNativeReader.freeze_clear _ (spec domains whole verb freezeVerb) _ whole).mp combined
    have healthy : freezeFault (fun act => act ∈ whole) freezeVerb (spec domains whole verb freezeVerb).contributes true none whole = none :=
      (StateNativeReader.freeze_clear _ (spec domains whole verb freezeVerb) none whole).mpr ⟨rfl,parts.2⟩
    have noFault : ¬((errors (fun act => act ∈ whole) (path bare) whole).isSome = true ∨
        ∃ a b, FreezeConflict (fun act => act ∈ whole) freezeVerb (spec domains whole verb freezeVerb).contributes true whole a b) := by
      simp only [parts.1,Option.isSome_none,Bool.false_eq_true,false_or,not_exists]
      exact parts.2
    dsimp only [spec] at noFault
    dsimp only [bare] at noFault
    cases chosen : whole.find? (fun root => decide (Earliest (fun act => act ∈ whole) freezeVerb whole root)) with
    | none =>
      refine ⟨whole,fun _ member => member,fun _ member _ => member,?_⟩
      simp only [decorate,Option.map_some,StateCompiledFieldEquations.decorate,data,freezeRead,spec,noFault,if_false,chosen,frozenData]
      exact congrArg Data.payload (bare_data environment domains verb _ whole)
    | some root =>
      have truth : decide (Earliest (fun act => act ∈ whole) freezeVerb whole root) = true := List.find?_some (p := fun other : Act => decide (Earliest (fun act => act ∈ whole) freezeVerb whole other)) chosen
      have first : Earliest (fun act => act ∈ whole) freezeVerb whole root := of_decide_eq_true truth
      refine ⟨causalCut (fun act => act ∈ whole) whole root,fun _ member => (List.mem_filter.mp member).1,?_,?_⟩
      · intro act member verbEq
        exact StateDomainSupportLocality.healthy_contributor_cut whole freezeVerb _ root first healthy act member
          ⟨act,member,by simp [verbEq],rfl⟩
      · simp only [decorate,Option.map_some,StateCompiledFieldEquations.decorate,data,freezeRead,spec,noFault,if_false,chosen,frozenData]
        rw [bare_data environment domains verb]
        rfl

/-- Closure dispatch preserves a reached result for either snapshot or frozen
presentation when both carry the computed progress kernel payload. -/
theorem run_payload (base : StateKernelSEC.Context) (decode : Act → Repeat.Evidence)
    (domains : List StateInstalledDomains.Domain) (verb : String) (bound : Nat) (scope raw : List Act)
    (current : Data Value)
    (payload : current.payload = some (.kernel (StateInstalledDomains.evaluate (context base decode) domains (.progress verb) (rawHistory scope))))
    (reached : bound ≤ protocolProgress (store decode scope) base.thread verb (base.limit verb) scope) :
    (StateOutputCompiler.Query.closure [.element (.progress bound)] readTest).run raw (.data current) =
      .data (.reached (.element (.progress bound))) := by
  have test : readTest (.element (.progress bound)) (.kernel
      (StateInstalledDomains.evaluate (context base decode) domains (.progress verb) (rawHistory scope))) = true := by
    rw [kernel_test]
    exact decide_eq_true reached
  cases current <;> simp_all [StateOutputCompiler.Query.run,StateReaderValues.unfrozen,
    StateRuleRefinement.nativeClosureThreshold,Data.payload]

/-- Earlier concrete progress reaches the same closure query through every
optional fault-freeze outcome, or the actual source reports a terminal fault. -/
theorem success_or_fault (environment : StateAuthoredBindings.Environment) (decode : Act → Repeat.Evidence)
    (domains : List StateInstalledDomains.Domain) (verb : String) (bound : Nat) (bounded : bound < 2^63)
    (coherent : ∀ act, (decode act).verb = act.verb) (A B : List Act)
    (growth : ∀ act ∈ A, act ∈ B)
    (consistent : ∀ a ∈ B, ∀ b ∈ B, a.addr = b.addr → a = b)
    (reached : bound ≤ protocolProgress (store decode A) environment.context.thread verb (environment.context.limit verb) A)
    (sourceName outputName : String) (declaration : Option String) (freezes : List (String × FreezeSpec)) :
    let installed := { environment with context := context environment.context decode }
    let bare := sourcePlan (StateInstalledTerm.source (StateInstalledDomains.term installed.context domains
      (.progress verb) (StateAuthoredBindings.resourceVerbs installed)))
    ∃ code, StateOutputCompiler.compileQuery [.element (.progress bound)]
      (StateAuthoredBindings.primitive installed domains (.progress verb) (.progress verb)) = some code ∧
      let output := (StateOutputCompiler.Output.threshold outputName sourceName code
        (decorate domains (StateScopePool.normalize B) verb declaration bare)).observe B freezes
      output = (outputName,.data (.reached (.element (.progress bound)))) ∨ ∃ evidence, output = (outputName,.fault evidence) := by
  intro installed bare
  let code : StateOutputCompiler.Query Value := .closure [.element (.progress bound)] readTest
  refine ⟨code,?_,?_⟩
  · have bounded' : bound < 9223372036854775808 := by simpa using bounded
    simp [StateOutputCompiler.compileQuery,StateAuthoredBindings.primitive,queryPolicy,readCheck,allowed,bounded',code]
  · cases fault : errors (fun act => act ∈ StateScopePool.normalize B)
        (path (decorate domains (StateScopePool.normalize B) verb declaration bare)) (StateScopePool.normalize B) with
    | some evidence =>
      right; refine ⟨evidence,?_⟩
      simp only [StateOutputCompiler.Output.observe,StateOutputCompiler.sourceValue,observe,fault]
      rfl
    | none =>
      left
      obtain ⟨scope,subset,retained,payload⟩ := healthy_payload installed domains (StateScopePool.normalize B) verb declaration fault
      have inside : ∀ act ∈ A, act.verb = verb → act ∈ scope := fun act member verbEq =>
        retained act ((StateScopePool.normalize_setEq B act).mpr (growth act member)) verbEq
      have scopeConsistent : ∀ a ∈ scope, ∀ b ∈ scope, a.addr = b.addr → a = b := by
        intro a ha b hb eq
        exact consistent a ((StateScopePool.normalize_setEq B a).mp (subset a ha))
          b ((StateScopePool.normalize_setEq B b).mp (subset b hb)) eq
      have later := Nat.le_trans reached (progress_restricted decode verb A scope coherent inside scopeConsistent
        environment.context.thread (environment.context.limit verb))
      simp only [StateOutputCompiler.Output.observe,StateOutputCompiler.sourceValue,observe,fault]
      exact congrArg (outputName, ·) (run_payload environment.context decode domains verb bound scope _ _ payload later)

end CBCL.StateProgressFreeze
