import LeanCbcl.StateFiniteFreezePolicy

/-! Finite compiled-output stability for every root-selection outcome and both
unfrozen and fault-frozen source declarations. No chosen root or source health
is assumed: those facts are obtained from actual metadata and observation. -/
namespace CBCL.StateFiniteOutputStability
open State StateLift StateLVar StateObservation StateObservationPlan StateInstalledCompiler
open StateFiniteFreezePolicy

/-- The source plan selected by optional authored fault-freeze metadata. -/
noncomputable def source (field : StateInstalledFinite.Field) (whole : List Act) : Option String → Plan StateInstalledLegacy.Value
  | none => sourcePlan (StateInstalledFinite.source field)
  | some verb => frozenPlan field whole verb

/-- The matching output dispatch metadata for this source declaration. -/
def freezes (field : StateInstalledFinite.Field) (whole : List Act) (name : String) :
    Option String → List (String × FreezeSpec)
  | none => []
  | some verb => [(name,freezeSpec field whole verb)]

/-- Reading a healthy finite source, with or without a freeze, entails that its
actual domain/top checker is clear; a guard-free substitute is not sufficient. -/
theorem source_clear (field : StateInstalledFinite.Field) (whole : List Act) (declaration : Option String)
    (clear : errors (fun act => act ∈ whole) (path (source field whole declaration)) whole = none) :
    (StateInstalledFinite.errorSpec field).read whole = none := by
  cases declaration with
  | none =>
    have original := clear
    simp only [source,StateInstalledFinite.source,StateInstalledTerm.source,
      StateInstalledFinite.term,List.foldr_cons,List.foldr_nil,StateInstalledTerm.Guard.apply,
      sourcePlan,path,errors] at original
    cases result : (StateInstalledFinite.errorSpec field).read whole with
    | none => rfl
    | some evidence =>
      simp only [result,unionError] at original
      exact original
  | some verb =>
    have combined : freezeFault (fun act => act ∈ whole) verb (freezeSpec field whole verb).contributes true
        ((StateInstalledFinite.errorSpec field).read whole) whole = none := by
      have original := clear
      simp only [source,frozenPlan,StateInstalledFinite.source,StateInstalledTerm.source,
        StateInstalledFinite.term,List.foldr_cons,List.foldr_nil,StateInstalledTerm.Guard.apply,
        sourcePlan,path,errors] at original
      cases result : (StateInstalledFinite.errorSpec field).read whole <;> simpa only [result,unionError] using original
    exact ((StateNativeReader.freeze_clear (fun act => act ∈ whole) (freezeSpec field whole verb) _ whole).mp combined).1

/-- The actual finite top guard rules out a nonfaulting top carrier. -/
theorem non_top (field : StateInstalledFinite.Field) (whole : List Act)
    (clear : (StateInstalledFinite.errorSpec field).read whole = none) :
    StateInstalledFinite.state field whole ≠ field.table.table.top := by
  intro top
  rw [StateInstalledFinite.native_error_refinement] at clear
  simp [StateInstalledFinite.nativeError,StateInstalledFinite.topErrorSpec,top] at clear
  split at clear <;> contradiction

/-- Selected, absent, and concurrent-root dispatch all preserve raw finite state
when the complete observed source is healthy. Concurrent conflicts are handled
by the error branch, rather than a healthy-root premise. -/
theorem scope_state (field : StateInstalledFinite.Field) (whole : List Act) (name : String)
    (declaration : Option String) (ranked : StateExecutableFreeze.Ranked (StateScopePool.normalize whole))
    (clear : errors (fun act => act ∈ StateScopePool.normalize whole)
      (path (source field (StateScopePool.normalize whole) declaration)) (StateScopePool.normalize whole) = none) :
    StateInstalledFinite.state field (StateThresholdDispatch.referenceScope whole
      (freezes field (StateScopePool.normalize whole) name declaration) name) =
      StateInstalledFinite.state field (StateScopePool.normalize whole) := by
  cases declaration with
  | none => rfl
  | some verb =>
    cases selected : StateScopePool.uniqueRoot (StateScopePool.normalize whole) verb with
    | none => simp [StateThresholdDispatch.referenceScope,freezes,freezeSpec,selected]
    | some root =>
      have combined : freezeFault (fun act => act ∈ StateScopePool.normalize whole) verb
          (freezeSpec field (StateScopePool.normalize whole) verb).contributes true
          ((StateInstalledFinite.errorSpec field).read (StateScopePool.normalize whole)) (StateScopePool.normalize whole) = none := by
        have original := clear
        simp only [source,frozenPlan,StateInstalledFinite.source,StateInstalledTerm.source,
          StateInstalledFinite.term,List.foldr_cons,List.foldr_nil,StateInstalledTerm.Guard.apply,
          sourcePlan,path,errors] at original
        cases result : (StateInstalledFinite.errorSpec field).read (StateScopePool.normalize whole) <;>
          simpa only [result,unionError] using original
      have parts := (StateNativeReader.freeze_clear _ (freezeSpec field (StateScopePool.normalize whole) verb) _ _).mp combined
      have healthy : freezeFault (fun act => act ∈ StateScopePool.normalize whole) verb
          (freezeSpec field (StateScopePool.normalize whole) verb).contributes true none (StateScopePool.normalize whole) = none :=
        (StateNativeReader.freeze_clear _ (freezeSpec field (StateScopePool.normalize whole) verb) none _).mpr ⟨rfl,parts.2⟩
      have first := StateScopePool.uniqueRoot_earliest (StateScopePool.normalize whole) ranked verb root selected
      simpa [StateThresholdDispatch.referenceScope,freezes,List.lookup,freezeSpec,selected] using
        state_cut field (StateScopePool.normalize whole) verb root first healthy

/-- Checked alternatives identify the same unique answer in the actual compiled
raw-query strategy, irrespective of alternative ordering or displayed payload. -/
theorem run_reached (field : StateInstalledFinite.Field) (queries : List Val) (query : Val)
    (checked : StateFiniteRead.check field queries = true) (member : query ∈ queries)
    (raw : List Act) (reached : StateFiniteRead.test field query (StateInstalledFinite.state field raw) = true)
    (payload : Data StateInstalledLegacy.Value) :
    (StateOutputCompiler.Query.raw (queries.map (fun q => StateInstalledLegacy.Value.element (.scalar q)))
      (StateFiniteRead.policy field).test (StateInstalledFinite.term field).state).run raw (.data payload) =
        .data (.reached (.element (.scalar query))) := by
  have pairChecked : StateFiniteRead.pairCheck field queries = true := by
    have check := checked
    simp only [StateFiniteRead.check,Bool.and_eq_true] at check
    exact check.2
  have notTop : StateInstalledFinite.state field raw ≠ field.table.table.top := by
    intro top
    simp [top,StateFiniteRead.test_top] at reached
  have hit : StateFiniteRead.reaches field query (StateInstalledFinite.state field raw) = true := by
    rw [StateFiniteRead.test_non_top field query _ notTop] at reached
    exact reached
  have found : (queries.map (fun q => StateInstalledLegacy.Value.element (.scalar q))).find?
      (fun q => (StateFiniteRead.policy field).test q (rawHistory raw)) = some (.element (.scalar query)) := by
    apply find_unique
    · exact List.mem_map.mpr ⟨query,member,rfl⟩
    · rw [StateFiniteRead.policy_actual_history]; exact reached
    · intro other inside read
      obtain ⟨value,valueMember,rfl⟩ := List.mem_map.mp inside
      by_cases same : value = query
      · rw [same]
      · rw [StateFiniteRead.policy_actual_history,StateFiniteRead.test_non_top field value _ notTop] at read
        have rejected := (StateFiniteRead.pairCheck_iff field queries).mp pairChecked query member value valueMember
          (Ne.symm same) (StateInstalledFinite.state field raw) notTop hit
        simp [read] at rejected
  simp only [StateOutputCompiler.Query.run,StateInstalledFinite.term,id_eq,nativeRawThreshold,found]

/-- Finite compiled output is stable-or-fault across growth for every optional
fault-freeze declaration and every actual root-selection outcome. -/
theorem output_success_or_fault (field : StateInstalledFinite.Field) (queries : List Val) (query : Val)
    (checked : StateFiniteRead.check field queries = true) (member : query ∈ queries) (A B : List Act)
    (growth : ∀ act ∈ A, act ∈ B)
    (reached : StateFiniteRead.test field query (StateInstalledFinite.state field A) = true)
    (declaration : Option String) (sourceName outputName : String)
    (ranked : StateExecutableFreeze.Ranked (StateScopePool.normalize B)) :
    ∃ code, StateOutputCompiler.compileQuery (queries.map (fun q => .element (.scalar q))) (StateFiniteRead.definition field) = some code ∧
      let output := (StateOutputCompiler.Output.threshold outputName sourceName code
        (source field (StateScopePool.normalize B) declaration)).observe B
          (freezes field (StateScopePool.normalize B) sourceName declaration)
      output = (outputName,.data (.reached (.element (.scalar query)))) ∨
        ∃ evidence, output = (outputName,.fault evidence) := by
  refine ⟨.raw (queries.map (fun q => .element (.scalar q))) (StateFiniteRead.policy field).test
    (StateInstalledFinite.term field).state,compiled_alternatives field queries checked,?_⟩
  cases fault : errors (fun act => act ∈ StateScopePool.normalize B)
      (path (source field (StateScopePool.normalize B) declaration)) (StateScopePool.normalize B) with
  | some evidence =>
    right; refine ⟨evidence,?_⟩
    simp [StateOutputCompiler.Output.observe,StateOutputCompiler.sourceValue,observe,fault,
      StateOutputCompiler.Query.run,nativeRawThreshold]
  | none =>
    left
    have notTop := non_top field (StateScopePool.normalize B) (source_clear field _ declaration fault)
    have inside : ∀ act ∈ A, act ∈ StateScopePool.normalize B := fun act present =>
      (StateScopePool.normalize_setEq B act).mpr (growth act present)
    have oldReach : StateFiniteRead.reaches field query (StateInstalledFinite.state field A) = true := by
      have both : (StateInstalledFinite.state field A != field.table.table.top) = true ∧
          StateFiniteRead.reaches field query (StateInstalledFinite.state field A) = true := by
        simpa only [StateFiniteRead.test,Bool.and_eq_true] using reached
      exact both.2
    have later := StateFiniteRead.reaches_upward field query _ _ (StateInstalledFinite.state_grows field inside) oldReach
    have rawReached : StateFiniteRead.test field query (StateInstalledFinite.state field
        (StateThresholdDispatch.referenceScope B (freezes field (StateScopePool.normalize B) sourceName declaration) sourceName)) = true := by
      rw [scope_state field B sourceName declaration ranked fault,StateFiniteRead.test_non_top field query _ notTop]
      exact later
    simp only [StateOutputCompiler.Output.observe,StateOutputCompiler.sourceValue,observe,fault]
    exact congrArg (outputName, ·) (run_reached field queries query checked member _ rawReached _)

/-- When the complete observed source is clear, the general disjunction cannot
be discharged by fault: the actual emitted output retains the reached answer. -/
theorem output_reached (field : StateInstalledFinite.Field) (queries : List Val) (query : Val)
    (checked : StateFiniteRead.check field queries = true) (member : query ∈ queries) (A B : List Act)
    (growth : ∀ act ∈ A, act ∈ B)
    (reached : StateFiniteRead.test field query (StateInstalledFinite.state field A) = true)
    (declaration : Option String) (sourceName outputName : String)
    (ranked : StateExecutableFreeze.Ranked (StateScopePool.normalize B))
    (clear : errors (fun act => act ∈ StateScopePool.normalize B)
      (path (source field (StateScopePool.normalize B) declaration)) (StateScopePool.normalize B) = none) :
    ∃ code, StateOutputCompiler.compileQuery (queries.map (fun q => .element (.scalar q))) (StateFiniteRead.definition field) = some code ∧
      (StateOutputCompiler.Output.threshold outputName sourceName code
        (source field (StateScopePool.normalize B) declaration)).observe B
          (freezes field (StateScopePool.normalize B) sourceName declaration) =
            (outputName,.data (.reached (.element (.scalar query)))) := by
  obtain ⟨code,compiled,result⟩ := output_success_or_fault field queries query checked member A B growth reached
    declaration sourceName outputName ranked
  refine ⟨code,compiled,?_⟩
  rcases result with success | ⟨evidence,fault⟩
  · exact success
  · have codeEq : code = .raw (queries.map (fun q => .element (.scalar q))) (StateFiniteRead.policy field).test
        (StateInstalledFinite.term field).state := Option.some.inj ((compiled_alternatives field queries checked).symm.trans compiled) |>.symm
    simp only [StateOutputCompiler.Output.observe,StateOutputCompiler.sourceValue,observe,clear,codeEq,
      StateOutputCompiler.Query.run,nativeRawThreshold] at fault
    split at fault <;> have impossible := congrArg Prod.snd fault <;> cases impossible

/-- Installation derives the final source-plan lookup from the original field
rule and clause-wide freeze metadata. The emitted threshold is compiled by the
actual one-declaration compiler; no final plan lookup is assumed. Other fields
and their freeze declarations may coexist in the installed clause. -/
theorem installed_threshold_success_or_fault (field : StateInstalledFinite.Field) (queries : List Val) (query : Val)
    (checked : StateFiniteRead.check field queries = true) (member : query ∈ queries) (A B : List Act)
    (growth : ∀ act ∈ A, act ∈ B)
    (reached : StateFiniteRead.test field query (StateInstalledFinite.state field A) = true)
    (declaration : Option String) (sourceName outputName : String)
    (ranked : StateExecutableFreeze.Ranked (StateScopePool.normalize B))
    (clause : StateInstalledClause.Clause StateInstalledLegacy.Value) (plans : Plans StateInstalledLegacy.Value)
    (compiled : StateInstalledClause.compile clause = some plans)
    (original : clause.fields.lookup sourceName = some (.source (StateInstalledFinite.source field)))
    (metadata : clause.freezes.lookup sourceName = declaration.map (freezeSpec field (StateScopePool.normalize B)))
    (definitions : StateInstalledLowering.Definitions StateInstalledLegacy.Value)
    (definition : definitions.lookup sourceName = some (StateFiniteRead.definition field)) :
    ∃ output, StateOutputCompiler.compileOne plans definitions
      (.threshold outputName sourceName (queries.map (fun q => .element (.scalar q)))) = some output ∧
      (output.observe B clause.freezes = (outputName,.data (.reached (.element (.scalar query)))) ∨
        ∃ evidence, output.observe B clause.freezes = (outputName,.fault evidence)) := by
  have lookup : plans.lookup sourceName = some (source field (StateScopePool.normalize B) declaration) := by
    have installed := StateCompiledFieldEquations.source_equation clause plans compiled sourceName
      (StateInstalledFinite.source field) original
    rw [metadata] at installed
    cases declaration <;> simpa only [Option.map_none,Option.map_some,
      StateCompiledFieldEquations.decorate,source,frozenPlan] using installed
  have sameMetadata : clause.freezes.lookup sourceName =
      (freezes field (StateScopePool.normalize B) sourceName declaration).lookup sourceName := by
    rw [metadata]
    cases declaration <;> simp [freezes]
  have scope : StateThresholdDispatch.referenceScope B clause.freezes sourceName =
      StateThresholdDispatch.referenceScope B (freezes field (StateScopePool.normalize B) sourceName declaration) sourceName := by
    simp only [StateThresholdDispatch.referenceScope,sameMetadata]
  obtain ⟨code,compiledQuery,result⟩ := output_success_or_fault field queries query checked member A B growth reached
    declaration sourceName outputName ranked
  let output := StateOutputCompiler.Output.threshold outputName sourceName code (source field (StateScopePool.normalize B) declaration)
  have emitted : StateOutputCompiler.compileOne plans definitions
      (.threshold outputName sourceName (queries.map (fun q => .element (.scalar q)))) = some output := by
    simp [StateOutputCompiler.compileOne,lookup,definition,compiledQuery,output]
  have same : output.observe B clause.freezes =
      output.observe B (freezes field (StateScopePool.normalize B) sourceName declaration) := by
    simp only [output,StateOutputCompiler.Output.observe,scope]
  refine ⟨output,emitted,?_⟩
  rcases result with success | ⟨evidence,fault⟩
  · exact Or.inl (same.trans success)
  · exact Or.inr ⟨evidence,same.trans fault⟩

end CBCL.StateFiniteOutputStability
