import LeanCbcl.StateDomainSupportLocality
import LeanCbcl.StateOutputCompiler

/-! Compiled finite queries compose domain-support locality with upward-closed
reads. The actual frozen source supplies domain, top and freeze faults. -/
namespace CBCL.StateFiniteFreezePolicy
open State StateLift StateLVar StateObservation StateObservationPlan StateInstalledCompiler

/-- Actual authored finite-field freeze metadata. -/
def freezeSpec (field : StateInstalledFinite.Field) (whole : List Act) (verb : String) : FreezeSpec :=
  ⟨verb,StateAuthoredBindings.contributes field.domains whole (.verbs [field.verb]),true⟩

/-- The concrete finite source retains all its guards under freezing. -/
noncomputable def frozenPlan (field : StateInstalledFinite.Field) (whole : List Act) (verb : String) :
    Plan StateInstalledLegacy.Value :=
  .freeze (freezeSpec field whole verb) (sourcePlan (StateInstalledFinite.source field))

/-- Healthy cuts preserve the finite carrier independently of its projection. -/
theorem state_cut (field : StateInstalledFinite.Field) (whole : List Act) (verb : String) (root : Act)
    (first : Earliest (fun act => act ∈ whole) verb whole root)
    (healthy : freezeFault (fun act => act ∈ whole) verb
      (freezeSpec field whole verb).contributes true none whole = none) :
    StateInstalledFinite.state field (causalCut (fun act => act ∈ whole) whole root) =
      StateInstalledFinite.state field whole := by
  have selected := StateDomainSupportLocality.selected_cut field.domains [field.verb] whole verb root first healthy
  have same : StateInstalledFinite.selected field (causalCut (fun act => act ∈ whole) whole root) =
      StateInstalledFinite.selected field whole := by
    simpa [StateDomainSupportLocality.selected,StateInstalledFinite.selected] using selected
  simp only [StateInstalledFinite.state,same]

/-- Compiled singleton queries test actual history, not the displayed payload. -/
theorem compiled_singleton (field : StateInstalledFinite.Field) (query : Val)
    (checked : StateFiniteRead.check field [query] = true) :
    ∃ code, StateOutputCompiler.compileQuery [.element (.scalar query)] (StateFiniteRead.definition field) = some code ∧
      ∀ (raw : List Act) (source : Data StateInstalledLegacy.Value),
        code.run raw (.data source) =
          if StateFiniteRead.test field query (StateInstalledFinite.state field raw) then
            .data (.reached (.element (.scalar query))) else .data .pending := by
  refine ⟨.raw [.element (.scalar query)] (StateFiniteRead.policy field).test (StateInstalledFinite.term field).state,?_,?_⟩
  · simp [StateOutputCompiler.compileQuery,StateFiniteRead.definition,StateFiniteRead.policy,StateFiniteRead.decode,checked]
  · intro raw source
    simp only [StateOutputCompiler.Query.run,StateInstalledFinite.term,id_eq,nativeRawThreshold,
      List.find?_cons,StateFiniteRead.policy_actual_history]
    cases StateFiniteRead.test field query (StateInstalledFinite.state field raw) <;> rfl

/-- Full installed finite alternatives compile through the source-owned raw policy. -/
theorem compiled_alternatives (field : StateInstalledFinite.Field) (queries : List Val)
    (checked : StateFiniteRead.check field queries = true) :
    StateOutputCompiler.compileQuery (queries.map (fun q => .element (.scalar q))) (StateFiniteRead.definition field) =
      some (.raw (queries.map (fun q => .element (.scalar q))) (StateFiniteRead.policy field).test
        (StateInstalledFinite.term field).state) := by
  have decoded : (queries.map (fun q => StateInstalledLegacy.Value.element (.scalar q))).mapM StateFiniteRead.decode = some queries := by
    clear checked
    induction queries with
    | nil => rfl
    | cons query rest ih =>
      simp only [List.map_cons,List.mapM_cons,StateFiniteRead.decode,ih]
      rfl
  simp [StateOutputCompiler.compileQuery,StateFiniteRead.definition,StateFiniteRead.policy,decoded,checked]

/-- A unique successful candidate is returned independently of alternative order. -/
theorem find_unique {α : Type} (queries : List α) (test : α → Bool) (query : α)
    (member : query ∈ queries) (reached : test query = true)
    (unique : ∀ other ∈ queries, test other = true → other = query) : queries.find? test = some query := by
  induction queries with
  | nil => simp at member
  | cons head rest ih =>
    cases hit : test head with
    | true =>
      rw [List.find?_cons,hit]
      exact congrArg some (unique head (by simp) hit)
    | false =>
      have tail : query ∈ rest := by
        rcases List.mem_cons.mp member with same | inside
        · subst head; simp [hit] at reached
        · exact inside
      simpa [hit] using ih tail (fun other inside => unique other (by simp [inside]))

/-- An earlier reached answer survives growth and an exact fault-policy freeze,
or the observed concrete source plan reports a terminal fault. -/
theorem compiled_success_or_fault (field : StateInstalledFinite.Field) (queries : List Val) (query : Val)
    (checked : StateFiniteRead.check field queries = true) (member : query ∈ queries) (A B : List Act)
    (growth : ∀ act ∈ A, act ∈ B)
    (reached : StateFiniteRead.test field query (StateInstalledFinite.state field A) = true)
    (verb : String) (root : Act) (first : Earliest (fun act => act ∈ B) verb B root) :
    ∃ code, StateOutputCompiler.compileQuery (queries.map (fun q => .element (.scalar q))) (StateFiniteRead.definition field) = some code ∧
      let output := code.run (causalCut (fun act => act ∈ B) B root)
        (observe (fun act => act ∈ B) (frozenPlan field B verb) B)
      output = .data (.reached (.element (.scalar query))) ∨ ∃ evidence, output = .fault evidence := by
  refine ⟨.raw (queries.map (fun q => .element (.scalar q))) (StateFiniteRead.policy field).test
    (StateInstalledFinite.term field).state,compiled_alternatives field queries checked,?_⟩
  cases fault : errors (fun act => act ∈ B) (path (frozenPlan field B verb)) B with
  | some evidence =>
    right
    refine ⟨evidence,?_⟩
    simp [observe,fault,StateOutputCompiler.Query.run,nativeRawThreshold]
  | none =>
    left
    have combined : freezeFault (fun act => act ∈ B) verb (freezeSpec field B verb).contributes true
        ((StateInstalledFinite.errorSpec field).read B) B = none := by
      have original := fault
      simp only [frozenPlan,StateInstalledFinite.source,StateInstalledTerm.source,
        StateInstalledFinite.term,List.foldr_cons,List.foldr_nil,StateInstalledTerm.Guard.apply,
        sourcePlan,path,errors] at original
      cases sourceError : (StateInstalledFinite.errorSpec field).read B <;>
        simpa only [sourceError,unionError] using original
    have clear := (StateNativeReader.freeze_clear (fun act => act ∈ B) (freezeSpec field B verb) _ B).mp combined
    have healthy : freezeFault (fun act => act ∈ B) verb (freezeSpec field B verb).contributes true none B = none :=
      (StateNativeReader.freeze_clear (fun act => act ∈ B) (freezeSpec field B verb) none B).mpr ⟨rfl,clear.2⟩
    have notTop : StateInstalledFinite.state field B ≠ field.table.table.top := by
      intro top
      have nativeClear := clear.1
      rw [StateInstalledFinite.native_error_refinement] at nativeClear
      simp [StateInstalledFinite.nativeError,StateInstalledFinite.topErrorSpec,top] at nativeClear
      split at nativeClear <;> contradiction
    have oldReach : StateFiniteRead.reaches field query (StateInstalledFinite.state field A) = true := by
      have both : (StateInstalledFinite.state field A != field.table.table.top) = true ∧
          StateFiniteRead.reaches field query (StateInstalledFinite.state field A) = true := by
        simpa only [StateFiniteRead.test,Bool.and_eq_true] using reached
      exact both.2
    have later := StateFiniteRead.reaches_upward field query _ _ (StateInstalledFinite.state_grows field growth) oldReach
    have test : StateFiniteRead.test field query (StateInstalledFinite.state field B) = true := by
      rw [StateFiniteRead.test_non_top field query _ notTop]
      exact later
    rw [show observe (fun act => act ∈ B) (frozenPlan field B verb) B =
      .data (data (fun act => act ∈ B) (frozenPlan field B verb) B) by simp [observe,fault]]
    have pairChecked : StateFiniteRead.pairCheck field queries = true := by
      have check := checked
      simp only [StateFiniteRead.check,Bool.and_eq_true] at check
      exact check.2
    have found : (queries.map (fun q => StateInstalledLegacy.Value.element (.scalar q))).find?
        (fun q => (StateFiniteRead.policy field).test q (rawHistory (causalCut (fun act => act ∈ B) B root))) =
          some (.element (.scalar query)) := by
      apply find_unique
      · exact List.mem_map.mpr ⟨query,member,rfl⟩
      · rw [StateFiniteRead.policy_actual_history,state_cut field B verb root first healthy]
        exact test
      · intro other otherMember hit
        obtain ⟨value,inside,rfl⟩ := List.mem_map.mp otherMember
        by_cases same : value = query
        · rw [same]
        · rw [StateFiniteRead.policy_actual_history,state_cut field B verb root first healthy] at hit
          have hitReach : StateFiniteRead.reaches field value (StateInstalledFinite.state field B) = true := by
            rw [StateFiniteRead.test_non_top field value _ notTop] at hit
            exact hit
          have rejected := (StateFiniteRead.pairCheck_iff field queries).mp pairChecked query member value inside
            (Ne.symm same) (StateInstalledFinite.state field B) notTop later
          simp [hitReach] at rejected
    simp only [StateOutputCompiler.Query.run,StateInstalledFinite.term,id_eq,nativeRawThreshold,found]

/-- The same stability result at the public compiled-output adapter, with its
actual normalization and unique-root selector. This connects the finite proof
to emitted query code rather than an independent threshold evaluator. -/
theorem output_success_or_fault (field : StateInstalledFinite.Field) (queries : List Val) (query : Val)
    (checked : StateFiniteRead.check field queries = true) (member : query ∈ queries) (A B : List Act)
    (growth : ∀ act ∈ A, act ∈ B)
    (reached : StateFiniteRead.test field query (StateInstalledFinite.state field A) = true)
    (verb sourceName outputName : String) (root : Act)
    (ranked : StateExecutableFreeze.Ranked (StateScopePool.normalize B))
    (selected : StateScopePool.uniqueRoot (StateScopePool.normalize B) verb = some root) :
    ∃ code, StateOutputCompiler.compileQuery (queries.map (fun q => .element (.scalar q))) (StateFiniteRead.definition field) = some code ∧
      let output := (StateOutputCompiler.Output.threshold outputName sourceName code
        (frozenPlan field (StateScopePool.normalize B) verb)).observe B
          [(sourceName,freezeSpec field (StateScopePool.normalize B) verb)]
      output = (outputName,.data (.reached (.element (.scalar query)))) ∨
        ∃ evidence, output = (outputName,.fault evidence) := by
  have inside : ∀ act ∈ A, act ∈ StateScopePool.normalize B := fun act present =>
    (StateScopePool.normalize_setEq B act).mpr (growth act present)
  have first := StateScopePool.uniqueRoot_earliest (StateScopePool.normalize B) ranked verb root selected
  obtain ⟨code,compiled,result⟩ := compiled_success_or_fault field queries query checked member A
    (StateScopePool.normalize B) inside reached verb root first
  refine ⟨code,compiled,?_⟩
  have scope : StateThresholdDispatch.referenceScope B
      [(sourceName,freezeSpec field (StateScopePool.normalize B) verb)] sourceName =
        causalCut (fun act => act ∈ StateScopePool.normalize B) (StateScopePool.normalize B) root := by
    simp [StateThresholdDispatch.referenceScope,List.lookup,freezeSpec,selected]
  simp only [StateOutputCompiler.Output.observe,StateOutputCompiler.sourceValue,scope]
  rcases result with success | ⟨evidence,fault⟩
  · exact Or.inl (congrArg (outputName, ·) success)
  · exact Or.inr ⟨evidence,congrArg (outputName, ·) fault⟩

end CBCL.StateFiniteFreezePolicy
