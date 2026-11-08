import LeanCbcl.StateAuthoredFiniteStability

/-! Invert successful compiled finite reads. Actual output names identify the
unique emitted threshold; its raw selected-scope success implies native success
over full accepted history because the observed source guards rule out top. -/
namespace CBCL.StateCompiledFiniteInversion
open State StateLift StateLVar StateObservation StateObservationPlan StateInstalledCompiler
open StateInstalledLowering StateOutputCompiler

/-- The name retained by each emitted output instruction. -/
def nameOf {V : Type} : Output V → String
  | .field name _ | .threshold name _ _ _ => name

/-- One-declaration output compilation preserves its exact authored name. -/
theorem compile_one_name {V : Type} (plans : Plans V) (definitions : Definitions V)
    (declaration : Declaration V) (output : Output V) (compiled : compileOne plans definitions declaration = some output) :
    nameOf output = declaration.name := by
  cases declaration with
  | field name definition =>
    cases found : plans.lookup name <;> simp [compileOne,found] at compiled
    next plan => subst output; rfl
  | threshold name source elements =>
    cases found : plans.lookup source with
    | none => simp [compileOne,found] at compiled
    | some plan =>
      cases definition : definitions.lookup source with
      | none => simp [compileOne,found,definition] at compiled
      | some data =>
        cases query : compileQuery elements data with
        | none => simp [compileOne,found,definition,query] at compiled
        | some code =>
          have same : Output.threshold name source code plan = output := by simpa [compileOne,found,definition,query] using compiled
          cases same
          rfl

/-- The complete actual code vector preserves the ordered declaration names. -/
theorem compiled_names {V : Type} (plans : Plans V) (definitions : Definitions V)
    (declarations : List (Declaration V)) (code : List (Output V))
    (compiled : compileDeclarations plans definitions declarations = some code) :
    code.map nameOf = declarations.map Declaration.name := by
  induction declarations generalizing definitions code with
  | nil => simp [compileDeclarations] at compiled; subst code; rfl
  | cons declaration rest ih =>
    cases head : compileOne plans definitions declaration with
    | none => simp [compileDeclarations,head] at compiled
    | some output =>
      cases tail : compileDeclarations plans (extend definitions declaration) rest with
      | none => simp [compileDeclarations,head,tail] at compiled
      | some more =>
        have same : output :: more = code := by simpa [compileDeclarations,head,tail] using compiled
        subst code
        simp only [List.map_cons,compile_one_name plans definitions declaration output head,ih _ more tail]

/-- Observing code retains the same exact output-name vector. -/
theorem observed_names {V : Type} (code : List (Output V)) (whole : List Act) (freezes : List (String × FreezeSpec)) :
    (code.map (Output.observe whole freezes)).map Prod.fst = code.map nameOf := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro output _
  cases output <;> rfl

/-- Successful raw finite query code identifies both an actual declared
alternative and its successful native test, independently of source payload. -/
theorem raw_success (field : StateInstalledFinite.Field) (queries : List Val) (query : Val) (raw : List Act)
    (source : StateReaderValues.Result StateInstalledLegacy.Value)
    (reached : (Query.raw (queries.map (fun q => StateInstalledLegacy.Value.element (.scalar q)))
      (StateFiniteRead.policy field).test (StateInstalledFinite.term field).state).run raw source =
        .data (.reached (.element (.scalar query)))) :
    query ∈ queries ∧ StateFiniteRead.test field query (StateInstalledFinite.state field raw) = true ∧
      ∃ payload, source = .data payload := by
  cases source with
  | fault evidence => simp [Query.run,nativeRawThreshold] at reached
  | data payload =>
    change nativeRawThreshold _ _ (rawHistory raw) (.data payload) = _ at reached
    cases found : (queries.map (fun q => StateInstalledLegacy.Value.element (.scalar q))).find?
        (fun q => (StateFiniteRead.policy field).test q (rawHistory raw)) with
    | none => simp [nativeRawThreshold,found] at reached
    | some selected =>
      have same : selected = StateInstalledLegacy.Value.element (.scalar query) := by
        simpa [nativeRawThreshold,found] using reached
      subst selected
      have hit := List.find?_some found
      have member := List.mem_of_find?_eq_some found
      obtain ⟨value,inside,same⟩ := List.mem_map.mp member
      have equal : value = query := by cases same; rfl
      subst value
      refine ⟨inside,?_,payload,rfl⟩
      simpa only [StateFiniteRead.policy_actual_history] using hit

/-- Every operational raw scope is contained in normalized full history,
including no-freeze, no-root and selected exact-cut branches. -/
theorem scope_inside (whole : List Act) (freezes : List (String × FreezeSpec)) (name : String) :
    ∀ act ∈ StateThresholdDispatch.referenceScope whole freezes name, act ∈ StateScopePool.normalize whole := by
  intro act member
  unfold StateThresholdDispatch.referenceScope at member
  split at member
  · exact member
  · split at member
    · exact member
    · exact (List.mem_filter.mp member).1

/-- A reached emitted finite output implies native success on full accepted
history, even if the query used an earlier freezer cut. Source health and
non-top state are recovered from the actual observation, not assumed. -/
theorem output_native_success (field : StateInstalledFinite.Field) (queries : List Val) (query : Val)
    (whole : List Act) (freezes : List (String × FreezeSpec)) (declaration : Option String) (name outputName : String)
    (reached : (Output.threshold outputName name
      (.raw (queries.map (fun q => StateInstalledLegacy.Value.element (.scalar q)))
        (StateFiniteRead.policy field).test (StateInstalledFinite.term field).state)
      (StateFiniteOutputStability.source field whole declaration)).observe whole freezes =
        (outputName,.data (.reached (.element (.scalar query))))) :
    query ∈ queries ∧ StateFiniteRead.test field query (StateInstalledFinite.state field whole) = true := by
  have planEqual := StateAuthoredFiniteStability.source_setEq field (StateScopePool.normalize_setEq whole) declaration
  rw [← planEqual] at reached
  have result := congrArg Prod.snd reached
  obtain ⟨member,rawReached,payload,sourceData⟩ := raw_success field queries query
    (StateThresholdDispatch.referenceScope whole freezes name)
    (sourceValue whole (StateFiniteOutputStability.source field (StateScopePool.normalize whole) declaration)) result
  have clear : errors (fun act => act ∈ StateScopePool.normalize whole)
      (path (StateFiniteOutputStability.source field (StateScopePool.normalize whole) declaration)) (StateScopePool.normalize whole) = none := by
    cases fault : errors (fun act => act ∈ StateScopePool.normalize whole)
        (path (StateFiniteOutputStability.source field (StateScopePool.normalize whole) declaration)) (StateScopePool.normalize whole) with
    | none => rfl
    | some evidence => simp [sourceValue,observe,fault] at sourceData
  have notTop := StateFiniteOutputStability.non_top field (StateScopePool.normalize whole)
    (StateFiniteOutputStability.source_clear field _ declaration clear)
  have oldReach : StateFiniteRead.reaches field query
      (StateInstalledFinite.state field (StateThresholdDispatch.referenceScope whole freezes name)) = true := by
    have both : (StateInstalledFinite.state field (StateThresholdDispatch.referenceScope whole freezes name) != field.table.table.top) = true ∧ StateFiniteRead.reaches field query
        (StateInstalledFinite.state field (StateThresholdDispatch.referenceScope whole freezes name)) = true := by
      simpa only [StateFiniteRead.test,Bool.and_eq_true] using rawReached
    exact both.2
  have later := StateFiniteRead.reaches_upward field query _ _
    (StateInstalledFinite.state_grows field (scope_inside whole freezes name)) oldReach
  refine ⟨member,?_⟩
  have success : StateFiniteRead.test field query (StateInstalledFinite.state field (StateScopePool.normalize whole)) = true := by
    rw [StateFiniteRead.test_non_top field query _ notTop]
    exact later
  simpa only [StateInstalledFinite.state_setEq field (StateScopePool.normalize_setEq whole)] using success

/-- Equal stored finite definitions have equal native tests over actual
history, even when their existential factory witnesses are represented separately. -/
theorem definition_tests (left right : StateInstalledFinite.Field)
    (same : StateFiniteRead.definition left = StateFiniteRead.definition right) (query : Val) (A : List Act) :
    StateFiniteRead.test left query (StateInstalledFinite.state left A) =
      StateFiniteRead.test right query (StateInstalledFinite.state right A) := by
  let probe := fun (definition : Definition StateInstalledLegacy.Value) => match definition with
    | .factored term (some policy) => policy.test (.element (.scalar query)) (term.state (rawHistory A))
    | _ => false
  have equal := congrArg probe same
  simpa only [probe,StateFiniteRead.definition,StateInstalledFinite.term,id_eq,StateFiniteRead.policy_actual_history] using equal

end CBCL.StateCompiledFiniteInversion
