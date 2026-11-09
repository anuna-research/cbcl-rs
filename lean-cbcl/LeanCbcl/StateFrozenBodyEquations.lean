import LeanCbcl.StateScopeProperties

/-! Successful own-freeze body equations. The logical selected-cut adapter is
first matched to the constructed pool's cut, active flag and wrapper, then the
same-field historical request is reduced using its completed compiled plan. -/
set_option autoImplicit false
namespace CBCL.StateFrozenBodyEquations
open State StateLift StateLVar StateObservation StateObservationPlan StateRuleRefinement StateInstalledCompiler
open StateCompiledFieldEquations StateReaderValues StateReaderReachability StateScopeProperties StateScopePool

/-- A selected clear freeze presents exactly its source observation at the
historical cut when active, or the current source when the root is absent. -/
theorem freeze_selected_equation {V : Type} (world : Act → Prop) (whole scope : List Act)
    (spec : FreezeSpec) (source : Plan V) (root : Act)
    (wholeClosed : CausallyClosed world whole) (scopeClosed : CausallyClosed world scope)
    (inside : ∀ act ∈ scope, act ∈ whole)
    (rawClear : StateNativeReader.error world whole source scope = none)
    (ownClear : freezeFault world spec.verb spec.contributes spec.policy none whole = none)
    (selected : (by classical exact whole.find? (fun root => decide (Earliest world spec.verb whole root))) = some root) :
    scopedObserve world whole (.freeze spec source) scope =
      (by
        classical
        exact if root ∈ scope then
          (frozen root.addr (FinSet.mk (scope.filter (fun act => decide (spec.contributes act ∧ ¬Ancestor world act root))))
            (scopedObserve world whole source (causalCut world whole root)))
        else scopedObserve world whole source scope) := by
  classical
  have noConflict : ¬∃ a b, FreezeConflict world spec.verb spec.contributes spec.policy whole a b := by
    rintro ⟨a,b,bad⟩
    exact ((StateNativeReader.freeze_clear world spec none whole).mp ownClear).2 a b bad
  simp only [scopedObserve,StateNativeReader.error,rawClear,ownClear,unionError,StateNativeReader.value,
    StateFreezeScopes.cachedFreeze,if_neg noConflict,selected]
  by_cases present : root ∈ scope
  · have historicalClear := cut_clear world whole scope source wholeClosed scopeClosed inside root present rawClear
    simp only [if_pos present]
    exact (frozen_data_refinement world whole _ source root.addr _ historicalClear).symm
  · simp only [if_neg present,frozenData]

/-- With no selected freezer, a clear freeze has the exact current source
observation and does not manufacture historical metadata. -/
theorem freeze_absent_equation {V : Type} (world : Act → Prop) (whole scope : List Act)
    (spec : FreezeSpec) (source : Plan V)
    (rawClear : StateNativeReader.error world whole source scope = none)
    (ownClear : freezeFault world spec.verb spec.contributes spec.policy none whole = none)
    (absent : (by classical exact whole.find? (fun root => decide (Earliest world spec.verb whole root))) = none) :
    scopedObserve world whole (.freeze spec source) scope = scopedObserve world whole source scope := by
  classical
  have noConflict : ¬∃ a b, FreezeConflict world spec.verb spec.contributes spec.policy whole a b := by
    rintro ⟨a,b,bad⟩
    exact ((StateNativeReader.freeze_clear world spec none whole).mp ownClear).2 a b bad
  simp only [scopedObserve,StateNativeReader.error,rawClear,ownClear,unionError,StateNativeReader.value,
    StateFreezeScopes.cachedFreeze,if_neg noConflict,absent,frozenData]

/-- Clear own-freeze finishing evaluates the same completed historical field
as the compiled plan, stripping its inner wrapper and applying the outer scope's
exact metadata. This includes same-scope cut hits and incomparable dependencies. -/
theorem finish_clear_refinement {V : Type} (entries : List StateAuthoredBindings.Entry) (whole : List Act)
    (fields : List (String × Rule V)) (freezes : List (String × FreezeSpec)) (plans : Plans V)
    (ranked : StateExecutableFreeze.Ranked whole)
    (consistent : ∀ a ∈ whole, ∀ b ∈ whole, a.addr = b.addr → a = b)
    (unique : (freezes.map Prod.fst).Nodup) (key : StateMemoizedReader.Key)
    (admitted : Admitted entries whole freezes key) (spec : FreezeSpec) (declared : freezes.lookup key.2 = some spec)
    (source : Plan V) (lookup : plans.lookup key.2 = some (.freeze spec source))
    (clear : StateNativeReader.error (fun act => act ∈ normalize whole) (normalize whole)
      (.freeze spec source) (scope whole freezes key) = none) :
    let ops := StateReaderValues.operations entries whole fields freezes
    (ops.finish key (scopedObserve (fun act => act ∈ normalize whole) (normalize whole) source (scope whole freezes key))).meaning
      (StateCompiledFieldEquations.meaning whole freezes plans) =
      scopedObserve (fun act => act ∈ normalize whole) (normalize whole) (.freeze spec source) (scope whole freezes key) := by
  classical
  let canonical := normalize whole
  let world := fun act => act ∈ canonical
  let current := scope whole freezes key
  let ops := StateReaderValues.operations entries whole fields freezes
  let normal := scopedObserve world canonical source current
  let target := StateCompiledFieldEquations.meaning whole freezes plans
  change (ops.finish key normal).meaning target = scopedObserve world canonical (.freeze spec source) current
  have parts : StateNativeReader.error world canonical source current = none ∧
      freezeFault world spec.verb spec.contributes spec.policy none canonical = none :=
    (StateNativeReader.union_clear _ _).mp clear
  have noConflict : ∀ a b, ¬FreezeConflict world spec.verb spec.contributes spec.policy canonical a b :=
    ((StateNativeReader.freeze_clear world spec none canonical).mp parts.2).2
  have fullClosed : CausallyClosed world canonical := by intro child member parent valid edge; exact valid
  have properties := admitted_properties entries whole freezes ranked consistent key admitted
  have combined := freeze_error_refinement world canonical current spec source
  rw [clear] at combined
  have noFault : ops.fault key normal = none := by
    simpa only [ops,normal,StateReaderValues.operations,ownFault,declared] using combined
  have rootSelection := root_find canonical (normalize_ranked whole ranked) (normalize_unique whole consistent) spec noConflict
  cases selected : uniqueRoot canonical spec.verb with
  | none =>
    have absent : canonical.find? (fun root => decide (Earliest world spec.verb canonical root)) = none := by
      rw [← rootSelection,selected]
    obtain ⟨_,inactive,_⟩ := absent_root_metadata entries whole fields freezes unique key spec declared selected
    have expected := freeze_absent_equation world canonical current spec source parts.1 parts.2 absent
    rw [expected]
    change (ops.finish key normal).meaning target = normal
    change ops.active key = false at inactive
    rw [StateMemoizedReader.Operations.finish,noFault,inactive]
    rfl
  | some root =>
    have selection : canonical.find? (fun root => decide (Earliest world spec.verb canonical root)) = some root := by
      rw [← rootSelection,selected]
    obtain ⟨index,cutIndex,cutScope,activeRoot,wrapper⟩ := selected_root_metadata entries whole fields freezes
      ranked consistent unique key admitted spec declared root selected
    change ops.cut key.2 = some index at cutIndex
    change (ops.active key = true ↔ root ∈ current) at activeRoot
    change (∀ value, ops.frozen key value = frozen root.addr (exclusions whole freezes key spec root) value) at wrapper
    have accepted := (uniqueRoot_accepted canonical spec.verb root selected).1
    have rootCut : root ∈ causalCut world canonical root := freezer_in_cut accepted accepted
    have expected := freeze_selected_equation world canonical current spec source root fullClosed properties.1 properties.2.1
      parts.1 parts.2 selection
    by_cases present : root ∈ current
    · have activeNow : ops.active key = true := activeRoot.mpr present
      have historicalClear := cut_clear world canonical current source fullClosed properties.1 properties.2.1 root present parts.1
      have inner : target (index,key.2) = frozen root.addr (exclusions whole freezes (index,key.2) spec root)
          (scopedObserve world canonical source (causalCut world canonical root)) := by
        simp only [target,StateCompiledFieldEquations.meaning,lookup]
        rw [cutScope]
        have historicalClosed := StateFreezeScopes.causal_cut_closed fullClosed root
        have inside : ∀ act ∈ causalCut world canonical root, act ∈ canonical := fun _ member => (List.mem_filter.mp member).1
        rw [freeze_selected_equation world canonical _ spec source root fullClosed historicalClosed inside historicalClear parts.2 selection]
        simp only [if_pos rootCut,exclusions,cutScope]
        rfl
      rw [expected,if_pos present]
      change (ops.finish key normal).meaning target = frozen root.addr (exclusions whole freezes key spec root)
        (scopedObserve world canonical source (causalCut world canonical root))
      rw [StateMemoizedReader.Operations.finish,noFault,activeNow,cutIndex,if_pos (rfl : true = true)]
      change StateMemoizedReader.Body.meaning target
        (if key.1 = index then .done (ops.frozen key normal)
         else .request (index,key.2) (fun value => .done (ops.frozen key (ops.unfrozen value)))) = _
      by_cases same : key.1 = index
      · rw [if_pos same]
        have sameScope : current = causalCut world canonical root := by
          change scope whole freezes key = _
          have equal : scope whole freezes key = scope whole freezes (index,key.2) := by
            simp only [StateReaderValues.scope,same]
          exact equal.trans cutScope
        change ops.frozen key normal = _
        simp only [wrapper,normal,sameScope]
      · rw [if_neg same]
        change ops.frozen key (ops.unfrozen (target (index,key.2))) = _
        rw [wrapper,inner]
        change frozen root.addr (exclusions whole freezes key spec root) (unfrozen _) = _
        rw [frozen_unfrozen,frozen_nested]
    · have inactive : ops.active key = false := by
        cases flag : ops.active key with
        | false => rfl
        | true => exact False.elim (present (activeRoot.mp flag))
      rw [expected,if_neg present]
      change (ops.finish key normal).meaning target = normal
      rw [StateMemoizedReader.Operations.finish,noFault,inactive]
      rfl

/-- Every admitted concrete field body agrees with its completed compiled
observation, including clear historical values and every terminal fault. -/
theorem prepared_body_equation (environment : StateAuthoredBindings.Environment) (entries : List StateAuthoredBindings.Entry)
    (whole : List Act) (clause : StateInstalledLowering.Clause StateInstalledLegacy.Value)
    (prepared : StateAuthoredBindings.prepare environment entries whole = some clause)
    (fields : List (String × Rule StateInstalledLegacy.Value))
    (resolved : StateInstalledLowering.resolve [] clause.declarations = some fields) (plans : Plans StateInstalledLegacy.Value)
    (compiled : StateInstalledClause.compile ⟨fields,clause.freezes⟩ = some plans)
    (ranked : StateExecutableFreeze.Ranked whole)
    (consistent : ∀ a ∈ whole, ∀ b ∈ whole, a.addr = b.addr → a = b)
    (key : StateMemoizedReader.Key) (admitted : Admitted entries whole clause.freezes key) :
    ((StateReaderValues.operations entries whole fields clause.freezes).body key).meaning
      (StateCompiledFieldEquations.meaning whole clause.freezes plans) = StateCompiledFieldEquations.meaning whole clause.freezes plans key := by
  cases selected : clause.freezes.lookup key.2 with
  | none => exact prepared_unfrozen_body environment entries whole clause prepared fields resolved plans compiled key admitted selected
  | some spec =>
    obtain ⟨rule,bare,found,bareCompiled,lookup,normal⟩ := prepared_body_normal environment entries whole clause
      prepared fields resolved plans compiled key admitted
    have fullLookup : plans.lookup key.2 = some (.freeze spec bare) := by simpa [decorate,selected] using lookup
    have target : StateCompiledFieldEquations.meaning whole clause.freezes plans key =
        scopedObserve (fun act => act ∈ normalize whole) (normalize whole) (.freeze spec bare)
          (scope whole clause.freezes key) := by simp only [StateCompiledFieldEquations.meaning,fullLookup]
    cases error : StateNativeReader.error (fun act => act ∈ normalize whole) (normalize whole)
        (.freeze spec bare) (scope whole clause.freezes key) with
    | some evidence =>
      have faulted : StateCompiledFieldEquations.meaning whole clause.freezes plans key = .fault evidence := by
        rw [target]
        simp only [scopedObserve,error]
      exact prepared_fault_body environment entries whole clause prepared fields resolved plans compiled key admitted evidence faulted
    | none =>
      rw [normal]
      exact (finish_clear_refinement entries whole fields clause.freezes plans ranked consistent
        (compiled_freezes_unique ⟨fields,clause.freezes⟩ plans compiled) key admitted spec selected bare fullLookup error).trans target.symm

/-- Successful preparation constructs the recursive cache-reference/compiled
meaning equation over the entire admitted field domain; no no-freeze restriction
or independently assumed body equation remains. -/
theorem prepared_reference_equivalence (environment : StateAuthoredBindings.Environment) (entries : List StateAuthoredBindings.Entry)
    (whole : List Act) (clause : StateInstalledLowering.Clause StateInstalledLegacy.Value)
    (prepared : StateAuthoredBindings.prepare environment entries whole = some clause)
    (fields : List (String × Rule StateInstalledLegacy.Value))
    (resolved : StateInstalledLowering.resolve [] clause.declarations = some fields) (plans : Plans StateInstalledLegacy.Value)
    (compiled : StateInstalledClause.compile ⟨fields,clause.freezes⟩ = some plans)
    (ranked : StateExecutableFreeze.Ranked whole)
    (consistent : ∀ a ∈ whole, ∀ b ∈ whole, a.addr = b.addr → a = b) :
    let ops := StateReaderValues.operations entries whole fields clause.freezes
    let rank := StateMemoizedReader.requestRank (fields.map Prod.fst).idxOf ops.cut
    ∃ requestRanked : ∀ key, (ops.body key).Below rank (rank key),
      ∀ key, Admitted entries whole clause.freezes key →
        StateMemoizedReader.reference ops.body rank requestRanked key = StateCompiledFieldEquations.meaning whole clause.freezes plans key := by
  let ops := StateReaderValues.operations entries whole fields clause.freezes
  have extracted : ∀ name source, ops.dependency name = some source →
      ∃ rule, (name,rule) ∈ fields ∧ source ∈ references rule :=
    StateAuthoredDependencies.extracted_reference environment entries whole clause prepared fields resolved
  have ordering := StateReaderIndices.compiled_dependency_ordering ⟨fields,clause.freezes⟩ plans compiled ops extracted
  let requestRanked := StateMemoizedReader.body_ranked ops (fields.map Prod.fst).idxOf ordering
  exact ⟨requestRanked,reference_on_domain (Admitted entries whole clause.freezes) ops.body _ requestRanked
    (fun key admitted => body_within environment entries whole clause prepared fields ranked consistent key admitted)
    (StateCompiledFieldEquations.meaning whole clause.freezes plans)
    (fun key admitted => prepared_body_equation environment entries whole clause prepared fields resolved plans compiled ranked consistent key admitted)⟩

/-- The actual native field-request transcript and every final cache lookup
agree with completed compiled meanings for all prepared freeze policies and
fault cases, under the explicit ranked/consistent accepted-history boundary. -/
theorem prepared_cache_equivalence (environment : StateAuthoredBindings.Environment) (entries : List StateAuthoredBindings.Entry)
    (whole : List Act) (clause : StateInstalledLowering.Clause StateInstalledLegacy.Value)
    (prepared : StateAuthoredBindings.prepare environment entries whole = some clause)
    (ranked : StateExecutableFreeze.Ranked whole)
    (consistent : ∀ a ∈ whole, ∀ b ∈ whole, a.addr = b.addr → a = b) :
    ∃ plans fields, StateAuthoredBindings.compile environment entries whole = some plans ∧
      StateInstalledLowering.resolve [] clause.declarations = some fields ∧
      let ops := StateReaderValues.operations entries whole fields clause.freezes
      let rank := StateMemoizedReader.requestRank (fields.map Prod.fst).idxOf ops.cut
      ∃ after, StateMemoizedReader.reads ops.body rank (initialKeys entries) [] =
        some ((initialKeys entries).map (StateCompiledFieldEquations.meaning whole clause.freezes plans),after) ∧
        StateMemoizedReader.Valid (StateCompiledFieldEquations.meaning whole clause.freezes plans) after ∧
        CacheWithin (Admitted entries whole clause.freezes) after := by
  obtain ⟨plans,fields,compiled,resolved,sound,requestRanked,after,ran,valid,provenance,_⟩ :=
    prepared_reachable_cache environment entries whole clause prepared ranked consistent
  have lowered : StateInstalledLowering.compile clause = some plans := by
    simpa [StateAuthoredBindings.compile,prepared] using compiled
  obtain ⟨actualFields,actualResolved,fieldCompiled⟩ := StateAuthoredDependencies.lowered_compiled_clause clause plans lowered
  have same : actualFields = fields := Option.some.inj (actualResolved.symm.trans resolved)
  subst actualFields
  obtain ⟨_,equalMeaning⟩ := prepared_reference_equivalence environment entries whole clause prepared fields resolved plans fieldCompiled ranked consistent
  have initial := initial_keys_admitted environment entries whole clause prepared ranked consistent
  have mapped : (initialKeys entries).map
      (StateMemoizedReader.reference (StateReaderValues.operations entries whole fields clause.freezes).body _ requestRanked) =
      (initialKeys entries).map (StateCompiledFieldEquations.meaning whole clause.freezes plans) := by
    apply List.map_congr_left
    intro key member
    exact equalMeaning key (initial key member)
  rw [mapped] at ran
  refine ⟨plans,fields,compiled,resolved,after,ran,?_,provenance⟩
  intro key value found
  have correct := valid key value found
  obtain ⟨before,later,equal,_⟩ := List.lookup_eq_some_iff.mp found
  have admitted := provenance key value (by simp [equal])
  exact correct.trans (equalMeaning key admitted)

/-- Top-level native source requests read complete compiled plan observations
at normalized full history, not merely an unconnected scoped helper. -/
theorem initial_meaning {V : Type} (whole : List Act) (freezes : List (String × FreezeSpec)) (plans : Plans V)
    (ranked : StateExecutableFreeze.Ranked whole)
    (consistent : ∀ a ∈ whole, ∀ b ∈ whole, a.addr = b.addr → a = b) (name : String) :
    StateCompiledFieldEquations.meaning whole freezes plans (0,name) =
      match plans.lookup name with
      | none => .data .pending
      | some plan => StateObservationPlan.observe (fun act => act ∈ normalize whole) plan (normalize whole) := by
  have fullScope : scope whole freezes (0,name) = normalize whole := by
    have present := (normalized_scopes_sound whole ranked consistent freezes).1.1
    simp only [scope,present,Option.getD_some]
  cases found : plans.lookup name with
  | none => simp [StateCompiledFieldEquations.meaning,found]
  | some plan =>
    simp only [StateCompiledFieldEquations.meaning,found,fullScope]
    exact StateNativeReader.native_reader_refinement (fun act => act ∈ normalize whole) plan (normalize whole)
      (fun _ _ _ valid _ => valid) (normalize_unique whole consistent)

end CBCL.StateFrozenBodyEquations


