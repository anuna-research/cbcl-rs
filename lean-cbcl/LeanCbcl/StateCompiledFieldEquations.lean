import LeanCbcl.StateReaderReachability

/-! Exact global lookup equations for the installed field compiler. A compiled
field retains its original source/derived rule and clause-wide freeze metadata;
references can be resolved against the completed dictionary without changing
which earlier compiled plan they denote. -/
set_option autoImplicit false
namespace CBCL.StateCompiledFieldEquations
open State StateLift StateObservation StateObservationPlan StateInstalledCompiler
open StateInstalledClause StateReaderReachability

/-- Freeze decoration preserves the already compiled source plan. -/
def decorate {V : Type} (freeze : Option FreezeSpec) (source : Plan V) : Plan V :=
  match freeze with | none => source | some spec => .freeze spec source

/-- Successful field compilation exposes its exact underlying rule plan. -/
theorem compile_field_equation {V : Type} (earlier : Plans V) (field : Field V) (plan : Plan V)
    (compiled : compileField earlier field = some plan) :
    ∃ source, compileRule earlier field.rule = some source ∧ plan = decorate field.freeze source := by
  cases found : compileRule earlier field.rule with
  | none => simp [compileField,found] at compiled
  | some source =>
    have same : decorate field.freeze source = plan := by simpa [compileField,found,decorate] using compiled
    exact ⟨source,rfl,same.symm⟩

/-- Only referenced lookups matter to rule compilation. -/
theorem compile_rule_congr {V : Type} (earlier final : Plans V) (rule : StateInstalledCompiler.Rule V)
    (same : ∀ name ∈ references rule, earlier.lookup name = final.lookup name) :
    compileRule earlier rule = compileRule final rule := by
  cases rule with
  | source _ => rfl
  | earlier name | derived _ name | threshold _ _ name | thresholdRaw _ _ _ name | thresholdLift _ _ name | freeze _ name =>
    simp only [compileRule,same name (by simp [references])]
  | pair combine left right =>
    simp only [compileRule,same left (by simp [references]),same right (by simp [references])]

/-- Rule compilation that succeeded against an earlier dictionary denotes
exactly the same plan in a unique completed dictionary containing that prefix. -/
theorem compile_rule_completed {V : Type} (earlier final : Plans V) (rule : StateInstalledCompiler.Rule V) (source : Plan V)
    (compiled : compileRule earlier rule = some source) (unique : (final.map Prod.fst).Nodup)
    (included : ∀ binding ∈ earlier, binding ∈ final) : compileRule final rule = some source := by
  have same : ∀ name ∈ references rule, earlier.lookup name = final.lookup name := by
    intro name used
    have present := StateInstalledRecognition.compile_rule_sound earlier rule source compiled name used
    have found := (lookup_present earlier name).mpr present
    cases selected : earlier.lookup name with
    | none => simp [selected] at found
    | some plan =>
      obtain ⟨before,after,equal,_⟩ := List.lookup_eq_some_iff.mp selected
      have member : (name,plan) ∈ earlier := by simp [equal]
      exact (lookup_original final unique name plan (included _ member)).symm
  rw [← compile_rule_congr earlier final rule same]
  exact compiled

/-- Ordered field compilation preserves the exact installed namespace. -/
theorem compile_fields_names {V : Type} (earlier : Plans V) (fields : List (String × Field V)) (plans : Plans V)
    (compiled : StateInstalledClause.compileFields earlier fields = some plans) : plans.map Prod.fst = fields.map Prod.fst := by
  induction fields generalizing earlier plans with
  | nil => simp [StateInstalledClause.compileFields] at compiled; subst plans; rfl
  | cons binding rest ih =>
    obtain ⟨name,field⟩ := binding
    cases head : compileField earlier field with
    | none => simp [StateInstalledClause.compileFields,head] at compiled
    | some plan =>
      cases tail : StateInstalledClause.compileFields ((name,plan)::earlier) rest with
      | none => simp [StateInstalledClause.compileFields,head,tail] at compiled
      | some more =>
        simp [StateInstalledClause.compileFields,head,tail] at compiled
        subst plans
        simp only [List.map_cons,ih _ more tail]

/-- Every emitted field has its exact source-rule equation in the completed
unique dictionary, including freezes attached before compiling dependencies. -/
theorem fields_equations {V : Type} (earlier : Plans V) (fields : List (String × Field V)) (plans final : Plans V)
    (compiled : StateInstalledClause.compileFields earlier fields = some plans) (unique : (final.map Prod.fst).Nodup)
    (old : ∀ binding ∈ earlier, binding ∈ final) (new : ∀ binding ∈ plans, binding ∈ final) :
    ∀ name field, (name,field) ∈ fields → ∃ source plan,
      compileRule final field.rule = some source ∧ plan = decorate field.freeze source ∧ final.lookup name = some plan := by
  induction fields generalizing earlier plans with
  | nil => intro name field impossible; simp at impossible
  | cons binding rest ih =>
    obtain ⟨headName,headField⟩ := binding
    cases head : compileField earlier headField with
    | none => simp [StateInstalledClause.compileFields,head] at compiled
    | some headPlan =>
      cases tail : StateInstalledClause.compileFields ((headName,headPlan)::earlier) rest with
      | none => simp [StateInstalledClause.compileFields,head,tail] at compiled
      | some more =>
        simp [StateInstalledClause.compileFields,head,tail] at compiled
        subst plans
        intro name field member
        rcases List.mem_cons.mp member with same | inside
        · cases same
          obtain ⟨source,bare,equal⟩ := compile_field_equation earlier headField headPlan head
          exact ⟨source,headPlan,compile_rule_completed earlier final headField.rule source bare unique old,equal,
            lookup_original final unique headName headPlan (new _ (by simp))⟩
        · apply ih ((headName,headPlan)::earlier) more tail ?_ ?_ name field inside
          · intro binding present
            rcases List.mem_cons.mp present with rfl | prior
            · exact new _ (by simp)
            · exact old _ prior
          · intro binding present; exact new _ (List.mem_cons_of_mem _ present)

/-- Successful whole-clause installation yields an exact final lookup equation
for every original rule and its attached freeze declaration. -/
theorem installed_equation {V : Type} (clause : StateInstalledClause.Clause V) (plans : Plans V)
    (compiled : StateInstalledClause.compile clause = some plans) (name : String) (rule : StateInstalledCompiler.Rule V)
    (found : clause.fields.lookup name = some rule) :
    ∃ source, compileRule plans rule = some source ∧
      plans.lookup name = some (decorate (clause.freezes.lookup name) source) := by
  unfold StateInstalledClause.compile at compiled
  split at compiled
  · rename_i metadata
    have names := compile_fields_names [] (attach clause.freezes clause.fields) plans compiled
    have unique : (plans.map Prod.fst).Nodup := by simpa [names,attach,List.map_map,Function.comp_def] using metadata.1
    obtain ⟨before,after,equal,_⟩ := List.lookup_eq_some_iff.mp found
    have member : (name,rule) ∈ clause.fields := by simp [equal]
    have attached : (name,⟨rule,clause.freezes.lookup name⟩) ∈ attach clause.freezes clause.fields :=
      List.mem_map.mpr ⟨(name,rule),member,rfl⟩
    obtain ⟨source,plan,bare,same,lookup⟩ := fields_equations [] (attach clause.freezes clause.fields) plans plans
      compiled unique (fun _ impossible => by simp at impossible) (fun _ member => member) name _ attached
    exact ⟨source,bare,by simpa [same] using lookup⟩
  · contradiction

/-- Primitive source lookup retains exactly its attached freeze decoration. -/
theorem source_equation {V : Type} (clause : StateInstalledClause.Clause V) (plans : Plans V)
    (compiled : StateInstalledClause.compile clause = some plans) (name : String) (source : Source V)
    (found : clause.fields.lookup name = some (.source source)) :
    plans.lookup name = some (decorate (clause.freezes.lookup name) (sourcePlan source)) := by
  obtain ⟨bare,rule,lookup⟩ := installed_equation clause plans compiled name (.source source) found
  simp only [compileRule,Option.some.injEq] at rule
  subst bare
  exact lookup

/-- A derived field consumes the completed compiled plan of its original
source, including any freeze attached before dependency compilation. -/
theorem derived_equation {V : Type} (clause : StateInstalledClause.Clause V) (plans : Plans V)
    (compiled : StateInstalledClause.compile clause = some plans) (name source : String) (post : V → V)
    (found : clause.fields.lookup name = some (.derived post source)) :
    ∃ prior, plans.lookup source = some prior ∧
      plans.lookup name = some (decorate (clause.freezes.lookup name) (.map post prior)) := by
  obtain ⟨bare,rule,lookup⟩ := installed_equation clause plans compiled name (.derived post source) found
  cases selected : plans.lookup source with
  | none => simp [compileRule,selected] at rule
  | some prior =>
    have same : .map post prior = bare := by simpa [compileRule,selected] using rule
    exact ⟨prior,rfl,by simpa [← same] using lookup⟩

/-- Successful preparation establishes uniqueness in the actual resolved rule
list, rather than assuming lookup agrees with a detached source inventory. -/
theorem prepared_unique (environment : StateAuthoredBindings.Environment) (entries : List StateAuthoredBindings.Entry)
    (whole : List Act) (clause : StateInstalledLowering.Clause StateInstalledLegacy.Value)
    (prepared : StateAuthoredBindings.prepare environment entries whole = some clause)
    (fields : List (String × StateInstalledCompiler.Rule StateInstalledLegacy.Value))
    (resolved : StateInstalledLowering.resolve [] clause.declarations = some fields) : (fields.map Prod.fst).Nodup := by
  obtain ⟨plans,compiled⟩ := StateAuthoredBindings.prepared_compiler_complete environment entries whole clause prepared
  have lowered : StateInstalledLowering.compile clause = some plans := by simpa [StateAuthoredBindings.compile,prepared] using compiled
  rw [StateAuthoredDependencies.resolve_names [] clause.declarations fields resolved]
  exact (StateInstalledRecognition.compile_sound clause plans lowered).1.1

/-- The operational dependency option equals the complete resolved rule
inventory, including the no-dependency case for primitive fields. -/
theorem dependency_equation (environment : StateAuthoredBindings.Environment) (entries : List StateAuthoredBindings.Entry)
    (whole : List Act) (clause : StateInstalledLowering.Clause StateInstalledLegacy.Value)
    (prepared : StateAuthoredBindings.prepare environment entries whole = some clause)
    (fields : List (String × StateInstalledCompiler.Rule StateInstalledLegacy.Value))
    (resolved : StateInstalledLowering.resolve [] clause.declarations = some fields) (name : String)
    (known : name ∈ (StateAuthoredBindings.rawFields entries).map Prod.fst)
    (rule : StateInstalledCompiler.Rule StateInstalledLegacy.Value) (found : fields.lookup name = some rule) :
    references rule = (StateAuthoredDependencies.lookupDependency entries name).toList := by
  cases rawFound : (StateAuthoredBindings.rawFields entries).lookup name with
  | none =>
    obtain ⟨⟨rawName,raw⟩,member,same⟩ := List.mem_map.mp known
    have different := List.lookup_eq_none_iff.mp rawFound (rawName,raw) member
    dsimp only at same different
    simp [same] at different
  | some raw =>
    obtain ⟨before,after,equal,_⟩ := List.lookup_eq_some_iff.mp rawFound
    have member : (name,raw) ∈ StateAuthoredBindings.rawFields entries := by simp [equal]
    obtain ⟨definition,declared,inventory⟩ := StateAuthoredDependencies.prepared_dependencies
      environment entries whole clause prepared name raw member
    have original := StateAuthoredDependencies.resolve_field [] clause.declarations fields resolved name definition declared
    have lookup := lookup_original fields (prepared_unique environment entries whole clause prepared fields resolved)
      name (StateInstalledLowering.lowerDefinition definition) original
    have same : rule = StateInstalledLowering.lowerDefinition definition := Option.some.inj (found.symm.trans lookup)
    rw [same,inventory]
    simp [StateAuthoredDependencies.lookupDependency,rawFound]

/-- Read the concrete completed plan at the actual allocated native scope. -/
noncomputable def meaning {V : Type} (whole : List Act) (freezes : List (String × FreezeSpec)) (plans : Plans V)
    (key : StateMemoizedReader.Key) : StateReaderValues.Result V :=
  match plans.lookup key.2 with
  | none => .data .pending
  | some plan => StateReaderValues.scopedObserve (fun act => act ∈ StateScopePool.normalize whole)
      (StateScopePool.normalize whole) plan (StateReaderValues.scope whole freezes key)

/-- Successful prepared compilation gives the exact bare-plan equation for the
normal portion of every admitted memoized field body. The remaining operation
is its own attached freeze finishing step, not a supplied normal-value callback. -/
theorem prepared_body_normal (environment : StateAuthoredBindings.Environment) (entries : List StateAuthoredBindings.Entry)
    (whole : List Act) (clause : StateInstalledLowering.Clause StateInstalledLegacy.Value)
    (prepared : StateAuthoredBindings.prepare environment entries whole = some clause)
    (fields : List (String × StateInstalledCompiler.Rule StateInstalledLegacy.Value))
    (resolved : StateInstalledLowering.resolve [] clause.declarations = some fields) (plans : Plans StateInstalledLegacy.Value)
    (compiled : StateInstalledClause.compile ⟨fields,clause.freezes⟩ = some plans)
    (key : StateMemoizedReader.Key) (admitted : Admitted entries whole clause.freezes key) :
    let ops := StateReaderValues.operations entries whole fields clause.freezes
    let target := meaning whole clause.freezes plans
    ∃ rule bare, fields.lookup key.2 = some rule ∧ compileRule plans rule = some bare ∧
      plans.lookup key.2 = some (decorate (clause.freezes.lookup key.2) bare) ∧
      (ops.body key).meaning target =
        (ops.finish key (StateReaderValues.scopedObserve (fun act => act ∈ StateScopePool.normalize whole)
          (StateScopePool.normalize whole) bare (StateReaderValues.scope whole clause.freezes key))).meaning target := by
  let ops := StateReaderValues.operations entries whole fields clause.freezes
  let target := meaning whole clause.freezes plans
  obtain ⟨rule,found,supported⟩ := admitted_rule environment entries whole clause prepared fields resolved key admitted
  have dependencies := dependency_equation environment entries whole clause prepared fields resolved key.2 admitted.1 rule found
  cases rule with
  | source source =>
    have noDependency : StateAuthoredDependencies.lookupDependency entries key.2 = none := by
      cases selected : StateAuthoredDependencies.lookupDependency entries key.2 <;> simp [references,selected] at dependencies ⊢
    have lookup := source_equation ⟨fields,clause.freezes⟩ plans compiled key.2 source found
    refine ⟨.source source,sourcePlan source,found,rfl,lookup,?_⟩
    simp only [StateMemoizedReader.Operations.body,StateReaderValues.operations,noDependency]
    change (ops.finish key (StateReaderValues.normal whole clause.freezes fields key none)).meaning target = _
    rw [StateReaderValues.normal_source whole clause.freezes fields key source found none (fun act => act ∈ StateScopePool.normalize whole)]
    rfl
  | derived post source =>
    have dependency : StateAuthoredDependencies.lookupDependency entries key.2 = some source := by
      cases selected : StateAuthoredDependencies.lookupDependency entries key.2 with
      | none => simp [references,selected] at dependencies
      | some name => simpa [references,selected] using dependencies.symm
    obtain ⟨prior,priorLookup,lookup⟩ := derived_equation ⟨fields,clause.freezes⟩ plans compiled key.2 source post found
    refine ⟨.derived post source,.map post prior,found,by simp [compileRule,priorLookup],lookup,?_⟩
    let dependencyValue := target (key.1,source)
    have body : (ops.body key).meaning target =
        (ops.finish key (ops.normal key (some (ops.unfrozen dependencyValue)))).meaning target := by
      simp only [dependencyValue,StateMemoizedReader.Operations.body,ops,StateReaderValues.operations,
        dependency,StateMemoizedReader.Body.meaning]
    have sourceMeaning : dependencyValue = StateReaderValues.scopedObserve
        (fun act => act ∈ StateScopePool.normalize whole) (StateScopePool.normalize whole) prior
        (StateReaderValues.scope whole clause.freezes key) := by
      simp only [dependencyValue,target,meaning,priorLookup]
      rfl
    rw [body]
    change (ops.finish key (StateReaderValues.normal whole clause.freezes fields key
      (some (StateReaderValues.unfrozen dependencyValue)))).meaning target = _
    rw [sourceMeaning,StateReaderValues.normal_derived whole clause.freezes fields key post source found prior
      (fun act => act ∈ StateScopePool.normalize whole)]
  | earlier _ | pair _ _ _ | threshold _ _ _ | thresholdRaw _ _ _ _ | thresholdLift _ _ _ | freeze _ _ =>
    simp [StateReaderValues.supported] at supported

/-- Root metadata cannot invent a freeze for a field without a declaration. -/
theorem missing_freeze_root (whole : List Act) (freezes : List (String × FreezeSpec)) (name : String)
    (missing : freezes.lookup name = none) :
    ((StateScopePool.selectedRoots whole freezes).map (fun (field,freezer) => (field,freezer.addr))).lookup name = none := by
  induction freezes with
  | nil => rfl
  | cons binding rest ih =>
    obtain ⟨field,spec⟩ := binding
    by_cases same : name = field
    · subst name; simp at missing
    · have tail : rest.lookup name = none := by simpa [List.lookup,beq_eq_false_iff_ne.mpr same] using missing
      cases root : StateScopePool.uniqueRoot whole spec.verb <;>
        simpa [StateScopePool.selectedRoots,root,List.lookup,beq_eq_false_iff_ne.mpr same] using ih tail

/-- With no own freeze, finishing preserves the complete normal observation,
including faults or a value obtained from a separately frozen dependency. -/
theorem finish_without_freeze {V : Type} (entries : List StateAuthoredBindings.Entry) (whole : List Act)
    (fields : List (String × StateInstalledCompiler.Rule V)) (freezes : List (String × FreezeSpec))
    (key : StateMemoizedReader.Key) (missing : freezes.lookup key.2 = none) (value : StateReaderValues.Result V) :
    (StateReaderValues.operations entries whole fields freezes).finish key value = .done value := by
  have rootMissing := missing_freeze_root (StateScopePool.normalize whole) freezes key.2 missing
  cases value <;> simp [StateMemoizedReader.Operations.finish,StateReaderValues.operations,StateReaderValues.ownFault,
    StateReaderValues.combinedFault,StateRuleRefinement.sourceError,StateObservation.unionError,missing,StateScopePool.active,rootMissing]

/-- Every admitted field without its own freeze has the complete compiled body
equation, including source faults and derived reads of frozen dependencies. -/
theorem prepared_unfrozen_body (environment : StateAuthoredBindings.Environment) (entries : List StateAuthoredBindings.Entry)
    (whole : List Act) (clause : StateInstalledLowering.Clause StateInstalledLegacy.Value)
    (prepared : StateAuthoredBindings.prepare environment entries whole = some clause)
    (fields : List (String × StateInstalledCompiler.Rule StateInstalledLegacy.Value))
    (resolved : StateInstalledLowering.resolve [] clause.declarations = some fields) (plans : Plans StateInstalledLegacy.Value)
    (compiled : StateInstalledClause.compile ⟨fields,clause.freezes⟩ = some plans)
    (key : StateMemoizedReader.Key) (admitted : Admitted entries whole clause.freezes key)
    (missing : clause.freezes.lookup key.2 = none) :
    ((StateReaderValues.operations entries whole fields clause.freezes).body key).meaning
        (meaning whole clause.freezes plans) = meaning whole clause.freezes plans key := by
  obtain ⟨rule,bare,found,bareCompiled,lookup,normal⟩ := prepared_body_normal environment entries whole clause
    prepared fields resolved plans compiled key admitted
  have target : meaning whole clause.freezes plans key =
      StateReaderValues.scopedObserve (fun act => act ∈ StateScopePool.normalize whole) (StateScopePool.normalize whole)
        bare (StateReaderValues.scope whole clause.freezes key) := by
    simp only [meaning,lookup,missing,decorate]
  rw [normal,finish_without_freeze entries whole fields clause.freezes key missing]
  exact target.symm

/-- The complete recursive cache reference equals the compiled observation
meaning for prepared clauses with no freezes. Own-freeze finishing remains the
additional case needed to extend this equation to the whole source language. -/
theorem prepared_no_freeze_reference (environment : StateAuthoredBindings.Environment) (entries : List StateAuthoredBindings.Entry)
    (whole : List Act) (clause : StateInstalledLowering.Clause StateInstalledLegacy.Value)
    (prepared : StateAuthoredBindings.prepare environment entries whole = some clause)
    (fields : List (String × StateInstalledCompiler.Rule StateInstalledLegacy.Value))
    (resolved : StateInstalledLowering.resolve [] clause.declarations = some fields) (plans : Plans StateInstalledLegacy.Value)
    (compiled : StateInstalledClause.compile ⟨fields,clause.freezes⟩ = some plans)
    (noFreezes : clause.freezes = []) (ranked : StateExecutableFreeze.Ranked whole)
    (consistent : ∀ a ∈ whole, ∀ b ∈ whole, a.addr = b.addr → a = b) :
    let ops := StateReaderValues.operations entries whole fields clause.freezes
    let rank := StateMemoizedReader.requestRank (fields.map Prod.fst).idxOf ops.cut
    ∃ requestRanked : ∀ key, (ops.body key).Below rank (rank key),
      ∀ key, Admitted entries whole clause.freezes key →
        StateMemoizedReader.reference ops.body rank requestRanked key = meaning whole clause.freezes plans key := by
  let ops := StateReaderValues.operations entries whole fields clause.freezes
  have extracted : ∀ name source, ops.dependency name = some source →
      ∃ rule, (name,rule) ∈ fields ∧ source ∈ references rule :=
    StateAuthoredDependencies.extracted_reference environment entries whole clause prepared fields resolved
  have ordering := StateReaderIndices.compiled_dependency_ordering ⟨fields,clause.freezes⟩ plans compiled ops extracted
  let requestRanked := StateMemoizedReader.body_ranked ops (fields.map Prod.fst).idxOf ordering
  refine ⟨requestRanked,reference_on_domain (Admitted entries whole clause.freezes) ops.body _ requestRanked
    (fun key admitted => body_within environment entries whole clause prepared fields ranked consistent key admitted)
    (meaning whole clause.freezes plans) ?_⟩
  intro key admitted
  exact prepared_unfrozen_body environment entries whole clause prepared fields resolved plans compiled key admitted
    (by simp [noFreezes])

/-- Prepared clauses without freezes execute the actual native field-request
transcript with results equal to the completed compiled plans, and every cache
lookup agrees with that meaning. The transcript includes threshold source reads;
threshold output adaptation is a separate stage. -/
theorem prepared_no_freeze_cache (environment : StateAuthoredBindings.Environment) (entries : List StateAuthoredBindings.Entry)
    (whole : List Act) (clause : StateInstalledLowering.Clause StateInstalledLegacy.Value)
    (prepared : StateAuthoredBindings.prepare environment entries whole = some clause)
    (noFreezes : clause.freezes = []) (ranked : StateExecutableFreeze.Ranked whole)
    (consistent : ∀ a ∈ whole, ∀ b ∈ whole, a.addr = b.addr → a = b) :
    ∃ plans fields, StateAuthoredBindings.compile environment entries whole = some plans ∧
      StateInstalledLowering.resolve [] clause.declarations = some fields ∧
      let ops := StateReaderValues.operations entries whole fields clause.freezes
      let rank := StateMemoizedReader.requestRank (fields.map Prod.fst).idxOf ops.cut
      ∃ after, StateMemoizedReader.reads ops.body rank (initialKeys entries) [] =
        some ((initialKeys entries).map (meaning whole clause.freezes plans),after) ∧
        StateMemoizedReader.Valid (meaning whole clause.freezes plans) after ∧
        CacheWithin (Admitted entries whole clause.freezes) after := by
  obtain ⟨plans,fields,compiled,resolved,sound,requestRanked,after,ran,valid,provenance,_⟩ :=
    prepared_reachable_cache environment entries whole clause prepared ranked consistent
  have lowered : StateInstalledLowering.compile clause = some plans := by
    simpa [StateAuthoredBindings.compile,prepared] using compiled
  obtain ⟨actualFields,actualResolved,fieldCompiled⟩ := StateAuthoredDependencies.lowered_compiled_clause clause plans lowered
  have same : actualFields = fields := Option.some.inj (actualResolved.symm.trans resolved)
  subst actualFields
  obtain ⟨_,equalMeaning⟩ := prepared_no_freeze_reference environment entries whole clause prepared fields resolved plans
    fieldCompiled noFreezes ranked consistent
  have initial := initial_keys_admitted environment entries whole clause prepared ranked consistent
  have mapped : (initialKeys entries).map
      (StateMemoizedReader.reference (StateReaderValues.operations entries whole fields clause.freezes).body _ requestRanked) =
      (initialKeys entries).map (meaning whole clause.freezes plans) := by
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

/-- A faulting compiled freeze node finishes immediately with the identical
complete witness union, without requesting or wrapping historical data. -/
theorem finish_faulting {V : Type} (entries : List StateAuthoredBindings.Entry) (whole : List Act)
    (fields : List (String × StateInstalledCompiler.Rule V)) (freezes : List (String × FreezeSpec))
    (key : StateMemoizedReader.Key) (spec : FreezeSpec) (selected : freezes.lookup key.2 = some spec)
    (source : Plan V) (evidence : Evidence)
    (faulted : StateNativeReader.error (fun act => act ∈ StateScopePool.normalize whole) (StateScopePool.normalize whole)
      (.freeze spec source) (StateReaderValues.scope whole freezes key) = some evidence) :
    (StateReaderValues.operations entries whole fields freezes).finish key
      (StateReaderValues.scopedObserve (fun act => act ∈ StateScopePool.normalize whole) (StateScopePool.normalize whole)
        source (StateReaderValues.scope whole freezes key)) = .done (.fault evidence) := by
  have combined := StateReaderValues.freeze_error_refinement (fun act => act ∈ StateScopePool.normalize whole)
    (StateScopePool.normalize whole) (StateReaderValues.scope whole freezes key) spec source
  rw [faulted] at combined
  have finishError : (StateReaderValues.operations entries whole fields freezes).fault key
      (StateReaderValues.scopedObserve (fun act => act ∈ StateScopePool.normalize whole) (StateScopePool.normalize whole)
        source (StateReaderValues.scope whole freezes key)) = some (.fault evidence) := by
    simpa only [StateReaderValues.operations,StateReaderValues.ownFault,selected] using combined
  simp only [StateMemoizedReader.Operations.finish,finishError]

/-- Every terminal compiled field fault satisfies the complete recursive body
equation, including own-freeze conflicts, domain/initializer/resource failures,
and unions with inherited dependency witnesses. -/
theorem prepared_fault_body (environment : StateAuthoredBindings.Environment) (entries : List StateAuthoredBindings.Entry)
    (whole : List Act) (clause : StateInstalledLowering.Clause StateInstalledLegacy.Value)
    (prepared : StateAuthoredBindings.prepare environment entries whole = some clause)
    (fields : List (String × StateInstalledCompiler.Rule StateInstalledLegacy.Value))
    (resolved : StateInstalledLowering.resolve [] clause.declarations = some fields) (plans : Plans StateInstalledLegacy.Value)
    (compiled : StateInstalledClause.compile ⟨fields,clause.freezes⟩ = some plans)
    (key : StateMemoizedReader.Key) (admitted : Admitted entries whole clause.freezes key) (evidence : Evidence)
    (faulted : meaning whole clause.freezes plans key = .fault evidence) :
    ((StateReaderValues.operations entries whole fields clause.freezes).body key).meaning
      (meaning whole clause.freezes plans) = meaning whole clause.freezes plans key := by
  cases selected : clause.freezes.lookup key.2 with
  | none => exact prepared_unfrozen_body environment entries whole clause prepared fields resolved plans compiled key admitted selected
  | some spec =>
    obtain ⟨rule,bare,found,bareCompiled,lookup,normal⟩ := prepared_body_normal environment entries whole clause
      prepared fields resolved plans compiled key admitted
    have target : meaning whole clause.freezes plans key =
        StateReaderValues.scopedObserve (fun act => act ∈ StateScopePool.normalize whole) (StateScopePool.normalize whole)
          (.freeze spec bare) (StateReaderValues.scope whole clause.freezes key) := by simp only [meaning,lookup,selected,decorate]
    have fullError : StateNativeReader.error (fun act => act ∈ StateScopePool.normalize whole) (StateScopePool.normalize whole)
        (.freeze spec bare) (StateReaderValues.scope whole clause.freezes key) = some evidence := by
      rw [← StateReaderValues.scoped_error,← target,faulted]
      rfl
    rw [normal,finish_faulting entries whole fields clause.freezes key spec selected bare evidence fullError]
    exact faulted.symm

end CBCL.StateCompiledFieldEquations
