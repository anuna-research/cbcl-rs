import LeanCbcl.StateFiniteOutputStability

/-! Recover the actual source factory executions from successful authored
preparation. Source identities are derived from the existing lowering pipeline,
not supplied as detached compiled-plan or policy assumptions. -/
set_option autoImplicit false
namespace CBCL.StateAuthoredSourceProvenance
open State StateLift StateLVar StateObservation StateObservationPlan StateInstalledCompiler
open StateAuthoredBindings StateInstalledLowering

/-- Every original authored field has an actual successful binding execution
and its exact resulting definition in the lowered declaration list. -/
theorem declaration_origin (environment : Environment) (resolvedDomains : List StateInstalledDomains.Domain)
    (resolvedTables : List (String × StateFiniteTable.Verified)) (entries : List Entry)
    (earlier : List (String × Binding)) (loweredFields : List (Declaration StateInstalledLegacy.Value))
    (bindings : List (String × Binding))
    (lowered : declarations environment resolvedDomains resolvedTables earlier entries = some (loweredFields,bindings)) :
    ∀ name rule, (name,rule) ∈ rawFields entries → ∃ prior binding,
      StateAuthoredBindings.bind environment resolvedDomains resolvedTables prior rule = some binding ∧
      .field name binding.definition ∈ loweredFields := by
  induction entries generalizing earlier loweredFields bindings with
  | nil => intro name rule impossible; simp [rawFields] at impossible
  | cons entry rest ih =>
    cases entry with
    | field fieldName fieldRule =>
      cases head : StateAuthoredBindings.bind environment resolvedDomains resolvedTables earlier fieldRule with
      | none => simp [declarations,head] at lowered
      | some binding =>
        cases tail : declarations environment resolvedDomains resolvedTables ((fieldName,binding)::earlier) rest with
        | none => simp [declarations,head,tail] at lowered
        | some output =>
          obtain ⟨more,last⟩ := output
          simp [declarations,head,tail] at lowered
          rcases lowered with ⟨rfl,rfl⟩
          intro name rule member
          have selected : (name,rule) = (fieldName,fieldRule) ∨ (name,rule) ∈ rawFields rest := by
            simpa [rawFields] using member
          rcases selected with same | inside
          · cases same
            exact ⟨earlier,binding,head,by simp⟩
          · obtain ⟨prior,binding,bound,present⟩ := ih _ more last tail name rule inside
            exact ⟨prior,binding,bound,List.mem_cons_of_mem _ present⟩
    | threshold thresholdName source elements =>
      cases tail : declarations environment resolvedDomains resolvedTables earlier rest with
      | none => simp [declarations,tail] at lowered
      | some output =>
        obtain ⟨more,last⟩ := output
        simp [declarations,tail] at lowered
        rcases lowered with ⟨rfl,rfl⟩
        intro name rule member
        obtain ⟨prior,binding,bound,present⟩ := ih earlier more last tail name rule (by simpa [rawFields] using member)
        exact ⟨prior,binding,bound,List.mem_cons_of_mem _ present⟩
    | domain _ | lattice _ | freeze _ _ _ =>
      exact ih earlier loweredFields bindings (by simpa [declarations] using lowered)

/-- Final source bindings come from the initial environment or an actual
successful authored field binding, including fields after auxiliary entries. -/
theorem bindings_origin (environment : Environment) (resolvedDomains : List StateInstalledDomains.Domain)
    (resolvedTables : List (String × StateFiniteTable.Verified)) (entries : List Entry)
    (earlier : List (String × Binding)) (loweredFields : List (Declaration StateInstalledLegacy.Value))
    (bindings : List (String × Binding))
    (lowered : declarations environment resolvedDomains resolvedTables earlier entries = some (loweredFields,bindings)) :
    ∀ name binding, (name,binding) ∈ bindings → (name,binding) ∈ earlier ∨
      ∃ prior rule, (name,rule) ∈ rawFields entries ∧
        StateAuthoredBindings.bind environment resolvedDomains resolvedTables prior rule = some binding := by
  induction entries generalizing earlier loweredFields bindings with
  | nil =>
    simp only [declarations,Option.some.injEq,Prod.mk.injEq] at lowered
    rcases lowered with ⟨rfl,rfl⟩
    exact fun _ _ member => Or.inl member
  | cons entry rest ih =>
    cases entry with
    | field fieldName fieldRule =>
      cases head : StateAuthoredBindings.bind environment resolvedDomains resolvedTables earlier fieldRule with
      | none => simp [declarations,head] at lowered
      | some binding =>
        cases tail : declarations environment resolvedDomains resolvedTables ((fieldName,binding)::earlier) rest with
        | none => simp [declarations,head,tail] at lowered
        | some result =>
          obtain ⟨more,last⟩ := result
          simp [declarations,head,tail] at lowered
          rcases lowered with ⟨rfl,rfl⟩
          intro name selected member
          rcases ih _ more last tail name selected member with old | ⟨prior,rule,inside,bound⟩
          · rcases List.mem_cons.mp old with same | old
            · cases same
              exact Or.inr ⟨earlier,fieldRule,by simp [rawFields],head⟩
            · exact Or.inl old
          · exact Or.inr ⟨prior,rule,by simpa only [rawFields,List.filterMap_cons,List.mem_cons] using Or.inr inside,bound⟩
    | threshold thresholdName source elements =>
      cases tail : declarations environment resolvedDomains resolvedTables earlier rest with
      | none => simp [declarations,tail] at lowered
      | some result =>
        obtain ⟨more,last⟩ := result
        simp [declarations,tail] at lowered
        rcases lowered with ⟨rfl,rfl⟩
        intro name binding member
        rcases ih earlier more last tail name binding member with old | ⟨prior,rule,inside,bound⟩
        · exact Or.inl old
        · exact Or.inr ⟨prior,rule,by simpa [rawFields] using inside,bound⟩
    | domain _ | lattice _ | freeze _ _ _ =>
      intro name binding member
      rcases ih earlier loweredFields bindings (by simpa [declarations] using lowered) name binding member with old | ⟨prior,rule,inside,bound⟩
      · exact Or.inl old
      · exact Or.inr ⟨prior,rule,by simpa [rawFields] using inside,bound⟩

/-- Original source names are a sublist of the validated shared namespace. -/
theorem raw_names_sublist (entries : List Entry) : List.Sublist ((rawFields entries).map Prod.fst) (declaredNames entries) := by
  induction entries with
  | nil => exact .slnil
  | cons entry rest ih =>
    cases entry with
    | field name rule => simpa only [rawFields,declaredNames,List.filterMap_cons,List.map_cons] using List.Sublist.cons₂ name ih
    | threshold name _ _ => simpa only [rawFields,declaredNames,List.filterMap_cons] using List.Sublist.cons name ih
    | lattice declaration => simpa only [rawFields,declaredNames,List.filterMap_cons] using List.Sublist.cons declaration.name ih
    | domain _ | freeze _ _ _ => simpa only [rawFields,declaredNames,List.filterMap_cons] using ih

/-- Successful static preparation exposes its actual domain/table resolution,
ordered binding pass and freeze-template pass. No source factory is postulated. -/
theorem static_trace (environment : Environment) (entries : List Entry) (prepared : Prepared)
    (accepted : prepareStatic environment entries = some prepared) :
    ∃ resolvedTables bindings,
      domains environment entries = some prepared.domains ∧
      tables environment entries = some resolvedTables ∧
      declarations environment prepared.domains resolvedTables [] entries = some (prepared.declarations,bindings) ∧
      freezeTemplates environment bindings entries = some prepared.freezes := by
  have lowered : lowerStatic environment entries = some prepared := by
    cases original : lowerStatic environment entries with
    | none => simp [prepareStatic,original] at accepted
    | some raw =>
      by_cases checked : preparedCheck raw = true
      · have same : raw = prepared := by simpa [prepareStatic,original,Option.filter,checked] using accepted
        subst prepared
        rfl
      · simp [prepareStatic,original,Option.filter,checked] at accepted
  by_cases checked : metadataCheck environment entries = true
  · cases domainResult : domains environment entries with
    | none => simp [lowerStatic,checked,domainResult] at lowered
    | some resolvedDomains =>
      cases tableResult : tables environment entries with
      | none => simp [lowerStatic,checked,domainResult,tableResult] at lowered
      | some resolvedTables =>
        cases declResult : declarations environment resolvedDomains resolvedTables [] entries with
        | none => simp [lowerStatic,checked,domainResult,tableResult,declResult] at lowered
        | some result =>
          obtain ⟨loweredFields,bindings⟩ := result
          cases freezeResult : freezeTemplates environment bindings entries with
          | none => simp [lowerStatic,checked,domainResult,tableResult,declResult,freezeResult] at lowered
          | some templates =>
            have same : (⟨loweredFields,resolvedDomains,templates⟩ : Prepared) = prepared := by
              simpa [lowerStatic,checked,domainResult,tableResult,declResult,freezeResult] using lowered
            cases same
            exact ⟨resolvedTables,bindings,rfl,rfl,declResult,freezeResult⟩
  · simp [lowerStatic,checked] at lowered

/-- Finite bindings expose the exact checked table and source factory result;
the stored query definition and freeze footprint cannot be substituted. -/
theorem finite_binding (environment : Environment) (resolvedDomains : List StateInstalledDomains.Domain)
    (resolvedTables : List (String × StateFiniteTable.Verified)) (earlier : List (String × Binding))
    (lattice : String) (declaration : StateInstalledFinite.Declaration) (binding : Binding)
    (bound : StateAuthoredBindings.bind environment resolvedDomains resolvedTables earlier (.finite lattice declaration) = some binding) :
    ∃ table field, resolvedTables.lookup lattice = some table ∧
      StateInstalledFinite.make environment.schema table resolvedDomains declaration = some field ∧
      binding = ⟨.finite lattice declaration,StateFiniteRead.definition field,.verbs [declaration.verb]⟩ := by
  cases found : resolvedTables.lookup lattice with
  | none => simp [StateAuthoredBindings.bind,found] at bound
  | some table =>
    cases made : StateInstalledFinite.make environment.schema table resolvedDomains declaration with
    | none => simp [StateAuthoredBindings.bind,found,made] at bound
    | some field =>
      have same : ⟨.finite lattice declaration,StateFiniteRead.definition field,.verbs [declaration.verb]⟩ = binding := by
        simpa [StateAuthoredBindings.bind,found,made] using bound
      exact ⟨table,field,rfl,made,same.symm⟩

/-- The finite source definition used by the compiler is recovered from an
original authored finite field in any successfully prepared clause. -/
theorem prepared_finite_source (environment : Environment) (entries : List Entry) (prepared : Prepared)
    (accepted : prepareStatic environment entries = some prepared)
    (name lattice : String) (declaration : StateInstalledFinite.Declaration)
    (present : (name,Rule.finite lattice declaration) ∈ rawFields entries) :
    ∃ resolvedTables table field,
      tables environment entries = some resolvedTables ∧ resolvedTables.lookup lattice = some table ∧
      StateInstalledFinite.make environment.schema table prepared.domains declaration = some field ∧
      Declaration.field name (StateFiniteRead.definition field) ∈ prepared.declarations := by
  obtain ⟨resolvedTables,bindings,_,tableResult,declResult,_⟩ := static_trace environment entries prepared accepted
  obtain ⟨prior,binding,bound,declared⟩ := declaration_origin environment prepared.domains resolvedTables entries
    [] prepared.declarations bindings declResult name (.finite lattice declaration) present
  obtain ⟨table,field,found,made,same⟩ := finite_binding environment prepared.domains resolvedTables prior lattice declaration binding bound
  subst binding
  exact ⟨resolvedTables,table,field,tableResult,found,made,declared⟩

/-- A successful option-valued factory walk retains an actual input and
successful factory result for every output. -/
theorem mapM_origin {α β : Type} (factory : α → Option β) (inputs : List α) (outputs : List β)
    (ran : inputs.mapM factory = some outputs) :
    ∀ output ∈ outputs, ∃ input ∈ inputs, factory input = some output := by
  induction inputs generalizing outputs with
  | nil => simp [List.mapM_nil] at ran; subst outputs; simp
  | cons input rest ih =>
    cases head : factory input with
    | none => simp [List.mapM_cons,head] at ran
    | some output =>
      cases tail : rest.mapM factory with
      | none => simp [List.mapM_cons,head,tail] at ran
      | some more =>
        have same : output :: more = outputs := by simpa [List.mapM_cons,head,tail] using ran
        subst outputs
        intro selected member
        rcases List.mem_cons.mp member with rfl | inside
        · exact ⟨input,by simp,head⟩
        · obtain ⟨origin,present,built⟩ := ih more tail selected inside
          exact ⟨origin,List.mem_cons_of_mem _ present,built⟩

/-- Each freeze template uses the footprint of the actual final source binding. -/
theorem freeze_origin (environment : Environment) (bindings : List (String × Binding)) (entries : List Entry)
    (templates : List FreezeTemplate) (ran : freezeTemplates environment bindings entries = some templates)
    (template : FreezeTemplate) (member : template ∈ templates) :
    ∃ binding, bindings.lookup template.field = some binding ∧ template.footprint = binding.footprint ∧
      Entry.freeze template.field template.verb template.policy ∈ entries := by
  let inputs := entries.filterMap (fun entry => match entry with
    | .freeze field verb policy => some (field,verb,policy) | _ => none)
  let factory := fun (field,verb,policy) => match bindings.lookup field with
    | none => none
    | some binding => do
      let senderRole ← environment.fromRoles.lookup verb
      if senderRole.isEmpty || !environment.schema.verbs.contains verb then none else
      some (⟨field,verb,binding.footprint,policy⟩ : FreezeTemplate)
  have built : inputs.mapM factory = some templates := ran
  obtain ⟨⟨field,verb,policy⟩,input,made⟩ := mapM_origin factory inputs templates built template member
  have original : Entry.freeze field verb policy ∈ entries := by
    obtain ⟨entry,present,same⟩ := List.mem_filterMap.mp input
    cases entry <;> simp_all
  cases found : bindings.lookup field with
  | none => simp [factory,found] at made
  | some binding =>
    cases role : environment.fromRoles.lookup verb with
    | none => simp [factory,found,role] at made
    | some senderRole =>
      have same : (⟨field,verb,binding.footprint,policy⟩ : FreezeTemplate) = template := by
        have parts : (senderRole.isEmpty = false ∧ verb ∈ environment.schema.verbs) ∧
            (⟨field,verb,binding.footprint,policy⟩ : FreezeTemplate) = template := by
          simpa [factory,found,role] using made
        exact parts.2
      cases same
      exact ⟨binding,found,rfl,original⟩

/-- Actual authored preparation establishes the native positive/default-bound
installation gate before constructing source metadata or finite tables. -/
theorem prepared_bounds (environment : Environment) (entries : List Entry) (prepared : Prepared)
    (accepted : prepareStatic environment entries = some prepared) :
    StateInstalledBounds.check environment.profile.definition.bounds = true := by
  have checked : metadataCheck environment entries = true := by
    by_cases result : metadataCheck environment entries = true
    · exact result
    · have absent : lowerStatic environment entries = none := by simp [lowerStatic,result]
      simp [prepareStatic,absent] at accepted
  simp only [metadataCheck,Bool.and_eq_true] at checked
  exact checked.2

/-- Authored namespace validation supplies uniqueness of original source names. -/
theorem prepared_raw_unique (environment : Environment) (entries : List Entry) (prepared : Prepared)
    (accepted : prepareStatic environment entries = some prepared) : ((rawFields entries).map Prod.fst).Nodup := by
  have checked : metadataCheck environment entries = true := by
    by_cases result : metadataCheck environment entries = true
    · exact result
    · have absent : lowerStatic environment entries = none := by simp [lowerStatic,result]
      simp [prepareStatic,absent] at accepted
  have parts := checked
  simp only [metadataCheck,Bool.and_eq_true,decide_eq_true_eq] at parts
  exact (raw_names_sublist entries).nodup parts.1.1.1.2

/-- Freeze targets of original finite fields recover the exact factory field,
source-owned definition and authored dependency footprint from preparation. -/
theorem prepared_finite_freeze (environment : Environment) (entries : List Entry) (prepared : Prepared)
    (accepted : prepareStatic environment entries = some prepared)
    (name lattice : String) (declaration : StateInstalledFinite.Declaration)
    (present : (name,Rule.finite lattice declaration) ∈ rawFields entries)
    (template : FreezeTemplate) (frozen : template ∈ prepared.freezes) (target : template.field = name) :
    ∃ resolvedTables table field bindings, ∃ binding : Binding,
      tables environment entries = some resolvedTables ∧ resolvedTables.lookup lattice = some table ∧
      declarations environment prepared.domains resolvedTables [] entries = some (prepared.declarations,bindings) ∧
      bindings.lookup name = some binding ∧
      StateInstalledFinite.make environment.schema table prepared.domains declaration = some field ∧
      binding.definition = StateFiniteRead.definition field ∧ template.footprint = .verbs [declaration.verb] := by
  obtain ⟨resolvedTables,bindings,_,tableResult,declResult,freezeResult⟩ := static_trace environment entries prepared accepted
  obtain ⟨binding,found,footprint,_⟩ := freeze_origin environment bindings entries prepared.freezes freezeResult template frozen
  rw [target] at found
  obtain ⟨before,after,equal,_⟩ := List.lookup_eq_some_iff.mp found
  have member : (name,binding) ∈ bindings := by simp [equal]
  rcases bindings_origin environment prepared.domains resolvedTables entries [] prepared.declarations bindings declResult
      name binding member with impossible | ⟨prior,rule,original,bound⟩
  · simp at impossible
  · have unique := prepared_raw_unique environment entries prepared accepted
    have first := StateReaderReachability.lookup_original (rawFields entries) unique name (.finite lattice declaration) present
    have second := StateReaderReachability.lookup_original (rawFields entries) unique name rule original
    have same : rule = .finite lattice declaration := Option.some.inj (second.symm.trans first)
    subst rule
    obtain ⟨table,field,lookup,made,bindingEq⟩ := finite_binding environment prepared.domains resolvedTables prior lattice declaration binding bound
    refine ⟨resolvedTables,table,field,bindings,binding,tableResult,lookup,declResult,found,made,?_,?_⟩
    · rw [bindingEq]
    · simpa only [bindingEq] using footprint

/-- The checked finite factory retains the exact authored verb and resolved domains. -/
theorem finite_factory_identity (schema : StateInstalledDomains.Schema) (table : StateFiniteTable.Verified)
    (resolvedDomains : List StateInstalledDomains.Domain) (declaration : StateInstalledFinite.Declaration)
    (field : StateInstalledFinite.Field)
    (made : StateInstalledFinite.make schema table resolvedDomains declaration = some field) :
    field.verb = declaration.verb ∧ field.domains = resolvedDomains := by
  unfold StateInstalledFinite.make at made
  split at made
  · contradiction
  · cases rows : declaration.rows.mapM (StateFiniteProjection.resolveRow table.table) with
    | none => simp [rows] at made
    | some resolvedRows =>
      cases projection : declaration.projection with
      | none =>
        have same : (⟨table,declaration.verb,resolvedRows,none,resolvedDomains⟩ : StateInstalledFinite.Field) = field := by
          simpa [rows,projection] using made
        cases same
        exact ⟨rfl,rfl⟩
      | some authored =>
        cases compiled : StateFiniteProjection.compile table.table authored with
        | none => simp [rows,projection,compiled] at made
        | some projected =>
          have same : (⟨table,declaration.verb,resolvedRows,some projected,resolvedDomains⟩ : StateInstalledFinite.Field) = field := by
            simpa [rows,projection,compiled] using made
          cases same
          exact ⟨rfl,rfl⟩

/-- A finite threshold source's optional fault-freeze metadata is recovered
from authored freeze templates and installation's stable-source gate. -/
theorem prepared_finite_metadata (environment : Environment) (entries : List Entry) (prepared : Prepared)
    (accepted : prepareStatic environment entries = some prepared)
    (name lattice : String) (declaration : StateInstalledFinite.Declaration)
    (present : (name,Rule.finite lattice declaration) ∈ rawFields entries)
    (outputName : String) (elements : List StateInstalledLegacy.Value)
    (threshold : Declaration.threshold outputName name elements ∈ prepared.declarations) (history : List Act) :
    ∃ field, ∃ freezeDeclaration : Option String,
      Declaration.field name (StateFiniteRead.definition field) ∈ prepared.declarations ∧
      field.domains = prepared.domains ∧
      (materialize prepared.domains history prepared.freezes).lookup name =
        freezeDeclaration.map (StateFiniteFreezePolicy.freezeSpec field history) := by
  obtain ⟨resolvedTables,table,field,_,_,made,declared⟩ := prepared_finite_source environment entries prepared accepted name lattice declaration present
  obtain ⟨verb,domainEq⟩ := finite_factory_identity environment.schema table prepared.domains declaration field made
  refine ⟨field,?_⟩
  have valid := (static_preparation_sound environment entries prepared accepted history).1
  have stable : stableSource (materialize prepared.domains history prepared.freezes) name = true := by
    have checked := valid.2.2.2
    exact List.all_eq_true.mp checked _ threshold
  cases found : (materialize prepared.domains history prepared.freezes).lookup name with
  | none => exact ⟨none,declared,domainEq,rfl⟩
  | some spec =>
    obtain ⟨before,after,equal,_⟩ := List.lookup_eq_some_iff.mp found
    have member : (name,spec) ∈ materialize prepared.domains history prepared.freezes := by simp [equal]
    obtain ⟨template,frozen,same⟩ := List.mem_map.mp member
    have target : template.field = name := congrArg Prod.fst same
    have exactSpec : (⟨template.verb,contributes prepared.domains history template.footprint,template.policy⟩ : FreezeSpec) = spec := congrArg Prod.snd same
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,footprint⟩ := prepared_finite_freeze environment entries prepared accepted name lattice declaration present template frozen target
    have policy : template.policy = true := by
      simpa only [stableSource,found,exactSpec.symm] using stable
    refine ⟨some template.verb,declared,domainEq,?_⟩
    simp only [Option.map_some]
    apply congrArg some
    rw [← exactSpec,footprint,← verb,← domainEq,policy]
    rfl

/-- Ordered lowering preserves the literal source and elements of authored
threshold declarations through intervening fields and auxiliary entries. -/
theorem declaration_threshold (environment : Environment) (resolvedDomains : List StateInstalledDomains.Domain)
    (resolvedTables : List (String × StateFiniteTable.Verified)) (entries : List Entry)
    (earlier : List (String × Binding)) (loweredFields : List (Declaration StateInstalledLegacy.Value))
    (bindings : List (String × Binding))
    (lowered : declarations environment resolvedDomains resolvedTables earlier entries = some (loweredFields,bindings))
    (name sourceName : String) (elements : List StateInstalledLegacy.Value)
    (member : Entry.threshold name sourceName elements ∈ entries) :
    Declaration.threshold name sourceName elements ∈ loweredFields := by
  induction entries generalizing earlier loweredFields bindings with
  | nil => simp at member
  | cons entry rest ih =>
    cases entry with
    | field fieldName rule =>
      cases head : StateAuthoredBindings.bind environment resolvedDomains resolvedTables earlier rule with
      | none => simp [declarations,head] at lowered
      | some binding =>
        cases tail : declarations environment resolvedDomains resolvedTables ((fieldName,binding)::earlier) rest with
        | none => simp [declarations,head,tail] at lowered
        | some output =>
          obtain ⟨more,last⟩ := output
          simp [declarations,head,tail] at lowered
          rcases lowered with ⟨rfl,rfl⟩
          exact List.mem_cons_of_mem _ (ih _ more last tail (by simpa using member))
    | threshold outputName source queries =>
      cases tail : declarations environment resolvedDomains resolvedTables earlier rest with
      | none => simp [declarations,tail] at lowered
      | some output =>
        obtain ⟨more,last⟩ := output
        simp [declarations,tail] at lowered
        rcases lowered with ⟨rfl,rfl⟩
        rcases List.mem_cons.mp member with same | inside
        · cases same; exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih earlier more last tail inside)
    | domain _ | lattice _ | freeze _ _ _ =>
      exact ih earlier loweredFields bindings (by simpa [declarations] using lowered) (by simpa using member)

/-- Successful authored preparation recovers the resolved source rule and
matching optional fault-freeze metadata for an actual authored finite threshold.
The field factory, lowered source membership and source metadata are conclusions. -/
theorem authored_finite_source (environment : Environment) (entries : List Entry) (prepared : Prepared)
    (accepted : prepareStatic environment entries = some prepared)
    (name lattice : String) (declaration : StateInstalledFinite.Declaration)
    (present : (name,Rule.finite lattice declaration) ∈ rawFields entries)
    (outputName : String) (elements : List StateInstalledLegacy.Value)
    (threshold : Entry.threshold outputName name elements ∈ entries) (history : List Act)
    (fields : List (String × StateInstalledCompiler.Rule StateInstalledLegacy.Value))
    (resolved : resolve [] prepared.declarations = some fields) :
    ∃ field, ∃ freezeDeclaration : Option String,
      Declaration.field name (StateFiniteRead.definition field) ∈ prepared.declarations ∧
      fields.lookup name = some (.source (StateInstalledFinite.source field)) ∧
      (materialize prepared.domains history prepared.freezes).lookup name =
        freezeDeclaration.map (StateFiniteFreezePolicy.freezeSpec field history) := by
  obtain ⟨resolvedTables,bindings,_,_,declResult,_⟩ := static_trace environment entries prepared accepted
  have loweredThreshold := declaration_threshold environment prepared.domains resolvedTables entries [] prepared.declarations
    bindings declResult outputName name elements threshold
  obtain ⟨field,freezeDeclaration,declared,_,metadata⟩ := prepared_finite_metadata environment entries prepared accepted
    name lattice declaration present outputName elements loweredThreshold history
  have sourceMember := StateAuthoredDependencies.resolve_field [] prepared.declarations fields resolved name
    (StateFiniteRead.definition field) declared
  have valid := (static_preparation_sound environment entries prepared accepted history).1
  have names : (fields.map Prod.fst).Nodup := by
    rw [StateAuthoredDependencies.resolve_names [] prepared.declarations fields resolved]
    exact valid.1
  have lookup := StateReaderReachability.lookup_original fields names name _ sourceMember
  refine ⟨field,freezeDeclaration,declared,?_,metadata⟩
  simpa only [StateFiniteRead.definition,lowerDefinition,StateInstalledFinite.source] using lookup

/-- Concrete authored installation constructs the source dictionary and its
exact guarded finite plan. The caller supplies neither a resolved source rule,
freeze identity, nor successful compilation/resolution as a premise. -/
theorem authored_finite_plan (environment : Environment) (entries : List Entry) (prepared : Prepared)
    (accepted : prepareStatic environment entries = some prepared)
    (name lattice : String) (declaration : StateInstalledFinite.Declaration)
    (present : (name,Rule.finite lattice declaration) ∈ rawFields entries)
    (outputName : String) (elements : List StateInstalledLegacy.Value)
    (threshold : Entry.threshold outputName name elements ∈ entries) (history : List Act) :
    ∃ field freezeDeclaration plans,
      StateAuthoredBindings.compile environment entries history = some plans ∧
      plans.lookup name = some (StateFiniteOutputStability.source field history freezeDeclaration) ∧
      (materialize prepared.domains history prepared.freezes).lookup name =
        freezeDeclaration.map (StateFiniteFreezePolicy.freezeSpec field history) ∧
      Declaration.field name (StateFiniteRead.definition field) ∈ prepared.declarations := by
  have preparedAt : prepare environment entries history = some (clauseAt prepared history) := by
    simp [prepare,accepted,clauseAt]
  obtain ⟨plans,compiled⟩ := prepared_compiler_complete environment entries history (clauseAt prepared history) preparedAt
  have lowered : StateInstalledLowering.compile (clauseAt prepared history) = some plans := by
    simpa only [StateAuthoredBindings.compile,preparedAt,Option.bind_some] using compiled
  obtain ⟨fields,resolved,fieldCompiled⟩ := StateAuthoredDependencies.lowered_compiled_clause (clauseAt prepared history) plans lowered
  obtain ⟨field,freezeDeclaration,declared,original,metadata⟩ := authored_finite_source environment entries prepared accepted
    name lattice declaration present outputName elements threshold history fields resolved
  have lookup := StateCompiledFieldEquations.source_equation
    (⟨fields,materialize prepared.domains history prepared.freezes⟩ : StateInstalledClause.Clause StateInstalledLegacy.Value)
    plans fieldCompiled name (StateInstalledFinite.source field) original
  rw [metadata] at lookup
  refine ⟨field,freezeDeclaration,plans,compiled,?_,metadata,declared⟩
  cases freezeDeclaration <;> simpa only [Option.map_none,Option.map_some,StateCompiledFieldEquations.decorate,
    StateFiniteOutputStability.source,StateFiniteFreezePolicy.frozenPlan] using lookup

end CBCL.StateAuthoredSourceProvenance
