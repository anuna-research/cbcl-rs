import LeanCbcl.StateNativeDataFreeze

/-! Authored count/existence source identity and freeze provenance. The closed
head inventory is proof metadata, not new dialect syntax or a supplied source
factory. Every binding equation is checked against the existing lowerer. -/
set_option autoImplicit false
namespace CBCL.StateAuthoredDataProvenance
open State StateLift StateLVar StateObservation StateObservationPlan StateInstalledCompiler
open StateInstalledLegacy StateInstalledLowering StateAuthoredBindings StateAuthoredSourceProvenance StateOutputCompiler

/-- The native data heads whose value/query laws are connected here. -/
inductive Head where
  | count (verb : String)
  | existsRule (verb : String)

/-- The single source performative retained by each head. -/
def Head.verb : Head → String
  | .count verb | .existsRule verb => verb

/-- The original dialect rule, using the existing rule inventory. -/
def Head.rule : Head → StateKernelClause.Rule
  | .count verb => .count verb
  | .existsRule verb => .existsRule verb

/-- The actual expression emitted by the existing kernel rule compiler. -/
def Head.expression : Head → StateKernel.Expr
  | .count verb => .count (.verb verb)
  | .existsRule verb => .existsRule (.verb verb)

/-- The existing source factory, not a callback stored by this proof. -/
noncomputable def Head.definition (head : Head) (environment : Environment) (domains : List StateInstalledDomains.Domain) : Definition Value :=
  primitive environment domains head.expression head.rule

/-- The guarded kernel source plan retained by that factory. -/
noncomputable def Head.bare (head : Head) (environment : Environment) (domains : List StateInstalledDomains.Domain) : Plan Value :=
  sourcePlan (StateInstalledTerm.source (StateInstalledDomains.term environment.context domains head.expression (resourceVerbs environment)))

/-- Actual authored binding retains the exact definition and dependency verbs. -/
theorem binding (head : Head) (environment : Environment) (domains : List StateInstalledDomains.Domain)
    (tables : List (String × StateFiniteTable.Verified)) (earlier : List (String × Binding)) :
    StateAuthoredBindings.bind environment domains tables earlier (.legacy head.rule) =
      some ⟨.legacy head.rule,head.definition environment domains,.verbs [head.verb]⟩ := by
  cases head <;> rfl

/-- Original source definitions lower to exactly the guarded kernel plan. -/
theorem lower_definition (head : Head) (environment : Environment) (domains : List StateInstalledDomains.Domain) :
    lowerDefinition (head.definition environment domains) = .source (StateInstalledTerm.source
      (StateInstalledDomains.term environment.context domains head.expression (resourceVerbs environment))) := by
  cases head <;> rfl

/-- Preparation retains the actual source-owned definition of an original field. -/
theorem prepared_source (head : Head) (environment : Environment) (entries : List Entry) (prepared : Prepared)
    (accepted : prepareStatic environment entries = some prepared) (name : String)
    (present : (name,StateAuthoredBindings.Rule.legacy head.rule) ∈ rawFields entries) :
    Declaration.field name (head.definition environment prepared.domains) ∈ prepared.declarations := by
  obtain ⟨tables,bindings,_,_,lowered,_⟩ := static_trace environment entries prepared accepted
  obtain ⟨prior,selected,bound,member⟩ := declaration_origin environment prepared.domains tables entries []
    prepared.declarations bindings lowered name (.legacy head.rule) present
  rw [binding head environment prepared.domains tables prior] at bound
  have same := Option.some.inj bound
  subst selected
  exact member

/-- A freeze target's footprint comes from the same actual final source binding. -/
theorem prepared_footprint (head : Head) (environment : Environment) (entries : List Entry) (prepared : Prepared)
    (accepted : prepareStatic environment entries = some prepared) (name : String)
    (present : (name,StateAuthoredBindings.Rule.legacy head.rule) ∈ rawFields entries)
    (template : FreezeTemplate) (frozen : template ∈ prepared.freezes) (target : template.field = name) :
    template.footprint = .verbs [head.verb] := by
  obtain ⟨tables,bindings,_,_,lowered,freezesBuilt⟩ := static_trace environment entries prepared accepted
  obtain ⟨selected,found,footprint,_⟩ := freeze_origin environment bindings entries prepared.freezes freezesBuilt template frozen
  rw [target] at found
  obtain ⟨before,after,equal,_⟩ := List.lookup_eq_some_iff.mp found
  have member : (name,selected) ∈ bindings := by simp [equal]
  rcases bindings_origin environment prepared.domains tables entries [] prepared.declarations bindings lowered name selected member with
    impossible | ⟨prior,rule,original,bound⟩
  · simp at impossible
  · have unique := prepared_raw_unique environment entries prepared accepted
    have a := StateReaderReachability.lookup_original (rawFields entries) unique name (.legacy head.rule) present
    have b := StateReaderReachability.lookup_original (rawFields entries) unique name rule original
    have same : rule = .legacy head.rule := Option.some.inj (b.symm.trans a)
    subst rule
    rw [binding head environment prepared.domains tables prior] at bound
    have selectedEq := Option.some.inj bound
    simpa only [← selectedEq] using footprint

/-- Threshold installation resolves optional fault-freeze metadata from actual
freeze templates, including declarations appearing after their source. -/
theorem prepared_metadata (head : Head) (environment : Environment) (entries : List Entry) (prepared : Prepared)
    (accepted : prepareStatic environment entries = some prepared) (name outputName : String)
    (present : (name,StateAuthoredBindings.Rule.legacy head.rule) ∈ rawFields entries) (elements : List Value)
    (threshold : Entry.threshold outputName name elements ∈ entries) (history : List Act) :
    ∃ declaration : Option String, (materialize prepared.domains history prepared.freezes).lookup name =
      declaration.map (StateNativeDataFreeze.spec prepared.domains [head.verb] history) := by
  obtain ⟨tables,bindings,_,_,lowered,_⟩ := static_trace environment entries prepared accepted
  have thresholdMember := declaration_threshold environment prepared.domains tables entries [] prepared.declarations bindings lowered
    outputName name elements threshold
  have valid := (static_preparation_sound environment entries prepared accepted history).1
  have stable : stableSource (materialize prepared.domains history prepared.freezes) name = true :=
    List.all_eq_true.mp valid.2.2.2 _ thresholdMember
  cases found : (materialize prepared.domains history prepared.freezes).lookup name with
  | none => exact ⟨none,rfl⟩
  | some freeze =>
    obtain ⟨before,after,equal,_⟩ := List.lookup_eq_some_iff.mp found
    have member : (name,freeze) ∈ materialize prepared.domains history prepared.freezes := by simp [equal]
    obtain ⟨template,frozen,same⟩ := List.mem_map.mp member
    have target : template.field = name := congrArg Prod.fst same
    have exactSpec : (⟨template.verb,contributes prepared.domains history template.footprint,template.policy⟩ : FreezeSpec) = freeze :=
      congrArg Prod.snd same
    have footprint := prepared_footprint head environment entries prepared accepted name present template frozen target
    have policy : template.policy = true := by simpa only [stableSource,found,exactSpec.symm] using stable
    refine ⟨some template.verb,?_⟩
    simp only [Option.map_some]
    apply congrArg some
    rw [← exactSpec,footprint,policy]
    rfl

/-- Successful authored preparation constructs the final exact guarded native
source plan and its matching optional freeze metadata, not detached identities. -/
theorem authored_plan (head : Head) (environment : Environment) (entries : List Entry) (prepared : Prepared)
    (accepted : prepareStatic environment entries = some prepared) (name outputName : String)
    (present : (name,StateAuthoredBindings.Rule.legacy head.rule) ∈ rawFields entries) (elements : List Value)
    (threshold : Entry.threshold outputName name elements ∈ entries) (history : List Act) :
    ∃ declaration plans, StateAuthoredBindings.compile environment entries history = some plans ∧
      plans.lookup name = some (StateNativeDataFreeze.decorate prepared.domains [head.verb] history declaration
        (head.bare environment prepared.domains)) ∧
      (materialize prepared.domains history prepared.freezes).lookup name =
        declaration.map (StateNativeDataFreeze.spec prepared.domains [head.verb] history) ∧
      Declaration.field name (head.definition environment prepared.domains) ∈ prepared.declarations := by
  have declared := prepared_source head environment entries prepared accepted name present
  obtain ⟨declaration,metadata⟩ := prepared_metadata head environment entries prepared accepted name outputName present elements threshold history
  have preparedAt : prepare environment entries history = some (clauseAt prepared history) := by simp [prepare,accepted,clauseAt]
  obtain ⟨plans,compiled⟩ := prepared_compiler_complete environment entries history (clauseAt prepared history) preparedAt
  have lowered : StateInstalledLowering.compile (clauseAt prepared history) = some plans := by
    simpa only [StateAuthoredBindings.compile,preparedAt,Option.bind_some] using compiled
  obtain ⟨fields,resolved,fieldCompiled⟩ := StateAuthoredDependencies.lowered_compiled_clause (clauseAt prepared history) plans lowered
  have member := StateAuthoredDependencies.resolve_field [] prepared.declarations fields resolved name _ declared
  have names : (fields.map Prod.fst).Nodup := by
    rw [StateAuthoredDependencies.resolve_names [] prepared.declarations fields resolved]
    exact (static_preparation_sound environment entries prepared accepted history).1.1
  have lookup := StateReaderReachability.lookup_original fields names name _ member
  rw [lower_definition] at lookup
  have final := StateCompiledFieldEquations.source_equation
    (⟨fields,materialize prepared.domains history prepared.freezes⟩ : StateInstalledClause.Clause Value)
    plans fieldCompiled name _ lookup
  rw [metadata] at final
  exact ⟨declaration,plans,compiled,final,metadata,declared⟩

/-- Output occurrence provenance recovers source-owned query code for any
original definition, without requiring a supplied definition lookup. -/
theorem emitted_policy (plans : Plans Value) (full : List (Declaration Value)) (unique : (full.map Declaration.name).Nodup)
    (name outputName : String) (elements : List Value) (definition : Definition Value)
    (declared : Declaration.field name definition ∈ full) (priorDefinitions : Definitions Value)
    (origins : StateAuthoredOutputProvenance.Origins full priorDefinitions)
    (plan : Plan Value) (lookup : plans.lookup name = some plan) (output : Output Value)
    (compiled : compileOne plans priorDefinitions (.threshold outputName name elements) = some output) :
    ∃ query, compileQuery elements definition = some query ∧ output = .threshold outputName name query plan := by
  cases found : priorDefinitions.lookup name with
  | none => simp [compileOne,lookup,found] at compiled
  | some selected =>
    obtain ⟨before,after,equal,_⟩ := List.lookup_eq_some_iff.mp found
    have member : (name,selected) ∈ priorDefinitions := by simp [equal]
    have same := StateAuthoredOutputProvenance.unique_definition full unique name selected definition
      (origins name selected member) declared
    subst selected
    cases queryBuilt : compileQuery elements definition with
    | none => simp [compileOne,lookup,found,queryBuilt] at compiled
    | some query =>
      have same : Output.threshold outputName name query plan = output := by simpa [compileOne,lookup,found,queryBuilt] using compiled
      exact ⟨query,rfl,same.symm⟩

end CBCL.StateAuthoredDataProvenance
