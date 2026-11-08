import LeanCbcl.StateAuthoredDataOutputs

/-! Concrete resource fields in actual authored programs. The installed native
verifier term is recovered from original resource metadata, not a display or
fault-classification callback. Domain guards and freeze attachment are retained. -/
set_option autoImplicit false
namespace CBCL.StateAuthoredResource
open State StateLift StateLVar StateObservation StateObservationPlan StateInstalledCompiler
open StateInstalledLegacy StateInstalledLowering StateAuthoredBindings StateAuthoredSourceProvenance StateOutputCompiler

/-- The exact concrete term used by the existing bounded-counter binder. -/
noncomputable def term (environment : Environment) (domains : List StateInstalledDomains.Domain)
    (name : String) (resource : Resource) : StateInstalledTerm.Term Value :=
  let native := StateInstalledResource.term resource.profile resource.decode
  {native with guards := native.guards ++ StateInstalledDomains.guards domains (resourceVerbs environment name)}

/-- The actual source-owned resource definition has no successful threshold policy. -/
noncomputable def definition (environment : Environment) (domains : List StateInstalledDomains.Domain)
    (name : String) (resource : Resource) : Definition Value := .factored (term environment domains name resource) none

/-- Installed domain guards retain their existing order around the native
resource snapshot. The outer resource guard is the certificate-backed one. -/
noncomputable def remainder (environment : Environment) (domains : List StateInstalledDomains.Domain)
    (name : String) (resource : Resource) : Source Value :=
  (StateInstalledDomains.guards domains (resourceVerbs environment name)).foldr StateInstalledTerm.Guard.apply
    (.snapshot (StateInstalledResource.snapshot resource.profile resource.decode))

/-- The source recovered by binding is the actual certificate-guarded native
snapshot, with all extra installed guards retained. -/
theorem source_shape (environment : Environment) (domains : List StateInstalledDomains.Domain)
    (name : String) (resource : Resource) :
    StateInstalledTerm.source (term environment domains name resource) =
      .resource resource.profile.config resource.decode (remainder environment domains name resource) := rfl

/-- Data-preserving guards respect equality of their actual underlying reads. -/
theorem guard_reads {V : Type} (guards : List StateInstalledTerm.Guard) (left right : Source V) (A : List Act)
    (same : sourceRead left A = sourceRead right A) :
    sourceRead (guards.foldr StateInstalledTerm.Guard.apply left) A =
      sourceRead (guards.foldr StateInstalledTerm.Guard.apply right) A := by
  induction guards with
  | nil => exact same
  | cons guard rest ih =>
    cases guard <;> simp only [List.foldr_cons,StateInstalledTerm.Guard.apply,sourceRead] <;> rw [ih]

/-- The exact bound source read is the verified native outcome and certificate
fault guard, retaining the extra installed domain-error guards. Only actual
configuration and accepted typed projection identities are supplied. -/
theorem native_read (environment : Environment) (domains : List StateInstalledDomains.Domain)
    (name : String) (resource : Resource) (A : List Act) (input : StateResourceVerifier.Input)
    (config : input.config = resource.profile.config) (projection : input.facts = CheckpointEvidence.project resource.decode A) :
    sourceRead (StateInstalledTerm.source (term environment domains name resource)) A =
      nativeGuard (StateResourceVerifier.nativeFaultRead input)
        (sourceRead ((StateInstalledDomains.guards domains (resourceVerbs environment name)).foldr StateInstalledTerm.Guard.apply
          (.snapshot (fun _ => .nativeResource (StateResourceVerifier.observe input)))) A) := by
  rw [source_shape]
  have bridge := StateInstalledClause.native_resource_source_refinement input resource.decode (remainder environment domains name resource) A projection
  rw [config] at bridge
  rw [bridge]
  apply congrArg (nativeGuard (StateResourceVerifier.nativeFaultRead input))
  apply guard_reads
  exact congrArg (fun value => StateObservationPlan.Observation.data (.snapshot value))
    (StateInstalledResource.snapshot_actual_history_refinement resource.profile resource.decode A input config projection)

/-- Original resource lookup recovers the native verifier term and raw footprint. -/
theorem binding (environment : Environment) (domains : List StateInstalledDomains.Domain)
    (tables : List (String × StateFiniteTable.Verified)) (earlier : List (String × Binding))
    (name : String) (resource : Resource) (found : environment.resources.lookup name = some resource) :
    StateAuthoredBindings.bind environment domains tables earlier (.legacy (.boundedCounter name)) =
      some ⟨.legacy (.boundedCounter name),definition environment domains name resource,.rawVerbs (resourceVerbs environment name)⟩ := by
  simp [StateAuthoredBindings.bind,found,legacyFootprint,definition,term]

/-- Actual authored preparation retains the concrete resource definition. -/
theorem prepared_source (environment : Environment) (entries : List Entry) (prepared : Prepared)
    (accepted : prepareStatic environment entries = some prepared) (name resourceName : String) (resource : Resource)
    (found : environment.resources.lookup resourceName = some resource)
    (present : (name,StateAuthoredBindings.Rule.legacy (.boundedCounter resourceName)) ∈ rawFields entries) :
    Declaration.field name (definition environment prepared.domains resourceName resource) ∈ prepared.declarations := by
  obtain ⟨tables,bindings,_,_,lowered,_⟩ := static_trace environment entries prepared accepted
  obtain ⟨prior,selected,bound,member⟩ := declaration_origin environment prepared.domains tables entries []
    prepared.declarations bindings lowered name (.legacy (.boundedCounter resourceName)) present
  rw [binding environment prepared.domains tables prior resourceName resource found] at bound
  have same := Option.some.inj bound
  subst selected
  exact member

/-- Resolve the actual source plan with its exact clause-wide optional freeze. -/
theorem authored_plan (environment : Environment) (entries : List Entry) (prepared : Prepared)
    (accepted : prepareStatic environment entries = some prepared) (name resourceName : String) (resource : Resource)
    (found : environment.resources.lookup resourceName = some resource)
    (present : (name,StateAuthoredBindings.Rule.legacy (.boundedCounter resourceName)) ∈ rawFields entries) (A : List Act) :
    ∃ plans, StateAuthoredBindings.compile environment entries A = some plans ∧
      plans.lookup name = some (StateCompiledFieldEquations.decorate
        ((materialize prepared.domains A prepared.freezes).lookup name)
        (sourcePlan (StateInstalledTerm.source (term environment prepared.domains resourceName resource)))) := by
  have declared := prepared_source environment entries prepared accepted name resourceName resource found present
  have preparedAt : prepare environment entries A = some (clauseAt prepared A) := by simp [prepare,accepted,clauseAt]
  obtain ⟨plans,compiled⟩ := prepared_compiler_complete environment entries A (clauseAt prepared A) preparedAt
  have lowered : StateInstalledLowering.compile (clauseAt prepared A) = some plans := by
    simpa only [StateAuthoredBindings.compile,preparedAt,Option.bind_some] using compiled
  obtain ⟨fields,resolved,fieldCompiled⟩ := StateAuthoredDependencies.lowered_compiled_clause (clauseAt prepared A) plans lowered
  have member := StateAuthoredDependencies.resolve_field [] prepared.declarations fields resolved name _ declared
  have names : (fields.map Prod.fst).Nodup := by
    rw [StateAuthoredDependencies.resolve_names [] prepared.declarations fields resolved]
    exact (static_preparation_sound environment entries prepared accepted A).1.1
  have lookup := StateReaderReachability.lookup_original fields names name _ member
  change fields.lookup name = some (.source (StateInstalledTerm.source (term environment prepared.domains resourceName resource))) at lookup
  exact ⟨plans,compiled,StateCompiledFieldEquations.source_equation ⟨fields,materialize prepared.domains A prepared.freezes⟩ plans fieldCompiled name _ lookup⟩

/-- A field declaration emits its actual completed source-plan instruction,
independently of unrelated threshold policies in the same clause. -/
theorem field_emitted (plans : Plans Value) (definitions : Definitions Value) (declarations : List (Declaration Value))
    (code : List (Output Value)) (compiled : compileDeclarations plans definitions declarations = some code)
    (name : String) (source : Plan Value) (definition : Definition Value)
    (present : Declaration.field name definition ∈ declarations) (found : plans.lookup name = some source) :
    Output.field name source ∈ code := by
  induction declarations generalizing definitions code with
  | nil => simp at present
  | cons declaration rest ih =>
    cases head : compileOne plans definitions declaration with
    | none => simp [compileDeclarations,head] at compiled
    | some output =>
      cases tail : compileDeclarations plans (extend definitions declaration) rest with
      | none => simp [compileDeclarations,head,tail] at compiled
      | some outputs =>
        have same : output :: outputs = code := by simpa [compileDeclarations,head,tail] using compiled
        subst code
        rcases List.mem_cons.mp present with original | later
        · subst declaration
          have selected : Output.field name source = output := by simpa [compileOne,found] using head
          simp [← selected]
        · exact List.mem_cons_of_mem _ (ih _ _ tail later)

/-- Actual complete authored compilation emits the concrete verified native
resource source with its exact guards and freeze decoration. No successful code
walk, source lookup or final observation is supplied as a premise. -/
theorem authored_emitted (environment : Environment) (entries : List Entry) (prepared : Prepared)
    (accepted : prepareStatic environment entries = some prepared) (name resourceName : String) (resource : Resource)
    (found : environment.resources.lookup resourceName = some resource)
    (present : (name,StateAuthoredBindings.Rule.legacy (.boundedCounter resourceName)) ∈ rawFields entries)
    (A : List Act) (ranked : StateExecutableFreeze.Ranked A)
    (consistent : ∀ a ∈ A, ∀ b ∈ A, a.addr = b.addr → a = b) :
    ∃ program, compileAuthored environment entries A = some program ∧ program.history = A ∧
      (name,sourceValue A (StateCompiledFieldEquations.decorate
        ((materialize prepared.domains A prepared.freezes).lookup name)
        (sourcePlan (StateInstalledTerm.source (term environment prepared.domains resourceName resource))))) ∈ program.observe := by
  have preparedAt : prepare environment entries A = some (clauseAt prepared A) := by simp [prepare,accepted,clauseAt]
  obtain ⟨plans,compiled,lookup⟩ := authored_plan environment entries prepared accepted name resourceName resource found present A
  obtain ⟨actual,fields,code,actualCompiled,_,codeCompiled,_⟩ := prepared_compiler_cache_refinement environment entries A (clauseAt prepared A) preparedAt ranked consistent
  have same : actual = plans := Option.some.inj (actualCompiled.symm.trans compiled)
  subst actual
  have member := field_emitted plans [] prepared.declarations code codeCompiled name _ _
    (prepared_source environment entries prepared accepted name resourceName resource found present) lookup
  have sourceLowered : StateInstalledLowering.compile (clauseAt prepared A) = some plans := by
    simpa only [StateAuthoredBindings.compile,preparedAt,Option.bind_some] using compiled
  let program : CompiledObservation := ⟨A,⟨(clauseAt prepared A).freezes,code⟩⟩
  refine ⟨program,?_,rfl,?_⟩
  · simp [compileAuthored,preparedAt,StateOutputCompiler.compileClause,sourceLowered,codeCompiled,program]
  · exact List.mem_map.mpr ⟨.field name _,member,rfl⟩

/-- A complete no-freeze, no-domain authored resource output equals the actual
native verifier read with its certificate-backed terminal fault. The only read
premises identify the native input's configuration and accepted projection. -/
theorem authored_native_read (environment : Environment) (entries : List Entry) (prepared : Prepared)
    (accepted : prepareStatic environment entries = some prepared) (name resourceName : String) (resource : Resource)
    (found : environment.resources.lookup resourceName = some resource)
    (present : (name,StateAuthoredBindings.Rule.legacy (.boundedCounter resourceName)) ∈ rawFields entries)
    (domains : prepared.domains = []) (freezes : prepared.freezes = [])
    (A : List Act) (ranked : StateExecutableFreeze.Ranked A)
    (consistent : ∀ a ∈ A, ∀ b ∈ A, a.addr = b.addr → a = b)
    (input : StateResourceVerifier.Input) (config : input.config = resource.profile.config)
    (projection : input.facts = CheckpointEvidence.project resource.decode (StateScopePool.normalize A)) :
    ∃ program, compileAuthored environment entries A = some program ∧
      (name,nativeGuard (StateResourceVerifier.nativeFaultRead input)
        (.data (.snapshot (.nativeResource (StateResourceVerifier.observe input))))) ∈ program.observe := by
  obtain ⟨program,compiled,_,member⟩ := authored_emitted environment entries prepared accepted name resourceName resource found present A ranked consistent
  rw [domains,freezes] at member
  have sourceEq : sourceValue A (sourcePlan (StateInstalledTerm.source (term environment [] resourceName resource))) =
      nativeGuard (StateResourceVerifier.nativeFaultRead input) (.data (.snapshot (.nativeResource (StateResourceVerifier.observe input)))) := by
    change observe (fun act => act ∈ StateScopePool.normalize A)
      (sourcePlan (StateInstalledTerm.source (term environment [] resourceName resource))) (StateScopePool.normalize A) = _
    rw [source_refinement,native_read environment [] resourceName resource (StateScopePool.normalize A) input config projection]
    rfl
  refine ⟨program,compiled,?_⟩
  simpa only [materialize,List.map_nil,List.lookup,StateCompiledFieldEquations.decorate,sourceEq] using member

end CBCL.StateAuthoredResource
