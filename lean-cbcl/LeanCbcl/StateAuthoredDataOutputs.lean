import LeanCbcl.StateAuthoredDataProvenance

/-! Native count/existence queries in complete actual authored output programs.
Source identity, query ownership, freeze metadata and output occurrence are
recovered from the existing compiler. No successful code walk is a premise. -/
set_option autoImplicit false
namespace CBCL.StateAuthoredDataOutputs
open State StateLift StateLVar StateObservation StateObservationPlan StateInstalledCompiler
open StateInstalledLegacy StateInstalledLowering StateAuthoredBindings StateAuthoredSourceProvenance StateOutputCompiler
open StateAuthoredDataProvenance

/-- Recover an actual emitted threshold and its source-owned query code in the
complete program, including the exact history and named global freeze metadata. -/
theorem authored_emitted (head : Head) (environment : Environment) (entries : List Entry) (prepared : Prepared)
    (accepted : prepareStatic environment entries = some prepared) (name outputName : String)
    (present : (name,StateAuthoredBindings.Rule.legacy head.rule) ∈ rawFields entries) (elements : List Value)
    (threshold : Entry.threshold outputName name elements ∈ entries) (B : List Act)
    (ranked : StateExecutableFreeze.Ranked B) (consistent : ∀ a ∈ B, ∀ b ∈ B, a.addr = b.addr → a = b) :
    ∃ declaration query program,
      compileAuthored environment entries B = some program ∧
      compileQuery elements (head.definition environment prepared.domains) = some query ∧
      Output.threshold outputName name query (StateNativeDataFreeze.decorate prepared.domains [head.verb] B declaration
        (head.bare environment prepared.domains)) ∈ program.program.outputs ∧
      program.history = B ∧ program.program.freezes.lookup name =
        declaration.map (StateNativeDataFreeze.spec prepared.domains [head.verb] B) := by
  have preparedAt : prepare environment entries B = some (clauseAt prepared B) := by simp [prepare,accepted,clauseAt]
  obtain ⟨declaration,sourcePlans,sourceCompiled,lookup,metadata,declared⟩ := authored_plan head environment entries prepared accepted
    name outputName present elements threshold B
  obtain ⟨plans,fields,code,compiled,resolved,codeCompiled,values,after,ran,adapted⟩ :=
    prepared_compiler_cache_refinement environment entries B (clauseAt prepared B) preparedAt ranked consistent
  have same : sourcePlans = plans := Option.some.inj (sourceCompiled.symm.trans compiled)
  subst sourcePlans
  obtain ⟨tables,bindings,_,_,lowered,_⟩ := static_trace environment entries prepared accepted
  have thresholdMember := declaration_threshold environment prepared.domains tables entries [] prepared.declarations bindings lowered
    outputName name elements threshold
  have unique := (static_preparation_sound environment entries prepared accepted B).1.1
  obtain ⟨priorDefinitions,output,origins,member,emitted⟩ := StateAuthoredOutputProvenance.emitted_origin plans prepared.declarations
    prepared.declarations [] code (by intro source definition impossible; simp at impossible) (fun _ inside => inside) codeCompiled _ thresholdMember
  obtain ⟨query,queryCompiled,outputEq⟩ := emitted_policy plans prepared.declarations unique name outputName elements _ declared
    priorDefinitions origins _ lookup output emitted
  have sourceLowered : StateInstalledLowering.compile (clauseAt prepared B) = some plans := by
    simpa only [StateAuthoredBindings.compile,preparedAt,Option.bind_some] using compiled
  let program : CompiledObservation := ⟨B,⟨(clauseAt prepared B).freezes,code⟩⟩
  have programCompiled : compileAuthored environment entries B = some program := by
    simp [compileAuthored,preparedAt,StateOutputCompiler.compileClause,sourceLowered,codeCompiled,program]
  exact ⟨declaration,query,program,programCompiled,queryCompiled,outputEq ▸ member,rfl,metadata⟩

/-- Domain-aware freeze specializations preserve accepted-set equality. -/
theorem spec_setEq (domains : List StateInstalledDomains.Domain) (names : List String) {A B : List Act} (same : SetEq A B) :
    StateNativeDataFreeze.spec domains names A = StateNativeDataFreeze.spec domains names B := by
  funext verb
  simp only [StateNativeDataFreeze.spec,contributes_setEq domains same]

/-- The source-plan decoration commutes with duplicate-delivery normalization. -/
theorem decorate_setEq {V : Type} (domains : List StateInstalledDomains.Domain) (names : List String)
    {A B : List Act} (same : SetEq A B) (declaration : Option String) (bare : Plan V) :
    StateNativeDataFreeze.decorate domains names A declaration bare = StateNativeDataFreeze.decorate domains names B declaration bare := by
  simp only [StateNativeDataFreeze.decorate,spec_setEq domains names same]

/-- Transfer a constructed source-cut output to the actual emitted occurrence
in the complete program. Global unrelated freezes cannot alter its named scope. -/
theorem dispatch_member (head : Head) (environment : Environment) (domains : List StateInstalledDomains.Domain)
    (B : List Act) (declaration : Option String) (name outputName : String) (query : Query Value)
    (program : CompiledObservation) (member : Output.threshold outputName name query
      (StateNativeDataFreeze.decorate domains [head.verb] B declaration (head.bare environment domains)) ∈ program.program.outputs)
    (history : program.history = B)
    (metadata : program.program.freezes.lookup name = declaration.map (StateNativeDataFreeze.spec domains [head.verb] B))
    (result : StateReaderValues.Result Value)
    (observed : (Output.threshold outputName name query
      (StateNativeDataFreeze.decorate domains [head.verb] (StateScopePool.normalize B) declaration (head.bare environment domains))).observe B
      (StateNativeDataFreeze.metadata domains [head.verb] (StateScopePool.normalize B) name declaration) = (outputName,result)) :
    (outputName,result) ∈ program.observe := by
  have normalized := StateScopePool.normalize_setEq B
  have sourceEq := decorate_setEq domains [head.verb] normalized declaration (head.bare environment domains)
  have specs := spec_setEq domains [head.verb] (fun act => (normalized act).symm)
  rw [specs] at metadata
  have sameMetadata : program.program.freezes.lookup name =
      (StateNativeDataFreeze.metadata domains [head.verb] (StateScopePool.normalize B) name declaration).lookup name := by
    rw [metadata]
    cases declaration <;> simp [StateNativeDataFreeze.metadata]
  have scope : StateThresholdDispatch.referenceScope B program.program.freezes name =
      StateThresholdDispatch.referenceScope B (StateNativeDataFreeze.metadata domains [head.verb] (StateScopePool.normalize B) name declaration) name := by
    simp only [StateThresholdDispatch.referenceScope,sameMetadata]
  have outputEq : (Output.threshold outputName name query
      (StateNativeDataFreeze.decorate domains [head.verb] B declaration (head.bare environment domains))).observe B program.program.freezes =
        (outputName,result) := by
    rw [← sourceEq]
    simpa only [Output.observe,scope] using observed
  have inProgram : (Output.threshold outputName name query
      (StateNativeDataFreeze.decorate domains [head.verb] B declaration (head.bare environment domains))).observe B program.program.freezes ∈ program.observe := by
    simp only [CompiledObservation.observe,Program.observe,history]
    exact List.mem_map.mpr ⟨_,member,rfl⟩
  simpa only [outputEq] using inProgram

/-- Actual authored count thresholds preserve earlier distinct-count success
or expose a named fault in the complete compiled program. Bound admission,
source policy, output occurrence and freeze identities are all derived. -/
theorem count_program_stability (environment : Environment) (entries : List Entry) (prepared : Prepared)
    (accepted : prepareStatic environment entries = some prepared) (name outputName verb : String) (bound : Nat)
    (present : (name,StateAuthoredBindings.Rule.legacy (.count verb)) ∈ rawFields entries)
    (threshold : Entry.threshold outputName name [.element (.count bound)] ∈ entries)
    (B : List Act) (ranked : StateExecutableFreeze.Ranked B)
    (consistent : ∀ a ∈ B, ∀ b ∈ B, a.addr = b.addr → a = b) :
    ∃ program, compileAuthored environment entries B = some program ∧
      ∀ A : List Act, (∀ act ∈ A, act ∈ B) →
        bound ≤ FinSet.card (FinSet.mk (StateDomainSupportLocality.selected prepared.domains [verb] A)) →
        (outputName,.data (.reached (.element (.count bound)))) ∈ program.observe ∨
          ∃ evidence, (outputName,.fault evidence) ∈ program.observe := by
  obtain ⟨declaration,query,program,compiled,queryCompiled,member,history,metadata⟩ := authored_emitted (.count verb) environment entries prepared
    accepted name outputName present [.element (.count bound)] threshold B ranked consistent
  have admitted : bound < 2^63 := by
    by_cases valid : bound < 2^63
    · exact valid
    · simp [compileQuery,Head.definition,Head.expression,Head.rule,primitive,queryPolicy,readCheck,StateInstalledLegacy.allowed,valid] at queryCompiled
  refine ⟨program,compiled,?_⟩
  intro A growth reached
  obtain ⟨code,codeCompiled,result⟩ := StateNativeDataFreeze.count_success_or_fault environment prepared.domains verb bound admitted A B growth reached
    name outputName declaration (StateScopePool.normalize_ranked B ranked)
  have same : code = query := Option.some.inj (codeCompiled.symm.trans queryCompiled)
  subst code
  rcases result with success | ⟨evidence,fault⟩
  · exact Or.inl (dispatch_member (.count verb) environment prepared.domains B declaration name outputName query program
      member history metadata _ success)
  · exact Or.inr ⟨evidence,dispatch_member (.count verb) environment prepared.domains B declaration name outputName query program
      member history metadata _ fault⟩

/-- Actual authored existence thresholds have the analogous complete-program
stability law, with no detached source or precompiled-output premise. -/
theorem exists_program_stability (environment : Environment) (entries : List Entry) (prepared : Prepared)
    (accepted : prepareStatic environment entries = some prepared) (name outputName verb : String)
    (present : (name,StateAuthoredBindings.Rule.legacy (.existsRule verb)) ∈ rawFields entries)
    (threshold : Entry.threshold outputName name [.element (.scalar (.bool true))] ∈ entries)
    (B : List Act) (ranked : StateExecutableFreeze.Ranked B)
    (consistent : ∀ a ∈ B, ∀ b ∈ B, a.addr = b.addr → a = b) :
    ∃ program, compileAuthored environment entries B = some program ∧
      ∀ A : List Act, (∀ act ∈ A, act ∈ B) →
        (StateDomainSupportLocality.selected prepared.domains [verb] A).isEmpty = false →
        (outputName,.data (.reached (.element (.scalar (.bool true))))) ∈ program.observe ∨
          ∃ evidence, (outputName,.fault evidence) ∈ program.observe := by
  obtain ⟨declaration,query,program,compiled,queryCompiled,member,history,metadata⟩ := authored_emitted (.existsRule verb) environment entries prepared
    accepted name outputName present [.element (.scalar (.bool true))] threshold B ranked consistent
  refine ⟨program,compiled,?_⟩
  intro A growth reached
  obtain ⟨code,codeCompiled,result⟩ := StateNativeDataFreeze.exists_success_or_fault environment prepared.domains verb A B growth reached
    name outputName declaration (StateScopePool.normalize_ranked B ranked)
  have same : code = query := Option.some.inj (codeCompiled.symm.trans queryCompiled)
  subst code
  rcases result with success | ⟨evidence,fault⟩
  · exact Or.inl (dispatch_member (.existsRule verb) environment prepared.domains B declaration name outputName query program
      member history metadata _ success)
  · exact Or.inr ⟨evidence,dispatch_member (.existsRule verb) environment prepared.domains B declaration name outputName query program
      member history metadata _ fault⟩

end CBCL.StateAuthoredDataOutputs
