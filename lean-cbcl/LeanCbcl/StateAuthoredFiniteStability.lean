import LeanCbcl.StateAuthoredOutputProvenance

/-! Authored finite thresholds reach the complete actual compiled program.
Preparation supplies factory identity, source guards, freeze metadata and the
prefix-owned query policy. No successful code walk or policy admission is a
premise. Prior success below refers to the recovered field's native finite test. -/
namespace CBCL.StateAuthoredFiniteStability
open State StateLift StateLVar StateObservation StateObservationPlan StateInstalledCompiler
open StateInstalledLowering StateOutputCompiler StateAuthoredBindings StateAuthoredSourceProvenance

/-- Freeze specialization depends on the accepted set, not its delivery list. -/
theorem freeze_spec_setEq (field : StateInstalledFinite.Field) {A B : List Act} (same : SetEq A B) (verb : String) :
    StateFiniteFreezePolicy.freezeSpec field A verb = StateFiniteFreezePolicy.freezeSpec field B verb := by
  simp only [StateFiniteFreezePolicy.freezeSpec,contributes_setEq field.domains same]

/-- The emitted source plan retains the same global contribution predicate
when the output adapter normalizes duplicate deliveries. -/
theorem source_setEq (field : StateInstalledFinite.Field) {A B : List Act} (same : SetEq A B) (declaration : Option String) :
    StateFiniteOutputStability.source field A declaration = StateFiniteOutputStability.source field B declaration := by
  cases declaration with
  | none => rfl
  | some verb => simp only [StateFiniteOutputStability.source,StateFiniteFreezePolicy.frozenPlan,freeze_spec_setEq field same]

/-- For any successfully prepared authored finite threshold, recover its
actual source and construct the complete compiled program. Every earlier native
finite success persists as the same named output or a named fault after growth,
for all freeze-root outcomes. The output is a member of the actual program's
observation vector, not a separately constructed one-declaration execution. -/
theorem authored_program_stability (environment : Environment) (entries : List Entry) (prepared : Prepared)
    (accepted : prepareStatic environment entries = some prepared)
    (name lattice : String) (declaration : StateInstalledFinite.Declaration)
    (present : (name,StateAuthoredBindings.Rule.finite lattice declaration) ∈ rawFields entries)
    (outputName : String) (queries : List Val)
    (threshold : Entry.threshold outputName name (queries.map (fun q => .element (.scalar q))) ∈ entries)
    (B : List Act) (ranked : StateExecutableFreeze.Ranked B)
    (consistent : ∀ a ∈ B, ∀ b ∈ B, a.addr = b.addr → a = b) :
    ∃ field program,
      compileAuthored environment entries B = some program ∧
      Declaration.field name (StateFiniteRead.definition field) ∈ prepared.declarations ∧
      StateFiniteRead.check field queries = true ∧
      ∀ (A : List Act) (query : Val), (∀ act ∈ A, act ∈ B) → query ∈ queries →
        StateFiniteRead.test field query (StateInstalledFinite.state field A) = true →
        (outputName,.data (.reached (.element (.scalar query)))) ∈ program.observe ∨
          ∃ evidence, (outputName,.fault evidence) ∈ program.observe := by
  have preparedAt : prepare environment entries B = some (clauseAt prepared B) := by
    simp [prepare,accepted,clauseAt]
  obtain ⟨field,freezeDeclaration,sourcePlans,sourceCompiled,lookup,metadata,declared⟩ := authored_finite_plan
    environment entries prepared accepted name lattice declaration present outputName
    (queries.map (fun q => .element (.scalar q))) threshold B
  obtain ⟨plans,fields,code,compiled,resolved,codeCompiled,values,after,ran,adapted⟩ :=
    prepared_compiler_cache_refinement environment entries B (clauseAt prepared B) preparedAt ranked consistent
  have samePlans : sourcePlans = plans := Option.some.inj (sourceCompiled.symm.trans compiled)
  subst sourcePlans
  obtain ⟨resolvedTables,bindings,_,_,declResult,_⟩ := static_trace environment entries prepared accepted
  have loweredThreshold := declaration_threshold environment prepared.domains resolvedTables entries [] prepared.declarations
    bindings declResult outputName name (queries.map (fun q => .element (.scalar q))) threshold
  have unique := (static_preparation_sound environment entries prepared accepted B).1.1
  obtain ⟨priorDefinitions,output,origins,member,emitted⟩ := StateAuthoredOutputProvenance.emitted_origin
    plans prepared.declarations prepared.declarations [] code
    (by intro source definition impossible; simp at impossible) (fun _ inside => inside) codeCompiled
    _ loweredThreshold
  have normalized := StateScopePool.normalize_setEq B
  have sourceEqual := source_setEq field normalized freezeDeclaration
  rw [← sourceEqual] at lookup
  obtain ⟨checked,outputEq⟩ := StateAuthoredOutputProvenance.finite_emitted plans prepared.declarations unique field name
    outputName queries declared priorDefinitions origins _ lookup output emitted
  have compiledSources : StateInstalledLowering.compile (clauseAt prepared B) = some plans := by
    simpa only [StateAuthoredBindings.compile,preparedAt,Option.bind_some] using compiled
  let program : CompiledObservation := ⟨B,⟨(clauseAt prepared B).freezes,code⟩⟩
  have programCompiled : compileAuthored environment entries B = some program := by
    simp [compileAuthored,preparedAt,StateOutputCompiler.compileClause,compiledSources,codeCompiled,program]
  refine ⟨field,program,programCompiled,declared,checked,?_⟩
  intro A query growth queryMember reached
  obtain ⟨queryCode,queryCompiled,result⟩ := StateFiniteOutputStability.output_success_or_fault field queries query checked
    queryMember A B growth reached freezeDeclaration name outputName (StateScopePool.normalize_ranked B ranked)
  have queryEq : queryCode = .raw (queries.map (fun q => .element (.scalar q))) (StateFiniteRead.policy field).test
      (StateInstalledFinite.term field).state :=
    Option.some.inj (queryCompiled.symm.trans (StateFiniteFreezePolicy.compiled_alternatives field queries checked))
  have specEqual : StateFiniteFreezePolicy.freezeSpec field B =
      StateFiniteFreezePolicy.freezeSpec field (StateScopePool.normalize B) :=
    funext (fun verb => freeze_spec_setEq field (fun act => (normalized act).symm) verb)
  rw [specEqual] at metadata
  have sameMetadata : (clauseAt prepared B).freezes.lookup name =
      (StateFiniteOutputStability.freezes field (StateScopePool.normalize B) name freezeDeclaration).lookup name := by
    change (materialize prepared.domains B prepared.freezes).lookup name = _
    rw [metadata]
    cases freezeDeclaration <;> simp [StateFiniteOutputStability.freezes]
  have scope : StateThresholdDispatch.referenceScope B (clauseAt prepared B).freezes name =
      StateThresholdDispatch.referenceScope B (StateFiniteOutputStability.freezes field (StateScopePool.normalize B) name freezeDeclaration) name := by
    simp only [StateThresholdDispatch.referenceScope,sameMetadata]
  have sameOutput : output.observe B (clauseAt prepared B).freezes =
      (Output.threshold outputName name queryCode (StateFiniteOutputStability.source field (StateScopePool.normalize B) freezeDeclaration)).observe B
        (StateFiniteOutputStability.freezes field (StateScopePool.normalize B) name freezeDeclaration) := by
    simp only [outputEq,queryEq,Output.observe,scope]
  have inProgram : output.observe B (clauseAt prepared B).freezes ∈ program.observe :=
    List.mem_map.mpr ⟨output,member,rfl⟩
  rcases result with success | ⟨evidence,fault⟩
  · rw [sameOutput,success] at inProgram
    exact Or.inl inProgram
  · rw [sameOutput,fault] at inProgram
    exact Or.inr ⟨evidence,inProgram⟩

end CBCL.StateAuthoredFiniteStability
