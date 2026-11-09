import LeanCbcl.StateCompiledFiniteInversion

/-! Preservation between successive actual authored compiled observations.
Earlier success is read from the complete emitted observation vector; no native
success, source-policy lookup or threshold occurrence is assumed. -/
namespace CBCL.StateAuthoredFinitePreservation
open State StateLift StateLVar StateObservation StateObservationPlan StateInstalledCompiler
open StateInstalledLowering StateOutputCompiler StateAuthoredBindings StateAuthoredSourceProvenance
open StateCompiledFiniteInversion

/-- Invert the named reached result of a complete actual authored program.
Validated output names identify the emitted finite threshold, whose native
full-history success is then recovered through its observed source guards. -/
theorem authored_reached_native (environment : Environment) (entries : List Entry) (prepared : Prepared)
    (accepted : prepareStatic environment entries = some prepared)
    (name lattice : String) (declaration : StateInstalledFinite.Declaration)
    (present : (name,StateAuthoredBindings.Rule.finite lattice declaration) ∈ rawFields entries)
    (outputName : String) (queries : List Val)
    (threshold : Entry.threshold outputName name (queries.map (fun q => .element (.scalar q))) ∈ entries)
    (A : List Act) (ranked : StateExecutableFreeze.Ranked A)
    (consistent : ∀ a ∈ A, ∀ b ∈ A, a.addr = b.addr → a = b)
    (program : CompiledObservation) (compiledProgram : compileAuthored environment entries A = some program)
    (query : Val) (reached : (outputName,.data (.reached (.element (.scalar query)))) ∈ program.observe) :
    ∃ field, Declaration.field name (StateFiniteRead.definition field) ∈ prepared.declarations ∧
      query ∈ queries ∧ StateFiniteRead.test field query (StateInstalledFinite.state field A) = true := by
  have preparedAt : prepare environment entries A = some (clauseAt prepared A) := by simp [prepare,accepted,clauseAt]
  obtain ⟨field,freezeDeclaration,sourcePlans,sourceCompiled,lookup,metadata,declared⟩ := authored_finite_plan
    environment entries prepared accepted name lattice declaration present outputName
    (queries.map (fun q => .element (.scalar q))) threshold A
  obtain ⟨plans,fields,code,compiled,resolved,codeCompiled,values,after,ran,adapted⟩ :=
    prepared_compiler_cache_refinement environment entries A (clauseAt prepared A) preparedAt ranked consistent
  have samePlans : sourcePlans = plans := Option.some.inj (sourceCompiled.symm.trans compiled)
  subst sourcePlans
  have sourceLowered : StateInstalledLowering.compile (clauseAt prepared A) = some plans := by
    simpa only [StateAuthoredBindings.compile,preparedAt,Option.bind_some] using compiled
  let actual : CompiledObservation := ⟨A,⟨(clauseAt prepared A).freezes,code⟩⟩
  have actualCompiled : compileAuthored environment entries A = some actual := by
    simp [compileAuthored,preparedAt,StateOutputCompiler.compileClause,sourceLowered,codeCompiled,actual]
  have programEq : program = actual := Option.some.inj (compiledProgram.symm.trans actualCompiled)
  rw [programEq] at reached
  change (outputName,.data (.reached (.element (.scalar query)))) ∈ code.map (Output.observe A (clauseAt prepared A).freezes) at reached
  obtain ⟨resolvedTables,bindings,_,_,declResult,_⟩ := static_trace environment entries prepared accepted
  have loweredThreshold := declaration_threshold environment prepared.domains resolvedTables entries [] prepared.declarations
    bindings declResult outputName name (queries.map (fun q => .element (.scalar q))) threshold
  have unique := (static_preparation_sound environment entries prepared accepted A).1.1
  obtain ⟨priorDefinitions,output,origins,member,emitted⟩ := StateAuthoredOutputProvenance.emitted_origin
    plans prepared.declarations prepared.declarations [] code
    (by intro source definition impossible; simp at impossible) (fun _ inside => inside) codeCompiled _ loweredThreshold
  obtain ⟨_,outputEq⟩ := StateAuthoredOutputProvenance.finite_emitted plans prepared.declarations unique field name outputName queries
    declared priorDefinitions origins _ lookup output emitted
  let observations := code.map (Output.observe A (clauseAt prepared A).freezes)
  have names : (observations.map Prod.fst).Nodup := by
    rw [show observations.map Prod.fst = code.map nameOf from observed_names code A (clauseAt prepared A).freezes,
      compiled_names plans [] prepared.declarations code codeCompiled]
    exact unique
  have named : (outputName,(output.observe A (clauseAt prepared A).freezes).2) = output.observe A (clauseAt prepared A).freezes := by
    rw [outputEq]
    rfl
  have outputMember : (outputName,(output.observe A (clauseAt prepared A).freezes).2) ∈ observations := by
    rw [named]
    exact List.mem_map.mpr ⟨output,member,rfl⟩
  have first := StateReaderReachability.lookup_original observations names outputName _ reached
  have second := StateReaderReachability.lookup_original observations names outputName _ outputMember
  have result := Option.some.inj (second.symm.trans first)
  have actualReached : output.observe A (clauseAt prepared A).freezes =
      (outputName,.data (.reached (.element (.scalar query)))) := named.symm.trans (congrArg (outputName, ·) result)
  rw [outputEq] at actualReached
  obtain ⟨queryMember,native⟩ := output_native_success field queries query A (clauseAt prepared A).freezes freezeDeclaration name outputName actualReached
  exact ⟨field,declared,queryMember,native⟩

/-- A finite threshold reached in an earlier actual authored compiled program
stays the same named reached result or exposes a named fault in every later
actual compiled observation of the same prepared dialect after accepted growth. -/
theorem successive_compiled (environment : Environment) (entries : List Entry) (prepared : Prepared)
    (accepted : prepareStatic environment entries = some prepared)
    (name lattice : String) (declaration : StateInstalledFinite.Declaration)
    (present : (name,StateAuthoredBindings.Rule.finite lattice declaration) ∈ rawFields entries)
    (outputName : String) (queries : List Val)
    (threshold : Entry.threshold outputName name (queries.map (fun q => .element (.scalar q))) ∈ entries)
    (A B : List Act) (growth : ∀ act ∈ A, act ∈ B)
    (rankedA : StateExecutableFreeze.Ranked A) (rankedB : StateExecutableFreeze.Ranked B)
    (consistentA : ∀ a ∈ A, ∀ b ∈ A, a.addr = b.addr → a = b)
    (consistentB : ∀ a ∈ B, ∀ b ∈ B, a.addr = b.addr → a = b)
    (earlier later : CompiledObservation)
    (compiledA : compileAuthored environment entries A = some earlier)
    (compiledB : compileAuthored environment entries B = some later)
    (query : Val) (reached : (outputName,.data (.reached (.element (.scalar query)))) ∈ earlier.observe) :
    (outputName,.data (.reached (.element (.scalar query)))) ∈ later.observe ∨
      ∃ evidence, (outputName,.fault evidence) ∈ later.observe := by
  obtain ⟨fieldA,declaredA,queryMember,native⟩ := authored_reached_native environment entries prepared accepted name lattice declaration
    present outputName queries threshold A rankedA consistentA earlier compiledA query reached
  obtain ⟨fieldB,program,compiled,declaredB,_,stable⟩ := StateAuthoredFiniteStability.authored_program_stability
    environment entries prepared accepted name lattice declaration present outputName queries threshold B rankedB consistentB
  have unique := (static_preparation_sound environment entries prepared accepted B).1.1
  have same := StateAuthoredOutputProvenance.unique_definition prepared.declarations unique name
    (StateFiniteRead.definition fieldA) (StateFiniteRead.definition fieldB) declaredA declaredB
  have nativeB : StateFiniteRead.test fieldB query (StateInstalledFinite.state fieldB A) = true := by
    rw [← definition_tests fieldA fieldB same query A]
    exact native
  have result := stable A query growth queryMember nativeB
  have sameProgram : program = later := Option.some.inj (compiled.symm.trans compiledB)
  simpa only [sameProgram] using result

/-- Every successfully compiled authored observation retains the validated
shared namespace, independently of the source values or freeze-root selection. -/
theorem authored_output_names_unique (environment : Environment) (entries : List Entry) (prepared : Prepared)
    (accepted : prepareStatic environment entries = some prepared) (history : List Act)
    (program : CompiledObservation) (compiled : compileAuthored environment entries history = some program) :
    (program.observe.map Prod.fst).Nodup := by
  have preparedAt : prepare environment entries history = some (clauseAt prepared history) := by
    simp [prepare,accepted,clauseAt]
  cases sources : StateInstalledLowering.compile (clauseAt prepared history) with
  | none => simp [compileAuthored,preparedAt,StateOutputCompiler.compileClause,sources] at compiled
  | some plans =>
    cases codeResult : compileDeclarations plans [] prepared.declarations with
    | none => simp [compileAuthored,preparedAt,StateOutputCompiler.compileClause,sources,show (clauseAt prepared history).declarations = prepared.declarations from rfl,codeResult] at compiled
    | some code =>
      have same : (⟨history,⟨(clauseAt prepared history).freezes,code⟩⟩ : CompiledObservation) = program := by
        simpa [compileAuthored,preparedAt,StateOutputCompiler.compileClause,sources,show (clauseAt prepared history).declarations = prepared.declarations from rfl,codeResult] using compiled
      cases same
      change ((code.map (Output.observe history (clauseAt prepared history).freezes)).map Prod.fst).Nodup
      rw [observed_names,compiled_names plans [] prepared.declarations code codeResult]
      exact (static_preparation_sound environment entries prepared accepted history).1.1

/-- Actual compiled finite observations reaching distinct alternatives cannot
be combined into a healthy compiled observation. Any ranked content-consistent
joint history containing both accepted sets exposes a named threshold fault. -/
theorem quasi_determinism (environment : Environment) (entries : List Entry) (prepared : Prepared)
    (accepted : prepareStatic environment entries = some prepared)
    (name lattice : String) (declaration : StateInstalledFinite.Declaration)
    (present : (name,StateAuthoredBindings.Rule.finite lattice declaration) ∈ rawFields entries)
    (outputName : String) (queries : List Val)
    (threshold : Entry.threshold outputName name (queries.map (fun q => .element (.scalar q))) ∈ entries)
    (A B C : List Act) (growthA : ∀ act ∈ A, act ∈ C) (growthB : ∀ act ∈ B, act ∈ C)
    (rankedA : StateExecutableFreeze.Ranked A) (rankedB : StateExecutableFreeze.Ranked B) (rankedC : StateExecutableFreeze.Ranked C)
    (consistentA : ∀ a ∈ A, ∀ b ∈ A, a.addr = b.addr → a = b)
    (consistentB : ∀ a ∈ B, ∀ b ∈ B, a.addr = b.addr → a = b)
    (consistentC : ∀ a ∈ C, ∀ b ∈ C, a.addr = b.addr → a = b)
    (left right joint : CompiledObservation)
    (compiledA : compileAuthored environment entries A = some left)
    (compiledB : compileAuthored environment entries B = some right)
    (compiledC : compileAuthored environment entries C = some joint)
    (queryA queryB : Val) (different : queryA ≠ queryB)
    (reachedA : (outputName,.data (.reached (.element (.scalar queryA)))) ∈ left.observe)
    (reachedB : (outputName,.data (.reached (.element (.scalar queryB)))) ∈ right.observe) :
    ∃ evidence, (outputName,.fault evidence) ∈ joint.observe := by
  have first := successive_compiled environment entries prepared accepted name lattice declaration present outputName queries threshold
    A C growthA rankedA rankedC consistentA consistentC left joint compiledA compiledC queryA reachedA
  have second := successive_compiled environment entries prepared accepted name lattice declaration present outputName queries threshold
    B C growthB rankedB rankedC consistentB consistentC right joint compiledB compiledC queryB reachedB
  rcases first with successA | fault
  · rcases second with successB | fault
    · have unique := authored_output_names_unique environment entries prepared accepted C joint compiledC
      have a := StateReaderReachability.lookup_original joint.observe unique outputName _ successA
      have b := StateReaderReachability.lookup_original joint.observe unique outputName _ successB
      have values := Option.some.inj (a.symm.trans b)
      have equal : queryA = queryB := by simpa using values
      exact False.elim (different equal)
    · exact fault
  · exact fault

end CBCL.StateAuthoredFinitePreservation
