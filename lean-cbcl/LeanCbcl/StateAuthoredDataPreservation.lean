import LeanCbcl.StateAuthoredDataOutputs

/-! Successive actual authored count/existence observations. Inversion starts
at the unique named emitted output, rather than assuming prior cardinality or
nonempty-source success. Source-owned policy code is recovered from compilation. -/
set_option autoImplicit false
namespace CBCL.StateAuthoredDataPreservation
open State StateLift StateLVar StateObservation StateObservationPlan StateInstalledCompiler
open StateInstalledLegacy StateInstalledLowering StateAuthoredBindings StateOutputCompiler
open StateAuthoredDataProvenance StateAuthoredDataOutputs

/-- Recover the actual observed threshold instruction from a named result in
an actual complete compiled program, using validated observation-name uniqueness. -/
theorem authored_reached (head : Head) (environment : Environment) (entries : List Entry) (prepared : Prepared)
    (accepted : prepareStatic environment entries = some prepared) (name outputName : String)
    (present : (name,StateAuthoredBindings.Rule.legacy head.rule) ∈ rawFields entries) (elements : List Value)
    (threshold : Entry.threshold outputName name elements ∈ entries) (A : List Act)
    (ranked : StateExecutableFreeze.Ranked A) (consistent : ∀ a ∈ A, ∀ b ∈ A, a.addr = b.addr → a = b)
    (program : CompiledObservation) (compiled : compileAuthored environment entries A = some program)
    (result : StateReaderValues.Result Value) (reached : (outputName,result) ∈ program.observe) :
    ∃ declaration query, compileQuery elements (head.definition environment prepared.domains) = some query ∧
      (Output.threshold outputName name query (head.decorate prepared.domains A declaration
        (head.bare environment prepared.domains))).observe A program.program.freezes = (outputName,result) := by
  obtain ⟨declaration,query,built,builtCompiled,queryCompiled,member,history,metadata⟩ := authored_emitted head environment entries prepared
    accepted name outputName present elements threshold A ranked consistent
  have same : program = built := Option.some.inj (compiled.symm.trans builtCompiled)
  subst program
  let output := Output.threshold outputName name query (head.decorate prepared.domains A declaration
    (head.bare environment prepared.domains))
  have inProgram : output.observe A built.program.freezes ∈ built.observe := by
    simp only [CompiledObservation.observe,Program.observe,history]
    exact List.mem_map.mpr ⟨output,member,rfl⟩
  have named : (outputName,(output.observe A built.program.freezes).2) = output.observe A built.program.freezes := rfl
  have namedMember : (outputName,(output.observe A built.program.freezes).2) ∈ built.observe := by rw [named]; exact inProgram
  have names := StateAuthoredFinitePreservation.authored_output_names_unique environment entries prepared accepted A built builtCompiled
  have first := StateReaderReachability.lookup_original built.observe names outputName _ reached
  have second := StateReaderReachability.lookup_original built.observe names outputName _ namedMember
  have equal := Option.some.inj (second.symm.trans first)
  exact ⟨declaration,query,queryCompiled,named.symm.trans (congrArg (outputName, ·) equal)⟩

/-- Raw dispatch scopes are contained in the actual accepted history. -/
theorem raw_inside (whole : List Act) (freezes : List (String × FreezeSpec)) (name : String) :
    ∀ act ∈ StateThresholdDispatch.referenceScope whole freezes name, act ∈ whole := by
  intro act member
  exact (StateScopePool.normalize_setEq whole act).mp (StateCompiledFiniteInversion.scope_inside whole freezes name act member)

/-- Count admission is recovered from the actual source-owned query compiler. -/
theorem count_admitted (environment : Environment) (domains : List StateInstalledDomains.Domain) (verb : String) (bound : Nat)
    (query : Query Value) (compiled : compileQuery [.element (.count bound)] ((Head.count verb).definition environment domains) = some query) :
    bound < 2^63 := by
  by_cases valid : bound < 2^63
  · exact valid
  · simp [compileQuery,Head.definition,Head.expression,Head.rule,primitive,queryPolicy,readCheck,StateInstalledLegacy.allowed,valid] at compiled

/-- An actual earlier compiled reached count implies its native distinct-count
predicate over the full accepted set, including when it read a smaller cut. -/
theorem count_native (environment : Environment) (entries : List Entry) (prepared : Prepared)
    (accepted : prepareStatic environment entries = some prepared) (name outputName verb : String) (bound : Nat)
    (present : (name,StateAuthoredBindings.Rule.legacy (.count verb)) ∈ rawFields entries)
    (threshold : Entry.threshold outputName name [.element (.count bound)] ∈ entries)
    (A : List Act) (ranked : StateExecutableFreeze.Ranked A)
    (consistent : ∀ a ∈ A, ∀ b ∈ A, a.addr = b.addr → a = b)
    (program : CompiledObservation) (compiled : compileAuthored environment entries A = some program)
    (reached : (outputName,.data (.reached (.element (.count bound)))) ∈ program.observe) :
    bound ≤ FinSet.card (FinSet.mk (StateDomainSupportLocality.selected prepared.domains [verb] A)) := by
  obtain ⟨declaration,query,queryCompiled,observed⟩ := authored_reached (.count verb) environment entries prepared accepted name outputName
    present [.element (.count bound)] threshold A ranked consistent program compiled _ reached
  obtain ⟨code,codeCompiled,run⟩ := StateNativeDataPolicies.compiled_count environment prepared.domains verb bound
    (count_admitted environment prepared.domains verb bound query queryCompiled)
  have same : code = query := Option.some.inj (codeCompiled.symm.trans queryCompiled)
  subst code
  have result := congrArg Prod.snd observed
  let raw := StateThresholdDispatch.referenceScope A program.program.freezes name
  let source := sourceValue A (StateNativeDataFreeze.decorate prepared.domains [verb] A declaration
    ((Head.count verb).bare environment prepared.domains))
  change query.run raw source = .data (.reached (.element (.count bound))) at result
  cases dataResult : source with
  | fault evidence => simp only [dataResult,StateNativeDataFreeze.query_fault] at result; contradiction
  | data payload =>
    rw [dataResult,run] at result
    have enough : bound ≤ FinSet.card (FinSet.mk (StateDomainSupportLocality.selected prepared.domains [verb] raw)) := by
      by_cases condition : bound ≤ FinSet.card (FinSet.mk (StateDomainSupportLocality.selected prepared.domains [verb] raw))
      · exact condition
      · simp [condition] at result
    exact Nat.le_trans enough (StateNativeDataPolicies.count_grows prepared.domains [verb] (raw_inside A program.program.freezes name))

/-- An actual earlier compiled existence success similarly recovers a witness
in the full accepted source selection, without a nonempty-source premise. -/
theorem exists_native (environment : Environment) (entries : List Entry) (prepared : Prepared)
    (accepted : prepareStatic environment entries = some prepared) (name outputName verb : String)
    (present : (name,StateAuthoredBindings.Rule.legacy (.existsRule verb)) ∈ rawFields entries)
    (threshold : Entry.threshold outputName name [.element (.scalar (.bool true))] ∈ entries)
    (A : List Act) (ranked : StateExecutableFreeze.Ranked A)
    (consistent : ∀ a ∈ A, ∀ b ∈ A, a.addr = b.addr → a = b)
    (program : CompiledObservation) (compiled : compileAuthored environment entries A = some program)
    (reached : (outputName,.data (.reached (.element (.scalar (.bool true))))) ∈ program.observe) :
    (StateDomainSupportLocality.selected prepared.domains [verb] A).isEmpty = false := by
  obtain ⟨declaration,query,queryCompiled,observed⟩ := authored_reached (.existsRule verb) environment entries prepared accepted name outputName
    present [.element (.scalar (.bool true))] threshold A ranked consistent program compiled _ reached
  obtain ⟨code,codeCompiled,run⟩ := StateNativeDataPolicies.compiled_exists environment prepared.domains verb
  have same : code = query := Option.some.inj (codeCompiled.symm.trans queryCompiled)
  subst code
  have result := congrArg Prod.snd observed
  let raw := StateThresholdDispatch.referenceScope A program.program.freezes name
  let source := sourceValue A (StateNativeDataFreeze.decorate prepared.domains [verb] A declaration
    ((Head.existsRule verb).bare environment prepared.domains))
  change query.run raw source = .data (.reached (.element (.scalar (.bool true)))) at result
  cases dataResult : source with
  | fault evidence => simp only [dataResult,StateNativeDataFreeze.query_fault] at result; contradiction
  | data payload =>
    rw [dataResult,run] at result
    have nonempty : (StateDomainSupportLocality.selected prepared.domains [verb] raw).isEmpty = false := by
      cases empty : (StateDomainSupportLocality.selected prepared.domains [verb] raw).isEmpty with
      | false => rfl
      | true => simp [empty] at result
    obtain ⟨act,member⟩ := List.isEmpty_eq_false_iff_exists_mem.mp nonempty
    exact List.isEmpty_eq_false_iff_exists_mem.mpr ⟨act,StateDomainSupportLocality.selected_grows prepared.domains [verb]
      (raw_inside A program.program.freezes name) act member⟩

/-- Native count success is preserved between actual authored compiled programs. -/
theorem count_successive (environment : Environment) (entries : List Entry) (prepared : Prepared)
    (accepted : prepareStatic environment entries = some prepared) (name outputName verb : String) (bound : Nat)
    (present : (name,StateAuthoredBindings.Rule.legacy (.count verb)) ∈ rawFields entries)
    (threshold : Entry.threshold outputName name [.element (.count bound)] ∈ entries)
    (A B : List Act) (growth : ∀ act ∈ A, act ∈ B)
    (rankedA : StateExecutableFreeze.Ranked A) (rankedB : StateExecutableFreeze.Ranked B)
    (consistentA : ∀ a ∈ A, ∀ b ∈ A, a.addr = b.addr → a = b)
    (consistentB : ∀ a ∈ B, ∀ b ∈ B, a.addr = b.addr → a = b)
    (earlier later : CompiledObservation) (compiledA : compileAuthored environment entries A = some earlier)
    (compiledB : compileAuthored environment entries B = some later)
    (reached : (outputName,.data (.reached (.element (.count bound)))) ∈ earlier.observe) :
    (outputName,.data (.reached (.element (.count bound)))) ∈ later.observe ∨ ∃ evidence, (outputName,.fault evidence) ∈ later.observe := by
  have native := count_native environment entries prepared accepted name outputName verb bound present threshold A rankedA consistentA earlier compiledA reached
  obtain ⟨program,compiled,stable⟩ := count_program_stability environment entries prepared accepted name outputName verb bound present threshold B rankedB consistentB
  have same : program = later := Option.some.inj (compiled.symm.trans compiledB)
  simpa only [same] using stable A growth native

/-- Native existence success is preserved between actual authored compiled programs. -/
theorem exists_successive (environment : Environment) (entries : List Entry) (prepared : Prepared)
    (accepted : prepareStatic environment entries = some prepared) (name outputName verb : String)
    (present : (name,StateAuthoredBindings.Rule.legacy (.existsRule verb)) ∈ rawFields entries)
    (threshold : Entry.threshold outputName name [.element (.scalar (.bool true))] ∈ entries)
    (A B : List Act) (growth : ∀ act ∈ A, act ∈ B)
    (rankedA : StateExecutableFreeze.Ranked A) (rankedB : StateExecutableFreeze.Ranked B)
    (consistentA : ∀ a ∈ A, ∀ b ∈ A, a.addr = b.addr → a = b)
    (consistentB : ∀ a ∈ B, ∀ b ∈ B, a.addr = b.addr → a = b)
    (earlier later : CompiledObservation) (compiledA : compileAuthored environment entries A = some earlier)
    (compiledB : compileAuthored environment entries B = some later)
    (reached : (outputName,.data (.reached (.element (.scalar (.bool true))))) ∈ earlier.observe) :
    (outputName,.data (.reached (.element (.scalar (.bool true))))) ∈ later.observe ∨ ∃ evidence, (outputName,.fault evidence) ∈ later.observe := by
  have native := exists_native environment entries prepared accepted name outputName verb present threshold A rankedA consistentA earlier compiledA reached
  obtain ⟨program,compiled,stable⟩ := exists_program_stability environment entries prepared accepted name outputName verb present threshold B rankedB consistentB
  have same : program = later := Option.some.inj (compiled.symm.trans compiledB)
  simpa only [same] using stable A growth native

end CBCL.StateAuthoredDataPreservation
