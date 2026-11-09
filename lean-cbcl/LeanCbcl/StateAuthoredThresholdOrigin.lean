import LeanCbcl.StateOutputQueryIdentity
import LeanCbcl.StateAuthoredFinitePreservation

/-! Invert successful named thresholds of complete authored programs to their
actual source-owned policy and captured source plan. -/
set_option autoImplicit false
namespace CBCL.StateAuthoredThresholdOrigin
open State StateLift StateObservation StateObservationPlan StateOutputCompiler
open StateAuthoredBindings StateInstalledLowering StateInstalledLegacy StateAuthoredSourceProvenance

/-- Actual named threshold success retains its original definition, query code,
and captured source plan; no policy/source correspondence is assumed. -/
theorem reached_origin (environment : Environment) (entries : List Entry) (prepared : Prepared)
    (accepted : prepareStatic environment entries = some prepared)
    (outputName sourceName : String) (elements : List Value)
    (threshold : Entry.threshold outputName sourceName elements ∈ entries)
    (A : List Act) (program : CompiledObservation)
    (compiled : compileAuthored environment entries A = some program)
    (result : Value) (reached : (outputName,.data (.reached result)) ∈ program.observe) :
    ∃ definition query source,
      Declaration.field sourceName definition ∈ prepared.declarations ∧
      compileQuery elements definition = some query ∧
      Output.threshold outputName sourceName query source ∈ program.program.outputs ∧
      query.run (StateThresholdDispatch.referenceScope A program.program.freezes sourceName)
        (sourceValue A source) = .data (.reached result) := by
  obtain ⟨other,plans,code,installed,_,instructions,history,body⟩ :=
    StateAuthoredOutputReplay.compile_authored_parts environment entries A program compiled
  have same : prepared = other := Option.some.inj (accepted.symm.trans installed)
  subst other
  obtain ⟨tables,bindings,_,_,declarations,_⟩ := static_trace environment entries prepared accepted
  have declared := declaration_threshold environment prepared.domains tables entries [] prepared.declarations
    bindings declarations outputName sourceName elements threshold
  obtain ⟨prior,output,origins,member,emitted⟩ := StateAuthoredOutputProvenance.emitted_origin
    plans prepared.declarations prepared.declarations [] code
    (by intro name definition impossible; simp at impossible) (fun _ inside => inside) instructions _ declared
  cases sourceFound : plans.lookup sourceName with
  | none => simp [compileOne,sourceFound] at emitted
  | some source =>
    cases definitionFound : prior.lookup sourceName with
    | none => simp [compileOne,sourceFound,definitionFound] at emitted
    | some definition =>
      cases queryFound : compileQuery elements definition with
      | none => simp [compileOne,sourceFound,definitionFound,queryFound] at emitted
      | some query =>
        have outputEq : Output.threshold outputName sourceName query source = output := by
          simpa [compileOne,sourceFound,definitionFound,queryFound] using emitted
        subst output
        have field : Declaration.field sourceName definition ∈ prepared.declarations := by
          obtain ⟨before,after,equal,_⟩ := List.lookup_eq_some_iff.mp definitionFound
          exact origins sourceName definition (by simp [equal])
        have actualMember : Output.threshold outputName sourceName query source ∈ program.program.outputs := by
          simpa [body] using member
        have observed : (outputName,query.run
            (StateThresholdDispatch.referenceScope A program.program.freezes sourceName) (sourceValue A source)) ∈ program.observe := by
          rw [CompiledObservation.observe,history,Program.observe]
          exact List.mem_map.mpr ⟨_,actualMember,rfl⟩
        have unique := StateAuthoredFinitePreservation.authored_output_names_unique environment entries prepared accepted A program compiled
        have first := StateReaderReachability.lookup_original program.observe unique outputName _ reached
        have second := StateReaderReachability.lookup_original program.observe unique outputName _ observed
        exact ⟨definition,query,source,field,queryFound,actualMember,Option.some.inj (second.symm.trans first)⟩

/-- Every successful actual authored threshold returns an authored alternative. -/
theorem reached_member (environment : Environment) (entries : List Entry) (prepared : Prepared)
    (accepted : prepareStatic environment entries = some prepared)
    (outputName sourceName : String) (elements : List Value)
    (threshold : Entry.threshold outputName sourceName elements ∈ entries)
    (A : List Act) (program : CompiledObservation)
    (compiled : compileAuthored environment entries A = some program)
    (result : Value) (reached : (outputName,.data (.reached result)) ∈ program.observe) : result ∈ elements := by
  obtain ⟨definition,query,source,declared,queryCompiled,_,success⟩ :=
    reached_origin environment entries prepared accepted outputName sourceName elements threshold A program compiled result reached
  have plain := StateAuthoredOutputReplay.prepared_declarations_plain environment entries prepared accepted _ declared
  exact StateOutputThresholdAgreement.reached_member query elements
    (StateThresholdDispatch.referenceScope A program.program.freezes sourceName) (sourceValue A source) result
    (StateOutputThresholdAgreement.compiled_alternatives definition elements query plain queryCompiled) success

/-- Decoding a finite alternative preserves its exact authored scalar wrapper. -/
theorem decode_inverse (value : Value) (scalar : Val) (decoded : StateFiniteRead.decode value = some scalar) :
    value = .element (.scalar scalar) := by
  cases value <;> simp_all [StateFiniteRead.decode]
  rename_i element
  cases element <;> simp_all [StateFiniteRead.decode]

/-- A successful finite alternative walk contains only the encoded scalars. -/
theorem decode_list_inverse (elements : List Value) (queries : List Val)
    (decoded : elements.mapM StateFiniteRead.decode = some queries) :
    elements = queries.map (fun query => .element (.scalar query)) := by
  induction elements generalizing queries with
  | nil => simpa using decoded.symm
  | cons element rest ih =>
    cases head : StateFiniteRead.decode element with
    | none => simp [List.mapM_cons,head] at decoded
    | some scalar =>
      cases tail : rest.mapM StateFiniteRead.decode with
      | none => simp [List.mapM_cons,head,tail] at decoded
      | some more =>
        have same : scalar::more = queries := by simpa [List.mapM_cons,head,tail] using decoded
        subst queries
        rw [decode_inverse element scalar head,ih more tail,List.map_cons]

/-- The actual policy of an authored threshold is singleton or belongs to its
original finite source rule, retaining the concrete finite factory. -/
theorem source_policy (environment : Environment) (entries : List Entry) (prepared : Prepared)
    (accepted : prepareStatic environment entries = some prepared)
    (outputName sourceName : String) (elements : List Value)
    (threshold : Entry.threshold outputName sourceName elements ∈ entries)
    (rule : StateAuthoredBindings.Rule) (present : (sourceName,rule) ∈ rawFields entries)
    (A : List Act) (program : CompiledObservation)
    (compiled : compileAuthored environment entries A = some program)
    (result : Value) (reached : (outputName,.data (.reached result)) ∈ program.observe) :
    (∃ element, elements = [.element element]) ∨
      ∃ (lattice : String) (declaration : StateInstalledFinite.Declaration)
        (field : StateInstalledFinite.Field) (queries : List Val),
        rule = .finite lattice declaration ∧
        elements = queries.map (fun query => .element (.scalar query)) ∧
        Declaration.field sourceName (StateFiniteRead.definition field) ∈ prepared.declarations := by
  obtain ⟨definition,query,_,declared,queryCompiled,_,_⟩ :=
    reached_origin environment entries prepared accepted outputName sourceName elements threshold A program compiled result reached
  obtain ⟨tables,bindings,_,_,declarations,_⟩ := static_trace environment entries prepared accepted
  obtain ⟨prior,binding,bound,fieldDeclared⟩ := declaration_origin environment prepared.domains tables entries []
    prepared.declarations bindings declarations sourceName rule present
  have unique := (static_preparation_sound environment entries prepared accepted A).1.1
  have same := StateAuthoredOutputProvenance.unique_definition prepared.declarations unique sourceName
    binding.definition definition fieldDeclared declared
  have actualQuery : compileQuery elements binding.definition = some query := by rw [same]; exact queryCompiled
  rcases StateOutputThresholdAgreement.bind_query_classification environment prepared.domains tables prior rule binding bound with
    singleton | ⟨lattice,declaration,field,ruleEq,definitionEq⟩
  · exact Or.inl (singleton elements query actualQuery)
  · rw [definitionEq] at actualQuery
    cases decoded : elements.mapM StateFiniteRead.decode with
    | none => simp [compileQuery,StateFiniteRead.definition,StateFiniteRead.policy,decoded] at actualQuery
    | some queries =>
      have encoded := decode_list_inverse elements queries decoded
      refine Or.inr ⟨lattice,declaration,field,queries,ruleEq,encoded,?_⟩
      rw [← definitionEq]
      exact fieldDeclared

/-- Head-complete quasi-determinism for actual authored threshold observations.
Every supported source rule is dispatched from its actual installed factory:
singleton results agree, and distinct finite results force a named joint fault. -/
theorem source_quasi_determinism (environment : Environment) (entries : List Entry) (prepared : Prepared)
    (accepted : prepareStatic environment entries = some prepared)
    (outputName sourceName : String) (elements : List Value)
    (threshold : Entry.threshold outputName sourceName elements ∈ entries)
    (rule : StateAuthoredBindings.Rule) (present : (sourceName,rule) ∈ rawFields entries)
    (A B C : List Act) (growthA : ∀ act ∈ A, act ∈ C) (growthB : ∀ act ∈ B, act ∈ C)
    (rankedA : StateExecutableFreeze.Ranked A) (rankedB : StateExecutableFreeze.Ranked B)
    (rankedC : StateExecutableFreeze.Ranked C)
    (consistentA : ∀ a ∈ A, ∀ b ∈ A, a.addr = b.addr → a = b)
    (consistentB : ∀ a ∈ B, ∀ b ∈ B, a.addr = b.addr → a = b)
    (consistentC : ∀ a ∈ C, ∀ b ∈ C, a.addr = b.addr → a = b)
    (left right joint : CompiledObservation)
    (compiledA : compileAuthored environment entries A = some left)
    (compiledB : compileAuthored environment entries B = some right)
    (compiledC : compileAuthored environment entries C = some joint)
    (leftResult rightResult : Value)
    (reachedA : (outputName,.data (.reached leftResult)) ∈ left.observe)
    (reachedB : (outputName,.data (.reached rightResult)) ∈ right.observe) :
    leftResult = rightResult ∨ ∃ evidence, (outputName,.fault evidence) ∈ joint.observe := by
  have first := reached_member environment entries prepared accepted outputName sourceName elements threshold A left compiledA leftResult reachedA
  have second := reached_member environment entries prepared accepted outputName sourceName elements threshold B right compiledB rightResult reachedB
  rcases source_policy environment entries prepared accepted outputName sourceName elements threshold rule present
    A left compiledA leftResult reachedA with singleton | finite
  · obtain ⟨element,rfl⟩ := singleton
    have l : leftResult = .element element := by simpa using first
    have r : rightResult = .element element := by simpa using second
    exact Or.inl (l.trans r.symm)
  · obtain ⟨lattice,declaration,field,queries,ruleEq,encoded,_⟩ := finite
    subst rule
    subst elements
    obtain ⟨queryA,_,leftEq⟩ := List.mem_map.mp first
    obtain ⟨queryB,_,rightEq⟩ := List.mem_map.mp second
    subst leftResult
    subst rightResult
    by_cases same : queryA = queryB
    · exact Or.inl (congrArg (fun query => Value.element (.scalar query)) same)
    · exact Or.inr (StateAuthoredFinitePreservation.quasi_determinism environment entries prepared accepted
        sourceName lattice declaration present outputName queries threshold A B C growthA growthB
        rankedA rankedB rankedC consistentA consistentB consistentC left right joint compiledA compiledB compiledC
        queryA queryB same reachedA reachedB)

/-- Every lowered source-field declaration originates in an authored field;
the initial metadata dictionary cannot manufacture output declarations. -/
theorem declarations_source_exists (environment : Environment) (domains : List StateInstalledDomains.Domain)
    (tables : List (String × StateFiniteTable.Verified)) (entries : List Entry)
    (earlier : List (String × Binding)) (output : List (Declaration Value)) (bindings : List (String × Binding))
    (lowered : declarations environment domains tables earlier entries = some (output,bindings)) :
    ∀ name definition, Declaration.field name definition ∈ output →
      ∃ rule, (name,rule) ∈ rawFields entries := by
  induction entries generalizing earlier output bindings with
  | nil =>
    have empty : output = [] := (congrArg Prod.fst (Option.some.inj lowered)).symm
    simp [empty]
  | cons entry rest ih =>
    cases entry with
    | field fieldName fieldRule =>
      cases head : StateAuthoredBindings.bind environment domains tables earlier fieldRule with
      | none => simp [declarations,head] at lowered
      | some binding =>
        cases tail : declarations environment domains tables ((fieldName,binding)::earlier) rest with
        | none => simp [declarations,head,tail] at lowered
        | some result =>
          obtain ⟨more,last⟩ := result
          simp [declarations,head,tail] at lowered
          rcases lowered with ⟨rfl,rfl⟩
          intro name definition member
          rcases List.mem_cons.mp member with same | later
          · cases same
            exact ⟨fieldRule,by simp [rawFields]⟩
          · obtain ⟨rule,inside⟩ := ih ((fieldName,binding)::earlier) more last tail name definition later
            exact ⟨rule,by simpa only [rawFields,List.filterMap_cons,List.mem_cons] using Or.inr inside⟩
    | threshold thresholdName source elements =>
      cases tail : declarations environment domains tables earlier rest with
      | none => simp [declarations,tail] at lowered
      | some result =>
        obtain ⟨more,last⟩ := result
        simp [declarations,tail] at lowered
        rcases lowered with ⟨rfl,rfl⟩
        intro name definition member
        obtain ⟨rule,inside⟩ := ih earlier more last tail name definition (by simpa using member)
        exact ⟨rule,by simpa [rawFields] using inside⟩
    | condition _ _ | domain _ | lattice _ | freeze _ _ _ =>
      intro name definition member
      obtain ⟨rule,inside⟩ := ih earlier output bindings (by simpa [declarations] using lowered) name definition member
      exact ⟨rule,by simpa [rawFields] using inside⟩

/-- A successful actual threshold identifies an authored source rule without a
caller-supplied source-existence premise. -/
theorem reached_source_exists (environment : Environment) (entries : List Entry) (prepared : Prepared)
    (accepted : prepareStatic environment entries = some prepared)
    (outputName sourceName : String) (elements : List Value)
    (threshold : Entry.threshold outputName sourceName elements ∈ entries)
    (A : List Act) (program : CompiledObservation)
    (compiled : compileAuthored environment entries A = some program)
    (result : Value) (reached : (outputName,.data (.reached result)) ∈ program.observe) :
    ∃ rule, (sourceName,rule) ∈ rawFields entries := by
  obtain ⟨definition,_,_,declared,_,_,_⟩ :=
    reached_origin environment entries prepared accepted outputName sourceName elements threshold A program compiled result reached
  obtain ⟨tables,bindings,_,_,lowered,_⟩ := static_trace environment entries prepared accepted
  exact declarations_source_exists environment prepared.domains tables entries [] prepared.declarations bindings lowered
    sourceName definition declared

/-- Complete authored threshold-success agreement. The original source rule and
its policy are derived from actual successful compiled observations. Different
successful results force a named fault in every compiled joint accepted history. -/
theorem quasi_determinism (environment : Environment) (entries : List Entry) (prepared : Prepared)
    (accepted : prepareStatic environment entries = some prepared)
    (outputName sourceName : String) (elements : List Value)
    (threshold : Entry.threshold outputName sourceName elements ∈ entries)
    (A B C : List Act) (growthA : ∀ act ∈ A, act ∈ C) (growthB : ∀ act ∈ B, act ∈ C)
    (rankedA : StateExecutableFreeze.Ranked A) (rankedB : StateExecutableFreeze.Ranked B)
    (rankedC : StateExecutableFreeze.Ranked C)
    (consistentA : ∀ a ∈ A, ∀ b ∈ A, a.addr = b.addr → a = b)
    (consistentB : ∀ a ∈ B, ∀ b ∈ B, a.addr = b.addr → a = b)
    (consistentC : ∀ a ∈ C, ∀ b ∈ C, a.addr = b.addr → a = b)
    (left right joint : CompiledObservation)
    (compiledA : compileAuthored environment entries A = some left)
    (compiledB : compileAuthored environment entries B = some right)
    (compiledC : compileAuthored environment entries C = some joint)
    (leftResult rightResult : Value)
    (reachedA : (outputName,.data (.reached leftResult)) ∈ left.observe)
    (reachedB : (outputName,.data (.reached rightResult)) ∈ right.observe) :
    leftResult = rightResult ∨ ∃ evidence, (outputName,.fault evidence) ∈ joint.observe := by
  obtain ⟨rule,present⟩ := reached_source_exists environment entries prepared accepted outputName sourceName elements threshold
    A left compiledA leftResult reachedA
  exact source_quasi_determinism environment entries prepared accepted outputName sourceName elements threshold rule present
    A B C growthA growthB rankedA rankedB rankedC consistentA consistentB consistentC left right joint
    compiledA compiledB compiledC leftResult rightResult reachedA reachedB

end CBCL.StateAuthoredThresholdOrigin
