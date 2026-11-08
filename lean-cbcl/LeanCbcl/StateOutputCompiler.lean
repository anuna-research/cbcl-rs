import LeanCbcl.StatePreparedOutputs

/-! Installed output compilation retains complete source plans and compiles
source-owned query policies into a closed dispatch inventory. Raw query history
is chosen from the source freezer, independently of its displayed payload.
Older generic full-history threshold plans are not used as output plans here. -/
namespace CBCL.StateOutputCompiler
open State StateLift StateObservation StateObservationPlan StateInstalledCompiler
open StateInstalledLowering StateThresholdDispatch StatePreparedOutputs

/-- The closed installed threshold strategy inventory. -/
inductive Query (V : Type) : Type 1 where
  | closure (alternatives : List V) (test : V → V → Bool)
  | raw {C : Type} (alternatives : List V) (test : V → C → Bool) (state : FinSet Act → C)
  | finite (spec : ThresholdSpec) (embed : spec.Carrier → V)

/-- Execute compiled query code, preserving completed source faults. -/
noncomputable def Query.run {V : Type} : Query V → List Act → StateReaderValues.Result V → StateReaderValues.Result V
  | .closure alternatives test, _, value =>
    StateRuleRefinement.nativeClosureThreshold alternatives test (StateReaderValues.unfrozen value)
  | .raw alternatives test state, history, value => nativeRawThreshold alternatives test (state (StateLVar.rawHistory history)) value
  | .finite spec embed, history, value => match value with
    | .fault evidence => .fault evidence
    | .data _ => nativeLiftThreshold spec embed (StateReaderValues.unfrozen value) history

/-- Validate and compile the policy retained by the original source definition. -/
noncomputable def compileQuery {V : Type} (elements : List V) : Definition V → Option (Query V)
  | .native _ (some policy) => if policy.check elements then some (.closure elements policy.test) else none
  | .factored term (some policy) => if policy.check elements then some (.raw elements policy.test term.state) else none
  | .lattice field => match StateInstalledLattice.prepareQuery field elements with
    | none => none
    | some query => some (.finite query.spec field.renderElement)
  | _ => none

/-- Query compilation preserves independent installed-policy dispatch. -/
theorem compile_query_refinement {V : Type} (definitions : Definitions V) (source : String)
    (elements : List V) (raw : List Act) (value : StateReaderValues.Result V) :
    ((definitions.lookup source).bind (compileQuery elements)).map (fun query => query.run raw value) =
      installedAt definitions source elements raw value := by
  cases found : definitions.lookup source with
  | none => simp [installedAt,found]
  | some definition =>
    cases definition with
    | native data policy => cases policy <;> simp [compileQuery,installedAt,found,Query.run]
    | factored term policy => cases policy <;> simp [compileQuery,installedAt,found,Query.run]
    | lattice field =>
      cases query : StateInstalledLattice.prepareQuery field elements with
      | none => simp [compileQuery,installedAt,found,query]
      | some queryValue =>
        simp only [compileQuery,found,Option.bind_some,query,Option.map_some,Query.run,installedAt]
        cases value <;> rfl
    | derived _ _ | pair _ _ _ => simp [compileQuery,installedAt,found]

/-- Output code captures the complete source plan and its query strategy. -/
inductive Output (V : Type) : Type 1 where
  | field (name : String) (source : Plan V)
  | threshold (name sourceName : String) (query : Query V) (source : Plan V)

/-- A complete installed source observation at normalized full history. -/
noncomputable def sourceValue {V : Type} (whole : List Act) (source : Plan V) : StateReaderValues.Result V :=
  observe (fun act => act ∈ StateScopePool.normalize whole) source (StateScopePool.normalize whole)

/-- Execute an output plan with the clause's retained freeze metadata. -/
noncomputable def Output.observe {V : Type} (whole : List Act) (freezes : List (String × FreezeSpec)) :
    Output V → String × StateReaderValues.Result V
  | .field name source => (name,sourceValue whole source)
  | .threshold name sourceName query source =>
    (name,query.run (referenceScope whole freezes sourceName) (sourceValue whole source))

/-- Compile one declaration against completed original source plans. -/
noncomputable def compileOne {V : Type} (plans : Plans V) (definitions : Definitions V) : Declaration V → Option (Output V)
  | .field name _ => (plans.lookup name).map (.field name)
  | .threshold name source elements => do
    let plan ← plans.lookup source
    let definition ← definitions.lookup source
    let query ← compileQuery elements definition
    return .threshold name source query plan

/-- Compile outputs in declaration order, extending source metadata each step. -/
noncomputable def compileDeclarations {V : Type} (plans : Plans V) (definitions : Definitions V) :
    List (Declaration V) → Option (List (Output V))
  | [] => some []
  | declaration::rest => do
    let output ← compileOne plans definitions declaration
    let tail ← compileDeclarations plans (extend definitions declaration) rest
    return output::tail

/-- Completed dictionary source interpretation; admitted compilation excludes
its total unknown-name fallback. -/
noncomputable def readPlans {V : Type} (whole : List Act) (plans : Plans V) (name : String) : StateReaderValues.Result V :=
  match plans.lookup name with | none => .data .pending | some plan => sourceValue whole plan

/-- Independent one-declaration output interpretation. -/
noncomputable def oneValue {V : Type} (whole : List Act) (freezes : List (String × FreezeSpec))
    (plans : Plans V) (definitions : Definitions V) : Declaration V → Option (String × StateReaderValues.Result V)
  | .field name _ => some (name,readPlans whole plans name)
  | .threshold name source elements =>
    (installedAt definitions source elements (referenceScope whole freezes source) (readPlans whole plans source)).map (name,·)

/-- Compiled output code preserves each original source/policy observation. -/
theorem compile_one_refinement {V : Type} (whole : List Act) (freezes : List (String × FreezeSpec))
    (plans : Plans V) (definitions : Definitions V) (declaration : Declaration V)
    (known : (plans.lookup (requestName declaration)).isSome = true) :
    (compileOne plans definitions declaration).map (Output.observe whole freezes) =
      oneValue whole freezes plans definitions declaration := by
  cases declaration with
  | field name definition =>
    cases found : plans.lookup name with
    | none => simp [requestName,found] at known
    | some plan => simp [compileOne,oneValue,readPlans,found,Output.observe]
  | threshold name source elements =>
    cases found : plans.lookup source with
    | none => simp [requestName,found] at known
    | some plan =>
      have query := compile_query_refinement definitions source elements (referenceScope whole freezes source) (sourceValue whole plan)
      simp only [oneValue,readPlans,found]
      rw [← query]
      cases definition : definitions.lookup source with
      | none => simp [compileOne,found,definition]
      | some definitionValue =>
        cases code : compileQuery elements definitionValue <;>
          simp [compileOne,found,definition,code,Output.observe]

/-- Reference output execution exposes the same one-output sequencing boundary. -/
theorem evaluate_cons_one {V : Type} (whole : List Act) (freezes : List (String × FreezeSpec))
    (plans : Plans V) (definitions : Definitions V) (declaration : Declaration V) (rest : List (Declaration V)) :
    evaluate (referenceScope whole freezes) (readPlans whole plans) definitions (declaration::rest) =
      (oneValue whole freezes plans definitions declaration).bind (fun output =>
        (evaluate (referenceScope whole freezes) (readPlans whole plans) (extend definitions declaration) rest).map (output::·)) := by
  cases declaration with
  | field name definition =>
    cases tail : evaluate (referenceScope whole freezes) (readPlans whole plans) (extend definitions (.field name definition)) rest <;> simp [evaluate,oneValue,tail,Declaration.name]
  | threshold name source elements =>
    cases found : installedAt definitions source elements (referenceScope whole freezes source) (readPlans whole plans source) <;>
      cases tail : evaluate (referenceScope whole freezes) (readPlans whole plans) (extend definitions (.threshold name source elements)) rest <;>
      simp [evaluate,oneValue,found,tail,Declaration.name]

/-- The complete installed output compiler refines independent source-owned,
cut-scoped output semantics, not generic full-history thresholdRaw plans. -/
theorem compile_outputs_refinement {V : Type} (whole : List Act) (freezes : List (String × FreezeSpec))
    (plans : Plans V) (definitions : Definitions V) (declarations : List (Declaration V))
    (known : ∀ declaration ∈ declarations, (plans.lookup (requestName declaration)).isSome = true) :
    (compileDeclarations plans definitions declarations).map (List.map (Output.observe whole freezes)) =
      evaluate (referenceScope whole freezes) (readPlans whole plans) definitions declarations := by
  induction declarations generalizing definitions with
  | nil => rfl
  | cons declaration rest ih =>
    have head := compile_one_refinement whole freezes plans definitions declaration (known declaration (by simp))
    have tail := ih (extend definitions declaration) (fun d member => known d (List.mem_cons_of_mem _ member))
    rw [evaluate_cons_one,← head,← tail]
    simp only [compileDeclarations]
    cases compileOne plans definitions declaration <;>
      cases compileDeclarations plans (extend definitions declaration) rest <;> rfl

/-- Prepared original field plans exist in the completed source dictionary.
This excludes output compiler fallback on unknown names constructively. -/
theorem prepared_sources_known (environment : StateAuthoredBindings.Environment)
    (entries : List StateAuthoredBindings.Entry) (whole : List Act)
    (clause : Clause StateInstalledLegacy.Value)
    (prepared : StateAuthoredBindings.prepare environment entries whole = some clause)
    (fields : List (String × Rule StateInstalledLegacy.Value))
    (resolved : resolve [] clause.declarations = some fields) (plans : Plans StateInstalledLegacy.Value)
    (compiled : StateInstalledClause.compile ⟨fields,clause.freezes⟩ = some plans)
    (ranked : StateExecutableFreeze.Ranked whole)
    (consistent : ∀ a ∈ whole, ∀ b ∈ whole, a.addr = b.addr → a = b) :
    ∀ declaration ∈ clause.declarations, (plans.lookup (requestName declaration)).isSome = true := by
  intro declaration member
  have admitted := prepared_output_admitted environment entries whole clause prepared ranked consistent declaration member
  obtain ⟨_,bare,_,_,found,_⟩ := StateCompiledFieldEquations.prepared_body_normal
    environment entries whole clause prepared fields resolved plans compiled (0,requestName declaration) admitted
  simp [found]

/-- A prepared clause produces actual compiled output code, and executing that
code equals the successful output adapted from its real empty-cache transcript. -/
theorem prepared_compiler_cache_refinement (environment : StateAuthoredBindings.Environment)
    (entries : List StateAuthoredBindings.Entry) (whole : List Act)
    (clause : Clause StateInstalledLegacy.Value)
    (prepared : StateAuthoredBindings.prepare environment entries whole = some clause)
    (ranked : StateExecutableFreeze.Ranked whole)
    (consistent : ∀ a ∈ whole, ∀ b ∈ whole, a.addr = b.addr → a = b) :
    ∃ plans fields code, StateAuthoredBindings.compile environment entries whole = some plans ∧
      resolve [] clause.declarations = some fields ∧ compileDeclarations plans [] clause.declarations = some code ∧
      let ops := StateReaderValues.operations entries whole fields clause.freezes
      let rank := StateMemoizedReader.requestRank (fields.map Prod.fst).idxOf ops.cut
      ∃ values after, StateMemoizedReader.reads ops.body rank (StateReaderReachability.initialKeys entries) [] = some (values,after) ∧
        evaluateValues (rawScope entries whole fields clause.freezes) [] clause.declarations values =
          some (code.map (Output.observe whole clause.freezes)) := by
  obtain ⟨plans,fields,compiled,resolved,values,after,outputs,ran,adapted,reference⟩ :=
    prepared_cache_outputs environment entries whole clause prepared ranked consistent
  have lowered : StateInstalledLowering.compile clause = some plans := by
    simpa [StateAuthoredBindings.compile,prepared] using compiled
  obtain ⟨actualFields,actualResolved,fieldCompiled⟩ := StateAuthoredDependencies.lowered_compiled_clause clause plans lowered
  have sameFields : actualFields = fields := Option.some.inj (actualResolved.symm.trans resolved)
  subst actualFields
  have sourceMeaning : ∀ name, StateCompiledFieldEquations.meaning whole clause.freezes plans (0,name) = readPlans whole plans name := by
    intro name
    exact StateFrozenBodyEquations.initial_meaning whole clause.freezes plans ranked consistent name
  have readsEqual : (fun name => StateCompiledFieldEquations.meaning whole clause.freezes plans (0,name)) = readPlans whole plans :=
    funext sourceMeaning
  rw [readsEqual] at reference
  have correct := compile_outputs_refinement whole clause.freezes plans [] clause.declarations
    (prepared_sources_known environment entries whole clause prepared fields resolved plans fieldCompiled ranked consistent)
  rw [reference] at correct
  cases codeCompiled : compileDeclarations plans [] clause.declarations with
  | none => simp [codeCompiled] at correct
  | some code =>
    have outputEqual : code.map (Output.observe whole clause.freezes) = outputs := by simpa [codeCompiled] using correct
    exact ⟨plans,fields,code,compiled,resolved,codeCompiled,values,after,ran,outputEqual.symm ▸ adapted⟩

/-- Installed output code retains its own immutable clause freeze metadata. -/
structure Program (V : Type) where
  /-- Validated clause-wide source freezer declarations. -/
  freezes : List (String × FreezeSpec)
  /-- Ordered compiled source/query output instructions. -/
  outputs : List (Output V)

/-- Execute the installed program's complete ordered output vector. -/
noncomputable def Program.observe {V : Type} (program : Program V) (whole : List Act) :
    List (String × StateReaderValues.Result V) := program.outputs.map (Output.observe whole program.freezes)

/-- Compile an installed clause through complete source plans and corrected
output code. Generic full-history threshold plans serve no output role. -/
noncomputable def compileClause {V : Type} (clause : Clause V) : Option (Program V) := do
  let sources ← StateInstalledLowering.compile clause
  let outputs ← compileDeclarations sources [] clause.declarations
  return ⟨clause.freezes,outputs⟩

/-- Source preparation is observation-specific. Retain that history so the
compiled authored result cannot silently evaluate a different observation. -/
structure CompiledObservation where
  /-- The history used to specialize authored source and contributor metadata. -/
  history : List Act
  /-- Source-owned output code prepared for this observation. -/
  program : Program StateInstalledLegacy.Value

/-- Execute the captured observation; history growth requires fresh preparation. -/
noncomputable def CompiledObservation.observe (compiled : CompiledObservation) :
    List (String × StateReaderValues.Result StateInstalledLegacy.Value) := compiled.program.observe compiled.history

/-- The authored output compiler recognizes actual declarations before emitting
code; it has no caller-supplied source policy or freeze metadata. -/
noncomputable def compileAuthored (environment : StateAuthoredBindings.Environment)
    (entries : List StateAuthoredBindings.Entry) (whole : List Act) : Option CompiledObservation := do
  let clause ← StateAuthoredBindings.prepare environment entries whole
  let program ← compileClause clause
  return ⟨whole,program⟩

/-- Top-level authored output compiler and actual empty-cache execution agree
on a complete successful vector, including every installed threshold strategy. -/
theorem authored_compiler_refinement (environment : StateAuthoredBindings.Environment)
    (entries : List StateAuthoredBindings.Entry) (whole : List Act)
    (clause : Clause StateInstalledLegacy.Value)
    (prepared : StateAuthoredBindings.prepare environment entries whole = some clause)
    (ranked : StateExecutableFreeze.Ranked whole)
    (consistent : ∀ a ∈ whole, ∀ b ∈ whole, a.addr = b.addr → a = b) :
    ∃ program fields, compileAuthored environment entries whole = some program ∧
      resolve [] clause.declarations = some fields ∧
      let ops := StateReaderValues.operations entries whole fields clause.freezes
      let rank := StateMemoizedReader.requestRank (fields.map Prod.fst).idxOf ops.cut
      ∃ values after, StateMemoizedReader.reads ops.body rank (StateReaderReachability.initialKeys entries) [] = some (values,after) ∧
        evaluateValues (rawScope entries whole fields clause.freezes) [] clause.declarations values = some program.observe := by
  obtain ⟨plans,fields,code,compiled,resolved,codeCompiled,values,after,ran,adapted⟩ :=
    prepared_compiler_cache_refinement environment entries whole clause prepared ranked consistent
  have sourceCompiled : StateInstalledLowering.compile clause = some plans := by
    simpa [StateAuthoredBindings.compile,prepared] using compiled
  refine ⟨⟨whole,⟨clause.freezes,code⟩⟩,fields,?_,resolved,values,after,ran,adapted⟩
  simp [compileAuthored,prepared,compileClause,sourceCompiled,codeCompiled]

end CBCL.StateOutputCompiler
