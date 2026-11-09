import LeanCbcl.StateConditionCompiler

/-! Installed output compilation retains complete source plans and compiles
source-owned query policies into a closed dispatch inventory. Raw query history
is chosen from the source freezer, independently of its displayed payload.
Older generic full-history threshold plans are not used as output plans here. -/
namespace CBCL.StateOutputCompiler
open State StateLift StateObservation StateObservationPlan StateInstalledCompiler
open StateInstalledLowering StateThresholdDispatch StatePreparedOutputs

/-- Output code captures the complete source plan and its query strategy. -/
inductive Output (V : Type) : Type 1 where
  | field (name : String) (source : Plan V)
  | threshold (name sourceName : String) (query : Query V) (source : Plan V)
  | condition (name : String) (truth : V) (code : StateConditionCompiler.Code V)

/-- Execute an output plan with the clause's retained freeze metadata. -/
noncomputable def Output.observe {V : Type} (whole : List Act) (freezes : List (String × FreezeSpec)) :
    Output V → String × StateReaderValues.Result V
  | .field name source => (name,sourceValue whole source)
  | .threshold name sourceName query source =>
    (name,query.run (referenceScope whole freezes sourceName) (sourceValue whole source))
  | .condition name truth code =>
    (name,StateConditionCompiler.truthResult truth (code.observe whole freezes))

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

/-- Reinsert condition observations in original authored order while retaining
base source/query instructions and the exact earlier definition prefix. -/
noncomputable def emitAuthored (maxNodes : Nat) (plans : Plans StateInstalledLegacy.Value) :
    List StateAuthoredBindings.Entry → List (Declaration StateInstalledLegacy.Value) →
      List (Output StateInstalledLegacy.Value) → Definitions StateInstalledLegacy.Value →
        Option (List (Output StateInstalledLegacy.Value))
  | [], [], [], _ => some []
  | .condition name expression :: rest, declarations, outputs, earlier => do
      let code ← StateConditionCompiler.compile maxNodes plans earlier expression
      let tail ← emitAuthored maxNodes plans rest declarations outputs earlier
      return .condition name (.element (.scalar (.bool true))) code :: tail
  | .field name _ :: rest, declaration :: declarations, output :: outputs, earlier
  | .threshold name _ _ :: rest, declaration :: declarations, output :: outputs, earlier =>
      if name != declaration.name then none else do
        let tail ← emitAuthored maxNodes plans rest declarations outputs (extend earlier declaration)
        return output :: tail
  | .domain _ :: rest, declarations, outputs, earlier
  | .lattice _ :: rest, declarations, outputs, earlier
  | .freeze _ _ _ :: rest, declarations, outputs, earlier => emitAuthored maxNodes plans rest declarations outputs earlier
  | _, _, _, _ => none

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

/-- Base authored source/threshold compilation, before condition interleaving.
StateAuthoredConditionOutputs.compileAuthored assembles the full v0.4 inventory;
this base stage has no caller-supplied source policy or freeze metadata. -/
noncomputable def compileAuthored (environment : StateAuthoredBindings.Environment)
    (entries : List StateAuthoredBindings.Entry) (whole : List Act) : Option CompiledObservation := do
  let clause ← StateAuthoredBindings.prepare environment entries whole
  let program ← compileClause clause
  return ⟨whole,program⟩

/-- The base source/threshold output stage agrees with actual empty-cache
execution. Full v0.4 condition assembly is refined separately. -/
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

namespace CBCL.StateConditionCompiler
open State StateLift StateObservation StateObservationPlan StateInstalledCompiler
open StateInstalledLowering StateOutputCompiler StateCondition StateThresholdDispatch

/-- A compiled leaf is exactly the existing source-owned threshold output,
followed by condition-only Boolean normalization. -/
theorem leaf_observe {V : Type} (whole : List Act) (freezes : List (String × FreezeSpec))
    (field : String) (query : Query V) (source : Plan V) :
    Code.observe whole freezes (.read field query source) =
      boolean ((Output.threshold "" field query source).observe whole freezes).2 := by
  simp only [Code.observe,Output.observe]


end CBCL.StateConditionCompiler
