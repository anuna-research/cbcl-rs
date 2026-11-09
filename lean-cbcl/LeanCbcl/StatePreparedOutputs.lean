import LeanCbcl.StateThresholdDispatch

/-! Output composition walks actual prepared declarations, retaining source
policy metadata as it goes. Thresholds cannot supply detached carrier tests. -/
namespace CBCL.StatePreparedOutputs
open State StateLift StateObservation StateObservationPlan StateInstalledCompiler
open StateInstalledLowering StateReaderReachability StateThresholdDispatch

/-- Each output requests its field, or the original source of its threshold. -/
def requestName {V : Type} : Declaration V → String
  | .field name _ => name
  | .threshold _ source _ => source

/-- Ordered output execution uses the named completed source and the source's
own policy. The scope provider selects raw-carrier evidence independently. -/
noncomputable def evaluate {V : Type} (scopes : String → List Act)
    (read : String → StateReaderValues.Result V) (definitions : Definitions V) :
    List (Declaration V) → Option (List (String × StateReaderValues.Result V))
  | [] => some []
  | declaration::rest => do
    let result ← match declaration with
      | .field name _ => some (read name)
      | .threshold _ source elements => installedAt definitions source elements (scopes source) (read source)
    let tail ← evaluate scopes read (extend definitions declaration) rest
    return (declaration.name,result)::tail

/-- Successful threshold lowering guarantees its source-owned output policy is
available for every raw history and every completed source result. -/
theorem threshold_available {V : Type} (definitions : Definitions V) (name source : String)
    (elements : List V) (rule : Rule V)
    (lowered : lowerRule definitions (.threshold name source elements) = some rule)
    (raw : List Act) (value : StateReaderValues.Result V) :
    ∃ result, installedAt definitions source elements raw value = some result := by
  cases found : definitions.lookup source with
  | none => simp [lowerRule,found] at lowered
  | some definition =>
    cases definition with
    | native data policy =>
      cases policy with
      | none => simp [lowerRule,found] at lowered
      | some policy =>
        cases checked : policy.check elements with
        | false => simp [lowerRule,found,checked] at lowered
        | true => simp [installedAt,found,checked]
    | factored term policy =>
      cases policy with
      | none => simp [lowerRule,found] at lowered
      | some policy =>
        cases checked : policy.check elements with
        | false => simp [lowerRule,found,checked] at lowered
        | true => simp [installedAt,found,checked]
    | lattice field =>
      cases query : StateInstalledLattice.prepareQuery field elements with
      | none => simp [lowerRule,found,query] at lowered
      | some query => simp [installedAt,found,query]
    | derived _ _ | pair _ _ _ => simp [lowerRule,found] at lowered

/-- Prepared output equality cannot be satisfied merely by two failed walks:
successful lowering constructs a complete output list for arbitrary reads. -/
theorem evaluate_complete {V : Type} (scopes : String → List Act)
    (read : String → StateReaderValues.Result V) (definitions : Definitions V)
    (declarations : List (Declaration V)) (fields : List (String × Rule V))
    (resolved : resolve definitions declarations = some fields) :
    ∃ outputs, evaluate scopes read definitions declarations = some outputs := by
  induction declarations generalizing definitions fields with
  | nil => exact ⟨[],rfl⟩
  | cons declaration rest ih =>
    cases head : lowerRule definitions declaration with
    | none => simp [resolve,head] at resolved
    | some rule =>
      cases tail : resolve (extend definitions declaration) rest with
      | none => simp [resolve,head,tail] at resolved
      | some more =>
        obtain ⟨outputs,complete⟩ := ih (extend definitions declaration) more tail
        cases declaration with
        | field name definition => simp [evaluate,complete]
        | threshold name source elements =>
          obtain ⟨result,available⟩ := threshold_available definitions name source elements rule head (scopes source) (read source)
          simp [evaluate,available,complete]

/-- Consume the actual cache transcript, one completed source result per
prepared declaration. Missing or extra source results fail explicitly. -/
noncomputable def evaluateValues {V : Type} (scopes : String → List Act) (definitions : Definitions V) :
    List (Declaration V) → List (StateReaderValues.Result V) → Option (List (String × StateReaderValues.Result V))
  | [], [] => some []
  | declaration::rest, value::values => do
    let result ← match declaration with
      | .field _ _ => some value
      | .threshold _ source elements => installedAt definitions source elements (scopes source) value
    let tail ← evaluateValues scopes (extend definitions declaration) rest values
    return (declaration.name,result)::tail
  | _, _ => none

/-- Source transcript consumption equals named-source execution in order. -/
theorem evaluate_values_map {V : Type} (scopes : String → List Act)
    (definitions : Definitions V) (declarations : List (Declaration V)) (read : String → StateReaderValues.Result V) :
    evaluateValues scopes definitions declarations (declarations.map (fun d => read (requestName d))) =
      evaluate scopes read definitions declarations := by
  induction declarations generalizing definitions with
  | nil => rfl
  | cons declaration rest ih =>
    cases declaration <;> simp_all [evaluateValues,evaluate,requestName]

/-- Only actually requested source observations and scopes affect outputs. -/
theorem evaluate_congr {V : Type} (leftScope rightScope : String → List Act)
    (leftRead rightRead : String → StateReaderValues.Result V) (definitions : Definitions V)
    (declarations : List (Declaration V))
    (same : ∀ declaration ∈ declarations,
      leftRead (requestName declaration) = rightRead (requestName declaration) ∧
      leftScope (requestName declaration) = rightScope (requestName declaration)) :
    evaluate leftScope leftRead definitions declarations = evaluate rightScope rightRead definitions declarations := by
  induction declarations generalizing definitions with
  | nil => rfl
  | cons declaration rest ih =>
    have head := same declaration (by simp)
    have tail := ih (extend definitions declaration) (fun d member => same d (List.mem_cons_of_mem _ member))
    cases declaration <;> simp only [requestName] at head <;> simp [evaluate,head.1,head.2,tail]

/-- The original shape inventory determines the exact requested source name. -/
def shapeName (shape : String × Option String) : String := shape.2.getD shape.1

/-- Original native source requests are precisely the shape projection. -/
theorem initial_keys_shapes (entries : List StateAuthoredBindings.Entry) :
    initialKeys entries = (entries.filterMap entryShape).map (fun shape => (0,shapeName shape)) := by
  induction entries with
  | nil => rfl
  | cons entry rest ih => cases entry <;> simpa [initialKeys,entryShape,shapeName] using ih

/-- Every request of the actual prepared output walk is admitted. -/
theorem prepared_output_admitted (environment : StateAuthoredBindings.Environment)
    (entries : List StateAuthoredBindings.Entry) (whole : List Act)
    (clause : Clause StateInstalledLegacy.Value)
    (prepared : StateAuthoredBindings.prepare environment entries whole = some clause)
    (ranked : StateExecutableFreeze.Ranked whole)
    (consistent : ∀ a ∈ whole, ∀ b ∈ whole, a.addr = b.addr → a = b) :
    ∀ declaration ∈ clause.declarations, Admitted entries whole clause.freezes (0,requestName declaration) := by
  intro declaration member
  apply initial_keys_admitted environment entries whole clause prepared ranked consistent
  rw [initial_keys_shapes,← prepared_shapes environment entries whole clause prepared]
  apply List.mem_map.mpr
  refine ⟨declarationShape declaration,List.mem_map.mpr ⟨declaration,member,rfl⟩,?_⟩
  cases declaration <;> rfl

/-- All prepared output paths compose recursive source semantics, exact raw
cuts, and source-owned installed policies in declaration order. This reference
uses corrected cut-scoped threshold dispatch, not old full-history thresholdRaw. -/
theorem prepared_outputs (environment : StateAuthoredBindings.Environment)
    (entries : List StateAuthoredBindings.Entry) (whole : List Act)
    (clause : Clause StateInstalledLegacy.Value)
    (prepared : StateAuthoredBindings.prepare environment entries whole = some clause)
    (fields : List (String × Rule StateInstalledLegacy.Value))
    (resolved : resolve [] clause.declarations = some fields)
    (plans : Plans StateInstalledLegacy.Value)
    (compiled : StateInstalledClause.compile ⟨fields,clause.freezes⟩ = some plans)
    (ranked : StateExecutableFreeze.Ranked whole)
    (consistent : ∀ a ∈ whole, ∀ b ∈ whole, a.addr = b.addr → a = b) :
    let ops := StateReaderValues.operations entries whole fields clause.freezes
    let rank := StateMemoizedReader.requestRank (fields.map Prod.fst).idxOf ops.cut
    ∃ requestRanked : ∀ key, (ops.body key).Below rank (rank key),
      evaluate (rawScope entries whole fields clause.freezes)
        (fun name => StateMemoizedReader.reference ops.body rank requestRanked (0,name)) [] clause.declarations =
      evaluate (referenceScope whole clause.freezes)
        (fun name => StateCompiledFieldEquations.meaning whole clause.freezes plans (0,name)) [] clause.declarations := by
  obtain ⟨requestRanked,equalMeaning⟩ := StateFrozenBodyEquations.prepared_reference_equivalence
    environment entries whole clause prepared fields resolved plans compiled ranked consistent
  refine ⟨requestRanked,?_⟩
  apply evaluate_congr
  intro declaration member
  have admitted := prepared_output_admitted environment entries whole clause prepared ranked consistent declaration member
  exact ⟨equalMeaning _ admitted,raw_scope_refinement entries whole fields clause.freezes ranked consistent
    (StateScopeProperties.compiled_freezes_unique ⟨fields,clause.freezes⟩ plans compiled) _ admitted⟩

/-- A real empty-cache run supplies the entire successful output walk. Source
fields and all installed threshold strategies compose through the same ordered
transcript, retaining global faults and exact raw cuts. The reference is the
corrected output semantics, not the older full-history thresholdRaw plans. -/
theorem prepared_cache_outputs (environment : StateAuthoredBindings.Environment)
    (entries : List StateAuthoredBindings.Entry) (whole : List Act)
    (clause : Clause StateInstalledLegacy.Value)
    (prepared : StateAuthoredBindings.prepare environment entries whole = some clause)
    (ranked : StateExecutableFreeze.Ranked whole)
    (consistent : ∀ a ∈ whole, ∀ b ∈ whole, a.addr = b.addr → a = b) :
    ∃ plans fields, StateAuthoredBindings.compile environment entries whole = some plans ∧
      resolve [] clause.declarations = some fields ∧
      let ops := StateReaderValues.operations entries whole fields clause.freezes
      let rank := StateMemoizedReader.requestRank (fields.map Prod.fst).idxOf ops.cut
      ∃ values after outputs,
        StateMemoizedReader.reads ops.body rank (initialKeys entries) [] = some (values,after) ∧
        evaluateValues (rawScope entries whole fields clause.freezes) [] clause.declarations values = some outputs ∧
        evaluate (referenceScope whole clause.freezes)
          (fun name => StateCompiledFieldEquations.meaning whole clause.freezes plans (0,name)) [] clause.declarations = some outputs := by
  obtain ⟨plans,fields,compiled,resolved,after,ran,_,_⟩ := StateFrozenBodyEquations.prepared_cache_equivalence
    environment entries whole clause prepared ranked consistent
  have lowered : StateInstalledLowering.compile clause = some plans := by
    simpa [StateAuthoredBindings.compile,prepared] using compiled
  obtain ⟨actualFields,actualResolved,fieldCompiled⟩ := StateAuthoredDependencies.lowered_compiled_clause clause plans lowered
  have sameFields : actualFields = fields := Option.some.inj (actualResolved.symm.trans resolved)
  subst actualFields
  let read := fun name => StateCompiledFieldEquations.meaning whole clause.freezes plans (0,name)
  obtain ⟨outputs,complete⟩ := evaluate_complete (referenceScope whole clause.freezes) read [] clause.declarations fields resolved
  have inventory : clause.declarations.map (fun d => (0,requestName d)) = initialKeys entries := by
    rw [initial_keys_shapes,← prepared_shapes environment entries whole clause prepared]
    rw [List.map_map]
    apply List.map_congr_left
    intro declaration _
    cases declaration <;> rfl
  have transcript : (initialKeys entries).map (StateCompiledFieldEquations.meaning whole clause.freezes plans) =
      clause.declarations.map (fun d => read (requestName d)) := by
    rw [← inventory,List.map_map]
    rfl
  have equalOutput : evaluate (rawScope entries whole fields clause.freezes) read [] clause.declarations =
      evaluate (referenceScope whole clause.freezes) read [] clause.declarations := by
    apply evaluate_congr
    intro declaration member
    have admitted := prepared_output_admitted environment entries whole clause prepared ranked consistent declaration member
    exact ⟨rfl,raw_scope_refinement entries whole fields clause.freezes ranked consistent
      (StateScopeProperties.compiled_freezes_unique ⟨fields,clause.freezes⟩ plans fieldCompiled) _ admitted⟩
  refine ⟨plans,fields,compiled,resolved,_,after,outputs,ran,?_,complete⟩
  rw [transcript,evaluate_values_map,equalOutput]
  exact complete

end CBCL.StatePreparedOutputs
