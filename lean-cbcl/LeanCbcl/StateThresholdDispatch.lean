import LeanCbcl.StateFrozenBodyEquations

/-! Native raw-threshold output dispatch. Completed source faults remain global;
healthy raw carriers are recomputed in the selected source freezer's exact cut.
This adapter is distinct from the older full-history thresholdRaw plan. -/
namespace CBCL.StateThresholdDispatch
open State StateLift StateLVar StateObservation StateObservationPlan StateInstalledCompiler
open StateScopePool StateReaderValues StateReaderReachability

/-- Semantic raw-state scope, with no allocated-index or cache dependency. -/
noncomputable def referenceScope (whole : List Act) (freezes : List (String × FreezeSpec))
    (name : String) : List Act :=
  match freezes.lookup name with
  | none => normalize whole
  | some spec => match uniqueRoot (normalize whole) spec.verb with
    | none => normalize whole
    | some root => causalCut (fun act => act ∈ normalize whole) (normalize whole) root

/-- The operational index used by native threshold output dispatch. -/
noncomputable def rawScope {V : Type} (entries : List StateAuthoredBindings.Entry) (whole : List Act)
    (fields : List (String × Rule V)) (freezes : List (String × FreezeSpec)) (name : String) : List Act :=
  scope whole freezes (((StateReaderValues.operations entries whole fields freezes).cut name).getD 0,name)

/-- The allocated raw-state scope is exactly the selected semantic cut, including
no-freeze and no-root cases. This does not assume raw-carrier locality. -/
theorem raw_scope_refinement {V : Type} (entries : List StateAuthoredBindings.Entry) (whole : List Act)
    (fields : List (String × Rule V)) (freezes : List (String × FreezeSpec))
    (ranked : StateExecutableFreeze.Ranked whole)
    (consistent : ∀ a ∈ whole, ∀ b ∈ whole, a.addr = b.addr → a = b)
    (unique : (freezes.map Prod.fst).Nodup) (name : String)
    (admitted : Admitted entries whole freezes (0,name)) :
    rawScope entries whole fields freezes name = referenceScope whole freezes name := by
  have full : scope whole freezes (0,name) = normalize whole := by
    simp only [scope,(normalized_scopes_sound whole ranked consistent freezes).1.1,Option.getD_some]
  cases declared : freezes.lookup name with
  | none =>
    have missing := StateCompiledFieldEquations.missing_freeze_root (normalize whole) freezes name declared
    have noCut : (StateReaderValues.operations entries whole fields freezes).cut name = none := by
      simp [StateReaderValues.operations,cutScope,missing]
    simpa [rawScope,referenceScope,declared,noCut] using full
  | some spec =>
    cases selected : uniqueRoot (normalize whole) spec.verb with
    | none =>
      have absent := StateScopeProperties.absent_root_metadata entries whole fields freezes unique (0,name) spec declared selected
      simpa [rawScope,referenceScope,declared,selected,absent.1] using full
    | some root =>
      obtain ⟨index,cutIndex,exactCut,_,_⟩ := StateScopeProperties.selected_root_metadata
        entries whole fields freezes ranked consistent unique (0,name) admitted spec declared root selected
      simpa [rawScope,referenceScope,declared,selected,cutIndex] using exactCut

/-- Fixed operational adapter: faults are returned before raw-state evaluation;
healthy observations consume the selected cut, including pending source payloads. -/
noncomputable def dispatch {V C : Type} (entries : List StateAuthoredBindings.Entry) (whole : List Act)
    (fields : List (String × Rule V)) (freezes : List (String × FreezeSpec)) (name : String)
    (alternatives : List V) (test : V → C → Bool) (state : FinSet Act → C) (source : Result V) : Result V :=
  match source with
  | .fault evidence => .fault evidence
  | .data _ => nativeRawThreshold alternatives test
      (state (rawHistory (rawScope entries whole fields freezes name))) (unfrozen source)

/-- Independent reference output uses exact causal history and completed source
faults, never the cache's scope index. -/
noncomputable def reference {V C : Type} (whole : List Act) (freezes : List (String × FreezeSpec))
    (name : String) (alternatives : List V) (test : V → C → Bool) (state : FinSet Act → C)
    (source : Result V) : Result V :=
  nativeRawThreshold alternatives test (state (rawHistory (referenceScope whole freezes name))) source

/-- Threshold adaptation composes exact source results with exact raw cuts. -/
theorem dispatch_refinement {V C : Type} (entries : List StateAuthoredBindings.Entry) (whole : List Act)
    (fields : List (String × Rule V)) (freezes : List (String × FreezeSpec))
    (ranked : StateExecutableFreeze.Ranked whole)
    (consistent : ∀ a ∈ whole, ∀ b ∈ whole, a.addr = b.addr → a = b)
    (unique : (freezes.map Prod.fst).Nodup) (name : String)
    (admitted : Admitted entries whole freezes (0,name))
    (alternatives : List V) (test : V → C → Bool) (state : FinSet Act → C) (source : Result V) :
    dispatch entries whole fields freezes name alternatives test state source =
      reference whole freezes name alternatives test state source := by
  have scopes := raw_scope_refinement entries whole fields freezes ranked consistent unique name admitted
  cases source with
  | fault _ => rfl
  | data value => cases value <;> simp [dispatch,reference,scopes,unfrozen,nativeRawThreshold]

/-- Compose a prepared source's independent recursive reader with the exact
raw-threshold output adapter. Alternatives and the source-owned carrier/test
are still explicit typed ports; this is not old thresholdRaw-plan equivalence. -/
theorem prepared_threshold_reference (environment : StateAuthoredBindings.Environment)
    (entries : List StateAuthoredBindings.Entry) (whole : List Act)
    (clause : StateInstalledLowering.Clause StateInstalledLegacy.Value)
    (prepared : StateAuthoredBindings.prepare environment entries whole = some clause)
    (fields : List (String × Rule StateInstalledLegacy.Value))
    (resolved : StateInstalledLowering.resolve [] clause.declarations = some fields)
    (plans : Plans StateInstalledLegacy.Value)
    (compiled : StateInstalledClause.compile ⟨fields,clause.freezes⟩ = some plans)
    (ranked : StateExecutableFreeze.Ranked whole)
    (consistent : ∀ a ∈ whole, ∀ b ∈ whole, a.addr = b.addr → a = b)
    (name : String) (admitted : Admitted entries whole clause.freezes (0,name))
    {C : Type} (alternatives : List StateInstalledLegacy.Value)
    (test : StateInstalledLegacy.Value → C → Bool) (state : FinSet Act → C) :
    let ops := StateReaderValues.operations entries whole fields clause.freezes
    let rank := StateMemoizedReader.requestRank (fields.map Prod.fst).idxOf ops.cut
    ∃ requestRanked : ∀ key, (ops.body key).Below rank (rank key),
      dispatch entries whole fields clause.freezes name alternatives test state
        (StateMemoizedReader.reference ops.body rank requestRanked (0,name)) =
      reference whole clause.freezes name alternatives test state
        (match plans.lookup name with
         | none => .data .pending
         | some plan => StateObservationPlan.observe (fun act => act ∈ normalize whole) plan (normalize whole)) := by
  obtain ⟨requestRanked,equalMeaning⟩ := StateFrozenBodyEquations.prepared_reference_equivalence
    environment entries whole clause prepared fields resolved plans compiled ranked consistent
  refine ⟨requestRanked,?_⟩
  rw [equalMeaning (0,name) admitted]
  rw [dispatch_refinement entries whole fields clause.freezes ranked consistent
    (StateScopeProperties.compiled_freezes_unique ⟨fields,clause.freezes⟩ plans compiled) name admitted]
  rw [StateFrozenBodyEquations.initial_meaning whole clause.freezes plans ranked consistent name]
  cases plans.lookup name <;> rfl

/-- All installed threshold strategies obtain their tests and carriers from the
named source definition. Unknown sources and unsupported policies fail closed.
The supplied scope affects raw carriers only; completed source faults win. -/
noncomputable def installedAt {V : Type} (definitions : StateInstalledLowering.Definitions V)
    (name : String) (elements : List V) (raw : List Act) (value : Result V) : Option (Result V) := do
  match definitions.lookup name with
  | none => none
  | some definition => match definition with
    | .native _ (some policy) =>
      if policy.check elements then some (StateRuleRefinement.nativeClosureThreshold elements policy.test (unfrozen value)) else none
    | .factored term (some policy) =>
      if policy.check elements then some (nativeRawThreshold elements policy.test (term.state (rawHistory raw)) value) else none
    | .lattice field => do
      let query ← StateInstalledLattice.prepareQuery field elements
      return match value with
      | .fault evidence => .fault evidence
      | .data _ => nativeLiftThreshold query.spec field.renderElement (unfrozen value) raw
    | _ => none

/-- A factored source's retained admissibility policy cannot be bypassed. -/
theorem installed_factored_rejects {V : Type} (definitions : StateInstalledLowering.Definitions V)
    (name : String) (elements : List V) (raw : List Act) (value : Result V)
    (term : StateInstalledTerm.Term V) (policy : StateInstalledTerm.Policy V term.Carrier)
    (declared : definitions.lookup name = some (.factored term (some policy)))
    (rejected : policy.check elements = false) : installedAt definitions name elements raw value = none := by
  simp [installedAt,declared,rejected]

/-- Source-owned threshold policies compose with actual allocated scope
selection for all three admitted installed query strategies. -/
theorem installed_scope_refinement {V : Type} (entries : List StateAuthoredBindings.Entry) (whole : List Act)
    (fields : List (String × Rule V)) (freezes : List (String × FreezeSpec))
    (ranked : StateExecutableFreeze.Ranked whole)
    (consistent : ∀ a ∈ whole, ∀ b ∈ whole, a.addr = b.addr → a = b)
    (unique : (freezes.map Prod.fst).Nodup) (name : String)
    (admitted : Admitted entries whole freezes (0,name))
    (definitions : StateInstalledLowering.Definitions V) (elements : List V) (value : Result V) :
    installedAt definitions name elements (rawScope entries whole fields freezes name) value =
      installedAt definitions name elements (referenceScope whole freezes name) value := by
  rw [raw_scope_refinement entries whole fields freezes ranked consistent unique name admitted]

end CBCL.StateThresholdDispatch
