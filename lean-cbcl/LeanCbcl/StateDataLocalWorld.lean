import LeanCbcl.StateFrozenSuccess

/-! Exact healthy data refinement between a common causal world and the output
interpreter's accepted local world, including nested freeze scopes. -/
set_option autoImplicit false
namespace CBCL.StateDataLocalWorld
open State StateLift StateLVar StateObservation StateObservationPlan

/-- A globally closed sub-scope is also closed in the containing accepted world. -/
theorem scope_closed_local (world : Act → Prop) (whole scope : List Act)
    (valid : ∀ act ∈ whole, world act) (closed : CausallyClosed world scope) :
    CausallyClosed (fun act => act ∈ whole) scope := by
  intro child member parent inside edge
  exact closed child member parent (valid parent inside) edge

/-- Global and containing-local worlds select the same earliest sub-scope roots. -/
theorem earliest_scope_local (world : Act → Prop) (whole scope : List Act)
    (valid : ∀ act ∈ whole, world act) (closed : CausallyClosed world scope)
    (inside : ∀ act ∈ scope, act ∈ whole) (verb : String) (root : Act) :
    Earliest world verb scope root ↔ Earliest (fun act => act ∈ whole) verb scope root := by
  exact (StateOutputWitnessReplay.earliest_local_iff world scope (fun act member => valid act (inside act member)) closed verb root).trans
    (StateOutputWitnessReplay.earliest_local_iff (fun act => act ∈ whole) scope inside
      (scope_closed_local world whole scope valid closed) verb root).symm

/-- Every nested error path agrees in the common and containing-local worlds. -/
theorem errors_scope_local (world : Act → Prop) (whole scope : List Act)
    (valid : ∀ act ∈ whole, world act) (closed : CausallyClosed world scope)
    (inside : ∀ act ∈ scope, act ∈ whole) (source : Path) :
    errors world source scope = errors (fun act => act ∈ whole) source scope := by
  rw [StateOutputWitnessReplay.errors_local world scope (fun act member => valid act (inside act member)) closed source]
  exact (StateOutputWitnessReplay.errors_local (fun act => act ∈ whole) scope inside
    (scope_closed_local world whole scope valid closed) source).symm

/-- Complete healthy data, including frozen status and exclusions, agrees in the
common world and the actual containing-local output world at every closed cut. -/
theorem healthy_data_local {V : Type} (world : Act → Prop) (whole : List Act)
    (valid : ∀ act ∈ whole, world act) (wholeClosed : CausallyClosed world whole) (source : Plan V)
    (scope : List Act) (closed : CausallyClosed world scope) (inside : ∀ act ∈ scope, act ∈ whole)
    (clear : errors world (path source) scope = none) :
    data world source scope = data (fun act => act ∈ whole) source scope := by
  classical
  induction source generalizing scope with
  | snapshot _ | read _ _ | context _ | contextAs _ _ | domain _ _ _ _ _ => rfl
  | guardCertified _ source ih | guardThreshold _ source ih | guardDomain _ _ source ih
  | resource _ _ source ih =>
    exact ih scope closed inside ((StateNativeReader.union_clear _ _).mp clear).2
  | embed f source ih | map f source ih => simp only [data,ih scope closed inside clear]
  | pair left right il ir =>
    have parts := (StateNativeReader.union_clear _ _).mp clear
    simp only [data,il scope closed inside parts.1,ir scope closed inside parts.2]
  | threshold spec source ih =>
    have same := errors_scope_local world whole scope valid closed inside (path source)
    simp only [data,same]
  | thresholdRaw alternatives test state source ih => rfl
  | thresholdOn alternatives test source ih => simp only [data,ih scope closed inside clear]
  | freeze spec source ih =>
    have localClear : errors (fun act => act ∈ whole) (path (.freeze spec source)) scope = none := by
      rw [← errors_scope_local world whole scope valid closed inside]
      exact clear
    rw [StateFrozenSuccess.freeze_data_clear world spec source scope clear,
      StateFrozenSuccess.freeze_data_clear (fun act => act ∈ whole) spec source scope localClear]
    have earliest : (fun act => decide (Earliest world spec.verb scope act)) =
        (fun act => decide (Earliest (fun node => node ∈ whole) spec.verb scope act)) := by
      funext act
      simp only [earliest_scope_local world whole scope valid closed inside spec.verb act]
    rw [← earliest]
    have rawClear := ((StateNativeReader.freeze_clear world spec _ scope).mp clear).1
    cases selected : scope.find? (fun act => decide (Earliest world spec.verb scope act)) with
    | none => exact ih scope closed inside rawClear
    | some root =>
      have member : root ∈ whole := inside root (List.mem_of_find?_eq_some selected)
      have ancestry : ∀ act, Ancestor world act root ↔ Ancestor (fun node => node ∈ whole) act root :=
        fun _ => StateOutputWitnessReplay.ancestor_local_iff world whole valid wholeClosed member
      have cutEq : causalCut world scope root = causalCut (fun node => node ∈ whole) scope root := by
        unfold causalCut
        congr 1
        funext act
        simp only [ancestry act]
      have excludedEq : FinSet.mk (scope.filter (fun act => decide (spec.contributes act ∧ ¬Ancestor world act root))) =
          FinSet.mk (scope.filter (fun act => decide (spec.contributes act ∧ ¬Ancestor (fun node => node ∈ whole) act root))) := by
        apply FinSet.ext
        intro act
        simp only [FinSet.mem_mk,List.mem_filter,decide_eq_true_eq]
        exact and_congr Iff.rfl (and_congr Iff.rfl (not_congr (ancestry act)))
      have cutClosed := StateFreezeScopes.causal_cut_closed closed root
      have cutInside : ∀ act ∈ causalCut world scope root, act ∈ scope :=
        fun _ member => (List.mem_filter.mp member).1
      have cutClear := StateFreezeScopes.source_clear_in_scope world (path source) cutClosed cutInside rawClear
      have cutData := ih _ cutClosed (fun act member => inside act (cutInside act member)) cutClear
      dsimp only
      rw [← cutEq,← cutData,excludedEq]

/-- The complete observation at an accepted scope uses the same data and fault
channels in the common and output-local worlds. -/
theorem observation_local {V : Type} (world : Act → Prop) (A : List Act)
    (valid : ∀ act ∈ A, world act) (closed : CausallyClosed world A) (source : Plan V) :
    observe world source A = observe (fun act => act ∈ A) source A := by
  have errors := StateOutputWitnessReplay.errors_local world A valid closed (path source)
  unfold observe
  rw [← errors]
  cases clear : StateObservation.errors world (path source) A with
  | some evidence => rfl
  | none => rw [healthy_data_local world A valid closed source A closed (fun _ member => member) clear]

/-- Actual emitted source observations equal common-world interpretation of the
normalized accepted scope, preserving every public data tag and exact evidence. -/
theorem source_value_global {V : Type} (world : Act → Prop) (A : List Act)
    (valid : ∀ act ∈ A, world act) (closed : CausallyClosed world A) (source : Plan V) :
    StateOutputCompiler.sourceValue A source = observe world source (StateScopePool.normalize A) := by
  have same := StateScopePool.normalize_setEq A
  have normalizedValid : ∀ act ∈ StateScopePool.normalize A, world act := fun act member => valid act ((same act).mp member)
  have normalizedClosed : CausallyClosed world (StateScopePool.normalize A) := by
    intro child member parent parentValid edge
    exact (same parent).mpr (closed child ((same child).mp member) parent parentValid edge)
  exact (observation_local world _ normalizedValid normalizedClosed source).symm

end CBCL.StateDataLocalWorld
