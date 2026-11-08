import LeanCbcl.StateObservationPlan
import LeanCbcl.StateResourceNative

/-! Value-level refinements of native read adapters. The reference operations
below consume already-observed source fields, just as state::threshold_read and
the freeze reader do. Their compiler equations are independent of the generic
SEC theorem. Wire extraction and the remaining resource worklist bridge are not
silently assumed by these adapter refinements. -/
namespace CBCL.StateRuleRefinement
open State StateLift StateLVar StateObservation StateObservationPlan

/-- The native closure threshold reads the already displayed source, unwraps
its frozen value, returns an existing fault first, and selects the first reached
installed alternative. Installation separately establishes source monotonicity,
read upward-closure, incompatible alternatives and allowed freeze policy; this
adapter equality alone is not a stability proof. -/
def nativeClosureThreshold {V Q : Type} (alternatives : List Q) (test : Q → V → Bool)
    (source : StateObservationPlan.Observation V) : StateObservationPlan.Observation Q :=
  match source with
  | .fault evidence => .fault evidence
  | .data current => match current.payload with
    | none => .data .pending
    | some value => match alternatives.find? (fun q => test q value) with
      | none => .data .pending
      | some q => .data (.reached q)

def compileClosureThreshold {V Q : Type} (alternatives : List Q) (test : Q → V → Bool)
    (source : Plan V) : Plan Q := .thresholdOn alternatives test source

theorem closure_threshold_refinement {V Q : Type} (world : Act → Prop)
    (alternatives : List Q) (test : Q → V → Bool) (source : Plan V) (A : List Act) :
    observe world (compileClosureThreshold alternatives test source) A =
      nativeClosureThreshold alternatives test (observe world source A) := by
  cases h : errors world (path source) A <;>
    simp [compileClosureThreshold,observe,path,data,nativeClosureThreshold,h]
  cases payload : (data world source A).payload with
  | none => simp [payload]
  | some value =>
    cases found : alternatives.find? (fun q => test q value) <;> simp [payload,found]

/-- Domain selection is the concrete conflict-aware raw opener selection, not
an error-only decorator of an unfiltered field. -/
theorem domain_source_refinement {V : Type} (world : Act → Prop)
    (verb key opener field : String) (display : FinSet Act → V) (A : List Act) :
    observe world (.domain verb key opener field display) A =
      match domainRead verb key opener field A with
      | .fault evidence => .fault evidence
      | .value selected => .data (.snapshot (display selected)) := by
  cases h : initialCarrier opener field A <;>
    simp [observe,path,errors,domainError,data,domainRead,h]

theorem context_source_refinement (world : Act → Prop) (decode : Act → Option Val) (A : List Act) :
    observe world (.context decode) A =
      match StateContext.read decode A with
      | .fault evidence => .fault evidence
      | .pending => .data .pending
      | .value value => .data (.context value) := by
  cases h : StateContext.read decode A <;> simp [observe,path,errors,contextError,data,h]

def nativeDerived {V W : Type} (function : V → W)
    (source : StateObservationPlan.Observation V) : StateObservationPlan.Observation W :=
  match source with
  | .fault evidence => .fault evidence
  | .data value => .data (mapData function value)

theorem derived_source_refinement {V W : Type} (world : Act → Prop) (function : V → W)
    (source : Plan V) (A : List Act) :
    observe world (.map function source) A = nativeDerived function (observe world source A) := by
  cases h : errors world (path source) A <;> simp [observe,path,data,nativeDerived,h]

def sourceError {V : Type} : StateObservationPlan.Observation V → Error
  | .fault e => some e
  | .data _ => none

def sourceData {V : Type} : StateObservationPlan.Observation V → Data V
  | .fault _ => .pending
  | .data value => value

theorem source_error_refinement {V : Type} (world : Act → Prop) (source : Plan V) (A : List Act) :
    sourceError (observe world source A) = errors world (path source) A := by
  cases h : errors world (path source) A <;> simp [observe,sourceError,h]

theorem cut_closed {world : Act → Prop} {A : List Act} (closed : CausallyClosed world A) (f : Act) :
    CausallyClosed world (causalCut world A f) := by
  classical
  intro child inside parent valid edge
  have accepted := List.mem_filter.mp inside
  have path : Ancestor world child f := of_decide_eq_true accepted.2
  exact List.mem_filter.mpr ⟨closed child accepted.1 parent valid edge,
    decide_eq_true (Ancestor.step valid edge path)⟩

theorem clear_cut {world : Act → Prop} {A : List Act} (closed : CausallyClosed world A)
    (source : Path) (clear : errors world source A = none) (f : Act) :
    errors world source (causalCut world A f) = none := by
  classical
  cases cut : errors world source (causalCut world A f) with
  | none => rfl
  | some e =>
    obtain ⟨enlarged,h,_⟩ := errors_persist world source (cut_closed closed f)
      (fun a ha => (List.mem_filter.mp ha).1) e cut
    rw [clear] at h
    contradiction

def presentFreeze {V : Type} : FreezeRead (Data V) → StateObservationPlan.Observation V
  | .fault e => .fault e
  | .snapshot value => .data value
  | .frozen freezer value excluded => .data (frozenData (.frozen freezer value excluded))

noncomputable def nativeFreeze {V : Type} (world : Act → Prop) (spec : FreezeSpec)
    (source : List Act → StateObservationPlan.Observation V) (A : List Act) :
    StateObservationPlan.Observation V :=
  presentFreeze (freezeRead world spec.verb spec.contributes spec.policy (sourceError (source A))
    (fun C => sourceData (source C)) A)

/-- The native freeze adapter and compiled typed plan have identical fault
unions and identical historical source values. The closed-cut premise is the
actual admission invariant, not a resource/finality assumption. -/
theorem freeze_source_refinement {V : Type} (world : Act → Prop) (spec : FreezeSpec)
    (source : Plan V) {A : List Act} (closed : CausallyClosed world A) :
    observe world (.freeze spec source) A =
      nativeFreeze world spec (fun C => observe world source C) A := by
  classical
  unfold nativeFreeze
  rw [source_error_refinement]
  cases raw : errors world (path source) A with
  | some e =>
    simp [observe,path,errors,freezeFault,data,freezeRead,raw,presentFreeze]
  | none =>
    by_cases conflict : ∃ a b, FreezeConflict world spec.verb spec.contributes spec.policy A a b
    · simp [observe,path,errors,freezeFault,data,freezeRead,raw,conflict,presentFreeze]
    · cases first : A.find? (fun f => decide (Earliest world spec.verb A f)) with
      | none =>
        simp [observe,path,errors,freezeFault,data,freezeRead,raw,conflict,first,presentFreeze,sourceData,frozenData]
      | some f =>
        have cut := clear_cut closed (path source) raw f
        simp [observe,path,errors,freezeFault,data,freezeRead,raw,conflict,first,presentFreeze,sourceData,frozenData,cut]

end CBCL.StateRuleRefinement
