import LeanCbcl.StateExecutableFreeze
import LeanCbcl.StateRuleRefinement

/-! Computable pending/value/frozen/fault composition for the live oracle.
Derived maps consume observed payloads. Freeze adaptation keeps the current
fault channel and delegates exact historical reads to StateExecutableFreeze. -/
set_option autoImplicit false
namespace CBCL.StateExecutableObservation
open State StateLift StateLVar StateObservationPlan StateRuleRefinement StateExecutableFreeze

/-- Enumerable counterpart of the observation tags used by this oracle profile. -/
inductive View (V : Type) where
  | pending
  | snapshot (value : V)
  | frozen (freezer : Nat) (value : V) (excluded : List Act)
  | fault (evidence : List Nat)

/-- Interpret enumerable observations in the existing semantic observation type. -/
def View.semantic {V : Type} : View V → Observation V
  | .pending => .data .pending
  | .snapshot value => .data (.snapshot value)
  | .frozen root value excluded => .data (.frozen root value (FinSet.mk excluded))
  | .fault evidence => .fault (fun address => address ∈ evidence)

/-- A derived field discards source freeze metadata while preserving its value and faults. -/
def View.map {V W : Type} (post : V → W) : View V → View W
  | .pending => .pending
  | .snapshot value | .frozen _ value _ => .snapshot (post value)
  | .fault evidence => .fault evidence

/-- Computable derived fields equal the existing independent native map adapter. -/
theorem map_refinement {V W : Type} (post : V → W) (source : View V) :
    (source.map post).semantic = nativeDerived post source.semantic := by
  cases source <;> rfl

/-- Extract only the current raw fault, before any historical cut. -/
def View.error {V : Type} : View V → Option (List Nat)
  | .fault evidence => some evidence
  | _ => none

/-- Enumerable faults map exactly to the existing semantic source-error channel. -/
theorem error_refinement {V : Type} (source : View V) :
    source.error.map (fun addresses => fun address => address ∈ addresses) = sourceError source.semantic := by
  cases source <;> rfl

/-- Present source data after the outer freeze has checked its raw fault channel. -/
def present {V : Type} : Read (View V) → View V
  | .fault evidence => .fault evidence
  | .snapshot (.fault _) => .pending
  | .snapshot value => value
  | .frozen root value excluded => match value with
      | .pending | .fault _ => .pending
      | .snapshot payload | .frozen _ payload _ => .frozen root payload excluded

/-- Functor on semantic frozen reads; the witness channel is untouched. -/
def mapRead {V W : Type} (post : V → W) : FreezeRead V → FreezeRead W
  | .snapshot value => .snapshot (post value)
  | .frozen root value excluded => .frozen root (post value) excluded
  | .fault evidence => .fault evidence

/-- Semantic freeze evaluation commutes with an arbitrary payload projection. -/
theorem map_read {V W : Type} (post : V → W) (world : Act → Prop) (verb : String)
    (contributes : Act → Prop) (policy : Bool) (raw : Option (Lattice.Set Nat))
    (evaluate : List Act → V) (A : List Act) :
    mapRead post (freezeRead world verb contributes policy raw evaluate A) =
      freezeRead world verb contributes policy raw (fun C => post (evaluate C)) A := by
  classical
  unfold freezeRead
  split
  · rfl
  · cases A.find? (fun a => decide (Earliest world verb A a)) <;> rfl

/-- Enumerable freeze presentation exactly matches the native semantic presenter. -/
theorem present_refinement {V : Type} (result : Read (View V)) :
    (present result).semantic = presentFreeze (mapRead (fun view => sourceData view.semantic) result.semantic) := by
  cases result with
  | fault evidence => rfl
  | snapshot view => cases view <;> rfl
  | frozen root view excluded => cases view <;> rfl

/-- Compose a source observation with an exact computable causal freeze. -/
def freeze {V : Type} (A : List Act) (verb : String) (contributes : Act → Bool) (policy : Bool)
    (source : List Act → View V) : View V :=
  present (StateExecutableFreeze.read A verb contributes policy (source A).error source)

/-- Complete compositional freeze refinement for arbitrary source observations;
no source-value correctness or fault-persistence premise is assumed. -/
theorem freeze_refinement {V : Type} (A : List Act) (ranked : Ranked A) (verb : String)
    (contributes : Act → Bool) (policy : Bool) (source : List Act → View V) :
    (freeze A verb contributes policy source).semantic =
      nativeFreeze (fun act => act ∈ A) ⟨verb,fun act => contributes act = true,policy⟩
        (fun C => (source C).semantic) A := by
  unfold freeze
  rw [present_refinement,StateExecutableFreeze.read_refinement A ranked,map_read,error_refinement]
  rfl

end CBCL.StateExecutableObservation
