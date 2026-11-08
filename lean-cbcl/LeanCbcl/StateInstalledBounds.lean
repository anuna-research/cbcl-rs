import LeanCbcl.StateInstalledContext

/-! Native R7 state bounds are positive tightenings of fixed defaults.
These checks precede authored source construction, including finite tables. -/
set_option autoImplicit false
namespace CBCL.StateInstalledBounds
open StateInstalledContext

/-- The exact native default upper bounds, in context metadata field order. -/
def defaults : Bounds := ⟨32,64,1000000000000,2048⟩

/-- Recognize positive state bounds that do not exceed the native defaults. -/
def check (bounds : Bounds) : Bool :=
  decide (bounds.maxString ≤ defaults.maxString ∧ bounds.maxList ≤ defaults.maxList ∧
    bounds.maxNumber ≤ defaults.maxNumber ∧ bounds.maxFields ≤ defaults.maxFields) &&
  decide (0 < bounds.maxString ∧ 0 < bounds.maxList ∧ 0 < bounds.maxNumber ∧ 0 < bounds.maxFields)

/-- Installation bounds used by typed source factories and machine-index proofs. -/
def Valid (bounds : Bounds) : Prop :=
  (bounds.maxString ≤ 2048 ∧ bounds.maxList ≤ 64 ∧ bounds.maxNumber ≤ 1000000000000 ∧ bounds.maxFields ≤ 32) ∧
  (0 < bounds.maxString ∧ 0 < bounds.maxList ∧ 0 < bounds.maxNumber ∧ 0 < bounds.maxFields)

/-- Successful checking is exactly the native state-bound constraint. -/
theorem check_iff (bounds : Bounds) : check bounds = true ↔ Valid bounds := by
  simp [check,Valid,defaults]

/-- Literal R7 rejection conditions, without collapsing its two diagnostics. -/
def rejected (bounds : Bounds) : Bool :=
  decide (bounds.maxString > 2048 ∨ bounds.maxList > 64 ∨ bounds.maxNumber > 1000000000000 ∨ bounds.maxFields > 32) ||
  decide (bounds.maxString = 0 ∨ bounds.maxList = 0 ∨ bounds.maxNumber ≤ 0 ∨ bounds.maxFields = 0)

/-- The positive model gate and the native disjunctive rejection tests agree. -/
theorem native_gate_refinement (bounds : Bounds) : check bounds = !rejected bounds := by
  apply Bool.eq_iff_iff.mpr
  simp [check,defaults,rejected]
  omega

/-- The installed list bound is positive and bounded by the default 64. -/
theorem list_bound (bounds : Bounds) (checked : check bounds = true) : 0 < bounds.maxList ∧ bounds.maxList ≤ 64 := by
  have valid := (check_iff bounds).mp checked
  exact ⟨valid.2.2.1,valid.1.2.1⟩

end CBCL.StateInstalledBounds
