import LeanCbcl.StateCondition

/-! Enumerable execution of the proved fault-first condition algebra. Evidence
lists are transport witnesses for the same semantic sets, including empty faults. -/
set_option autoImplicit false
namespace CBCL.StateExecutableCondition
open State StateObservation StateObservationPlan StateCondition

/-- Enumerable condition outcomes preserve terminal empty evidence. -/
inductive Result where
  | pending
  | reached
  | fault (ids : List Nat)
  deriving BEq

/-- Interpret enumerable evidence in the kernel's exact observation type. -/
def Result.semantic : Result → Observation Bool
  | .pending => .data .pending
  | .reached => .data (.reached true)
  | .fault ids => .fault (fun id => id ∈ ids)

/-- Executable counterpart of the condition merge, retaining all witnesses. -/
def merge : Result → Result → Result
  | .fault a, .fault b => .fault (a ++ b)
  | .fault a, _ => .fault a
  | _, .fault b => .fault b
  | .reached, .reached => .reached
  | _, _ => .pending

/-- The executable merge refines the proved condition operator exactly. -/
theorem merge_refinement (a b : Result) : (merge a b).semantic = StateCondition.merge a.semantic b.semantic := by
  cases a <;> cases b <;> try rfl
  rename_i a b
  apply congrArg Observation.fault
  funext id
  apply propext
  exact List.mem_append

/-- Execute every sibling before resolving pending and successful outcomes. -/
def combine : List Result → Result
  | [] => .reached
  | first :: rest => merge first (combine rest)

/-- Whole condition execution preserves status and exact dependency evidence. -/
theorem combine_refinement (values : List Result) :
    (combine values).semantic = StateCondition.combine (values.map Result.semantic) := by
  induction values with
  | nil => rfl
  | cons head tail ih => rw [combine,merge_refinement,ih]; rfl

end CBCL.StateExecutableCondition
