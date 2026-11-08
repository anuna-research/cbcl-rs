import LeanCbcl.StateResourceCycle
import LeanCbcl.StateResourceTests

namespace CBCL.StateResourceKahnTests
open StateResourceKahn

def chainParents (node : Nat) : List Nat := if node = 2 then [1] else []
def cycleParents (node : Nat) : List Nat := if node = 1 then [2] else if node = 2 then [1] else []
def missingParents (node : Nat) : List Nat := if node = 2 then [3] else []

theorem acyclic_pass_removes_all : nativeKahn chainParents [1,2] = [] := by decide

theorem cycle_pass_retains_nodes : nativeKahn cycleParents [1,2] ≠ [] := by decide

theorem cycle_pass_has_witness : HasCycle cycleParents [1,2] :=
  (nativeKahn_cycle_iff cycleParents [1,2]).mp cycle_pass_retains_nodes

/-- The structural pass releases an external missing reference rather than
misclassifying the waiting operation as a cycle. -/
theorem missing_reference_is_not_a_cycle : nativeKahn missingParents [1,2] = [] := by decide

theorem budget_pass_keeps_missing_reference : nativeBudgetRemaining missingParents [1,2] = [2] := by decide

theorem budget_pass_processes_independent_component : nativeBudgetProcessed missingParents [1,2] = [1] := by decide

end CBCL.StateResourceKahnTests
