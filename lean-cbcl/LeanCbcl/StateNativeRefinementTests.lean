import LeanCbcl.StateRuleRefinement
import LeanCbcl.StateResourceTests
import LeanCbcl.StateResourceSummary
import LeanCbcl.StateCountRefinement

namespace CBCL.StateNativeRefinementTests
open State StateLift StateResource StateResourceNative StateResourceTests
open StateObservation StateObservationPlan StateRuleRefinement

theorem native_initialization_accepts : initializationCheck config opener root = true :=
  (initializationCheck_iff config opener root).mpr valid_opener

theorem native_operation_shape_accepts : operationCheck config opener root burn = true :=
  (operationCheck_iff config opener root burn).mpr valid_burn_shape

theorem empty_certificate_accounts_rejected : ¬validAccounts (.value []) := by simp [validAccounts]

theorem account_spelling_rejected : allocationsCheck (.value [("alice",1)]) = false := by decide

theorem grouped_negative_budget : groupedIncoming [[1],[2]] (-3) = some 0 := by decide

theorem grouped_near_limit : groupedIncoming [[2^127-1],[2^127-1]] (-(2^127)) = some (2^127-2) := by decide

/-- The read strategy consumes the actual displayed source, not an unrelated
lift/contribution function. This is the former source-coherence counterexample. -/
theorem source_linked_threshold_pending (world : Act → Prop) (A : List Act) :
    observe world (.thresholdOn [10] (fun q value : Nat => decide (q ≤ value))
      (.snapshot (fun _ => 0))) A = .data .pending := rfl

theorem source_linked_threshold_reached (world : Act → Prop) (A : List Act) :
    observe world (.thresholdOn [10] (fun q value : Nat => decide (q ≤ value))
      (.snapshot (fun _ => 12))) A = .data (.reached 10) := rfl

theorem frozen_closure_threshold (excluded : FinSet Act) :
    nativeClosureThreshold [10] (fun q value : Nat => decide (q ≤ value))
      (.data (.frozen 7 12 excluded)) = .data (.reached 10) := rfl

theorem fault_closure_threshold (e : Evidence) :
    nativeClosureThreshold [10] (fun q value : Nat => decide (q ≤ value))
      (.fault e) = .fault e := rfl

end CBCL.StateNativeRefinementTests
