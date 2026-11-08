import LeanCbcl.StateReaderReachability
import LeanCbcl.StateAuthoredBindingsTests

/-! Non-vacuity and native entry-order witnesses for complete request safety. -/
namespace CBCL.StateReaderReachabilityTests
open State StateAuthoredBindings StateReaderReachability StateAuthoredBindingsTests

/-- Threshold output names are absent from the native field-request sequence;
its repeated source reuses the same scoped cache key. -/
theorem review_request_keys : initialKeys review =
    [(0,"reviewers"),(0,"votes"),(0,"votes"),(0,"sealed")] := rfl

/-- The concrete installed context/count/threshold/freeze example establishes
admitted requests without assuming a successful preparation result. -/
theorem review_requests_admitted (context : StateKernelSEC.Context) (whole : List Act)
    (ranked : StateExecutableFreeze.Ranked whole)
    (consistent : ∀ a ∈ whole, ∀ b ∈ whole, a.addr = b.addr → a = b) :
    ∃ clause, prepare (environment context) review whole = some clause ∧
      ∀ key ∈ initialKeys review, Admitted review whole clause.freezes key := by
  cases prepared : prepare (environment context) review whole with
  | none => have nonempty := review_prepares context whole; simp [prepared] at nonempty
  | some clause =>
    exact ⟨clause,rfl,initial_keys_admitted (environment context) review whole clause prepared ranked consistent⟩

end CBCL.StateReaderReachabilityTests
