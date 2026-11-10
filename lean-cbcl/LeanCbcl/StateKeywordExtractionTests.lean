import LeanCbcl.StateKeywordExtraction
import LeanCbcl.StateNonnegativeAdmissionTests

/-! Grammar, duplicate, routing and amount-preservation fixtures. -/
namespace CBCL.StateKeywordExtractionTests
open State StateKeywordExtraction

/-- A valid numeric writer supplies the exact typed field used by the sum. -/
theorem numeric_extracted : extract [.atom (.keyword "amount"),.atom (.num 5)] = some [("amount",.int 5)] := by decide

/-- Ambiguous data keys reject even when their values are equal or nonnegative. -/
theorem duplicates_rejected : extract (encode [("amount",.atom (.num 10)),("amount",.atom (.num (-1)))]) = none ∧
    extract (encode [("amount",.atom (.num 1)),("amount",.atom (.num 1))]) = none := by decide

/-- Low-level routing exclusion does not invent a duplicate-data failure.
Boundary recognition separately rejects this input before reaching R7. -/
theorem routing_repetitions : extract (encode [("thread",.atom (.str "a")),("thread",.atom (.str "b")),("amount",.atom (.num 5))]) =
    some [("amount",.int 5)] := by decide

/-- Duplicate lifted and unlifted routing keys reject at message recognition. -/
theorem boundary_routing_repetitions_rejected :
    ∀ key ∈ ["thread","sender","caused-by","from","to"],
      parseBoundary (encode [(key,.atom (.str "a")),("amount",.atom (.num 5)),(key,.atom (.str "b"))]) = none := by decide

/-- A single routing key remains valid; canonicalisation preserves opaque values. -/
theorem boundary_order :
    parseBoundary (encode [("thread",.atom (.str "a")),("amount",.atom (.num 5))]) =
      some [("thread",.atom (.str "a")),("amount",.atom (.num 5))] ∧
    canonicalRows [("other",.atom (.keyword "amount")),("amount",.atom (.num 5))] =
      [("amount",.atom (.num 5)),("other",.atom (.keyword "amount"))] := by
  simp +decide [canonicalRows,List.mergeSort]

/-- Positional and dangling keyword parameters reject before extraction. -/
theorem malformed_rejected : extract [.atom (.num 5)] = none ∧ extract [.atom (.keyword "amount")] = none := by decide

/-- A keyword-looking value cannot create a numeric amount at the next key. -/
theorem keyword_value_does_not_forge : StateNonnegativeAdmission.findItems "amount"
    (encode [("other",.atom (.keyword "amount")),("amount",.atom (.num 5))]) = some (.atom (.keyword "amount")) := rfl

/-- Checked numeric amounts are derived from recognized source parameters,
without supplying the earlier NumericExtraction relation. -/
theorem checked_amount : 0 ≤ amount "amount" StateAuthoredEventSumTests.writer :=
  StateKeywordExtraction.checked_amount StateNonnegativeAdmissionTests.shapes "mint" "amount"
    StateAuthoredEventSumTests.writer [.atom (.symbol "mint")] [.atom (.keyword "amount"),.atom (.num 5)]
    (by decide) numeric_extracted (by decide) rfl (by decide)

end CBCL.StateKeywordExtractionTests
