import LeanCbcl.StateNonnegativeAdmission
import LeanCbcl.StateAuthoredEventSumTests

/-! Shape projection fixtures preserve first-keyword behavior and scalar types.
The message/typed-field relation is proved for this concrete expanded message. -/
namespace CBCL.StateNonnegativeAdmissionTests
open State StateInstalledLegacy StateNonnegativeAdmission

/-- The contributing writer's required nonnegative shape. -/
def shapes : List WriterShape := [⟨"mint","amount",true,true⟩]
/-- Expanded typed writer message. -/
def message : SExpr := .list [.atom (.symbol "mint"),.atom (.keyword "amount"),.atom (.num 5)]

/-- Successful shape projection is computed, not presumed from metadata. -/
theorem checked : checkedWriter shapes StateAuthoredEventSumTests.writer message = true := by decide

/-- The expanded numeric lookup agrees with the actual fixture's typed fields. -/
theorem extracted : NumericExtraction StateAuthoredEventSumTests.writer message := by
  intro field n found
  by_cases same : field = "amount"
  · subst field
    have number : n = 5 := by simpa [findKeyword,findItems,message] using found.symm
    subst n
    rfl
  · have different : "amount" ≠ field := Ne.symm same
    simp [findKeyword,findItems,message,different,beq_iff_eq] at found

/-- The sum premise follows from the computed checks and extraction. -/
theorem checked_writer_amount : 0 ≤ amount "amount" StateAuthoredEventSumTests.writer :=
  checked_amount shapes "mint" "amount" StateAuthoredEventSumTests.writer message rfl rfl checked extracted

/-- A negative first occurrence cannot be rescued by a later positive one. -/
theorem negative_first_rejected : checkProjection ⟨"mint","amount",true,true⟩
    (.list [.atom (.keyword "amount"),.atom (.num (-1)),.atom (.keyword "amount"),.atom (.num 5)]) = false := by decide

/-- A positive first occurrence is not overwritten by a later negative one. -/
theorem positive_first_retained : checkProjection ⟨"mint","amount",true,true⟩
    (.list [.atom (.keyword "amount"),.atom (.num 5),.atom (.keyword "amount"),.atom (.num (-1))]) = true := by decide

/-- A dangling required keyword has no value. -/
theorem dangling_rejected : checkProjection ⟨"mint","amount",true,true⟩
    (.list [.atom (.keyword "amount")]) = false := by decide

/-- A quoted numeral is a string, not a numeric atom. -/
theorem quoted_number_rejected : checkProjection ⟨"mint","amount",true,true⟩
    (.list [.atom (.keyword "amount"),.atom (.str "5")]) = false := by decide

end CBCL.StateNonnegativeAdmissionTests
