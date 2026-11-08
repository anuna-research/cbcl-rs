import LeanCbcl.StateFiniteRead
import LeanCbcl.StateFiniteProjectionTests

/-! SPEC-038 TEST-3808: finite reads are typed against the source's installed
carrier and checked projection, including non-top common-upper-state rejection. -/
set_option autoImplicit false
namespace CBCL.StateFiniteReadTests
open State StateLift StateInstalledFinite StateFiniteRead

/-- Finite source with an actual checked numeric stable projection. -/
def field : Field := {
  table := ⟨StateFiniteProjectionTests.table,64,StateFiniteProjectionTests.native_table_checks⟩
  verb := "vote"
  rows := []
  projection := some ⟨⟨true,[(StateFiniteProjectionTests.table.bottom,.int 0),
    (StateFiniteProjectionTests.table.top,.int 1)]⟩,StateFiniteProjectionTests.numeric_projection_accepted⟩
  domains := [] }

theorem named_bottom_accepted : check field [.str "empty"] = true := by decide

theorem named_top_rejected : check field [.str "conflict"] = false := by decide

theorem numeric_projection_accepted : check field [.int 0] = true := by decide

theorem mixed_query_common_upper_rejected : check field [.str "empty",.int 0] = false := by decide

theorem duplicate_query_rejected : check field [.int 0,.int 0] = false := by decide

theorem empty_query_rejected : check field [] = false := by decide

theorem boolean_query_on_numeric_projection_rejected : check field [.bool true] = false := by decide

theorem unknown_named_query_rejected : check field [.str "unknown"] = false := by decide

theorem oversized_numeric_query_rejected : check field [.int (2^63)] = false := by decide

/-- Matching a structured contribution literal cannot bypass row validation. -/
theorem invalid_literal_factory_rejected : StateInstalledFinite.make
    ⟨["vote"],[(("vote","phase"),.list)]⟩ field.table []
    ⟨"vote",[⟨"phase",.list [],"empty"⟩],none⟩ = none := by decide

theorem unknown_keyword_factory_rejected : StateInstalledFinite.make
    ⟨["vote"],[]⟩ field.table [] ⟨"vote",[⟨"phase",.str "yes","empty"⟩],none⟩ = none := by decide

theorem empty_contributions_factory_rejected : StateInstalledFinite.make
    ⟨["vote"],[]⟩ field.table [] ⟨"vote",[],none⟩ = none := by decide

theorem valid_literal_factory_accepted : (StateInstalledFinite.make
    ⟨["vote"],[(("vote","phase"),.string)]⟩ field.table []
    ⟨"vote",[⟨"phase",.str "yes","empty"⟩],none⟩).isSome = true := by decide

end CBCL.StateFiniteReadTests
