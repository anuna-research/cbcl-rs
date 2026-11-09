import LeanCbcl.StateFiniteProjection

/-! SPEC-038 TEST-3808: native finite row checks reject invalid data before
constructing a source or any stable threshold policy. -/
set_option autoImplicit false
namespace CBCL.StateFiniteProjectionTests
open State StateLift StateFiniteTable StateFiniteProjection

/-- Two-element bounded carrier, with all four ordered join rows. -/
def table : StateFiniteTable.Resolved := {
  name := "presence"
  elements := ["empty","conflict"]
  bottom := ⟨0,by decide⟩
  top := ⟨1,by decide⟩
  rows := [((⟨0,by decide⟩,⟨0,by decide⟩),⟨0,by decide⟩),
    ((⟨0,by decide⟩,⟨1,by decide⟩),⟨1,by decide⟩),
    ((⟨1,by decide⟩,⟨0,by decide⟩),⟨1,by decide⟩),
    ((⟨1,by decide⟩,⟨1,by decide⟩),⟨1,by decide⟩)] }

/-- Both table laws and projection order are computed, without axioms. -/
theorem native_table_checks : StateFiniteTable.check 64 table = true := by decide

theorem numeric_projection_accepted : StateFiniteProjection.check table
    ⟨true,[(table.bottom,.int 0),(table.top,.int 1)]⟩ = true := by decide

theorem boolean_projection_accepted : StateFiniteProjection.check table
    ⟨true,[(table.bottom,.bool false),(table.top,.bool true)]⟩ = true := by decide

theorem decreasing_projection_rejected : StateFiniteProjection.check table
    ⟨true,[(table.bottom,.int 1),(table.top,.int 0)]⟩ = false := by decide

theorem string_stable_projection_rejected : StateFiniteProjection.check table
    ⟨true,[(table.bottom,.str "empty"),(table.top,.str "conflict")]⟩ = false := by decide

theorem mixed_stable_projection_rejected : StateFiniteProjection.check table
    ⟨true,[(table.bottom,.int 0),(table.top,.bool true)]⟩ = false := by decide

theorem snapshot_string_projection_accepted : StateFiniteProjection.check table
    ⟨false,[(table.bottom,.str "empty"),(table.top,.str "conflict")]⟩ = true := by decide

theorem top_row_required : StateFiniteProjection.check table
    ⟨false,[(table.bottom,.int 0)]⟩ = false := by decide

theorem duplicate_row_rejected : StateFiniteProjection.check table
    ⟨false,[(table.bottom,.int 0),(table.bottom,.int 0),(table.top,.int 1)]⟩ = false := by decide

theorem structured_projection_rejected : StateFiniteProjection.check table
    ⟨false,[(table.bottom,.list []),(table.top,.int 1)]⟩ = false := by decide

theorem oversized_literal_rejected : scalarCheck (.int (2^63)) = false := by decide

theorem unknown_contribution_rejected : resolveRow table ⟨"phase",.str "yes","unknown"⟩ = none := by decide

theorem structured_contribution_rejected : resolveRow table ⟨"phase",.list [],"empty"⟩ = none := by decide

/-- Both rows match; the second must not be ignored after the first match. -/
theorem every_matching_row_contributes : contribution table
    [⟨"phase",.str "yes",table.bottom,by decide⟩,⟨"phase",.str "yes",table.top,by decide⟩]
    ⟨1,"vote","@alice",[],[("phase",.str "yes")],[]⟩ = table.top := by decide

theorem nonmatching_row_contributes_bottom : contribution table
    [⟨"phase",.str "yes",table.top,by decide⟩]
    ⟨1,"vote","@alice",[],[("phase",.str "no")],[]⟩ = table.bottom := by decide

end CBCL.StateFiniteProjectionTests
