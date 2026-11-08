import LeanCbcl.StateObservation
/-! Regression: a monotone, extensional guard reporting every identity must
not qualify as a certified observation extension. -/
namespace CBCL.StateEvidenceSupportTests
open CBCL.State CBCL.StateObservation
/--
error: Fields missing: `support`

Hint: Add missing fields:
  
  ̲ ̲ ̲s̲u̲p̲p̲o̲r̲t̲ ̲:̲=̲ ̲_̲
-/
#guard_msgs in
example : ErrorSpec := {
  read := fun _ => some (fun _ => True)
  equiv := fun _ => rfl
  grow := by
    intro A B growth evidence observed
    cases Option.some.inj observed
    exact ⟨(fun _ => True),rfl,fun _ member => member⟩ }
end CBCL.StateEvidenceSupportTests
