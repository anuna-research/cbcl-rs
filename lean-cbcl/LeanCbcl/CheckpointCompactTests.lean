import LeanCbcl.CheckpointCompact

/-! Kernel-checked examples and axiom audit; no native evaluation trust shortcut. -/
namespace CBCL.CheckpointCompact.Tests
open CBCL.State CBCL.StateKernelQueries CBCL.StateKernelSemantics

private def opener (n : Nat) : Act :=
  ⟨n, "open", "@a", [], [("value", .int n)], []⟩

private def initialTail : List (Act × Bool) :=
  [(opener 1, false), (opener 1, true), (opener 2, false), (opener 1, true)]

example : ValidTail [] initialTail := by
  simp [initialTail, ValidTail, ExactCoverage, Compatible, opener]

example : Initial.run "open" .empty initialTail = .many (opener 1) (opener 2) := by decide

example : Initial.render "value" (Initial.run "open" .empty initialTail) = .absent := by decide

example : Initial.render "value" (Initial.run "open" .empty initialTail) =
    project "value" false (sole (acts "open" (extend [] initialTail))) := by
  apply Initial.from_genesis
  simp [initialTail, ValidTail, ExactCoverage, Compatible, opener]

private def writer (n : Nat) : Act :=
  ⟨n, "write", "@a", [], [("value", .int n)], []⟩

private def clock : Clock := fun _ a => if a.addr = 99 then none else some (a.addr, 0)
private def rank : SignerRank := fun _ => 0
private def lwwTail : List (Act × Bool) :=
  [(writer 1, false), (writer 3, false), (writer 2, false),
   (writer 99, false), (writer 3, true)]

example : ValidTail [] lwwTail := by
  simp [lwwTail, ValidTail, ExactCoverage, Compatible, writer]

/-- Includes an older valid HLC loser, an invalid-clock act and a covered repeat. -/
example : LwwRegister.render "value"
    (LwwRegister.run clock rank "write" "clock" none lwwTail) = .value (.int 3) := by
  decide

example : LwwRegister.incoming clock rank "write" "clock" (writer 99) = none := rfl

example : LwwRegister.render "value"
    (LwwRegister.run clock rank "write" "clock" none lwwTail) =
    project "value" false (choose clock rank (.hlc "clock") (acts "write" (extend [] lwwTail))) := by
  apply LwwRegister.from_genesis
  simp [lwwTail, ValidTail, ExactCoverage, Compatible, writer]

#print axioms Initial.step_preserves
#print axioms Initial.continuation
#print axioms Initial.sole_acts_eq
#print axioms Initial.continuation_sole_acts
#print axioms Initial.from_genesis
#print axioms LwwRegister.step_preserves
#print axioms LwwRegister.continuation
#print axioms LwwRegister.acts_live_eq
#print axioms LwwRegister.choose_acts_live_eq
#print axioms LwwRegister.choose_live_eq
#print axioms LwwRegister.continuation_choose
#print axioms LwwRegister.from_genesis

end CBCL.CheckpointCompact.Tests
