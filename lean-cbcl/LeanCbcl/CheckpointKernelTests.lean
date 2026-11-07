import LeanCbcl.CheckpointKernel
import LeanCbcl.CheckpointCompactTests

/-! Executable adversarial instances of the proved compact continuation law.
Closed examples use kernel reduction (`decide`), never `native_decide`.
-/
namespace CBCL.CheckpointKernel.Tests
open State StateKernelQueries StateKernel CheckpointSummary

private def act (id : Nat) (verb signer item value : String) (stamp : Int)
    (refs : List Nat := []) : Act :=
  ⟨id, verb, signer, [], [("item", .str item), ("value", .str value),
    ("title", .str value), ("stamp", .int stamp)], refs⟩

private def clock : Clock := fun field a => match a.get field with
  | some (.int stamp) => if 0 ≤ stamp then some (stamp.toNat, 0) else none
  | _ => none
private def input : Input :=
  ⟨[], "open", clock, fun signer => if signer = "@b" then 1 else 0,
    fun _ => none, 0, fun _ => 0, fun _ => .pending []⟩

private def fields : List (String × Rule) :=
  [("title", .initial "open" "title"), ("values", .values "put" "value"),
   ("byKey", .valuesPerKey "put" "item" "value" (some "drop")),
   ("set", .observedSet "put" "drop" "item"),
   ("latest", .lwwRegister "put" "value" "stamp"),
   ("bySigner", .lwwPerSigner "put" "value" "stamp"),
   ("map", .lwwMap "put" "item" "value" "stamp" (some "drop"))]
private def older := act 1 "put" "@a" "x" "old" 1
private def newer := act 2 "put" "@a" "x" "new" 2
private def removeNewer := act 3 "drop" "@a" "x" "unused" 3 [2]
private def opener := act 10 "open" "@a" "unused" "Drawing" 0
private def history := [opener, older, newer]
private def tail := [removeNewer, newer, act 4 "put" "@b" "y" "other" 2 [1]]

/-- The complete seven-rule clause, not just a toy scalar fold. -/
example : ((Snapshot.checkpoint input fields history).advance input tail).render input =
    fullFold input fields (history ++ tail) :=
  render_advance_checkpoint input fields history tail

/-- Every history cut and arbitrary suffix is covered by the theorem. -/
example (H D : List Act) :
    ((Snapshot.checkpoint input fields H).advance input D).render input =
      fullFold input fields (H ++ D) := render_advance_checkpoint input fields H D

private def mapRead (s : Snapshot) (name key : String) : Option Cell :=
  match (s.render input).lookup name with
  | some (.mapped read) => read (.str key)
  | _ => none

/-- The older surviving HLC contribution resurfaces after the winner is removed. -/
example : mapRead ((Snapshot.checkpoint input fields history).advance input [removeNewer])
    "map" "x" = some (.value (.str "old")) := by decide

/-- Global LWW ignores observed replacement; only its maximum is retained. -/
example : (CheckpointCompact.LwwRegister.liveActs
    (CheckpointCompact.LwwRegister.run input.clock input.signerRank "put" "stamp" none
      [(older, false), (newer, false), (removeNewer, false)])).length = 1 := by decide

private def cfg := Config.current "put" (some "item") (some "drop")
private def earlyRemove := act 8 "drop" "@a" "x" "unused" 8 [1]
private def pendingCut := RowState.checkpoint cfg [earlyRemove]

example : pendingCut.row.live = [] := by decide
example : (some (.str "x"), 1) ∈ pendingCut.row.pending := by decide
example : (pendingCut.advance cfg [older]).row.live = [] := by decide
example : (pendingCut.advance cfg [older]).row.pending = [] := by decide

/-- A mutation dropping pending suppressions wrongly resurrects the late target. -/
private def forgottenPending : RowState := ⟨pendingCut.coverage, ⟨pendingCut.row.live, []⟩⟩
example : (forgottenPending.advance cfg [older]).row.live = [older] := by decide
example : (forgottenPending.advance cfg [older]).row.live ≠
    (pendingCut.advance cfg [older]).row.live := by decide

/-- Cross-key references cannot suppress a contribution from another key. -/
private def foreignRemove := act 8 "drop" "@a" "y" "unused" 8 [1]
example : ((RowState.checkpoint cfg [foreignRemove]).advance cfg [older]).row.live = [older] := by decide
example : ((RowState.checkpoint cfg [foreignRemove]).advance cfg [older]).row.pending = [] := by decide

/-- A non-state message resolves every pending scope for its now-known identity. -/
private def note := act 1 "note" "@a" "x" "not a contribution" 0
example : (pendingCut.advance cfg [note]).row.pending = [] := by decide
example : (pendingCut.advance cfg [note]).row.live = [] := by decide

/-- Removing only the winner from a lossy LWW map loses an otherwise live value. -/
private def fullRow := RowState.checkpoint cfg [older, newer]
private def winnerOnly : RowState := ⟨fullRow.coverage, ⟨[newer], []⟩⟩
example : (fullRow.advance cfg [removeNewer]).row.live = [older] := by decide
example : (winnerOnly.advance cfg [removeNewer]).row.live = [] := by decide

/-- An already-covered delivery cannot undo compaction or duplicate a value. -/
example : ((Snapshot.checkpoint input fields history).advance input [newer]).schema = fields := by decide
example : (fullRow.advance cfg [newer]).row.live = fullRow.row.live := by decide

/-- References in another authenticated signer's scope do not retire our write. -/
private def ownCfg := Config.own "put"
private def otherSigner := act 2 "put" "@b" "x" "other" 2 [1]
example : ((RowState.checkpoint ownCfg [older]).advance ownCfg [otherSigner]).row.live =
    [otherSigner, older] := by decide

#print axioms step_preserves
#print axioms checkpoint_continuation
#print axioms live_current
#print axioms live_own
#print axioms rule_step_valid
#print axioms rule_render_eq
#print axioms snapshot_advance_valid
#print axioms resume_valid_snapshot
#print axioms render_advance_checkpoint
#print axioms render_checkpoint
#print axioms native_expression
#print axioms native_compile_fields
#print axioms fullFoldRaw_native
#print axioms native_compile_clause
#print axioms render_advance_native_clause

end CBCL.CheckpointKernel.Tests
