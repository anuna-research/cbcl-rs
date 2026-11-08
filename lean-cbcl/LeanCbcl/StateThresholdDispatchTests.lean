import LeanCbcl.StateThresholdDispatch

/-! Raw threshold scope witnesses distinguish retained carrier from displayed
source payload, including pending data. These are adapter-level fixtures,
not authored threshold admission witnesses. -/
namespace CBCL.StateThresholdDispatchTests
open State StateLVar StateLift StateObservation StateObservationPlan StateThresholdDispatch StateInstalledCompiler

/-- A freezer cut excludes a concurrent branch. -/
def acts : List Act := [⟨0,"open","@a",[],[],[]⟩,⟨1,"close","@a",[0],[],[]⟩,
  ⟨2,"write","@b",[0],[],[]⟩]

/-- Symbolic adapter metadata, separate from threshold admission. -/
def freezes : List (String × FreezeSpec) := [("count",⟨"close",fun _ => True,false⟩)]

/-- Historical threshold evaluation uses two acts, excluding the third branch. -/
theorem allocated_raw_cut : (rawScope (V := Nat) [] acts [] freezes "count").map Act.addr = [0,1] := by decide

/-- Pending display is not a reason to skip the source's raw-carrier query. -/
theorem pending_source_reaches : dispatch [] acts [] freezes "count" [2] (fun q n => decide (q ≤ n))
    (fun history => FinSet.card history) (.data .pending) = .data (.reached 2) := by
  have count : FinSet.card (rawHistory (rawScope (V := Nat) [] acts [] freezes "count")) = 2 := by decide
  simp [dispatch,nativeRawThreshold,StateReaderValues.unfrozen,count]

/-- A misleading displayed count cannot substitute for the retained raw state. -/
theorem display_does_not_replace_raw : dispatch [] acts [] freezes "count" [3] (fun q n => decide (q ≤ n))
    (fun history => FinSet.card history) (.data (.snapshot 100)) = .data .pending := by
  have count : FinSet.card (rawHistory (rawScope (V := Nat) [] acts [] freezes "count")) = 2 := by decide
  simp [dispatch,nativeRawThreshold,StateReaderValues.unfrozen,count]

end CBCL.StateThresholdDispatchTests
