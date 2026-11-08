import LeanCbcl.StateReaderValues

/-! Concrete value-layer witnesses, using actual indexed scopes and native
source reads rather than caller-provided leaf callbacks. -/
namespace CBCL.StateReaderValuesTests
open State StateLift StateObservation StateObservationPlan StateInstalledCompiler StateReaderValues

/-- A freezer and a concurrent sibling produce different full/cut sizes. -/
def acts : List Act := [⟨0,"open","@a",[],[],[]⟩,⟨1,"close","@a",[0],[],[]⟩,⟨2,"mark","@b",[0],[],[]⟩]

/-- The field's native supersede-freeze metadata. -/
def freezes : List (String × FreezeSpec) := [("events",⟨"close",fun _ => True,false⟩)]

/-- A concrete installed native source counts the accepted history it receives. -/
def fields : List (String × Rule Nat) := [("events",.source (.snapshot FinSet.card))]

/-- The fixed normal operation reads the selected cut, not the full observation. -/
theorem cut_value_witness : (match normal acts freezes fields (1,"events") none with
  | .data (.snapshot count) => count == 2
  | _ => false) = true := by decide

/-- A full-history source remains independent of the already allocated cut. -/
theorem whole_value_witness : (match normal acts freezes fields (0,"events") none with
  | .data (.snapshot count) => count == 3
  | _ => false) = true := by decide

/-- Dependency unwrapping preserves the exact historical payload. -/
theorem unwrapped_value_witness : (match unfrozen (.data (.frozen 1 (7 : Nat) (FinSet.mk []))) with
  | .data (.snapshot amount) => amount == 7
  | _ => false) = true := by decide

/-- Outer frozen presentation replaces the inner freezer identity and payload
wrapper while preserving its historical value. -/
theorem outer_wrapper_witness : (match frozen 9 (FinSet.mk []) (frozen 1 (FinSet.mk []) (.data (.snapshot (7 : Nat)))) with
  | .data (.frozen root value _) => root == 9 && value == 7
  | _ => false) = true := by decide

/-- Independent normal and freeze faults both retain their witness addresses. -/
theorem fault_union_witness : (match combinedFault (V := Nat) (some (fun address => address = 9))
    (.fault (fun address => address = 7)) with
  | some (.fault evidence) => evidence 7 ∧ evidence 9
  | _ => False) := ⟨Or.inl rfl,Or.inr rfl⟩

end CBCL.StateReaderValuesTests
