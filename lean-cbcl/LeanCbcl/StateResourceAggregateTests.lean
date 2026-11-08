import LeanCbcl.StateResourceValidated
import LeanCbcl.StateResourceTests

namespace CBCL.StateResourceAggregateTests
open State CheckpointEvidence StateResource StateResourceTests StateResourceFinalize

/-- Test fixture for the mint case. -/
def mint : ResourceFact := {burn with id := 4,data := {burn.data with
  signer := "@treasury",kind := .increment,amount := 7,selected := {burn.data.selected with
    verb := "mint",authenticatedFrom := .value "@treasury"}}}
/-- Test fixture for the pay case. -/
def pay : ResourceFact := {burn with id := 4,data := {burn.data with
  signer := "@treasury",kind := .transfer,amount := 5,selected := {burn.data.selected with
    verb := "pay",authenticatedFrom := .value "@treasury",recipient := some "@alice",recipientStatus := .recognized}}}
/-- Test fixture for the funded Burn case. -/
def fundedBurn : ResourceFact := {burn with data := {burn.data with deps := [4]}}
/-- Test fixture for the bounded case. -/
def bounded : ResourceConfig := {config with ceiling := some 1000,headroomKey := some "space"}
/-- Test fixture for the bounded Opener case. -/
def boundedOpener : ResourceFact := {opener with data := {opener.data with selected := {opener.data.selected with
  headroomAllocations := .value [("@bob",0),("@alice",0),("@treasury",0)]}}}
/-- Test fixture for the treasury Burn case. -/
def treasuryBurn : ResourceFact := {burn with data := {burn.data with signer := "@treasury",amount := 5,selected := {burn.data.selected with authenticatedFrom := .value "@treasury"}}}

theorem unbounded_mint_value : ((finish config opener [mint]).map AggregateSnapshot.value) = some 1007 := by decide

/-- Address order may temporarily debit the receiver before the funding act.
The native aggregate permits signed intermediates and checks final budgets. -/
theorem funded_address_order : ((finish config opener [fundedBurn,pay]).map fun snapshot =>
    (snapshot.rights "@treasury",snapshot.rights "@alice",snapshot.value)) = some (995,4,999) := by decide

theorem negative_final_budget_rejected : (finish config opener [burn]).isSome = false := by decide

theorem bounded_burn_conservation : ((finish bounded boundedOpener [treasuryBurn]).bind fun snapshot =>
    snapshot.headroom.map fun space => (snapshot.value,space "@treasury")) = some (995,5) := by decide

theorem broken_conservation_rejected : (finish {bounded with ceiling := some 999} boundedOpener []).isSome = false := by decide

end CBCL.StateResourceAggregateTests
