import Lean
import LeanCbcl.StateResourceVerifier
import LeanCbcl.StateResourceTests

/-! Live resource profile with one decrement and fixed account configuration.
Typed extraction is explicit; this profile does not establish native admission,
wire extraction, or complete resource witness-byte correspondence. -/
namespace CBCL.StateResourceOracle
open Lean State CheckpointEvidence StateResource StateResourcePreflight StateResourceAggregate StateResourceTests

/-- Installed account configuration is checked independently of each history. -/
theorem installed : NativeConfiguration config ∧ (config.initialVerb :: operationNames config).Nodup := by
  exact ⟨(configurationCheck_iff config).mp (by decide),by decide⟩

/-- Compare complete verifier status and ready balances, with explicit input bounds. -/
def run (j : Json) : Except String Json := do
  let amount ← (← j.getObjVal? "amount").getInt?
  if amount < -(2^63) || amount ≥ 2^63 then throw "amount outside signed native wire integer"
  let owner ← (← j.getObjVal? "owner").getStr?
  if !["@treasury","@alice","@bob","@outsider"].contains owner then throw "unknown fixture account"
  let hasRoot ← (← j.getObjVal? "root").getBool?
  let hasOpener ← (← j.getObjVal? "opener").getBool?
  let operation : ResourceFact := {burn with data := {burn.data with signer := owner, amount := amount, selected := {burn.data.selected with authenticatedFrom := .value owner}}}
  let facts := (if hasRoot then [root] else []) ++ (if hasOpener then [opener] else []) ++ [operation]
  if unique : (facts.map Fact.id).Nodup then
    if bounded : facts.length ≤ 2^63 - 1 then
      if allocations : facts.all (fun node => decide (((accounts node.data.selected.initialAllocations).map Prod.fst).length ≤ 2^63 - 1)) = true then
        let input : StateResourceVerifier.Input := ⟨config,facts,unique,bounded,(fun _ => installed),
          fun node member => of_decide_eq_true (List.all_eq_true.mp allocations node member)⟩
        match StateResourceVerifier.observe input with
        | .pending => return Json.mkObj [("status",.str "pending")]
        | .fault => return Json.mkObj [("status",.str "fault")]
        | .ready snapshot => return Json.mkObj [("status",.str "ready"),("value",toJson snapshot.value),
            ("rights",Json.mkObj (["@treasury","@alice","@bob"].map (fun account => (account,toJson (snapshot.rights account)))))]
      else throw "account slice exceeds native bound"
    else throw "fact slice exceeds native bound"
  else throw "duplicate fact identity"

end CBCL.StateResourceOracle
