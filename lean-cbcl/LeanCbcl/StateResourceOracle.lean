import Lean
import LeanCbcl.StateResourceRendering
import LeanCbcl.StateResourceTests

/-! Live resource profile with fixed account configuration and explicit decrement/funding graphs.
Typed extraction is explicit; this profile does not establish native admission,
wire extraction, or complete native fault-reason correspondence. -/
namespace CBCL.StateResourceOracle
open Lean State CheckpointEvidence StateResource StateResourcePreflight StateResourceAggregate StateResourceTests

/-- Installed account configuration is checked independently of each history. -/
theorem installed : NativeConfiguration config ∧ (config.initialVerb :: operationNames config).Nodup := by
  exact ⟨(configurationCheck_iff config).mp (by decide),by decide⟩

/-- Execute the complete checked verifier on a recognized finite fixture. -/
def observeFacts (j : Json) (facts : Facts) : Except String Json := do
  let names : List (Nat × String) ← fromJson? (← j.getObjVal? "addresses")
  if !(decide (names.map Prod.fst).Nodup) || !(decide (names.map Prod.snd).Nodup) then
    throw "address dictionary must have unique identities and names"
  if names.length != facts.length || !(facts.all (fun node => (names.lookup node.id).isSome)) then
    throw "address dictionary must cover exactly the accepted fixture identities"
  let address := fun id => (names.lookup id).getD ""

  if unique : (facts.map Fact.id).Nodup then
    if bounded : facts.length ≤ 2^63 - 1 then
      if allocations : facts.all (fun node => decide (((accounts node.data.selected.initialAllocations).map Prod.fst).length ≤ 2^63 - 1)) = true then
        let input : StateResourceVerifier.Input := ⟨config,facts,unique,bounded,(fun _ => installed),
          fun node member => of_decide_eq_true (List.all_eq_true.mp allocations node member)⟩
        match StateResourceVerifier.observe input with
        | .pending => return Json.mkObj [("status",.str "pending")]
        | .fault =>
          let some bytes := StateResourceRendering.evidenceBytes config facts address
            | throw "resource evidence pool move failed"
          return Json.mkObj [("status",.str "fault"),("evidence",toJson ((StateResourceRendering.witnesses config facts).mergeSort (fun a b => decide (a ≤ b)))),("witness_bytes",.str bytes)]
        | .ready snapshot => return Json.mkObj [("status",.str "ready"),("value",toJson snapshot.value),
            ("rights",Json.mkObj (["@treasury","@alice","@bob"].map (fun account => (account,toJson (snapshot.rights account)))))]
      else throw "account slice exceeds native bound"
    else throw "fact slice exceeds native bound"
  else throw "duplicate fact identity"


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
  observeFacts j facts

/-- Optional transport flags default only when absent; present values stay typed. -/
def optionalFlag (j : Json) (name : String) : Except String Bool :=
  match j.getObjVal? name with
  | .error _ => pure false
  | .ok value => value.getBool?

/-- A funding transfer and dependent burn exercise retained resource cones.
Missing funding, omitted dependencies and an independent same-owner fork are
explicit fixture choices, not expected-result inputs. -/
def graphRun (j : Json) : Except String Json := do
  let funding ← (← j.getObjVal? "funding").getInt?
  let spend ← (← j.getObjVal? "spend").getInt?
  if funding < -(2^63) || funding ≥ 2^63 || spend < -(2^63) || spend ≥ 2^63 then
    throw "amount outside signed native wire integer"
  let included ← (← j.getObjVal? "included").getBool?
  let dependency ← (← j.getObjVal? "dependency").getBool?
  let fork ← (← j.getObjVal? "fork").getBool?
  let context ← optionalFlag j "context"
  let citedContext ← optionalFlag j "cited_context"
  let note : ResourceFact := ⟨6,{signer := "@treasury",kind := .other,amount := 0,prev := none,deps := [],selected := {resource := "coins",verb := "tell",predecessors := [2]}}⟩
  let payment : ResourceFact := {burn with id := 4, data := {burn.data with signer := "@treasury", kind := .transfer, amount := funding, selected := {burn.data.selected with verb := "pay", authenticatedFrom := .value "@treasury", recipient := some "@alice", recipientStatus := .recognized, predecessors := [2] ++ (if citedContext then [6] else [])}}}
  let spent : ResourceFact := {burn with data := {burn.data with amount := spend, deps := if dependency then [4] else [], selected := {burn.data.selected with predecessors := if dependency then [2,4] else [2]}}}
  let competing : ResourceFact := {spent with id := 5, data := {spent.data with amount := 1}}
  observeFacts j ([root,opener,spent] ++ (if included then [payment] else []) ++ (if fork then [competing] else []) ++ (if context then [note] else []))

end CBCL.StateResourceOracle
