import Lean
import LeanCbcl.StateResourceRendering
import LeanCbcl.StateFreezeRendering
import LeanCbcl.StateResourceTests

/-! Live resource profile with fixed account configuration and explicit decrement/funding graphs.
Typed extraction is explicit; this profile does not establish native admission,
wire extraction, or complete native fault-reason correspondence. -/
namespace CBCL.StateResourceOracle
open Lean State CheckpointEvidence StateResource StateResourcePreflight StateResourceAggregate StateResourceTests

/-- Installed account configuration is checked independently of each history. -/
theorem installed : NativeConfiguration config ∧ (config.initialVerb :: operationNames config).Nodup := by
  exact ⟨(configurationCheck_iff config).mp (by decide),by decide⟩

/-- Recognize the physical bounds required by the complete resource verifier. -/
def checkedInput (facts : Facts) : Except String StateResourceVerifier.Input := do
  if unique : (facts.map Fact.id).Nodup then
    if bounded : facts.length ≤ 2^63 - 1 then
      if allocations : facts.all (fun node => decide (((accounts node.data.selected.initialAllocations).map Prod.fst).length ≤ 2^63 - 1)) = true then
        return ⟨config,facts,unique,bounded,(fun _ => installed),
          fun node member => of_decide_eq_true (List.all_eq_true.mp allocations node member)⟩
      else throw "account slice exceeds native bound"
    else throw "fact slice exceeds native bound"
  else throw "duplicate fact identity"

/-- Fixed unbounded-resource snapshot in the native ordered map representation. -/
def readyValue (snapshot : StateResourceFinalize.AggregateSnapshot) : StateJsonValue.Value :=
  .map [(.str "rights",.map (["@alice","@bob","@treasury"].map (fun owner =>
    (StateJsonValue.Value.str owner,StateJsonValue.Value.int (snapshot.rights owner))))),
    (.str "status",.str "ready"),(.str "value",.int snapshot.value)]

/-- Normalize complete computed witnesses, comparing membership and raw array bytes. -/
def faultJson (address : Nat → String) (ids : List Nat) : Except String Json := do
  let some names := (StateAddressPool.sortPool (ids.map address).toArray).map StateAddressDigits.adjacent
    | throw "resource evidence pool move failed"
  return Json.mkObj [("status",.str "fault"),("evidence",toJson ((StateLift.FinSet.dedup ids).mergeSort (fun a b => decide (a ≤ b)))),
    ("witness_bytes",.str (StateJsonValue.emit (.list (names.map StateJsonValue.Value.str)) ""))]

/-- Present the actual full-history verifier read without a frozen wrapper. -/
def readJson (facts : Facts) (address : Nat → String) : StateResourceValidated.Read → Except String Json
  | .pending => pure (Json.mkObj [("status",.str "pending")])
  | .fault => faultJson address (StateResourceRendering.witnesses config facts)
  | .ready snapshot => Json.parse (StateJsonValue.render (readyValue snapshot))

/-- Execute the complete checked verifier and optional pay-triggered freeze.
Raw authorization faults are supplied to the common executable freeze read. -/
def observeFacts (j : Json) (facts : Facts) (freeze : Bool := false) : Except String Json := do
  let names : List (Nat × String) ← fromJson? (← j.getObjVal? "addresses")
  if !(decide (names.map Prod.fst).Nodup) || !(decide (names.map Prod.snd).Nodup) then
    throw "address dictionary must have unique identities and names"
  if names.length != facts.length || !(facts.all (fun node => (names.lookup node.id).isSome)) then
    throw "address dictionary must cover exactly the accepted fixture identities"
  let address := fun id => (names.lookup id).getD ""
  let input ← checkedInput facts
  let current := StateResourceVerifier.observe input
  if !freeze then return ← readJson facts address current
  let policy ← (← j.getObjVal? "fault_policy").getBool?
  let acts : List Act := facts.map (fun fact => ⟨fact.id,fact.data.selected.verb,fact.data.signer,fact.data.selected.predecessors,[],[]⟩)
  let raw := if StateResourceValidated.isFault current then some (StateResourceRendering.witnesses config facts) else none
  let evaluate := fun scope : List Act => do
    let cutFacts := facts.filter (fun fact => scope.any (fun act => act.addr == fact.id))
    let cutInput ← checkedInput cutFacts
    let .ready snapshot := StateResourceVerifier.observe cutInput
      | throw "freezer cut has no ready resource snapshot in this fixture"
    pure (readyValue snapshot)
  match StateExecutableFreeze.read acts "pay"
      (fun act => act.verb == config.initialVerb || StateResourceCycle.operationVerbCheck config act.verb) policy raw evaluate with
  | .snapshot _ => readJson facts address current
  | .fault ids => faultJson address ids
  | .frozen root captured excluded => do
    let value ← captured
    let some bytes := StateFreezeRendering.emitFrozen address root value excluded
      | throw "frozen resource evidence pool move failed"
    return Json.mkObj [("status",.str "frozen"),("rendered",.str bytes)]


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
def graphRun (j : Json) (freeze : Bool := false) : Except String Json := do
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
  observeFacts j ([root,opener,spent] ++ (if included then [payment] else []) ++ (if fork then [competing] else []) ++ (if context then [note] else [])) freeze

end CBCL.StateResourceOracle
