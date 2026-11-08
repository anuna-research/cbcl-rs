import LeanCbcl.StateResourceOracle

/-! Bounded arbitrary typed resource graphs at observe_facts' boundary.
Address aliases and common instance tags are fixture representations, not native
message, signature, content-hash or admission extraction. -/
namespace CBCL.StateResourceFactsOracle
open Lean State CheckpointEvidence StateResource StateResourceTests

/-- Decimal padded aliases satisfy native state-address spelling for bounded IDs. -/
def address (id : Nat) : String :=
  let digits := toString id
  "sha256-" ++ String.ofList (List.replicate (64 - digits.length) '0') ++ digits

/-- Recognize bounded reference IDs, including accepted-absent references. -/
def reference (j : Json) : Except String Nat := do
  let id ← j.getNat?
  if id > 32 then throw "resource reference exceeds 32"
  return id

/-- Recognize dependency/causal lists while retaining duplicate references. -/
def references (j : Json) : Except String (List Nat) := do
  let values ← j.getArr?
  if values.size > 16 then throw "resource references exceed 16"
  values.toList.mapM reference

/-- Closed account dictionary includes one deliberately unauthorized signer. -/
def owner (j : Json) : Except String String := do
  let index ← j.getNat?
  match ["@treasury","@alice","@bob","@outsider"][index]? with
  | some name => return name
  | none => throw "unknown resource owner"

/-- Reject extra source fields rather than accepting caller-selected results. -/
def keys (allowed : List String) (j : Json) : Except String Unit := do
  let object ← j.getObj?
  if object.toList.any (fun field => !allowed.contains field.1) then throw "unknown resource source field"

/-- Decode one typed operation, preserving absent previous and duplicate deps.
Every row is recognized before the complete verifier is evaluated. -/
def operation (id : Nat) (j : Json) : Except String ResourceFact := do
  keys ["kind","owner","recipient","amount","prev","deps","causes"] j
  let verb ← (← j.getObjVal? "kind").getStr?
  let kind ← match verb with
    | "mint" => pure ResourceKind.increment
    | "burn" => pure ResourceKind.decrement
    | "pay" => pure ResourceKind.transfer
    | "tell" => pure ResourceKind.other
    | _ => throw "unknown resource operation"
  let signer ← owner (← j.getObjVal? "owner")
  let recipient ← owner (← j.getObjVal? "recipient")
  let amount ← (← j.getObjVal? "amount").getInt?
  if amount < -(2^63) || amount ≥ 2^63 then throw "amount outside signed native wire integer"
  let previous ← j.getObjVal? "prev"
  let prev ← match previous with
    | .null => pure none
    | other => (reference other).map some
  let deps ← references (← j.getObjVal? "deps")
  let causes ← references (← j.getObjVal? "causes")
  let selected : ResourceSelected := {resource := "coins",verb := verb,predecessors := causes,authenticatedFrom := .value signer,amountStatus := .recognized,previousStatus := if prev.isSome then .recognized else .absent,dependenciesStatus := .recognized,recipient := if verb == "pay" then some recipient else none,recipientStatus := if verb == "pay" then .recognized else .absent}
  return ⟨id,{signer := signer,kind := kind,amount := amount,prev := prev,deps := deps,selected := selected}⟩

/-- Execute the full verifier on up to sixteen typed operations, including cycles,
missing evidence, cross-owner links, forks, transfers and causal context. -/
def run (j : Json) : Except String Json := do
  keys ["profile","root","opener","reverse","nodes"] j
  let hasRoot ← (← j.getObjVal? "root").getBool?
  let hasOpener ← (← j.getObjVal? "opener").getBool?
  let reverse ← (← j.getObjVal? "reverse").getBool?
  let nodes ← (← j.getObjVal? "nodes").getArr?
  if nodes.size > 16 then throw "resource nodes exceed 16"
  let operations ← nodes.toList.zipIdx.mapM (fun (node,index) => operation (index + 3) node)
  let facts := (if hasRoot then [root] else []) ++ (if hasOpener then [opener] else []) ++ operations
  let facts := if reverse then facts.reverse else facts
  let names := facts.map (fun fact => (fact.id,address fact.id))
  let request := Json.mkObj [("addresses",toJson names)]
  StateResourceOracle.observeFacts request facts

end CBCL.StateResourceFactsOracle
