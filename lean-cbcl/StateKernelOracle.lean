import Lean
import LeanCbcl.StateFiniteRead
import LeanCbcl.StateExecutableFreeze

/-! JSON-lines differential oracle. Inputs contain only authored finite data and
histories, never expected Rust results. Evaluation calls the same checked table,
projection, contribution, state and read functions used by the Lean proofs.
The profile has finite data/read paths and causal freezes; domains, context
and resources remain separate. -/
open Lean CBCL.State CBCL.StateFiniteTable CBCL.StateInstalledFinite
namespace StateKernelOracle

abbrev Check := Except String

def array (j : Json) : Check (List Json) := j.getArr?.map Array.toList

def pair (j : Json) : Check (Json × Json) := do
  match ← array j with
  | [a,b] => return (a,b)
  | _ => throw "expected pair"

def scalar (j : Json) : Check Val :=
  match j with
  | .str s => pure (.str s)
  | .bool b => pure (.bool b)
  | .num _ => j.getInt?.map Val.int
  | _ => throw "expected scalar"

def scalarJson : Val → Json
  | .str s => .str s
  | .int n => toJson n
  | .bool b => .bool b
  | .list values => toJson (values.map fun value => match value with
      | .str s => Json.str s | .int n => toJson n | .bool b => .bool b)

def table (j : Json) : Check Definition := do
  let elements ← (← array (← j.getObjVal? "elements")).mapM Json.getStr?
  let rows ← (← array (← j.getObjVal? "rows")).mapM fun row => do
    match ← array row with
    | [a,b,c] => return (← a.getStr?,← b.getStr?,← c.getStr?)
    | _ => throw "expected join triple"
  return ⟨"rank",elements,← (← j.getObjVal? "bottom").getStr?,← (← j.getObjVal? "top").getStr?,rows⟩

def projection (j : Json) : Check (Option CBCL.StateFiniteProjection.Declaration) := do
  if j == .null then return none
  let stable ← (← j.getObjVal? "stable").getBool?
  let rows ← (← array (← j.getObjVal? "rows")).mapM fun row => do
    let (name,value) ← pair row
    return (← name.getStr?,← scalar value)
  return some ⟨stable,rows⟩

def contribution (j : Json) : Check CBCL.StateFiniteProjection.Contribution := do
  match ← array j with
  | [key,value,element] => return ⟨← key.getStr?,← scalar value,← element.getStr?⟩
  | _ => throw "expected contribution triple"

def act (j : Json) : Check Act := do
  let (address,verb,preds,rawFields) ← match ← array j with
    | [address,fields] => pure (address,"mark",[],fields)
    | [address,verb,preds,fields] => do pure (address,← verb.getStr?,← (← array preds).mapM Json.getNat?,fields)
    | _ => throw "expected identity/fields pair or identity/verb/predecessors/fields tuple"
  let fields ← (← array rawFields).mapM fun field => do
    let (key,value) ← pair field
    return (← key.getStr?,← scalar value)
  return ⟨← address.getNat?,verb,"@a",preds,fields,[]⟩

structure Input where
  definition : Definition
  declaration : CBCL.StateInstalledFinite.Declaration
  queries : Option (List Val)
  history : List Act
  freeze : Option Bool

def input (j : Json) : Check Input := do
  let definition ← table (← j.getObjVal? "table")
  let rows ← (← array (← j.getObjVal? "contributions")).mapM contribution
  let projection ← projection (← j.getObjVal? "projection")
  let rawQueries ← j.getObjVal? "queries"
  let queries ← if rawQueries == .null then pure none else (array rawQueries >>= fun qs => qs.mapM scalar).map some
  let history ← (← array (← j.getObjVal? "acts")).mapM act
  let freeze ← match j.getObjVal? "freeze" with
    | .error _ => pure none
    | .ok .null => pure none
    | .ok value => value.getBool?.map some
  if !CBCL.StateExecutableFreeze.rankedCheck history then throw "predecessor identities must decrease"
  if !history.all (fun a => history.all (fun b => a.addr != b.addr || a == b)) then throw "conflicting identity payloads"
  if !history.all (fun a => a.preds.all (fun reference => history.any (fun parent => parent.addr == reference))) then throw "missing predecessor"
  if !history.all (fun a => decide (a.fields.map Prod.fst).Nodup) then throw "duplicate field keyword"
  return ⟨definition,⟨"mark",rows,projection⟩,queries,history,freeze⟩

def schema : CBCL.StateInstalledDomains.Schema :=
  ⟨["mark"],[(("mark","phase"),.string),(("mark","amount"),.number),(("mark","flag"),.boolean)]⟩

def evaluate (request : Input) : Json := Id.run do
  let rejected := Json.mkObj [("installed",.bool false)]
  let some verified := CBCL.StateFiniteTable.compile 64 request.definition | return rejected
  let some field := make schema verified [] request.declaration | return rejected
  if request.queries.any (fun qs => !CBCL.StateFiniteRead.check field qs) then return rejected
  let current := state field request.history
  let fault : Bool := current == field.table.table.top
  let evidence := ((request.history.filter (fun a => a.verb == "mark" && CBCL.StateInstalledFinite.contribution field a != field.table.table.bottom)).map Act.addr).eraseDups
  let evidence := evidence.mergeSort (fun a b => decide (a ≤ b))
  if request.freeze == some false && request.queries.isSome then return rejected
  let sorted (addresses : List Nat) := addresses.eraseDups.mergeSort (fun a b => decide (a ≤ b))
  let frozen := match request.freeze with
    | none => if fault then CBCL.StateExecutableFreeze.Read.fault evidence else .snapshot (display field current)
    | some policy => CBCL.StateExecutableFreeze.read request.history "close" (fun a => a.verb == "mark") policy
        (if fault then some evidence else none) (fun scope => display field (state field scope))
  let observation := match frozen with
    | .snapshot value => Json.mkObj [("status",.str "snapshot"),("value",scalarJson value)]
    | .fault addresses => Json.mkObj [("status",.str "fault"),("evidence",toJson (sorted addresses))]
    | .frozen root value excluded => Json.mkObj [("status",.str "frozen"),("freezer",toJson root),
        ("excluded",toJson (sorted (excluded.map Act.addr))),("value",scalarJson value)]
  let threshold := request.queries.map fun qs =>
    match frozen with
    | .fault addresses => Json.mkObj [("status",.str "fault"),("evidence",toJson (sorted addresses))]
    | _ => match qs.find? (fun q => CBCL.StateFiniteRead.test field q current) with
        | none => Json.mkObj [("status",.str "pending")]
        | some q => Json.mkObj [("status",.str "reached"),("element",scalarJson q)]
  return Json.mkObj [("installed",.bool true),("observation",observation),("threshold",threshold.getD .null)]

end StateKernelOracle

def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let answer := match Json.parse line >>= StateKernelOracle.input with
      | .error error => Json.mkObj [("error",.str error)]
      | .ok request => StateKernelOracle.evaluate request
    stdout.putStrLn answer.compress
    stdout.flush
