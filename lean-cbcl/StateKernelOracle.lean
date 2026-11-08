import Lean
import LeanCbcl.StateFiniteRead

/-! JSON-lines differential oracle. Inputs contain only authored finite data and
histories, never expected Rust results. Evaluation calls the same checked table,
projection, contribution, state and read functions used by the Lean proofs.
This initial profile has no domains, context, resources or freezes. -/
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
  let (address,fields) ← pair j
  let fields ← (← array fields).mapM fun field => do
    let (key,value) ← pair field
    return (← key.getStr?,← scalar value)
  return ⟨← address.getNat?,"mark","@a",[],fields,[]⟩

structure Input where
  definition : Definition
  declaration : CBCL.StateInstalledFinite.Declaration
  queries : Option (List Val)
  history : List Act

def input (j : Json) : Check Input := do
  let definition ← table (← j.getObjVal? "table")
  let rows ← (← array (← j.getObjVal? "contributions")).mapM contribution
  let projection ← projection (← j.getObjVal? "projection")
  let rawQueries ← j.getObjVal? "queries"
  let queries ← if rawQueries == .null then pure none else (array rawQueries >>= fun qs => qs.mapM scalar).map some
  return ⟨definition,⟨"mark",rows,projection⟩,queries,← (← array (← j.getObjVal? "acts")).mapM act⟩

def schema : CBCL.StateInstalledDomains.Schema :=
  ⟨["mark"],[(("mark","phase"),.string),(("mark","amount"),.number),(("mark","flag"),.boolean)]⟩

def evaluate (request : Input) : Json := Id.run do
  let rejected := Json.mkObj [("installed",.bool false)]
  let some verified := CBCL.StateFiniteTable.compile 64 request.definition | return rejected
  let some field := make schema verified [] request.declaration | return rejected
  if request.queries.any (fun qs => !CBCL.StateFiniteRead.check field qs) then return rejected
  let current := state field request.history
  let fault : Bool := current == field.table.table.top
  let evidence := ((request.history.filter (fun a => CBCL.StateInstalledFinite.contribution field a != field.table.table.bottom)).map Act.addr).eraseDups
  let evidence := evidence.mergeSort (fun a b => decide (a ≤ b))
  let observation := if fault then Json.mkObj [("status",.str "fault"),("evidence",toJson evidence)] else
    Json.mkObj [("status",.str "snapshot"),("value",scalarJson (display field current))]
  let threshold := request.queries.map fun qs =>
    if fault then Json.mkObj [("status",.str "fault"),("evidence",toJson evidence)] else
      match qs.find? (fun q => CBCL.StateFiniteRead.test field q current) with
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
