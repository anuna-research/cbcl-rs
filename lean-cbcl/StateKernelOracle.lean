import Lean
import LeanCbcl.StateResourceOracle
import LeanCbcl.StateShapeOracle
import LeanCbcl.StateJsonOracle
import LeanCbcl.StateContextOracle
import LeanCbcl.StateFiniteRead
import LeanCbcl.StateFiniteDenseCache
import LeanCbcl.StateExecutableFreeze
import LeanCbcl.StateCausalRank
import LeanCbcl.StateExecutableObservation

/-! JSON-lines differential oracle. Inputs contain only authored finite data and
histories, never expected Rust results. Evaluation calls the same checked table,
projection, contribution, state and read functions used by the Lean proofs.
Profiles cover finite reads, causal freezes, observed events/sums, immutable
context, mandatory/nonnegative shape projections, and decrement/funding/fork
resource verifier profiles. Resource admission/extraction remain explicit boundaries. -/
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

/-- Finite-profile opaque symbols cannot equal any verified scalar row. The
bounded token grammar is [a-z][a-z0-9_-]*; this is not a general wire decoder. -/
def finiteLiteral (j : Json) : Check Val := do
  match j with
  | .arr _ =>
    match ← array j with
    | [.str "symbol",.str name] =>
      let lower := fun c : Char => decide ('a' ≤ c ∧ c ≤ 'z')
      let digit := fun c : Char => decide ('0' ≤ c ∧ c ≤ '9')
      match name.toList with
      | [] => throw "empty finite symbol token"
      | head::tail =>
        if lower head && tail.all (fun c => lower c || digit c || c == '_' || c == '-') then
          return .list [.str "symbol",.str name]
        else throw "finite symbol token requires [a-z][a-z0-9_-]*"
    | _ => throw "expected finite symbol token [symbol,name]"
  | _ => scalar j

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
    return (← name.getStr?,← finiteLiteral value)
  return some ⟨stable,rows⟩

def contribution (j : Json) : Check CBCL.StateFiniteProjection.Contribution := do
  match ← array j with
  | [key,value,element] => return ⟨← key.getStr?,← finiteLiteral value,← element.getStr?⟩
  | _ => throw "expected contribution triple"

def actWith (decode : Json → Check Val) (j : Json) : Check Act := do
  let (address,verb,preds,rawFields) ← match ← array j with
    | [address,fields] => pure (address,"mark",[],fields)
    | [address,verb,preds,fields] => do pure (address,← verb.getStr?,← (← array preds).mapM Json.getNat?,fields)
    | _ => throw "expected identity/fields pair or identity/verb/predecessors/fields tuple"
  let fields ← (← array rawFields).mapM fun field => do
    let (key,value) ← pair field
    return (← key.getStr?,← decode value)
  return ⟨← address.getNat?,verb,"@a",preds,fields,[]⟩

/-- Other profiles retain their existing scalar-only input contract. -/
def act (j : Json) : Check Act := actWith scalar j

def validateHistory (history : List Act) : Check Unit := do
  if !history.all (fun a => history.all (fun b => a.addr != b.addr || a == b)) then throw "conflicting identity payloads"
  if !history.all (fun a => a.preds.all (fun reference => history.any (fun parent => parent.addr == reference))) then throw "missing predecessor"
  if !CBCL.StateCausalRank.causalCheck history then throw "causal cycle or invalid topological witness"
  if !history.all (fun a => decide (a.fields.map Prod.fst).Nodup) then throw "duplicate field keyword"
  return ()

structure Input where
  limit : Nat
  definition : Definition
  declaration : CBCL.StateInstalledFinite.Declaration
  queries : Option (List Val)
  history : List Act
  freeze : Option Bool

def input (j : Json) : Check Input := do
  let limit ← match j.getObjVal? "max-list" with
    | .error _ => pure 64
    | .ok value => value.getNat?
  if limit > 2^32-1 then throw "max-list exceeds native u32 range"
  let definition ← table (← j.getObjVal? "table")
  let rows ← (← array (← j.getObjVal? "contributions")).mapM contribution
  let projection ← projection (← j.getObjVal? "projection")
  let rawQueries ← j.getObjVal? "queries"
  let queries ← if rawQueries == .null then pure none else (array rawQueries >>= fun qs => qs.mapM scalar).map some
  let history ← (← array (← j.getObjVal? "acts")).mapM (actWith finiteLiteral)
  let freeze ← match j.getObjVal? "freeze" with
    | .error _ => pure none
    | .ok .null => pure none
    | .ok value => value.getBool?.map some
  validateHistory history
  return ⟨limit,definition,⟨"mark",rows,projection⟩,queries,history,freeze⟩

def schema : CBCL.StateInstalledDomains.Schema :=
  ⟨["mark"],[(("mark","phase"),.string),(("mark","amount"),.number),(("mark","flag"),.boolean)]⟩

def evaluate (request : Input) : Json := Id.run do
  let rejected := Json.mkObj [("installed",.bool false)]
  if !CBCL.StateInstalledBounds.check ⟨32,request.limit,1000000000000,2048⟩ then return rejected
  let some verified := CBCL.StateFiniteTable.compile request.limit request.definition | return rejected
  let some field := make schema verified [] request.declaration | return rejected
  let gates := request.queries.map (fun qs =>
    (CBCL.StateFiniteDenseCache.check .bits64 field qs,CBCL.StateFiniteDenseCache.check .bits32 field qs))
  if gates.any (fun gate => gate.1 != gate.2) then
    return Json.mkObj [("error",.str "finite machine backends disagree")]
  if gates.any (fun gate => !gate.1) then return rejected
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

structure NestedInput where
  history : List Act
  sourcePolicy : Option Bool
  derivedPolicy : Option Bool

def optionalPolicy (j : Json) (name : String) : Check (Option Bool) := do
  match ← j.getObjVal? name with
  | .null => return none
  | value => value.getBool?.map some

def nestedInput (j : Json) : Check NestedInput := do
  let history ← (← array (← j.getObjVal? "acts")).mapM act
  validateHistory history
  return ⟨history,← optionalPolicy j "source_freeze",← optionalPolicy j "derived_freeze"⟩

def eventMap (history : List Act) : CBCL.StateKernelQueries.FiniteMap :=
  CBCL.StateKernelQueries.evalMap (fun _ _ => none) (fun _ => 0) history
    ⟨.withField (.verb "mark") "amount",.address,.address,"amount",true⟩

def eventsJson (events : CBCL.StateKernelQueries.FiniteMap) : Check Json := do
  let rows ← events.keys.mapM fun key => do
    match key,events.read key with
    | .int identity,.event signer value =>
      if identity < 0 then throw "negative event identity" else
      return (identity.toNat,Json.mkObj [("by",.str signer),("value",scalarJson value)])
    | _,_ => throw "unexpected event support or payload"
  return toJson ((rows.mergeSort (fun a b => decide (a.1 ≤ b.1))).map (fun (id,value) => Json.arr #[toJson id,value]))

def viewJson {V : Type} (render : V → Check Json) : CBCL.StateExecutableObservation.View V → Check Json
  | .pending => pure (Json.mkObj [("status",.str "pending")])
  | .snapshot value => do return Json.mkObj [("status",.str "snapshot"),("value",← render value)]
  | .fault evidence => pure (Json.mkObj [("status",.str "fault"),
      ("evidence",toJson (evidence.eraseDups.mergeSort (fun a b => decide (a ≤ b))))])
  | .frozen root value excluded => do return Json.mkObj [("status",.str "frozen"),("freezer",toJson root),
      ("excluded",toJson ((excluded.map Act.addr).eraseDups.mergeSort (fun a b => decide (a ≤ b)))),("value",← render value)]

def nestedSource (request : NestedInput) (scope : List Act) :
    CBCL.StateExecutableObservation.View CBCL.StateKernelQueries.FiniteMap :=
  match request.sourcePolicy with
  | none => .snapshot (eventMap scope)
  | some policy => CBCL.StateExecutableObservation.freeze scope "close" (fun a => a.verb == "mark") policy
      (fun cut => .snapshot (eventMap cut))

def evaluateNested (request : NestedInput) : Check Json := do
  let normal := fun scope => (nestedSource request scope).map CBCL.StateKernelAggregates.mapSum
  let derived := match request.derivedPolicy with
    | none => normal request.history
    | some policy => CBCL.StateExecutableObservation.freeze request.history "seal" (fun a => a.verb == "mark") policy normal
  return Json.mkObj [("installed",.bool true),("source",← viewJson eventsJson (nestedSource request request.history)),
    ("derived",← viewJson (fun value => pure (toJson value)) derived)]

def run (j : Json) : Check Json :=
  match j.getObjVal? "profile" with
  | .ok (.str "resource-freeze") => CBCL.StateResourceOracle.graphRun j true
  | .ok (.str "resource-graph") => CBCL.StateResourceOracle.graphRun j
  | .ok (.str "resource-decrement") => CBCL.StateResourceOracle.run j
  | .ok (.str "nonnegative-shape") => CBCL.StateShapeOracle.run j
  | .ok (.str "keyword-extraction") => CBCL.StateShapeOracle.keywordRun j
  | .ok (.str "state-render") => CBCL.StateJsonOracle.run j
  | .ok (.str "frozen-wrapper") => CBCL.StateJsonOracle.frozenRun j
  | .ok (.str "fault-evidence") => CBCL.StateJsonOracle.faultRun j
  | .ok (.str "context") => StateContextOracle.run j
  | .ok (.str "context-wrapper") => StateContextOracle.wrapperRun j
  | .ok (.str "events-sum") => nestedInput j >>= evaluateNested
  | .error _ | .ok (.str "finite") => input j |>.map evaluate
  | _ => .error "unknown oracle profile"

end StateKernelOracle

def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let answer := match Json.parse line >>= StateKernelOracle.run with
      | .error error => Json.mkObj [("error",.str error)]
      | .ok response => response
    stdout.putStrLn answer.compress
    stdout.flush
