import Lean
import LeanCbcl.StateExecutableContext
import LeanCbcl.StateCausalRank
import LeanCbcl.StateContextCastSyntax
import LeanCbcl.Parser

/-! Context profile for the live oracle. Canonical address hashing and wire
recognition remain input/normalization boundaries; cast validation, projection
and complete witness calculation execute the proved context functions. -/
open Lean CBCL.State CBCL.CheckpointEvidence CBCL.StateInstalledContext
namespace StateContextOracle
abbrev Check := Except String

structure Fact where
  id : Nat
  verb : String
  signer : String
  parents : List Nat
  thread : Option String
  cast : ResourceField (List ResourceRoleBinding)
  pin : ResourceField String
  deriving DecidableEq

def Fact.act (fact : Fact) : Act := ⟨fact.id,fact.verb,fact.signer,fact.parents,[],[]⟩
def Fact.metadata (fact : Fact) : MessageMetadata := ⟨fact.thread,fact.cast,fact.pin⟩

def parseCast (value : Json) : Check (ResourceField (List ResourceRoleBinding)) := do
  match value with
  | .null => return .absent
  | .str "malformed" => return .malformed .wrongType
  | .obj _ =>
    let text ← (← value.getObjVal? "syntax").getStr?
    let raw ← CBCL.parse text
    return CBCL.StateContextCastSyntax.field raw
  | _ =>
    let bindings : List (String × List String) ← fromJson? value
    return .value (bindings.map (fun (role,accounts) => ⟨role,accounts⟩))

def parsePin (value : Json) : Check (ResourceField String) :=
  match value with
  | .null => pure .absent
  | .str "correct" => pure (.value "dialect")
  | .str "wrong" => pure (.value "wrong")
  | .str "malformed" => pure (.malformed .wrongType)
  | _ => .error "unknown pin variant"

def fact (j : Json) : Check Fact := do
  return ⟨← (← j.getObjVal? "id").getNat?,← (← j.getObjVal? "verb").getStr?,
    ← (← j.getObjVal? "signer").getStr?,← fromJson? (← j.getObjVal? "parents"),
    ← fromJson? (← j.getObjVal? "thread"),← parseCast (← j.getObjVal? "cast"),← parsePin (← j.getObjVal? "pin")⟩

structure Input where
  name : String
  path : List String
  query : Option String
  facts : List Fact

def input (j : Json) : Check Input := do
  let facts ← (← (← j.getObjVal? "facts").getArr?).toList.mapM fact
  if !facts.all (fun a => facts.all (fun b => a.id != b.id || a == b)) then throw "conflicting context identity"
  if !facts.all (fun child => child.parents.all (fun parent => facts.any (fun a => a.id == parent))) then
    throw "context graph requires present predecessors"
  if !CBCL.StateCausalRank.causalCheck (facts.map Fact.act) then throw "context graph contains a causal cycle"
  return ⟨← (← j.getObjVal? "name").getStr?,← fromJson? (← j.getObjVal? "path"),
    ← fromJson? (← j.getObjVal? "query"),facts⟩

def definition (name : String) : Definition :=
  ⟨name,"dialect","body",some "@a",[⟨"chair",false⟩,⟨"reviewer",true⟩],⟨32,64,1000000000000,2048⟩,some "open"⟩

def profile (request : Input) : Profile := {
  definition := definition request.name
  metadata := fun id => ((request.facts.find? (fun fact => fact.id == id)).map Fact.metadata).getD ⟨none,.absent,.absent⟩
  address := fun id => s!"act:{id}" }

def support (request : Input) : List String :=
  ((request.facts.map (fun fact => s!"act:{fact.id}")) ++ request.facts.flatMap (fun fact => match fact.cast with
    | .value bindings => bindings.flatMap ResourceRoleBinding.accounts
    | _ => [])).eraseDups

def scalarJson : Val → Check Json
  | .str text => pure (.str text)
  | .int number => pure (toJson number)
  | .bool flag => pure (.bool flag)
  | _ => .error "unsupported context scalar"

def render : Nat → List String → CBCL.StateInstalledLegacy.Value → Check Json
  | 0, _, _ => .error "context value exceeds serialization depth"
  | fuel + 1, names, .object fields => do return Json.mkObj (← fields.mapM (fun (key,value) => do return (key,← render fuel names value)))
  | fuel + 1, names, .list values => do return toJson (← values.mapM (render fuel names))
  | _ + 1, _, .kernel (.cell .absent) => pure .null
  | _ + 1, _, .kernel (.cell (.value value)) => scalarJson value
  | _ + 1, _, .kernel (.integer number) => pure (toJson number)
  | _ + 1, _, .kernel (.boolean value) => pure (.bool value)
  | _ + 1, names, .kernel (.values member) =>
      pure (toJson ((names.filter (fun name => member (.str name))).mergeSort (fun a b => decide (a ≤ b))))
  | _ + 1, _, _ => .error "unexpected context value representation"

def evaluate (request : Input) : Check Json := do
  let p := profile request
  let rejected := Json.mkObj [("installed",.bool false)]
  if !validPath p.definition request.path then return rejected
  if request.query.any (fun query => !((queryPolicy request.path).any (fun policy =>
      policy.check [.element (.member (.str query))]))) then return rejected
  let result := CBCL.StateExecutableContext.read p request.path (request.facts.map Fact.act)
  let value ← match result.error with
    | some evidence => pure (Json.mkObj [("status",.str "fault"),
        ("evidence",toJson (evidence.eraseDups.mergeSort (fun a b => decide (a ≤ b))))])
    | none => match result.value with | none => pure .null | some value => render 32 (support request) value
  let threshold := request.query.map fun query =>
    if result.error.isSome then value else
      let reached := (result.value.map (CBCL.StateInstalledLegacy.readTest (.element (.member (.str query))))).getD false
      if reached then Json.mkObj [("status",.str "reached"),("element",Json.mkObj [("member",.str query)])]
      else Json.mkObj [("status",.str "pending")]
  return Json.mkObj [("installed",.bool true),("value",value),("threshold",threshold.getD .null),
    ("schema",.str (if stablePath request.path then "context" else "snapshot"))]

def run (j : Json) : Check Json := input j >>= evaluate
end StateContextOracle
