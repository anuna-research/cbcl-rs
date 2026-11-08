import Lean
import LeanCbcl.StateJsonValue

/-! Exact byte-spelling oracle for public native state Value/render_json.
Inputs retain every container's stored order. No state admission, constructor
canonicalization or cryptographic identity is inferred from this campaign. -/
namespace CBCL.StateJsonOracle
open Lean StateJsonValue

/-- Closed tagged native value grammar with explicit depth and i128 bounds. -/
def value : Nat → Json → Except String Value
  | 0,_ => throw "state JSON value exceeds depth 32"
  | fuel+1,j => do
    let parts ← j.getArr?
    match parts.toList with
    | [.str "absent"] => return .absent
    | [.str "str",.str text] => return .str text
    | [.str "int",.str text] =>
      let some n := text.toInt? | throw "expected signed integer text"
      if toString n != text then throw "integer text must be canonical signed decimal"
      if n < -(2^127) ∨ 2^127 ≤ n then throw "integer exceeds native i128"
      return .int n
    | [.str "bool",.bool flag] => return .bool flag
    | [.str "list",items] => return .list (← (← items.getArr?).toList.mapM (value fuel))
    | [.str "set",items] => return .set (← (← items.getArr?).toList.mapM (value fuel))
    | [.str "map",entries] =>
      let rows ← (← entries.getArr?).toList.mapM (fun row => do
        match (← row.getArr?).toList with
        | [key,data] => return (← value fuel key,← value fuel data)
        | _ => throw "expected native map key/value pair")
      return .map rows
    | [.str "event",.str signer,data] => return .event signer (← value fuel data)
    | _ => throw "expected tagged native state value"

/-- Compare operational append emission, whose equality to the declarative
spelling is proved, with actual native UTF-8 strings rather than parsed JSON. -/
def run (j : Json) : Except String Json := do
  let current ← value 32 (← j.getObjVal? "value")
  let fields ← (← (← j.getObjVal? "state").getArr?).toList.mapM (fun row => do
    match (← row.getArr?).toList with
    | [.str name,data] => return (name,← value 32 data)
    | _ => throw "expected named state field")
  return Json.mkObj [("rendered",.str (emit current "")),("state",.str (emitState fields ""))]

end CBCL.StateJsonOracle
