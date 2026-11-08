import Lean
import LeanCbcl.StateNonnegativeAdmission
import LeanCbcl.StateKeywordExtraction

/-! Closed JSON transport for live comparison of the mandatory/nonnegative
projection with native shape validation. Tagged atoms preserve scalar kinds. -/
namespace CBCL.StateShapeOracle
open Lean State StateInstalledLegacy StateNonnegativeAdmission

/-- Decode a tagged expanded-message tree, rejecting malformed constructors. -/
def tree : Nat → Json → Except String SExpr
  | 0,_ => throw "shape tree exceeds depth 32"
  | fuel+1,j => do
    let items ← j.getArr?
    match items.toList with
    | [.str "num",value] => return .atom (.num (← value.getInt?))
    | [.str "str",.str value] => return .atom (.str value)
    | [.str "symbol",.str value] => return .atom (.symbol value)
    | [.str "keyword",.str value] => return .atom (.keyword value)
    | [.str "bool",.bool value] => return .atom (.bool value)
    | [.str "list",values] =>
      let children ← values.getArr?
      return .list (← children.toList.mapM (tree fuel))
    | _ => throw "expected tagged shape tree"

/-- Decode recognized writer metadata and evaluate only the requested projection. -/
def run (j : Json) : Except String Json := do
  let shapes ← (← (← j.getObjVal? "shapes").getArr?).toList.mapM fun row => do
    let verb ← (← row.getObjVal? "verb").getStr?
    let field ← (← row.getObjVal? "field").getStr?
    let required ← (← row.getObjVal? "required").getBool?
    let numeric ← (← row.getObjVal? "nonnegative").getBool?
    return (⟨verb,field,required,numeric⟩ : WriterShape)
  let verb ← (← j.getObjVal? "verb").getStr?
  let message ← tree 32 (← j.getObjVal? "message")
  let act : Act := ⟨0,verb,"@a",[],[],[]⟩
  return Json.mkObj [("checked",toJson (checkedWriter shapes act message))]

/-- Closed state-shape/extraction campaign. All keys are drawn from amount,
other and routing fields, and generated numbers stay inside native state bounds.
This checks the state-shape stage, not protocol or authentication admission. -/
def keywordRun (j : Json) : Except String Json := do
  let .list params ← tree 32 (← j.getObjVal? "params") | throw "params must be a tagged list"
  let rejected := Json.mkObj [("accepted",.bool false)]
  let some rows := StateKeywordExtraction.parse params | return rejected
  if rows.any (fun row => !["amount","other","thread"].contains row.1) then return rejected
  if rows.any (fun row => row.1 == "thread" && match row.2 with | .atom (.str _) => false | _ => true) then
    throw "keyword profile thread values must be strings"
  if rows.any (fun row => row.1 == "amount" && match row.2 with | .atom (.num n) => decide (n < -1000000000000 ∨ 1000000000000 < n) | _ => false) then return rejected
  let some values := StateKeywordExtraction.extract params | return rejected
  let writer : State.Act := ⟨0,"mint","@a",[],values,[]⟩
  let shapes : List StateInstalledLegacy.WriterShape := [⟨"mint","amount",true,true⟩]
  let source : SExpr := .list ([.atom (.symbol "mint"),.list []] ++ params)
  if !StateNonnegativeAdmission.checkedWriter shapes writer source then return rejected
  return Json.mkObj [("accepted",.bool true),("amount",Lean.toJson (State.amount "amount" writer))]

end CBCL.StateShapeOracle
