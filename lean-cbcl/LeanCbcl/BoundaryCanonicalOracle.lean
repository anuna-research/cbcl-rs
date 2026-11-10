import Lean
import LeanCbcl.BoundaryShapeCanonical

/-! Closed transport for direct Rust/function conformance, not state admission.
Parameter values are opaque tagged JSON. Shape metadata transports typed atom
octets; the oracle independently computes length framing and recursive sort keys.
This adapter is tested, not an extraction proof of Rust's AST or atom encoder. -/
set_option autoImplicit false
namespace CBCL.BoundaryCanonicalOracle
open Lean

/-- Recognize only a complete tagged keyword token; all values stay opaque. -/
def keyword (value : Json) : Option String := do
  let items ← value.getArr?.toOption
  match items.toList with
  | [.str "keyword", .str key] => some key
  | _ => none

/-- Construct the exact tagged keyword spelling used by the Rust adapter. -/
def keyToken (key : String) : Json := Json.arr #[Json.str "keyword",Json.str key]

/-- This executable adapter satisfies the proven scanner's key-token law. -/
theorem keyword_keyToken (key : String) : keyword (keyToken key) = some key := by
  rfl

/-- A recognized canonical-expression tree with opaque typed atom octets. -/
inductive Expr where
  | atom (octets : String)
  | list (children : List Expr)

/-- Recognize all metadata before computing a key; exhausted budgets reject. -/
def decodeExpr : Nat → Json → Except String Expr
  | 0, _ => throw "canonical metadata depth exceeded"
  | depth+1, input => do
    let items ← input.getArr?
    match items.toList with
    | [.str "atom",.str octets] => return .atom octets
    | [.str "list",.arr children] => return .list (← children.toList.mapM (decodeExpr depth))
    | _ => throw "expected canonical atom/list metadata"

mutual
/-- Complete RFC 9804 byte-length framing; no truncation/default branch. -/
def encodeExpr : Expr → String
  | .atom octets => toString octets.toUTF8.size ++ ":" ++ octets
  | .list children => "(" ++ encodeExprs children ++ ")"
/-- Concatenate exactly the canonical encodings of all child expressions. -/
def encodeExprs : List Expr → String
  | [] => ""
  | child :: rest => encodeExpr child ++ encodeExprs rest
end

mutual
/-- Return recognized metadata without changing atoms or list positions. -/
def exprJson : Expr → Json
  | .atom octets => Json.arr #[.str "atom",.str octets]
  | .list children => Json.arr #[.str "list",toJson (exprsJson children)]
/-- Serialize every recognized metadata child. -/
def exprsJson : List Expr → List Json
  | [] => []
  | child :: rest => exprJson child :: exprsJson rest
end

/-- Opaque shape label, preserving all nonchild metadata. -/
structure Label where
  /-- Shape/rule constructor, used only for its declared rank. -/
  kind : String
  /-- Performative or keyword name; empty on max-depth constraints. -/
  name : String
  /-- Recognized canonical metadata preceding recursive child rules. -/
  metadata : List Expr

/-- Recognize authored shape/metadata trees without changing sibling order. -/
def decodeTree : Nat → Json → Except String (BoundaryShapeCanonical.Tree Label)
  | 0, _ => throw "shape conformance depth exceeded"
  | depth+1, input => do
    let kind ← (← input.getObjVal? "kind").getStr?
    if !["root","shape","require","optional","max-depth"].contains kind then throw "unknown shape kind"
    let name ← (← input.getObjVal? "name").getStr?
    let rawMetadata ← (← input.getObjVal? "prefix").getArr?
    let metadata ← rawMetadata.toList.mapM (decodeExpr 32)
    let children ← (← input.getObjVal? "children").getArr?
    return .node ⟨kind,name,metadata⟩ (← children.toList.mapM (decodeTree depth))

mutual
/-- Complete shape/rule expression after child ordering, without a fuel cutoff. -/
def expression : BoundaryShapeCanonical.Tree Label → Expr
  | .node label children => .list (label.metadata ++ expressions children)
/-- Reconstruct all recursive child expressions. -/
def expressions : List (BoundaryShapeCanonical.Tree Label) → List Expr
  | [] => []
  | child :: rest => expression child :: expressions rest
end

/-- Exact native tuple components: rule rank, UTF-8 name, canonical subtree.
Top-level shapes omit rank; the transport root is never sorted as a sibling. -/
def shapeKey (tree : BoundaryShapeCanonical.Tree Label) : List (List UInt8) :=
  let .node label _ := tree
  let name := label.name.toUTF8.data.toList
  let encoded := (encodeExpr (expression tree)).toUTF8.data.toList
  if label.kind == "shape" then [name,encoded]
  else [[if label.kind == "max-depth" then 1 else 0],name,encoded]

mutual
/-- Return unchanged metadata and the normalized child order completely. -/
def encodeTree : BoundaryShapeCanonical.Tree Label → Json
  | .node label children => Json.mkObj [
      ("kind",toJson label.kind),("name",toJson label.name),("prefix",toJson (exprsJson label.metadata)),
      ("children",toJson (encodeTrees children))]
/-- Return every normalized child. -/
def encodeTrees : List (BoundaryShapeCanonical.Tree Label) → List Json
  | [] => []
  | child :: rest => encodeTree child :: encodeTrees rest
end

/-- Direct function outputs, with no Rust-supplied expected order or sort key. -/
def run (input : Json) : Except String Json := do
  match ← (← input.getObjVal? "operation").getStr? with
  | "params" =>
    let params ← (← input.getObjVal? "params").getArr?
    return Json.mkObj [("params",toJson (BoundaryCanonical.canonicalTokens keyword keyToken params.toList))]
  | "shapes" =>
    let tree ← decodeTree 16 (← input.getObjVal? "tree")
    return Json.mkObj [("tree",encodeTree (BoundaryShapeCanonical.complete shapeKey tree))]
  | _ => throw "unknown canonicalisation operation"

end CBCL.BoundaryCanonicalOracle
