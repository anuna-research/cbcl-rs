import LeanCbcl.SExpr
import LeanCbcl.Dialect
import LeanCbcl.PatternMatch

/-!
# CBCL Template Expansion

Implements the bounded template expansion language described in the paper.
Mirrors `src/cbcl/template-expansion.scm` at a structural level.
-/

namespace CBCL

def isSymbolHead : SExpr → Bool
  | .list (.atom (.symbol _) :: _) => true
  | _ => false

def cbclTypeOf : SExpr → String
  | .atom (.str _) => "string"
  | .atom (.num _) => "number"
  | .atom (.bool _) => "boolean"
  | .atom (.symbol s) =>
    if s.startsWith "@" then "agent" else "symbol"
  | .atom (.keyword _) => "symbol"
  | .list _ => "list"

def typeMatches (value : SExpr) (typeName : String) : Bool :=
  match typeName with
  | "string" => match value with | .atom (.str _) => true | _ => false
  | "number" => match value with | .atom (.num _) => true | _ => false
  | "boolean" => match value with | .atom (.bool _) => true | _ => false
  | "symbol" => match value with | .atom (.symbol _) => true | .atom (.keyword _) => true | _ => false
  | "list" => match value with | .list _ => true | _ => false
  | "agent" => match value with | .atom (.symbol s) => s.startsWith "@" | .atom (.str s) => s.startsWith "@" | _ => false
  | _ => false

def evaluateCondition (cond : SExpr) (bindings : Bindings) : Except String Bool :=
  match cond with
  | .list [ .atom (.symbol "="), .atom (.symbol param), value ] =>
    match bindings.lookup param with
    | some v => .ok (v == value)
    | none => .error s!"Unbound parameter in equality test: {param}"
  | .list [ .atom (.symbol "member"), .atom (.symbol param), .list values ] =>
    match bindings.lookup param with
    | some v => .ok (values.contains v)
    | none => .error s!"Unbound parameter in membership test: {param}"
  | .list [ .atom (.symbol "type?"), .atom (.symbol param), .atom (.symbol typeName) ] =>
    match bindings.lookup param with
    | some v => .ok (typeMatches v typeName)
    | none => .error s!"Unbound parameter in type test: {param}"
  | _ => .error "Invalid condition"

mutual
  def expandTemplate (template : SExpr) (bindings : Bindings) : Except String SExpr :=
    match template with
    | .list [ .atom (.symbol "literal"), msg ] =>
      .ok (substituteBindings msg bindings)
    | .atom (.symbol param) =>
      match bindings.lookup param with
      | some v => .ok v
      | none => .error s!"Unbound parameter in template: {param}"
    | .list [ .atom (.keyword k), .atom (.symbol param) ] =>
      match bindings.lookup param with
      | some v => .ok (.list [.atom (.keyword k), v])
      | none => .error s!"Unbound parameter in tagged substitution: {param}"
    | .list (.atom (.symbol "cond") :: clauses) =>
      expandConditionalTemplate clauses bindings
    | .list [] =>
      .error "Sequence template must contain at least one template"
    | .list xs =>
      if isSymbolHead template then
        .ok (substituteBindings template bindings)
      else
        expandSequenceTemplate xs bindings
    | other =>
      .ok (substituteBindings other bindings)

  def expandConditionalTemplate (clauses : List SExpr) (bindings : Bindings) : Except String SExpr :=
    match clauses with
    | [] => .error "No condition matched and no else clause provided"
    | clause :: rest =>
      match clause with
      | .list [ .atom (.symbol "else"), template ] =>
        expandTemplate template bindings
      | .list [ condition, template ] =>
        match evaluateCondition condition bindings with
        | .error msg => .error msg
        | .ok true => expandTemplate template bindings
        | .ok false => expandConditionalTemplate rest bindings
      | _ => .error "Invalid conditional clause"

  def expandSequenceTemplate (templates : List SExpr) (bindings : Bindings) : Except String SExpr :=
    let rec go (ts : List SExpr) (acc : List SExpr) : Except String (List SExpr) :=
      match ts with
      | [] => .ok acc.reverse
      | t :: rest =>
        match expandTemplate t bindings with
        | .error msg => .error msg
        | .ok v => go rest (v :: acc)
    match go templates [] with
    | .ok xs => .ok (.list xs)
    | .error msg => .error msg
end

def expandPerformative (perf : PerformativeDef) (args : List SExpr) : Except String SExpr :=
  let pattern := SExpr.list perf.params
  let actual := SExpr.list args
  match matchPattern pattern actual [] with
  | none => .error "Argument pattern mismatch"
  | some bindings =>
    expandTemplate perf.template bindings

end CBCL
