import LeanCbcl.SExpr
import LeanCbcl.Dialect

/-!
# CBCL Dialect Parser

Parses `(define ...)` / `(define-dialect ...)` S-expressions into Dialect records.
-/

namespace CBCL

def defaultResourceBounds : ResourceBounds :=
  { maxDepth := 16, maxExpansionSize := 1024, verificationTime := 50 }

structure DialectAccum where
  name          : String
  extends_      : List String
  author        : String
  performatives : List PerformativeDef
  resources     : ResourceBounds
  examples      : List SExpr
  signature     : Option String
  hash          : Option String
  protocol      : Option String

def sexprToSymbol? : SExpr → Option String
  | .atom (.symbol s) => some s
  | _ => none

def sexprToStringLike? : SExpr → Option String
  | .atom (.symbol s) => some s
  | .atom (.str s) => some s
  | _ => none

def sexprToNat? : SExpr → Option Nat
  | .atom (.num n) =>
    if _ : n ≥ 0 then some n.toNat else none
  | _ => none

def parseExtendsValue (val : SExpr) : Except String (List String) :=
  match val with
  | .atom (.symbol s) => .ok [s]
  | .list xs =>
    let rec go (ys : List SExpr) (acc : List String) : Except String (List String) :=
      match ys with
      | [] => .ok acc.reverse
      | y :: rest =>
        match sexprToSymbol? y with
        | some s => go rest (s :: acc)
        | none => .error "extends list must contain only symbols"
    go xs []
  | _ => .error "extends must be a symbol or list of symbols"

def applyResourceKey (rb : ResourceBounds) (key : String) (value : Nat) :
    Except String ResourceBounds :=
  match key with
  | "max-depth" => .ok { rb with maxDepth := value }
  | "max-expansion-size" => .ok { rb with maxExpansionSize := value }
  | "max-expansion" => .ok { rb with maxExpansionSize := value }
  | "max-verify-time" => .ok { rb with verificationTime := value }
  | "verification-time" => .ok { rb with verificationTime := value }
  | _ => .error s!"Unknown resource key: {key}"

def parseResourceSpec (spec : SExpr) (rb : ResourceBounds) :
    Except String ResourceBounds :=
  match spec with
  | .list xs =>
    let rec go (ys : List SExpr) (acc : ResourceBounds) : Except String ResourceBounds :=
      match ys with
      | [] => .ok acc
      | .list [ .atom (.keyword key), val ] :: rest =>
        match sexprToNat? val with
        | some n =>
          match applyResourceKey acc key n with
          | .ok rb' => go rest rb'
          | .error msg => .error msg
        | none => .error "resource values must be non-negative integers"
      | .atom (.keyword key) :: val :: rest =>
        match sexprToNat? val with
        | some n =>
          match applyResourceKey acc key n with
          | .ok rb' => go rest rb'
          | .error msg => .error msg
        | none => .error "resource values must be non-negative integers"
      | _ => .error "invalid resource specification"
    go xs rb
  | _ => .error "resources must be a list"

def parseExtendClause (clause : SExpr) : Except String PerformativeDef :=
  match clause with
  | .list (.atom (.symbol "extend") :: .atom (.symbol name) :: .list params :: body) =>
    match body with
    | [] => .error "extend clause requires a template body"
    | [t] => .ok { name := name, params := params, template := t }
    | _ => .ok { name := name, params := params, template := .list body }
  | _ => .error "invalid extend clause"

def applyKeywordClause (acc : DialectAccum) (key : String) (vals : List SExpr) :
    Except String DialectAccum :=
  match key with
  | "extends" =>
    match vals with
    | [] => .error "extends requires a value"
    | [v] =>
      match parseExtendsValue v with
      | .ok exts => .ok { acc with extends_ := exts }
      | .error msg => .error msg
    | _ =>
      let v := SExpr.list vals
      match parseExtendsValue v with
      | .ok exts => .ok { acc with extends_ := exts }
      | .error msg => .error msg
  | "author" =>
    match vals with
    | [v] =>
      match sexprToStringLike? v with
      | some s => .ok { acc with author := s }
      | none => .error "author must be a symbol or string"
    | _ => .error "author requires exactly one value"
  | "resources" | "resource-requirements" =>
    match vals with
    | [v] =>
      match parseResourceSpec v acc.resources with
      | .ok rb => .ok { acc with resources := rb }
      | .error msg => .error msg
    | _ => .error "resources requires a single list value"
  | "examples" =>
    match vals with
    | [v] =>
      match v with
      | .list xs => .ok { acc with examples := xs }
      | _ => .ok { acc with examples := [v] }
    | _ => .ok { acc with examples := vals }
  | "signature" | "signed" =>
    match vals with
    | [v] =>
      match sexprToStringLike? v with
      | some s => .ok { acc with signature := some s }
      | none => .error "signature must be a symbol or string"
    | _ => .error "signature requires exactly one value"
  | "hash" =>
    match vals with
    | [v] =>
      match sexprToStringLike? v with
      | some s => .ok { acc with hash := some s }
      | none => .error "hash must be a symbol or string"
    | _ => .error "hash requires exactly one value"
  | "protocol" =>
    match vals with
    | [v] =>
      match sexprToStringLike? v with
      | some s => .ok { acc with protocol := some s }
      | none => .error "protocol must be a symbol or string"
    | _ => .error "protocol requires exactly one value"
  | _ => .error s!"unknown dialect clause: {key}"

def parseDialectClauses (clauses : List SExpr) (acc : DialectAccum) :
    Except String DialectAccum :=
  match clauses with
  | [] => .ok acc
  | .atom (.keyword key) :: rest =>
    match rest with
    | [] => .error s!"keyword clause {key} missing value"
    | v :: rest' =>
      match applyKeywordClause acc key [v] with
      | .ok acc' => parseDialectClauses rest' acc'
      | .error msg => .error msg
  | clause :: rest =>
    match clause with
    | .list (.atom (.keyword key) :: vals) =>
      match applyKeywordClause acc key vals with
      | .ok acc' => parseDialectClauses rest acc'
      | .error msg => .error msg
    | .list (.atom (.symbol "extend") :: _) =>
      match parseExtendClause clause with
      | .ok perf => parseDialectClauses rest { acc with performatives := acc.performatives ++ [perf] }
      | .error msg => .error msg
    | _ => .error "unknown dialect clause"
termination_by clauses.length

def parseDialect (sexpr : SExpr) : Except String Dialect :=
  match sexpr with
  | .list (.atom (.symbol head) :: .atom (.symbol name) :: clauses) =>
    if head == "define" || head == "define-dialect" then
      let acc : DialectAccum := {
        name := name
        extends_ := []
        author := "unknown"
        performatives := []
        resources := defaultResourceBounds
        examples := []
        signature := none
        hash := none
        protocol := none
      }
      match parseDialectClauses clauses acc with
      | .ok acc' =>
        .ok { name := acc'.name
            , extends_ := acc'.extends_
            , author := acc'.author
            , performatives := acc'.performatives
            , resources := acc'.resources
            , examples := acc'.examples
            , signature := acc'.signature
            , hash := acc'.hash
            , protocol := acc'.protocol
            }
      | .error msg => .error msg
    else
      .error "expected (define ...) or (define-dialect ...)"
  | _ => .error "expected (define ...) or (define-dialect ...)"

end CBCL
