import LeanCbcl.SExpr
import LeanCbcl.Dialect

/-!
# CBCL Dialect Parser

Parses `(define ...)` / `(define-dialect ...)` S-expressions into Dialect records.
-/

namespace CBCL

/-- Default resource limits applied to a dialect when no explicit `resources`
clause is given: depth 16, expansion size 1024, verification time 50. -/
def defaultResourceBounds : ResourceBounds :=
  { maxDepth := 16, maxExpansionSize := 1024, verificationTime := 50 }

/-- Mutable accumulator threaded through dialect-clause parsing; it collects the
fields of the dialect being built before they are copied into a final `Dialect`. -/
structure DialectAccum where
  /-- The dialect's name, taken from the `(define <name> ...)` head. -/
  name          : String
  /-- Names of dialects this one extends, from any `extends` clause. -/
  extends_      : List String
  /-- The declared author, defaulting to `"unknown"`. -/
  author        : String
  /-- Performative definitions collected from `extend` clauses. -/
  performatives : List PerformativeDef
  /-- Resource bounds, starting from `defaultResourceBounds`. -/
  resources     : ResourceBounds
  /-- Example S-expressions gathered from `examples` clauses. -/
  examples      : List SExpr
  /-- Optional cryptographic signature string, if a `signature`/`signed` clause is present. -/
  signature     : Option String
  /-- Optional hash string, if a `hash` clause is present. -/
  hash          : Option String
  /-- Optional protocol identifier, if a `protocol` clause is present. -/
  protocol      : Option String

/-- Extracts the underlying name from a symbol atom, returning `none` for any
other S-expression. -/
def sexprToSymbol? : SExpr → Option String
  | .atom (.symbol s) => some s
  | _ => none

/-- Extracts a string from either a symbol atom or a string-literal atom,
returning `none` for any other S-expression. -/
def sexprToStringLike? : SExpr → Option String
  | .atom (.symbol s) => some s
  | .atom (.str s) => some s
  | _ => none

/-- Extracts a `Nat` from a non-negative numeric atom, returning `none` for
negative numbers or any other S-expression. -/
def sexprToNat? : SExpr → Option Nat
  | .atom (.num n) =>
    if _ : n ≥ 0 then some n.toNat else none
  | _ => none

/-- Parses the value of an `extends` clause: a single symbol yields a one-element
list, and a list of symbols yields their names; anything else is an error. -/
def parseExtendsValue (val : SExpr) : Except String (List String) :=
  match val with
  | .atom (.symbol s) => .ok [s]
  | .list xs =>
    let rec
    /-- Folds over the list elements, requiring each to be a symbol; accumulates
    names in reverse, then restores order once the list is exhausted. -/
    go (ys : List SExpr) (acc : List String) : Except String (List String) :=
      match ys with
      | [] => .ok acc.reverse
      | y :: rest =>
        match sexprToSymbol? y with
        | some s => go rest (s :: acc)
        | none => .error "extends list must contain only symbols"
    go xs []
  | _ => .error "extends must be a symbol or list of symbols"

/-- Updates one field of `rb` according to a recognized resource key
(`max-depth`, `max-expansion-size`/`max-expansion`, or
`max-verify-time`/`verification-time`); an unknown key is an error. -/
def applyResourceKey (rb : ResourceBounds) (key : String) (value : Nat) :
    Except String ResourceBounds :=
  match key with
  | "max-depth" => .ok { rb with maxDepth := value }
  | "max-expansion-size" => .ok { rb with maxExpansionSize := value }
  | "max-expansion" => .ok { rb with maxExpansionSize := value }
  | "max-verify-time" => .ok { rb with verificationTime := value }
  | "verification-time" => .ok { rb with verificationTime := value }
  | _ => .error s!"Unknown resource key: {key}"

/-- Parses a `resources` list into updated `ResourceBounds`, accepting either
`(:key value)` pairs or flat `:key value` sequences and applying each via
`applyResourceKey` starting from `rb`. -/
def parseResourceSpec (spec : SExpr) (rb : ResourceBounds) :
    Except String ResourceBounds :=
  match spec with
  | .list xs =>
    let rec
    /-- Iterates over the resource entries, applying each keyword/value pair to
    the accumulated bounds via `applyResourceKey` until the list is exhausted. -/
    go (ys : List SExpr) (acc : ResourceBounds) : Except String ResourceBounds :=
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

/-- Parses an `(extend <name> (<params>) <body>...)` clause into a
`PerformativeDef`, using the single body element as the template or wrapping
multiple body elements in a list; an empty body is an error. -/
def parseExtendClause (clause : SExpr) : Except String PerformativeDef :=
  match clause with
  | .list (.atom (.symbol "extend") :: .atom (.symbol name) :: .list params :: body) =>
    match body with
    | [] => .error "extend clause requires a template body"
    | [t] => .ok { name := name, params := params, template := t }
    | _ => .ok { name := name, params := params, template := .list body }
  | _ => .error "invalid extend clause"

/-- Applies a single dialect clause identified by `key` (e.g. `extends`,
`author`, `resources`, `examples`, `signature`, `hash`, `protocol`) with its
values to the accumulator, updating the corresponding field or erroring. -/
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

/-- Recursively consumes the list of dialect clauses, dispatching bare
`:keyword value` pairs and `(:keyword ...)`/`(extend ...)` lists to the
appropriate handler and threading the resulting accumulator through. -/
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

/-- Top-level entry point: parses a `(define <name> ...)` or
`(define-dialect <name> ...)` S-expression, seeding a `DialectAccum` with
defaults, running the clause parser, and building the final `Dialect`. -/
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
