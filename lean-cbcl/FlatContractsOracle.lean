import LeanCbcl.FlatContracts.Resolution
open Lean CBCL.FlatContracts
namespace FlatContractsOracle
abbrev Check := Except String

def array (j : Json) : Check (List Json) := j.getArr?.map Array.toList

def atom (j : Json) : Check Atom := do
  let a ← match ← array j with
    | [.str "integer",.str n] => match n.toInt? with
        | some n => pure (.integer n) | none => throw "invalid integer"
    | [.str "float",.str n] => match n.toNat? with
        | some n => pure (.float n) | none => throw "invalid bits"
    | [.str "decimal",.str n,scale] => match n.toInt? with
        | some n => pure (.decimal n (← scale.getNat?)) | none => throw "invalid coefficient"
    | [.str "string",.str s] => pure (.string s)
    | [.str "symbol",.str s] => pure (.symbol s)
    | [.str "keyword",.str s] => pure (.keyword s)
    | [.str "bool",.bool b] => pure (.bool b)
    | _ => throw "invalid atom tag"
  if decide a.Valid then return a else throw "invalid numeric representation"

def value : Nat → Json → Check Value
  | 0,_ => .error "transport depth exceeded"
  | fuel+1,j => do
    let xs ← array j
    match xs with
    | .str "list"::rest => return .list (← rest.mapM (value fuel))
    | _ => return .atom (← atom j)

def builtin : String → Check Builtin
  | "integer" => .ok .integer | "float" => .ok .float | "decimal" => .ok .decimal
  | "number" => .ok .number | "nonnegative" => .ok .nonnegative | "string" => .ok .string
  | "hlc" => .ok .hlc | "symbol" => .ok .symbol | "keyword" => .ok .keyword
  | "bool" => .ok .bool | "list" => .ok .list | _ => .error "unknown builtin"

def cmp : String → Check Cmp
  | ">" => .ok .gt | ">=" => .ok .ge | "<" => .ok .lt | "<=" => .ok .le
  | _ => .error "unknown comparator"

/-- Closed reference profile: mathematical whole-string languages. -/
def digit (c : Char) : Prop := '0' ≤ c ∧ c ≤ '9'
instance (c : Char) : Decidable (digit c) := by unfold digit; infer_instance

def language (source text : String) : Prop :=
  match source with
  | "" => text = ""
  | "." => text.toList.length = 1 ∧ '\n' ∉ text.toList ∧ '\r' ∉ text.toList
  | "[0-9]{4}" => text.toList.length = 4 ∧ ∀ c ∈ text.toList, digit c
  | "INV-[0-9]+" => text.startsWith "INV-" = true ∧ text.toList.length > 4 ∧
      ∀ c ∈ text.toList.drop 4, digit c
  | "^x$" => text = "^x$"
  | _ => False
instance (source text : String) : Decidable (language source text) := by
  unfold language; split <;> infer_instance

def backend : RegexBackend := ⟨fun source text => decide (language source text),language,fun _ => 1⟩
theorem backend_correct : RegexCorrect backend := by
  intro source text; exact decide_eq_true_iff

def supported (source : String) : Bool := ["",".","[0-9]{4}","INV-[0-9]+","^x$"].contains source

def predicate (j : Json) : Check Predicate := do
  match ← array j with
  | [.str "matches",.str source] =>
      if supported source then return .pattern source else throw "unsupported oracle regex profile"
  | .str "length"::bounds =>
      let bounds ← bounds.mapM fun bound => do
        match ← array bound with
        | [.str op,n] => return (← cmp op,← n.getNat?)
        | _ => throw "invalid length bound"
      return .length bounds
  | [.str op,a] => return .bound (← cmp op) (← atom a)
  | _ => throw "invalid predicate"

def expr : Nat → Json → Check CBCL.FlatContracts.Expr
  | 0,_ => .error "transport depth exceeded"
  | fuel+1,j => do
    match ← array j with
    | [.str "builtin",.str name] => return .leaf (.builtin (← builtin name))
    | [.str "ref",.str name] => return .ref name
    | .str "enum"::atoms => return .leaf (.enumeration (← atoms.mapM atom))
    | .str "refine"::.str name::predicates =>
        return .leaf (.refined (← builtin name) (← predicates.mapM predicate))
    | .str "all"::children => return .all (← children.mapM (expr fuel))
    | .str "any"::children => return .any (← children.mapM (expr fuel))
    | _ => throw "invalid expression"

def nodes : CBCL.FlatContracts.Expr → Nat
  | .leaf _ | .ref _ => 1
  | .all children | .any children => 1 + (children.map nodes).sum

def builtinName : Builtin → String
  | .integer => "integer" | .float => "float" | .decimal => "decimal" | .number => "number"
  | .nonnegative => "nonnegative" | .string => "string" | .hlc => "hlc" | .symbol => "symbol"
  | .keyword => "keyword" | .bool => "bool" | .list => "list"
def cmpName : Cmp → String | .gt => ">" | .ge => ">=" | .lt => "<" | .le => "<="
def symbol (s : String) : Value := .atom (.symbol s)
def predicateSource : Predicate → Value
  | .bound op a => .list [symbol (cmpName op),.atom a]
  | .pattern p => .list [symbol "matches",.atom (.string p)]
  | .length bounds => .list (symbol "length" :: bounds.map (fun b =>
      .list [symbol (cmpName b.1),.atom (.integer (Int.ofNat b.2))]))
def source : CBCL.FlatContracts.Expr → Value
  | .leaf (.builtin b) => symbol (builtinName b)
  | .leaf (.enumeration atoms) => .list (symbol "one-of" :: atoms.map Value.atom)
  | .leaf (.refined b predicates) => .list (symbol (builtinName b) :: predicates.map predicateSource)
  | .ref name => symbol name
  | .all children => .list (symbol "and" :: children.map source)
  | .any children => .list (symbol "or" :: children.map source)

def nameValid (name : String) : Bool :=
  let lower := fun c : Char => decide ('a' ≤ c ∧ c ≤ 'z')
  match name.toList with
  | [] => false
  | c::cs => lower c && decide (cs.length < 48) &&
      cs.all (fun c => lower c || decide ('0' ≤ c ∧ c ≤ '9') || c == '-') &&
      !(builtin name).isOk && !["and","or","matches","length","one-of","type","default"].contains name

def run (j : Json) : Check Json := do
  let fields ← j.getObj?
  if fields.toArray.size != 4 then throw "expected four request fields"
  let definitions ← (← array (← j.getObjVal? "definitions")).mapM fun item => do
    match ← array item with
    | [.str name,body] => return (name,← expr 128 body)
    | _ => throw "invalid declaration"
  let rawRoot ← j.getObjVal? "contract"
  let rawDefinitions ← j.getObjVal? "definitions"
  if rawRoot.compress.utf8ByteSize + rawDefinitions.compress.utf8ByteSize > 8192 then
    throw "unsupported oracle source-size profile"
  let root ← expr 128 rawRoot
  if nodes root + (definitions.map (fun d => nodes d.2)).sum > 128 then
    throw "unsupported oracle source-node profile"
  let input ← value 128 (← j.getObjVal? "value")
  let work ← (← j.getObjVal? "work").getNat?
  let verdict := if !(source root).fits || !definitions.all (fun d => (source d.2).fits) || definitions.length > 128 || !(definitions.map Prod.fst).all nameValid ||
      !(decide (definitions.map Prod.fst).Nodup) then "definition-error"
    else match install 32 definitions root with
    | none => "definition-error"
    | some code => match check backend Value.fits code input work with
      | .accepted => "accepted" | .violation => "violation" | .resourceLimit => "resource-limit"
  return Json.mkObj [("verdict",.str verdict)]
end FlatContractsOracle

def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let answer := match Json.parse line >>= FlatContractsOracle.run with
      | .error error => Json.mkObj [("error",.str error)]
      | .ok response => response
    stdout.putStrLn answer.compress
    stdout.flush
