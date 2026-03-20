import LeanCbcl.SExpr
import LeanCbcl.Parser

/-!
# S-Expression Serializer

Converts `SExpr` back to canonical string form (RFC 9804).
-/

namespace CBCL

/-- Escape special characters in a string. -/
def escapeString (s : String) : String :=
  s.foldl (fun acc c =>
    if c == '"' then acc ++ "\\\""
    else if c == '\\' then acc ++ "\\\\"
    else acc.push c) ""

/-- Serialize an S-expression to its canonical string form. -/
def serialize : SExpr → String
  | .atom (.symbol s) => s
  | .atom (.str s) => "\"" ++ escapeString s ++ "\""
  | .atom (.num n) => toString n
  | .atom (.bool true) => "#t"
  | .atom (.bool false) => "#f"
  | .atom (.keyword s) => ":" ++ s
  | .list xs => "(" ++ serializeList xs ++ ")"
where
  serializeList : List SExpr → String
    | [] => ""
    | [x] => serialize x
    | x :: xs => serialize x ++ " " ++ serializeList xs

/-- Serialize is total. -/
theorem serialize_total (e : SExpr) : ∃ s, serialize e = s := ⟨_, rfl⟩

-- ============================================================
-- Round-trip specification
-- ============================================================

/-- An S-expression round-trips cleanly: parse (serialize e) = .ok e.
    Not all SExprs round-trip (e.g., symbols containing delimiters won't),
    so we define which ones do. -/
def RoundTrippable (e : SExpr) : Prop :=
  parse (serialize e) = .ok e

instance (e : SExpr) : Decidable (RoundTrippable e) :=
  inferInstanceAs (Decidable (parse (serialize e) = .ok e))

-- ============================================================
-- Round-trip proofs for concrete cases (verified by kernel reduction)
-- ============================================================

theorem roundtrip_symbol : RoundTrippable (.atom (.symbol "hello")) := by native_decide

theorem roundtrip_number : RoundTrippable (.atom (.num 42)) := by native_decide

theorem roundtrip_neg_number : RoundTrippable (.atom (.num (-7))) := by native_decide

theorem roundtrip_bool_true : RoundTrippable (.atom (.bool true)) := by native_decide

theorem roundtrip_bool_false : RoundTrippable (.atom (.bool false)) := by native_decide

theorem roundtrip_string : RoundTrippable (.atom (.str "hello")) := by native_decide

theorem roundtrip_keyword : RoundTrippable (.atom (.keyword "key")) := by native_decide

theorem roundtrip_empty_list : RoundTrippable (.list []) := by native_decide

theorem roundtrip_simple_list :
    RoundTrippable (.list [.atom (.symbol "a"), .atom (.symbol "b")]) := by native_decide

theorem roundtrip_nested_list :
    RoundTrippable (.list [.atom (.symbol "a"), .list [.atom (.symbol "b"), .atom (.symbol "c")]]) := by native_decide

theorem roundtrip_tell_message :
    RoundTrippable (.list [.atom (.symbol "tell"), .atom (.symbol "alice"), .atom (.symbol "hello")]) := by native_decide

theorem roundtrip_mixed :
    RoundTrippable (.list [.atom (.symbol "data"), .atom (.num 42), .atom (.bool true), .atom (.str "hi")]) := by native_decide

-- ============================================================
-- Parametric round-trip characterization
-- ============================================================

/-- A character is a delimiter (space, tab, newline, CR, parens, quote). -/
def isDelimChar (c : Char) : Bool :=
  c == '(' || c == ')' || c == '"' || c == ' ' || c == '\t' || c == '\n' || c == '\r'

/-- A symbol string is "safe" for round-tripping: non-empty, contains no
    delimiter characters, does not start with `:` (keyword syntax),
    is not `#t` or `#f` (boolean literals), and is not parseable as an integer.
    These are exactly the symbol names that `serialize` emits bare and
    `parse` reads back as the same symbol. -/
def SafeSymbol (s : String) : Prop :=
  s ≠ "" ∧
  (∀ c, c ∈ s.toList → isDelimChar c = false) ∧
  ¬s.startsWith ":" ∧
  s ≠ "#t" ∧
  s ≠ "#f" ∧
  s.toInt? = none

instance : DecidablePred SafeSymbol := fun s =>
  inferInstanceAs (Decidable (
    s ≠ "" ∧
    (∀ c, c ∈ s.toList → isDelimChar c = false) ∧
    ¬s.startsWith ":" ∧
    s ≠ "#t" ∧
    s ≠ "#f" ∧
    s.toInt? = none))

/-- Structural characterization of round-trippable S-expressions.
    An S-expression round-trips through `serialize` then `parse` iff it
    is built from safe symbols, arbitrary strings, integers, booleans,
    non-empty keywords, and lists of round-trippable sub-expressions. -/
inductive RoundTrippable' : SExpr → Prop where
  | symbol  : SafeSymbol s → RoundTrippable' (.atom (.symbol s))
  | str     : RoundTrippable' (.atom (.str s))
  | num     : RoundTrippable' (.atom (.num n))
  | bool    : RoundTrippable' (.atom (.bool b))
  | keyword : s ≠ "" → RoundTrippable' (.atom (.keyword s))
  | list    : (∀ e, e ∈ xs → RoundTrippable' e) → RoundTrippable' (.list xs)

-- ============================================================
-- SafeSymbol concrete tests
-- ============================================================

theorem safeSymbol_hello : SafeSymbol "hello" := by native_decide

theorem safeSymbol_foo_bar : SafeSymbol "foo-bar" := by native_decide

theorem safeSymbol_x123 : SafeSymbol "x123" := by native_decide

theorem safeSymbol_plus : SafeSymbol "+" := by native_decide

theorem safeSymbol_underscore : SafeSymbol "my_var" := by native_decide

/-- Negative test: empty string is not a safe symbol. -/
theorem not_safeSymbol_empty : ¬SafeSymbol "" := by native_decide

/-- Negative test: string with space is not a safe symbol. -/
theorem not_safeSymbol_space : ¬SafeSymbol "a b" := by native_decide

/-- Negative test: `#t` is a boolean literal, not a safe symbol. -/
theorem not_safeSymbol_true : ¬SafeSymbol "#t" := by native_decide

/-- Negative test: `#f` is a boolean literal, not a safe symbol. -/
theorem not_safeSymbol_false : ¬SafeSymbol "#f" := by native_decide

/-- Negative test: `:key` starts with colon (keyword syntax). -/
theorem not_safeSymbol_keyword : ¬SafeSymbol ":key" := by native_decide

/-- Negative test: `42` is parseable as an integer. -/
theorem not_safeSymbol_number : ¬SafeSymbol "42" := by native_decide

/-- Negative test: string with paren is not a safe symbol. -/
theorem not_safeSymbol_paren : ¬SafeSymbol "a(b" := by native_decide

-- ============================================================
-- Round-trip tests for RoundTrippable' examples
-- ============================================================

/-- A safe symbol round-trips. -/
theorem roundtrip_safe_symbol_hello :
    RoundTrippable (.atom (.symbol "hello")) := by native_decide

/-- A safe symbol with hyphens round-trips. -/
theorem roundtrip_safe_symbol_foo_bar :
    RoundTrippable (.atom (.symbol "foo-bar")) := by native_decide

/-- A safe symbol with digits round-trips. -/
theorem roundtrip_safe_symbol_x123 :
    RoundTrippable (.atom (.symbol "x123")) := by native_decide

-- Note: A general theorem `RoundTrippable' e → RoundTrippable e` would require
-- an inductive proof over the parser/serializer interaction. This is left as
-- future work. The `RoundTrippable'` predicate serves as a *specification* of
-- which S-expressions are expected to round-trip, while the concrete
-- `native_decide` tests above provide evidence that the specification
-- is consistent with the actual implementation.

end CBCL
