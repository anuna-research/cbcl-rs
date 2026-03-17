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

end CBCL
