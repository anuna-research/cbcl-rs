import LeanCbcl.LexicalNames
import LeanCbcl.InstalledSyntaxTests

namespace CBCL.InstalledSyntax.Raw.Tests
open FormalLanguage
open CBCL.InstalledSyntax.Tests

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

def codes (s : String) := ((lexer env).lex (encode s)).map (List.map Fin.val)
def atom (n : Nat) := some [n+2]

example : codes "9223372036854775807" = atom 0 := by decide
example : codes "-9223372036854775808" = atom 0 := by decide
example : codes "9223372036854775808" = none := by decide
example : codes "-9223372036854775809" = none := by decide
example : codes "00000000000000000000000000000000000000000001" = atom 0 := by decide
example : codes "1-2" = none := by decide
example : codes "1-" = none := by decide
example : codes "--3" = atom 5 := by decide
example : codes "-" = atom 5 := by decide
example : codes "-0" = atom 0 := by decide
example : codes "#t" = atom 0 := by decide
example : codes "#f)" = some [2, 1] := by decide
example : codes "#t\"x\"" = some [2, 3] := by decide
example : codes "#true" = none := by decide
example : codes "#tx" = none := by decide
example : codes "#t:" = none := by decide
example : codes "#" = none := by decide
example : codes ":" = none := by decide
example : codes ":thread" = atom 3 := by decide
example : codes ":sender" = atom 3 := by decide
example : codes ":caused-by" = atom 4 := by decide
example : codes ":threadx" = atom 2 := by decide
example : codes ":1" = atom 2 := by decide
example : codes "@" = atom 5 := by decide
example : codes "@alice" = atom 6 := by decide
example : codes "\"();#t\"" = atom 1 := by decide
example : codes "\"\\n\\r\\t\\\\\\\"\"" = atom 1 := by decide
example : codes "\"\\q\"" = none := by decide
example : codes "\"unterminated" = none := by decide
example : codes "\"trailing\\" = none := by decide
example : codes "\"λ😀\"" = atom 1 := by decide
example : codes "λ" = none := by decide
example : codes "[" = none := by decide
example : codes "; arbitrary λ ) #z\n#t; eof comment" = atom 0 := by decide
example : codes (String.ofList [' ', '\t', '\n', '\x0c', '\r']) = some [] := by decide

/-- Concrete text to concrete recursive syntax, not just lexer success. -/
def lexes (source : String) (e : SExpr) : Prop :=
  (lexer env).lex (encode source) = some (SyntaxTree.encode (classifyTree env e))
instance (s : String) (e : SExpr) : Decidable (lexes s e) := inferInstanceAs (Decidable (_ = _))

example : lexes " (tell);eof" (msg "tell") := by
  simp only [lexes, msg, SExpr.sym, classifyTree, SyntaxTree.encode, List.map_cons, List.map_nil]
  decide
example : lexes "(lang d (signed sig (ship parcel)))"
    (lang "d" (msg "signed" [.sym "sig", msg "ship" [.sym "parcel"]])) := by
  simp only [lexes, msg, lang, SExpr.sym, classifyTree, SyntaxTree.encode, List.map_cons, List.map_nil]
  decide
example : lexes "(lang e (stop))" (lang "e" (msg "stop")) := by
  simp only [lexes, msg, lang, SExpr.sym, classifyTree, SyntaxTree.encode, List.map_cons, List.map_nil]
  decide
example : lexes "(lang d (shipx))" (lang "d" (msg "shipx")) := by
  simp only [lexes, msg, lang, SExpr.sym, classifyTree, SyntaxTree.encode, List.map_cons, List.map_nil]
  decide
example : lexes "(tellx)" (msg "tellx") := by
  simp only [lexes, msg, SExpr.sym, classifyTree, SyntaxTree.encode, List.map_cons, List.map_nil]
  decide
example : lexes "(tell :caused-by (hash) :thread \"λ\")"
    (msg "tell" [kw "caused-by", .list [.sym "hash"], kw "thread", .atom (.str "λ")]) := by
  simp only [lexes, msg, kw, SExpr.sym, classifyTree, SyntaxTree.encode, List.map_cons, List.map_nil]
  decide

-- These execute the reference check proved equal to the finite raw DPDA.
example : check env "(tell)" = true := by decide
example : check env " ; before\n(lang d (signed sig (ship parcel))); after" = true := by decide
example : check env "(lang d (lang e (stop)))" = true := by decide
example : check env "(lang d (lang e (ship)))" = false := by decide
example : check env "(lang absent (tell))" = false := by decide
example : check env "(ship)" = false := by decide
example : check env "(lang d (shipx))" = false := by decide
example : check env "(tellx)" = false := by decide
example : check env "(tell :thread 1)" = false := by decide
example : check env "(tell :thread x)" = true := by decide
example : check env "(tell :caused-by ())" = false := by decide
example : check env "(tell :caused-by (hash))" = true := by decide
example : check env "(tell payload @)" = true := by decide
example : check env "(tell payload @alice)" = false := by decide
example : check env "(tell 9223372036854775807 -9223372036854775808)" = true := by decide
example : check env "(tell 9223372036854775808)" = false := by decide
example : check env "(tell #tx)" = false := by decide
example : check env "(tell #f)" = true := by decide
example : check env "(tell --3)" = true := by decide
example : check env "(tell 1-2)" = false := by decide
example : check env "(tell :x)" = false := by decide
example : check env "(tell :x :)" = false := by decide
example : check env "" = false := by decide
example : check env "; only comment" = false := by decide
example : check env "tell" = false := by decide
example : check env "()" = false := by decide
example : check env "(tell" = false := by decide
example : check env ")(tell)" = false := by decide
example : check env "(tell))" = false := by decide
example : check env "(tell)(tell)" = false := by decide
example : check env "(tell) trailing" = false := by decide

example : (Raw.environmentDCFL env).machine.accepts
    (encode "(lang d (signed sig (ship parcel)))") = true := by
  rw [← check_correct]
  decide

example : (Raw.environmentDCFL env).machine.accepts (encode "(tell)(tell)") = false := by
  rw [← check_correct]
  decide

end CBCL.InstalledSyntax.Raw.Tests
