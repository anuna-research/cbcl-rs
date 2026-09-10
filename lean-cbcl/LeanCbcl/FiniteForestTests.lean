import LeanCbcl.FiniteForest

/-! SPEC-018 TEST-1800 / compiler portion of TEST-1801.
These exercise the generic compiler, not installed CBCL message admission. -/
namespace CBCL.FormalLanguage.ForestTests

/-- Only a single list at the root is accepted. Its children are arbitrary. -/
def oneList : ForestAlgebra 1 3 where
  empty := 0
  atom _ _ := 2
  list s _ := if s == 0 then 1 else 2
  accept s := s == 1

private def openToken : Fin 3 := 0
private def closeToken : Fin 3 := 1
private def atomToken : Fin 3 := 2

example : oneList.machine.accepts [] = false := by decide
example : oneList.machine.accepts [atomToken] = false := by decide
example : oneList.machine.accepts [openToken, closeToken] = true := by decide
example : oneList.machine.accepts [openToken, atomToken, closeToken] = true := by decide
example : oneList.machine.accepts [closeToken] = false := by decide
example : oneList.machine.accepts [openToken, openToken, closeToken] = false := by decide
example : oneList.machine.accepts [openToken, closeToken, closeToken] = false := by decide
example : oneList.machine.accepts [openToken, closeToken, openToken, closeToken] = false := by decide

/-- Every list tree is accepted, without any bound on children or nesting. -/
theorem arbitrary_list (xs : List (SyntaxTree 1)) :
    oneList.machine.accepts (SyntaxTree.encode (.node xs)) = true := by
  have h := oneList.accepts_encoding [.node xs]
  simpa [ForestAlgebra.foldForest, ForestAlgebra.foldTree, oneList] using h

/-- Finite recogniser witness for the recursive test algebra. -/
def certificate : IsRealtimeDCFL oneList.language := oneList.isRealtimeDCFL

end CBCL.FormalLanguage.ForestTests
