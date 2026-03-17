/-!
# S-Expressions for CBCL

Models RFC 9804 canonical S-expressions as an inductive type.
This is the foundational data structure — all CBCL messages are S-expressions.

Mirrors: `src/cbcl/csexp.scm`
-/

namespace CBCL

/-- Atoms are the leaf values of S-expressions.
    In the Scheme implementation these are symbols, strings, numbers, booleans, keywords. -/
inductive Atom where
  | symbol : String → Atom
  | str    : String → Atom
  | num    : Int → Atom
  | bool   : Bool → Atom
  | keyword : String → Atom
  deriving Repr, BEq, DecidableEq, Inhabited

/-- S-expressions: either an atom or a list of S-expressions.
    This corresponds to the DCFL (Deterministic Context-Free Language) grammar. -/
inductive SExpr where
  | atom : Atom → SExpr
  | list : List SExpr → SExpr
  deriving Repr, BEq, Inhabited

end CBCL

mutual
def decEqSExpr : (a b : CBCL.SExpr) → Decidable (a = b)
  | .atom a, .atom b =>
    if h : a = b then isTrue (congrArg CBCL.SExpr.atom h)
    else isFalse (fun heq => h (CBCL.SExpr.atom.inj heq))
  | .list as_, .list bs =>
    match decEqSExprList as_ bs with
    | isTrue h  => isTrue (congrArg CBCL.SExpr.list h)
    | isFalse h => isFalse (fun heq => h (CBCL.SExpr.list.inj heq))
  | .atom _, .list _ => isFalse CBCL.SExpr.noConfusion
  | .list _, .atom _ => isFalse CBCL.SExpr.noConfusion

def decEqSExprList : (as_ bs : List CBCL.SExpr) → Decidable (as_ = bs)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (fun h => nomatch h)
  | _ :: _, [] => isFalse (fun h => nomatch h)
  | a :: as_, b :: bs =>
    match decEqSExpr a b, decEqSExprList as_ bs with
    | isTrue h1, isTrue h2  => isTrue (by rw [h1, h2])
    | isFalse h1, _         => isFalse (fun heq => h1 (List.cons.inj heq).1)
    | _, isFalse h2         => isFalse (fun heq => h2 (List.cons.inj heq).2)
end

instance : DecidableEq CBCL.SExpr := decEqSExpr

namespace CBCL

/-- Size of an S-expression (number of constructors).
    Used as a termination measure for recursive functions. -/
def SExpr.size : SExpr → Nat
  | .atom _ => 1
  | .list xs => 1 + xs.foldl (fun acc e => acc + e.size) 0

/-- Byte-level size estimate for resource bound checking.
    Mirrors the expansion-size tracking in r2-resource-bounds.scm. -/
def SExpr.byteSize : SExpr → Nat
  | .atom (.symbol s) => s.length
  | .atom (.str s) => s.length + 2  -- quotes
  | .atom (.num n) => toString n |>.length
  | .atom (.bool _) => 2
  | .atom (.keyword s) => s.length + 1  -- colon prefix
  | .list xs => 2 + xs.foldl (fun acc e => acc + e.byteSize + 1) 0  -- parens + spaces

/-- Depth of an S-expression tree.
    Used for R2 max-depth enforcement. -/
def SExpr.depth : SExpr → Nat
  | .atom _ => 0
  | .list [] => 1
  | .list xs => 1 + xs.foldl (fun acc e => max acc e.depth) 0

-- Convenience constructors
def SExpr.sym (s : String) : SExpr := .atom (.symbol s)
def SExpr.int (n : Int) : SExpr := .atom (.num n)

/-- Check if an S-expression is a specific symbol -/
def SExpr.isSymbol (s : String) : SExpr → Bool
  | .atom (.symbol s') => s == s'
  | _ => false

/-- Size is always positive -/
theorem SExpr.size_pos : ∀ (e : SExpr), 0 < e.size := by
  intro e
  cases e with
  | atom a => simp [SExpr.size]
  | list xs => simp [SExpr.size]; omega

/-- Depth of an atom is zero -/
theorem SExpr.depth_atom : ∀ (a : Atom), (SExpr.atom a).depth = 0 := by
  intro a; simp [SExpr.depth]

end CBCL
