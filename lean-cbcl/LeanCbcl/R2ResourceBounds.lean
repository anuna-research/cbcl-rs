import LeanCbcl.SExpr
import LeanCbcl.Dialect

/-!
# R2 Constraint: Resource Bounds

Formalizes the R2 safety constraint: dialects must declare resource bounds within
system limits, and evaluation must terminate within those bounds.

Mirrors: `src/cbcl/r2-resource-bounds.scm`

## Key theorem
Evaluation with resource limits always terminates: we model evaluation steps
using a fuel parameter that strictly decreases, establishing termination.
-/

namespace CBCL

/-- Runtime resource tracking state. Mirrors `<resource-context>`. -/
structure ResourceState where
  currentDepth  : Nat
  expansionSize : Nat
  maxDepth      : Nat
  maxExpSize    : Nat
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A resource state is within bounds. -/
def ResourceState.withinBounds (rs : ResourceState) : Prop :=
  rs.currentDepth < rs.maxDepth ∧ rs.expansionSize < rs.maxExpSize

/-- Remaining fuel: how many more depth steps we can take. -/
def ResourceState.remainingDepth (rs : ResourceState) : Nat :=
  rs.maxDepth - rs.currentDepth

/-- Enter a new depth level. Returns `none` if limit exceeded. -/
def ResourceState.enterDepth (rs : ResourceState) : Option ResourceState :=
  if rs.currentDepth + 1 < rs.maxDepth then
    some { rs with currentDepth := rs.currentDepth + 1 }
  else
    none

/-- Record expansion. Returns `none` if limit exceeded. -/
def ResourceState.addExpansion (rs : ResourceState) (size : Nat) : Option ResourceState :=
  if rs.expansionSize + size < rs.maxExpSize then
    some { rs with expansionSize := rs.expansionSize + size }
  else
    none

/-- Exit a depth level. -/
def ResourceState.exitDepth (rs : ResourceState) : ResourceState :=
  { rs with currentDepth := rs.currentDepth - 1 }

/-- Create initial resource state from bounds. -/
def ResourceState.initial (bounds : ResourceBounds) : ResourceState :=
  { currentDepth := 0, expansionSize := 0,
    maxDepth := bounds.maxDepth, maxExpSize := bounds.maxExpansionSize }

/-- Verify R2 static constraints on a dialect's declared bounds. -/
def verifyR2 (d : Dialect) : Bool :=
  let rb := d.resources
  0 < rb.maxDepth && rb.maxDepth ≤ maxAllowedDepth &&
  0 < rb.maxExpansionSize && rb.maxExpansionSize ≤ maxAllowedExpansionSize &&
  0 < rb.verificationTime && rb.verificationTime ≤ maxAllowedVerificationTime

-- ============================================================
-- Termination proof for bounded evaluation
-- ============================================================

/-- A fuel-based evaluation model. Each step consumes fuel.
    When fuel reaches 0, evaluation halts. -/
def boundedEval (fuel : Nat) (expr : SExpr) (rs : ResourceState) :
    Option (SExpr × ResourceState) :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    match expr with
    | .atom _ => some (expr, rs)
    | .list [] => some (expr, rs)
    | .list (hd :: tl) =>
      match rs.enterDepth with
      | none => none
      | some rs' =>
        match rs'.addExpansion expr.byteSize with
        | none => none
        | some rs'' =>
          match boundedEval fuel' hd rs'' with
          | none => none
          | some (_, rs''') => some (.list (hd :: tl), rs'''.exitDepth)

/-- Bounded evaluation always terminates (trivially, by fuel). -/
theorem boundedEval_terminates (fuel : Nat) (expr : SExpr) (rs : ResourceState) :
    ∃ result, boundedEval fuel expr rs = result :=
  ⟨_, rfl⟩

/-- Entering depth strictly decreases remaining depth. -/
theorem enterDepth_decreases (rs rs' : ResourceState)
    (h : rs.enterDepth = some rs') :
    rs'.remainingDepth < rs.remainingDepth := by
  simp [ResourceState.enterDepth] at h
  obtain ⟨hlt, hrfl⟩ := h
  subst hrfl
  simp [ResourceState.remainingDepth]
  omega

/-- With 0 fuel, evaluation always returns none. -/
theorem boundedEval_zero (expr : SExpr) (rs : ResourceState) :
    boundedEval 0 expr rs = none := rfl

/-- Atoms always evaluate successfully (given fuel > 0). -/
theorem boundedEval_atom (fuel : Nat) (a : Atom) (rs : ResourceState) :
    boundedEval (fuel + 1) (.atom a) rs = some (.atom a, rs) := rfl

/-- The base dialect passes R2 verification. -/
theorem r2_base_dialect_valid : verifyR2 baseDialect = true := by native_decide

/-- If R2 verification passes, the bounds are within system limits. -/
theorem r2_verification_implies_valid (d : Dialect) (h : verifyR2 d = true) :
    d.resources.isValid := by
  simp only [verifyR2, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

end CBCL
