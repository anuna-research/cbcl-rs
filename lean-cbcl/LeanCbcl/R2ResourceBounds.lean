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

/-- Entering depth strictly decreases remaining depth. -/
theorem enterDepth_decreases (rs rs' : ResourceState)
    (h : rs.enterDepth = some rs') :
    rs'.remainingDepth < rs.remainingDepth := by
  simp [ResourceState.enterDepth] at h
  obtain ⟨hlt, hrfl⟩ := h
  subst hrfl
  simp [ResourceState.remainingDepth]
  omega

-- ============================================================
-- Bounded evaluation (processes all children)
-- ============================================================

/-- A fuel-based evaluation model that recursively processes all children
    of a list node, threading the resource state through each child. -/
def boundedEvalFull (fuel : Nat) (expr : SExpr) (rs : ResourceState) :
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
          match evalChildren fuel' (hd :: tl) rs'' with
          | none => none
          | some (children, rs''') => some (.list children, rs'''.exitDepth)
where
  evalChildren (fuel : Nat) (children : List SExpr) (rs : ResourceState) :
      Option (List SExpr × ResourceState) :=
    match children with
    | [] => some ([], rs)
    | child :: rest =>
      match boundedEvalFull fuel child rs with
      | none => none
      | some (child', rs') =>
        match evalChildren fuel rest rs' with
        | none => none
        | some (rest', rs'') => some (child' :: rest', rs'')

/-- With 0 fuel, full evaluation always returns none. -/
theorem boundedEvalFull_zero (expr : SExpr) (rs : ResourceState) :
    boundedEvalFull 0 expr rs = none := by
  simp [boundedEvalFull]

/-- Atoms always evaluate successfully under full evaluation (given fuel > 0). -/
theorem boundedEvalFull_atom (fuel : Nat) (a : Atom) (rs : ResourceState) :
    boundedEvalFull (fuel + 1) (.atom a) rs = some (.atom a, rs) := by
  simp [boundedEvalFull]

/-- Helper: evalChildren preserves the depth invariant. If each recursive
    call to `boundedEvalFull` satisfies `rs'.currentDepth ≤ rs.currentDepth`,
    then so does `evalChildren`. -/
private theorem evalChildren_depth_bounded
    (ih : ∀ (expr : SExpr) (rs rs' : ResourceState) (e : SExpr),
      boundedEvalFull fuel expr rs = some (e, rs') →
      rs'.currentDepth ≤ rs.currentDepth)
    (children : List SExpr) (rs rs' : ResourceState) (cs : List SExpr)
    (h : boundedEvalFull.evalChildren fuel children rs = some (cs, rs')) :
    rs'.currentDepth ≤ rs.currentDepth := by
  induction children generalizing rs rs' cs with
  | nil =>
    simp [boundedEvalFull.evalChildren] at h
    obtain ⟨_, h2⟩ := h
    subst h2; omega
  | cons child rest ihc =>
    simp only [boundedEvalFull.evalChildren] at h
    revert h
    match heval : boundedEvalFull fuel child rs with
    | none => intro h; simp at h
    | some (child', rs_mid) =>
      simp only []
      match hrest : boundedEvalFull.evalChildren fuel rest rs_mid with
      | none => intro h; simp at h
      | some (rest', rs_final) =>
        simp only []
        intro h
        simp at h
        obtain ⟨_, h2⟩ := h
        subst h2
        have h1 := ih child rs rs_mid child' heval
        have h2 := ihc rs_mid rs_final rest' hrest
        omega

/-- If `boundedEvalFull` returns `some (_, rs')`, then
    `rs'.currentDepth ≤ rs.currentDepth`. Depth returns to the original
    level (or lower) after `exitDepth`. -/
theorem boundedEvalFull_depth_bounded :
    ∀ (fuel : Nat) (expr : SExpr) (rs rs' : ResourceState) (e : SExpr),
      boundedEvalFull fuel expr rs = some (e, rs') →
      rs'.currentDepth ≤ rs.currentDepth := by
  intro fuel
  induction fuel with
  | zero =>
    intro expr rs rs' e h
    simp [boundedEvalFull] at h
  | succ n ih =>
    intro expr rs rs' e h
    match expr with
    | .atom _ =>
      simp [boundedEvalFull] at h
      obtain ⟨_, h2⟩ := h
      subst h2; omega
    | .list [] =>
      simp [boundedEvalFull] at h
      obtain ⟨_, h2⟩ := h
      subst h2; omega
    | .list (hd :: tl) =>
      simp only [boundedEvalFull] at h
      revert h
      match hd1 : rs.enterDepth with
      | none => intro h; simp at h
      | some rs1 =>
        simp only []
        match hd2 : rs1.addExpansion (SExpr.list (hd :: tl)).byteSize with
        | none => intro h; simp at h
        | some rs2 =>
          simp only []
          match hd3 : boundedEvalFull.evalChildren n (hd :: tl) rs2 with
          | none => intro h; simp at h
          | some (children, rs3) =>
            simp only []
            intro h
            simp at h
            obtain ⟨_, h2⟩ := h
            rw [← h2]
            simp [ResourceState.exitDepth]
            have hchildren := evalChildren_depth_bounded ih (hd :: tl) rs2 rs3 children hd3
            -- rs1.currentDepth = rs.currentDepth + 1 (from enterDepth)
            simp [ResourceState.enterDepth] at hd1
            obtain ⟨_, hrfl⟩ := hd1
            -- rs2.currentDepth = rs1.currentDepth (addExpansion preserves currentDepth)
            simp [ResourceState.addExpansion] at hd2
            obtain ⟨_, hrfl2⟩ := hd2
            -- Now substitute to get rs2.currentDepth = rs.currentDepth + 1
            subst hrfl; subst hrfl2
            simp at hchildren
            omega

/-- The base dialect passes R2 verification. -/
theorem r2_base_dialect_valid : verifyR2 baseDialect = true := by native_decide

/-- If R2 verification passes, the bounds are within system limits. -/
theorem r2_verification_implies_valid (d : Dialect) (h : verifyR2 d = true) :
    d.resources.isValid := by
  simp only [verifyR2, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

end CBCL
