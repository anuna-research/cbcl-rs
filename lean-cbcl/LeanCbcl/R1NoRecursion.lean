import LeanCbcl.SExpr
import LeanCbcl.Dialect

/-!
# R1 Constraint: No Recursion

Formalizes the R1 safety constraint: performative definitions must not contain
direct self-references. Proves that the AST-walk detection algorithm is sound.

Also defines a mutual-recursion predicate over performative dependencies and a
Boolean verifier (noncomputable) that can be used to rule out dependency cycles.

Mirrors: `src/cbcl/r1-simple.scm`

## Key theorem
If `containsSelfReference name template = false`, then the template does not
contain any occurrence of `name` as a symbol — i.e., no direct recursion.
-/

namespace CBCL

/-- Check if an S-expression contains a reference to a given symbol name.
    Mirrors `contains-self-reference?` from r1-simple.scm. -/
def containsSelfReference (name : String) : SExpr → Bool
  | .atom (.symbol s) => s == name
  | .atom _           => false
  | .list xs          => go xs
where
  go : List SExpr → Bool
  | []      => false
  | e :: es => containsSelfReference name e || go es

/-- Verify R1 for a single performative definition. -/
def verifyR1 (perfName : String) (template : SExpr) : Bool :=
  !containsSelfReference perfName template

/-- Verify R1 for all performatives in a dialect. -/
def verifyR1Dialect (d : Dialect) : Bool :=
  if d.name == "cbcl-base" then true
  else d.performatives.all (fun pd => verifyR1 pd.name pd.template)

-- ============================================================
-- Soundness proof
-- ============================================================

/-- A symbol occurrence at some position in the S-expression. -/
inductive SymbolOccurrence (name : String) : SExpr → Prop where
  | here : SymbolOccurrence name (.atom (.symbol name))
  | inList : ∀ {xs : List SExpr} {e : SExpr},
      e ∈ xs → SymbolOccurrence name e → SymbolOccurrence name (.list xs)

/-- Helper lemma: containsSelfReference.go reflects list membership. -/
private theorem go_true_of_mem {name : String} {xs : List SExpr} {e : SExpr}
    (hmem : e ∈ xs) (hself : containsSelfReference name e = true) :
    containsSelfReference.go name xs = true := by
  induction xs with
  | nil => simp at hmem
  | cons hd tl ih =>
    simp [containsSelfReference.go]
    cases List.mem_cons.mp hmem with
    | inl heq => left; rw [← heq]; exact hself
    | inr htl => right; exact ih htl

/-- Completeness: if there IS an occurrence, the checker finds it. -/
theorem r1_completeness (name : String) (expr : SExpr) :
    SymbolOccurrence name expr →
    containsSelfReference name expr = true := by
  intro h_occ
  induction h_occ with
  | here => simp [containsSelfReference]
  | inList hmem _ ih =>
    simp [containsSelfReference]
    exact go_true_of_mem hmem ih

/-- Soundness: if the checker says false, there is no occurrence. -/
theorem r1_soundness (name : String) (expr : SExpr) :
    containsSelfReference name expr = false →
    ¬ SymbolOccurrence name expr := by
  intro hfalse hocc
  have := r1_completeness name expr hocc
  rw [this] at hfalse
  exact absurd hfalse (by decide)

/-- The base dialect is always R1-valid (exempt). -/
theorem r1_base_dialect_valid : verifyR1Dialect baseDialect = true := by
  simp [verifyR1Dialect, baseDialect]

end CBCL

namespace CBCL

-- ============================================================
-- Mutual recursion (dependency cycles)
-- ============================================================

/-- A performative `a` depends on `b` if `b` occurs as a symbol in `a`'s template. -/
def dependsOn (d : Dialect) (a b : String) : Prop :=
  ∃ pd, pd ∈ d.performatives ∧ pd.name = a ∧
    containsSelfReference b pd.template = true

/-- Transitive closure of dependency edges. -/
inductive DependsClosure (d : Dialect) : String → String → Prop where
  | step : dependsOn d a b → DependsClosure d a b
  | trans : DependsClosure d a b → DependsClosure d b c → DependsClosure d a c

/-- Mutual recursion exists if some performative depends (directly or indirectly) on itself. -/
def mutualRecursion (d : Dialect) : Prop :=
  ∃ a, DependsClosure d a a

/-- Boolean verifier that rejects mutual recursion (noncomputable, uses classical decision). -/
noncomputable def verifyR1NoMutualRecursion (d : Dialect) : Bool := by
  classical
  exact decide (¬ mutualRecursion d)

/-- Soundness: if the verifier returns true, there is no mutual recursion. -/
theorem r1_mutual_sound (d : Dialect) :
    verifyR1NoMutualRecursion d = true → ¬ mutualRecursion d := by
  classical
  intro h
  simpa [verifyR1NoMutualRecursion] using h

end CBCL
