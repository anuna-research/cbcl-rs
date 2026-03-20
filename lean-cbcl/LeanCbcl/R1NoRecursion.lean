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
-- Computable cycle detection (DFS on dependency graph)
-- ============================================================

/-- Get the names of performatives referenced in a template. -/
def referencedPerformatives (perfNames : List String) (template : SExpr) : List String :=
  perfNames.filter (fun name => containsSelfReference name template)

/-- Build adjacency list for the dependency graph. -/
def buildDepGraph (d : Dialect) : List (String × List String) :=
  let names := d.performativeNames
  d.performatives.map fun pd => (pd.name, referencedPerformatives names pd.template)

/-- DFS-based cycle detection with visited/visiting sets.
    Returns `true` if no cycle is reachable from `node`. -/
def dfsNoCycle (graph : List (String × List String)) (fuel : Nat)
    (visiting : List String) (visited : List String) (node : String) : Bool :=
  if fuel == 0 then false  -- conservative: out of fuel → report possible cycle
  else if visited.contains node then true  -- already fully explored
  else if visiting.contains node then false  -- back edge → cycle!
  else
    let visiting' := node :: visiting
    let neighbors := match graph.find? (fun p => p.1 == node) with
      | some (_, ns) => ns
      | none => []
    neighbors.all (fun n => dfsNoCycle graph (fuel - 1) visiting' visited n)
termination_by fuel
decreasing_by
  simp_all
  omega

/-- DFS-only cycle check (used internally by checkNoCycles). -/
def dfsCheckNoCycles (d : Dialect) : Bool :=
  let graph := buildDepGraph d
  let names := d.performativeNames
  let fuel := names.length * names.length + 1
  names.all (fun name => dfsNoCycle graph fuel [] [] name)

/-- A direct check: no performative references itself by name. -/
def checkNoDirectCycles (d : Dialect) : Bool :=
  d.performatives.all (fun pd => !containsSelfReference pd.name pd.template)

/-- checkNoDirectCycles is sound: if it returns true, no direct self-reference exists. -/
theorem checkNoDirectCycles_sound (d : Dialect) (h : checkNoDirectCycles d = true) :
    ∀ pd ∈ d.performatives, containsSelfReference pd.name pd.template = false := by
  intro pd hpd
  simp [checkNoDirectCycles] at h
  have := h pd hpd
  simpa using this

/-- Combined check: both direct self-reference and DFS cycle detection.
    The direct check handles the case where `List.find?` might not return
    the right entry for duplicate performative names; the DFS handles
    mutual recursion through the dependency graph. -/
def checkNoCycles (d : Dialect) : Bool :=
  let graph := buildDepGraph d
  let names := d.performativeNames
  let fuel := names.length * names.length + 1
  checkNoDirectCycles d &&
    names.all (fun name => dfsNoCycle graph fuel [] [] name)

/-- The base dialect has no cycles. -/
theorem checkNoCycles_base : checkNoCycles baseDialect = true := by native_decide

/-- The base dialect has no direct cycles. -/
theorem checkNoDirectCycles_base : checkNoDirectCycles baseDialect = true := by native_decide

/-- Soundness (direct self-reference): if `checkNoCycles` returns true,
    then no performative directly references itself by name. -/
theorem checkNoCycles_sound (d : Dialect) (h : checkNoCycles d = true) :
    ∀ pd ∈ d.performatives, containsSelfReference pd.name pd.template = false := by
  simp [checkNoCycles] at h
  exact checkNoDirectCycles_sound d h.1

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
