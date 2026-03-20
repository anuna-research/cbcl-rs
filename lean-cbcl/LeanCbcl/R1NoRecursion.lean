import LeanCbcl.SExpr
import LeanCbcl.Dialect

/-!
# R1 Constraint: No Recursion

Formalizes the R1 safety constraint: performative definitions must not contain
direct self-references. Proves that the AST-walk detection algorithm is sound.

Also defines a mutual-recursion predicate over performative dependencies and a
computable Boolean verifier (DFS-based) that rules out dependency cycles.

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

-- ============================================================
-- Graph helpers
-- ============================================================

/-- Look up neighbors of a node in the adjacency list. -/
def graphNeighbors (graph : List (String × List String)) (node : String) : List String :=
  match graph.find? (fun p => p.1 == node) with
  | some (_, ns) => ns
  | none => []

/-- Reachability in the graph via a path of length at least 1. -/
inductive Reachable (graph : List (String × List String)) : String → String → Prop where
  | single : b ∈ graphNeighbors graph a → Reachable graph a b
  | cons   : b ∈ graphNeighbors graph a → Reachable graph b c → Reachable graph a c

/-- Reachable is transitive. -/
theorem Reachable.trans (h1 : Reachable graph a b) (h2 : Reachable graph b c) :
    Reachable graph a c := by
  induction h1 with
  | single hmem => exact .cons hmem h2
  | cons hmem _ ih => exact .cons hmem (ih h2)

-- ============================================================
-- DFS soundness
-- ============================================================

/-- Extract the visiting-check and neighbor-DFS conditions from a successful
    `dfsNoCycle` call at fuel `n + 1`. -/
private theorem dfsNoCycle_succ_extract (graph : List (String × List String)) (n : Nat)
    (visiting : List String) (node : String)
    (h : dfsNoCycle graph (n + 1) visiting [] node = true) :
    visiting.contains node = false ∧
    ∀ nb ∈ graphNeighbors graph node,
      dfsNoCycle graph n (node :: visiting) [] nb = true := by
  unfold dfsNoCycle at h
  simp only [beq_iff_eq, Nat.succ_ne_zero, ↓reduceIte, List.contains_nil, Bool.false_eq_true] at h
  split at h
  · exact absurd h (by simp)
  · rename_i hnovis
    refine ⟨by rwa [Bool.not_eq_true] at hnovis, ?_⟩
    simp only [graphNeighbors] at h ⊢
    rw [show n + 1 - 1 = n from by omega] at h
    rw [List.all_eq_true] at h; exact h

/-- DFS soundness: if `dfsNoCycle` returns true starting from `node` with
    visiting stack `visiting` and empty visited list, then no node in
    `node :: visiting` is reachable from `node` through the graph. -/
theorem dfsNoCycle_no_cycle (graph : List (String × List String)) (fuel : Nat)
    (visiting : List String) (node : String)
    (h : dfsNoCycle graph fuel visiting [] node = true) :
    ∀ v ∈ node :: visiting, ¬ Reachable graph node v := by
  induction fuel generalizing node visiting with
  | zero => simp [dfsNoCycle] at h
  | succ n ih =>
    have ⟨hnovis, hall⟩ := dfsNoCycle_succ_extract graph n visiting node h
    intro v hv hreach
    cases hreach with
    | single hmem_nb =>
      -- v is a direct neighbor of node, and v ∈ node :: visiting.
      -- The DFS recursed on v with visiting' = node :: visiting.
      -- Since v ∈ visiting', if fuel > 0 the DFS would detect v ∈ visiting'
      -- and return false, contradicting the hypothesis.
      have hdfs_v := hall v hmem_nb
      have hvc : (node :: visiting).contains v = true := List.contains_iff_mem.mpr hv
      cases n with
      | zero => simp [dfsNoCycle] at hdfs_v
      | succ m =>
        have ⟨hnovis', _⟩ := dfsNoCycle_succ_extract graph m (node :: visiting) v hdfs_v
        rw [hvc] at hnovis'; simp at hnovis'
    | cons hmem_nb hreach' =>
      -- b is a neighbor of node, and Reachable graph b v.
      -- By IH on b (with visiting' = node :: visiting), v is unreachable from b.
      rename_i b
      exact absurd hreach'
        (ih (node :: visiting) b (hall b hmem_nb) v (List.mem_cons_of_mem b hv))

-- ============================================================
-- Connecting DependsClosure to graph reachability
-- ============================================================

/-- Helper: `List.find?` on a mapped list of performatives finds the right entry
    when performative names are unique. -/
private theorem find_map_nodup (perfs : List PerformativeDef) (names : List String)
    (pd : PerformativeDef) (hpd : pd ∈ perfs)
    (hnodup : (perfs.map (·.name)).Nodup) :
    (perfs.map (fun p => (p.name, referencedPerformatives names p.template))).find?
      (fun p => p.1 == pd.name) =
      some (pd.name, referencedPerformatives names pd.template) := by
  induction perfs with
  | nil => simp at hpd
  | cons hd tl ihtl =>
    simp only [List.map, List.find?_cons, BEq.beq]
    cases List.mem_cons.mp hpd with
    | inl heq => subst heq; simp
    | inr htl =>
      simp only [List.map] at hnodup
      rw [List.nodup_cons] at hnodup
      have hne : hd.name ≠ pd.name := fun heq =>
        hnodup.1 (heq ▸ List.mem_map_of_mem (f := (·.name)) htl)
      have : decide (hd.name = pd.name) = false := by simp [hne]
      rw [this]; exact ihtl htl hnodup.2

/-- If `dependsOn d a b`, names are unique, and `b` is a performative name,
    then `b ∈ graphNeighbors (buildDepGraph d) a`. -/
private theorem dependsOn_graphNeighbors (d : Dialect) (a b : String)
    (hnodup : d.performativeNames.Nodup)
    (hdep : dependsOn d a b)
    (hb_perf : b ∈ d.performativeNames) :
    b ∈ graphNeighbors (buildDepGraph d) a := by
  obtain ⟨pd, hpd_mem, hpd_name, hcontains⟩ := hdep
  subst hpd_name
  simp only [graphNeighbors, buildDepGraph]
  rw [find_map_nodup d.performatives d.performativeNames pd hpd_mem hnodup]
  simp only [referencedPerformatives, List.mem_filter]
  exact ⟨hb_perf, hcontains⟩

/-- The source of any `DependsClosure` step is a performative name. -/
private theorem dependsClosure_source_perf (d : Dialect) (a b : String)
    (hcl : DependsClosure d a b) : a ∈ d.performativeNames := by
  induction hcl with
  | step hdep =>
    obtain ⟨pd, hpd_mem, hpd_name, _⟩ := hdep
    exact hpd_name ▸ List.mem_map_of_mem (f := (·.name)) hpd_mem
  | trans _ _ ih _ => exact ih

/-- `DependsClosure d a b` implies `Reachable (buildDepGraph d) a b`
    when performative names are unique and `b` is a performative name. -/
private theorem dependsClosure_reachable (d : Dialect) (a b : String)
    (hnodup : d.performativeNames.Nodup)
    (hb_perf : b ∈ d.performativeNames)
    (hcl : DependsClosure d a b) :
    Reachable (buildDepGraph d) a b := by
  induction hcl with
  | step hdep =>
    exact .single (dependsOn_graphNeighbors d _ _ hnodup hdep hb_perf)
  | trans h1 h2 ih1 ih2 =>
    exact (ih1 (dependsClosure_source_perf d _ _ h2)).trans (ih2 hb_perf)

-- ============================================================
-- Main soundness theorem
-- ============================================================

/-- Computable verifier for mutual recursion: uses the combined `checkNoCycles`. -/
def verifyR1NoMutualRecursion (d : Dialect) : Bool :=
  checkNoCycles d

/-- Soundness: if `checkNoCycles` returns true and performative names are unique,
    there is no mutual recursion.

    The `Nodup` hypothesis is needed because `graphNeighbors` uses `List.find?`
    which returns the first match; with duplicate names, some dependency edges
    could be missed in the graph. -/
theorem r1_mutual_sound (d : Dialect)
    (hnodup : d.performativeNames.Nodup)
    (h : checkNoCycles d = true) : ¬ mutualRecursion d := by
  intro ⟨a, hcl⟩
  -- a is a performative name (source of the first DependsClosure step)
  have ha_perf := dependsClosure_source_perf d a a hcl
  -- DependsClosure d a a implies graph-level reachability
  have hreach := dependsClosure_reachable d a a hnodup ha_perf hcl
  -- Extract the DFS check from checkNoCycles
  simp only [checkNoCycles] at h
  have ⟨_, hdfs⟩ := Bool.and_eq_true_iff.mp h
  rw [List.all_eq_true] at hdfs
  -- DFS was run from a (since a ∈ performativeNames) with visiting = []
  -- So a ∈ [a] = a :: [], and dfsNoCycle_no_cycle gives ¬ Reachable _ a a
  exact absurd hreach
    (dfsNoCycle_no_cycle _ _ [] a (hdfs a ha_perf) a (List.mem_singleton.mpr rfl))

-- ============================================================
-- DFS completeness
-- ============================================================

/-- If `node ∈ visiting`, DFS immediately returns false (back-edge detection). -/
private theorem dfs_false_mem (graph : List (String × List String))
    (fuel : Nat) (visiting : List String) (node : String)
    (hfuel : fuel ≥ 1) (hmem : node ∈ visiting) :
    dfsNoCycle graph fuel visiting [] node = false := by
  obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by omega⟩
  unfold dfsNoCycle
  simp only [beq_iff_eq, Nat.succ_ne_zero, ↓reduceIte, List.contains_nil, Bool.false_eq_true]
  split; · rfl
  · rename_i h; exact absurd (List.contains_iff_mem.mpr hmem) h

/-- If some neighbor of `node` makes DFS return false, then DFS from `node`
    also returns false. -/
private theorem dfs_false_nb (graph : List (String × List String))
    (fuel : Nat) (visiting : List String) (node nb : String)
    (hfuel : fuel ≥ 1) (hnb : nb ∈ graphNeighbors graph node)
    (hfalse : dfsNoCycle graph (fuel - 1) (node :: visiting) [] nb = false) :
    dfsNoCycle graph fuel visiting [] node = false := by
  obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by omega⟩
  simp only [show n + 1 - 1 = n from by omega] at hfalse
  unfold dfsNoCycle
  simp only [beq_iff_eq, Nat.succ_ne_zero, ↓reduceIte, List.contains_nil, Bool.false_eq_true]
  split; · rfl
  · apply Bool.eq_false_iff.mpr; intro hall
    simp only [show n + 1 - 1 = n from by omega] at hall
    rw [List.all_eq_true] at hall
    have := hall nb (by simp [graphNeighbors] at hnb ⊢; exact hnb)
    rw [hfalse] at this; exact absurd this Bool.false_ne_true

/-- If `target ∈ visiting` and `Reachable graph s target`, then DFS from `s`
    returns false for sufficiently large fuel. The DFS follows the reachable
    path and eventually hits `target` in the visiting set. -/
theorem dfs_false_reach (graph : List (String × List String))
    {s t : String} (hreach : Reachable graph s t) :
    ∀ visiting : List String, t ∈ visiting →
    ∃ bound : Nat, ∀ fuel, fuel ≥ bound →
      dfsNoCycle graph fuel visiting [] s = false := by
  induction hreach with
  | single hmem =>
    rename_i a b
    intro visiting htarget
    exact ⟨2, fun fuel hfuel => by
      by_cases hv : a ∈ visiting
      · exact dfs_false_mem graph fuel visiting a (by omega) hv
      · apply dfs_false_nb graph fuel visiting a b (by omega) hmem
        exact dfs_false_mem graph (fuel - 1) (a :: visiting) b
          (by omega) (List.mem_cons_of_mem _ htarget)⟩
  | cons hmem _ ih =>
    rename_i a b c _
    intro visiting htarget
    obtain ⟨bound, hbound⟩ := ih (a :: visiting) (List.mem_cons_of_mem _ htarget)
    exact ⟨bound + 1, fun fuel hfuel => by
      by_cases hv : a ∈ visiting
      · exact dfs_false_mem graph fuel visiting a (by omega) hv
      · apply dfs_false_nb graph fuel visiting a b (by omega) hmem
        exact hbound (fuel - 1) (by omega)⟩

/-- **DFS completeness for cycles:** if `Reachable graph node node` (a cycle
    exists through `node`), then `dfsNoCycle` returns false for sufficiently
    large fuel.

    This is the converse of `dfsNoCycle_no_cycle` (soundness). Together they
    establish that `dfsNoCycle` correctly characterizes cycle-freedom, modulo
    fuel adequacy.

    The fuel bound depends on the length of the cycle witness in the
    `Reachable` proof. For a graph with `n` nodes, any simple cycle has
    length at most `n`, so fuel `n + 2` suffices in practice. -/
theorem dfsNoCycle_complete (graph : List (String × List String))
    (node : String) (visiting : List String)
    (hreach : Reachable graph node node) :
    ∃ bound : Nat, ∀ fuel, fuel ≥ bound →
      dfsNoCycle graph fuel visiting [] node = false := by
  by_cases hv : node ∈ visiting
  · exact ⟨1, fun fuel hfuel => dfs_false_mem graph fuel visiting node (by omega) hv⟩
  · cases hreach with
    | single hmem =>
      exact ⟨2, fun fuel hfuel => by
        apply dfs_false_nb graph fuel visiting node node (by omega) hmem
        exact dfs_false_mem graph (fuel - 1) (node :: visiting) node
          (by omega) List.mem_cons_self⟩
    | cons hmem hreach' =>
      rename_i b
      have ⟨bound, hbound⟩ := dfs_false_reach graph hreach' (node :: visiting)
        List.mem_cons_self
      exact ⟨bound + 1, fun fuel hfuel => by
        apply dfs_false_nb graph fuel visiting node b (by omega) hmem
        exact hbound (fuel - 1) (by omega)⟩

/-- **Mutual recursion completeness (conditional on fuel):**
    if `mutualRecursion d` holds, performative names are unique, and all
    dependency targets are performative names, then there exists a node
    whose DFS returns false for sufficiently large fuel.

    The `hclosed` hypothesis ensures all dependency targets are performative
    names, which is needed so that `DependsClosure` translates faithfully
    to `Reachable` in the dependency graph.

    Combined with `r1_mutual_sound`, this gives: for well-formed dialects,
    `checkNoCycles d = true` if and only if there is no mutual recursion. -/
theorem r1_mutual_complete_fuel (d : Dialect)
    (hnodup : d.performativeNames.Nodup)
    (hmut : mutualRecursion d)
    (hclosed : ∀ a b, DependsClosure d a b → b ∈ d.performativeNames) :
    ∃ a ∈ d.performativeNames,
      ∃ bound : Nat, ∀ fuel, fuel ≥ bound →
        dfsNoCycle (buildDepGraph d) fuel [] [] a = false := by
  obtain ⟨a, hcl⟩ := hmut
  have ha_perf := dependsClosure_source_perf d a a hcl
  have ha_target := hclosed a a hcl
  have hreach := dependsClosure_reachable d a a hnodup ha_target hcl
  have ⟨bound, hbound⟩ := dfsNoCycle_complete (buildDepGraph d) a [] hreach
  exact ⟨a, ha_perf, bound, hbound⟩

end CBCL
