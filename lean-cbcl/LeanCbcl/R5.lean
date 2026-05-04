import LeanCbcl.R1NoRecursion

/-!
# R5 Sub-check Soundness — Acyclicity + Reachability + Definedness + Uniqueness (REQ-515 / CON-515 / TEST-515)

Lean port of four SPEC-002 R5 sub-checks:

* **REQ-204 (acyclicity).** Mirrors Rust
  `crates/cbcl-core/src/protocol.rs::CausalProtocol::check_acyclicity`,
  a 3-colour DFS over the successor graph emitting one
  `ProtocolViolation::Cycle` per back-edge.

* **REQ-205 (reachability).** Mirrors Rust
  `crates/cbcl-core/src/protocol.rs::CausalProtocol::check_reachability`,
  a BFS from `begin` over the successor graph emitting one
  `ProtocolViolation::Unreachable` per step not visited.

* **REQ-206 (performative definedness).** Mirrors Rust
  `crates/cbcl-core/src/protocol.rs::CausalProtocol::check_performative_definedness`,
  a set-membership pass that emits one
  `ProtocolViolation::UndefinedPerformative` per referenced
  performative absent from the dialect's installed-ancestor closure.

* **REQ-207 (step uniqueness, post-fix).** Mirrors Rust
  `crates/cbcl-core/src/protocol.rs::CausalProtocol::check_step_uniqueness`,
  a per-step pass that emits one `ProtocolViolation::DuplicateStep`
  per `StepDecl` whose predecessor or successor list contains
  repeats.

Acyclicity and reachability reuse the SPEC-001 graph layer
(`graphNeighbors`, `Reachable`) and the underlying DFS algorithm
(`dfsNoCycle`) from `LeanCbcl/R1NoRecursion.lean`. Reachability adds a
new forward-DFS helper (`dfsReaches`) since the Rust BFS visits
*forward* (from `begin` outward) whereas R1's DFS searches *for
cycles*. A forward DFS is equivalent to BFS for soundness — both
visit exactly the reachable set — and yields a smaller proof against
the existing `Reachable` inductive. Definedness and uniqueness are
both pure list-membership / `List.Nodup` checks and reduce to
`List.filterMap_eq_nil_iff`.

## Theorems

* `checkAcyclicity_sound` / `checkReachability_sound` — soundness
  (`check returns [] → property holds`). This is REQ-515's mandatory
  direction for both graph sub-checks.

* `check_acyclicity_iff_no_cycle` / `check_reachability_iff_all_reachable`
  — the headline iff theorems named in CON-515. Both directions are
  proven: soundness (`check = [] → property`) by DFS soundness from
  `R1NoRecursion.lean`; completeness (`property → check = []`) by a
  König-style argument that bounds DFS recursion depth by the number
  of graph keys in cycle-free / explicit-path graphs.

* `check_performative_definedness_iff_all_defined` /
  `check_step_uniqueness_iff_no_duplicates` — full iff (no fuel, no
  graph traversal), each follows directly from
  `List.filterMap_eq_nil_iff`.
-/

namespace CBCL

/-! ## Surface model — `StepDecl` / `ProtocolGraph` / `ProtocolViolation`. -/


/-- A step in the causal protocol graph (mirrors Rust `StepDecl` in
    `crates/cbcl-core/src/protocol.rs`).

    The Rust `predecessors`/`successors` are `Vec<NodeRef>` where
    `NodeRef ∈ { Single | Any | All }`; for the acyclicity proof only the
    underlying performative-name reference set matters, so the Lean
    surface model collapses both to `List String`. -/
structure StepDecl where
  performative : String
  predecessors : List String
  successors   : List String
  deriving Repr

/-- Parsed causal protocol declaration (mirrors Rust `CausalProtocol`).
    The Rust `BTreeMap<String, StepDecl>` is rendered here as a plain
    `List StepDecl`; uniqueness of step names is supplied as a separate
    `Nodup` hypothesis on the soundness theorem (matching the R1 pattern
    in `R1NoRecursion.lean`).

    Named `ProtocolGraph` rather than `CausalProtocol` to avoid clash
    with `LeanCbcl/Verify.lean`'s `CausalProtocol` (which models the
    *predecessor pattern* of a single message — Rust `NodeRef`). The
    R5 dependency-graph type and the verifier's pattern type are
    separate concepts despite both Rust files reusing the
    `CausalProtocol` name. -/
structure ProtocolGraph where
  steps : List StepDecl
  deriving Repr

/-- Protocol-level violation found during R5 verification (mirrors Rust
    `ProtocolViolation`). The `cycle`, `unreachable`,
    `undefinedPerformative`, and `duplicateStep` constructors are used
    by the REQ-204, REQ-205, REQ-206, and REQ-207 proofs respectively. -/
inductive ProtocolViolation where
  | cycle (participants : List String) : ProtocolViolation
  | unreachable (step : String)        : ProtocolViolation
  | undefinedPerformative (name : String) : ProtocolViolation
  | duplicateStep (name : String)      : ProtocolViolation
  deriving Repr

/-! ## Successor graph + acyclicity check. -/

/-- Successor adjacency list (mirrors Rust `successor_graph`). Note that
    Rust's helper additionally inserts referenced-but-undeclared
    performatives as zero-out-degree keys; the Lean check is sound
    without that step (a node that is only referenced as a successor of
    another step but has no declaration of its own cannot be the source
    of a cycle witness — see `reachable_source_in_stepNames`). -/
def ProtocolGraph.successorGraph (p : ProtocolGraph) : List (String × List String) :=
  p.steps.map (fun s => (s.performative, s.successors))

/-- Performative names declared by a protocol. -/
def ProtocolGraph.stepNames (p : ProtocolGraph) : List String :=
  p.steps.map (·.performative)

/-- Acyclicity check (REQ-204) — Lean port of Rust
    `CausalProtocol::check_acyclicity`. Uses the existing fuel-bounded
    `dfsNoCycle` from `R1NoRecursion.lean` rather than the Rust
    white/gray/black colour scheme; both algorithms detect the same
    back-edges and the proof obligations are smaller against the
    already-proven DFS soundness lemma. Fuel `|names|² + 1` matches the
    R1 convention. Returns `[]` iff no performative is reachable from
    itself in the successor graph. -/
def ProtocolGraph.checkAcyclicity (p : ProtocolGraph) : List ProtocolViolation :=
  let graph := p.successorGraph
  let names := p.stepNames
  let fuel  := names.length * names.length + 1
  names.filterMap fun n =>
    if dfsNoCycle graph fuel [] [] n then none
    else some (.cycle [n])

/-- Cycle predicate: a protocol has a cycle iff some performative is
    reachable from itself via the successor graph (REQ-204). -/
def ProtocolGraph.hasCycle (p : ProtocolGraph) : Prop :=
  ∃ a, Reachable p.successorGraph a a

/-! ## Soundness — `checkAcyclicity = [] → ¬ hasCycle`. -/

/-- Helper: any node that has a graph neighbour in `successorGraph` is a
    declared step name. The successor graph is built solely from
    `p.steps.map (·.performative)`, so `find?` can only return a `some`
    for keys that appear in `stepNames`. -/
private theorem source_in_stepNames_of_neighbor (p : ProtocolGraph) {src tgt : String}
    (hmem : tgt ∈ graphNeighbors p.successorGraph src) : src ∈ p.stepNames := by
  simp only [graphNeighbors] at hmem
  match heq : p.successorGraph.find? (fun q => q.1 == src) with
  | some entry =>
      have hentry_mem : entry ∈ p.successorGraph := List.mem_of_find?_eq_some heq
      have hpred := List.find?_some heq
      simp only at hpred  -- beta-reduce (fun q => q.1 == src) entry
      have heq_src : entry.1 = src := beq_iff_eq.mp hpred
      simp only [ProtocolGraph.successorGraph, List.mem_map] at hentry_mem
      obtain ⟨step, hstep, hmap⟩ := hentry_mem
      have hperf : step.performative = src := by
        have := congrArg Prod.fst hmap
        simp at this
        exact this.trans heq_src
      simp only [ProtocolGraph.stepNames, List.mem_map]
      exact ⟨step, hstep, hperf⟩
  | none =>
      rw [heq] at hmem
      simp at hmem

/-- Helper: the source of a `Reachable` step is always a declared step name. -/
private theorem reachable_source_in_stepNames (p : ProtocolGraph) {a b : String}
    (hr : Reachable p.successorGraph a b) : a ∈ p.stepNames := by
  cases hr with
  | single hmem  => exact source_in_stepNames_of_neighbor p hmem
  | cons hmem _  => exact source_in_stepNames_of_neighbor p hmem

/-- Helper: extract per-node DFS success from `checkAcyclicity = []`.

    `checkAcyclicity` is a `filterMap` whose result is empty iff the
    body `if dfsNoCycle … then none else some _` is `none` for every
    name. -/
private theorem dfs_true_of_check_empty (p : ProtocolGraph)
    (h : p.checkAcyclicity = []) :
    ∀ n ∈ p.stepNames,
      dfsNoCycle p.successorGraph (p.stepNames.length * p.stepNames.length + 1)
        [] [] n = true := by
  intro n hn
  simp only [ProtocolGraph.checkAcyclicity, List.filterMap_eq_nil_iff] at h
  have := h n hn
  by_cases hdfs : dfsNoCycle p.successorGraph
      (p.stepNames.length * p.stepNames.length + 1) [] [] n = true
  · exact hdfs
  · simp [hdfs] at this

/-- **Soundness (REQ-515 part 1):** if `checkAcyclicity` returns `[]`,
    no performative is reachable from itself in the successor graph
    (i.e. the protocol step graph is acyclic). -/
theorem checkAcyclicity_sound (p : ProtocolGraph)
    (h : p.checkAcyclicity = []) : ¬ p.hasCycle := by
  intro ⟨a, hreach⟩
  have ha_perf := reachable_source_in_stepNames p hreach
  have hdfs := dfs_true_of_check_empty p h a ha_perf
  have hno := dfsNoCycle_no_cycle p.successorGraph
    (p.stepNames.length * p.stepNames.length + 1) [] a hdfs
  exact hno a (List.mem_singleton.mpr rfl) hreach

/-! ## Completeness — `¬ hasCycle → checkAcyclicity = []`. -/

/-- Helper: a `Nodup` list whose elements are all in `l₂` is no longer
    than `l₂`. Stdlib has `Sublist.length_le`, but subset is weaker than
    sublist, so we prove this via induction + `List.erase`. -/
private theorem nodup_subset_length_le {α} [DecidableEq α] :
    ∀ (l₁ : List α), l₁.Nodup → ∀ (l₂ : List α), (∀ x ∈ l₁, x ∈ l₂) →
      l₁.length ≤ l₂.length
  | [], _, _, _ => Nat.zero_le _
  | a :: t, h_nodup, l₂, h_sub => by
    have ha_notin : a ∉ t := (List.nodup_cons.mp h_nodup).1
    have ht_nodup : t.Nodup := (List.nodup_cons.mp h_nodup).2
    have ha_in : a ∈ l₂ := h_sub a List.mem_cons_self
    have ht_sub : ∀ x ∈ t, x ∈ l₂.erase a := by
      intro x hx
      have hx_in : x ∈ l₂ := h_sub x (List.mem_cons_of_mem _ hx)
      have hx_neq : x ≠ a := fun heq => ha_notin (heq ▸ hx)
      exact (List.mem_erase_of_ne hx_neq).mpr hx_in
    have ht_le : t.length ≤ (l₂.erase a).length :=
      nodup_subset_length_le t ht_nodup _ ht_sub
    have h_erase : (l₂.erase a).length = l₂.length - 1 :=
      List.length_erase_of_mem ha_in
    have h_pos : l₂.length ≥ 1 := List.length_pos_of_mem ha_in
    simp only [List.length_cons]
    omega

/-- Helper: if `nb ∈ graphNeighbors graph node` (the neighbor list is
    non-empty), then `node` is a key of `graph`. The successor graph
    only returns neighbors via `graph.find?` keyed on `node`, so a
    non-empty neighbor list witnesses `node`'s membership in the keys. -/
private theorem node_key_of_neighbor_mem
    (graph : List (String × List String)) {node nb : String}
    (h : nb ∈ graphNeighbors graph node) :
    node ∈ graph.map Prod.fst := by
  simp only [graphNeighbors] at h
  match heq : graph.find? (fun p => p.1 == node) with
  | some entry =>
      have h_entry_mem : entry ∈ graph := List.mem_of_find?_eq_some heq
      have h_pred := List.find?_some heq
      simp only at h_pred
      have h_eq : entry.1 = node := beq_iff_eq.mp h_pred
      exact List.mem_map.mpr ⟨entry, h_entry_mem, h_eq⟩
  | none =>
      rw [heq] at h
      simp at h

/-- **DFS completeness for acyclic graphs** (the converse of
    `dfsNoCycle_no_cycle`): if the graph has no cycle, DFS at sufficient
    fuel returns true.

    Strengthened induction: `visiting` is the DFS stack of ancestors of
    `node`. The invariant `(∀ v ∈ visiting, Reachable graph v node)`
    ensures that if any neighbour of `node` is in `visiting`, a cycle
    would exist — contradicting acyclicity. Hence in cycle-free graphs
    the back-edge check never fires; the recursion only bottoms out via
    fuel exhaustion (which we rule out by the bound) or empty neighbour
    list. The bound `visiting.length + fuel ≥ keys.length + 1` plus
    `visiting.Nodup ∧ visiting ⊆ keys` then closes the fuel-out case. -/
private theorem dfsNoCycle_acyclic_returns_true
    (graph : List (String × List String))
    (h_acyclic : ∀ a, ¬ Reachable graph a a) :
    ∀ (fuel : Nat) (visiting : List String) (node : String),
      visiting.Nodup →
      (∀ v ∈ visiting, v ∈ graph.map Prod.fst) →
      (∀ v ∈ visiting, Reachable graph v node) →
      node ∉ visiting →
      visiting.length + fuel ≥ (graph.map Prod.fst).length + 1 →
      dfsNoCycle graph fuel visiting [] node = true := by
  intro fuel
  induction fuel with
  | zero =>
      intro visiting node h_nodup h_sub _ _ h_fuel
      exfalso
      have h_len : visiting.length ≤ (graph.map Prod.fst).length :=
        nodup_subset_length_le visiting h_nodup _ h_sub
      omega
  | succ n ih =>
      intro visiting node h_nodup h_sub h_inv h_notin h_fuel
      unfold dfsNoCycle
      simp only [beq_iff_eq, Nat.add_one_ne_zero, ↓reduceIte,
                 List.contains_nil, Bool.false_eq_true]
      have h_not_visiting : (visiting.contains node) = false := by
        simp [h_notin]
      rw [h_not_visiting]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [show n + 1 - 1 = n from by omega]
      rw [List.all_eq_true]
      intro nb h_nb
      have h_node_key : node ∈ graph.map Prod.fst :=
        node_key_of_neighbor_mem graph h_nb
      have h_nb_neq_node : nb ≠ node := by
        intro heq
        exact h_acyclic node (.single (heq ▸ h_nb))
      have h_nb_notin_visiting : nb ∉ visiting := by
        intro h_in
        exact h_acyclic nb ((h_inv nb h_in).trans (.single h_nb))
      have h_nb_notin' : nb ∉ node :: visiting := by
        intro h_in
        cases h_in with
        | head _ => exact h_nb_neq_node rfl
        | tail _ h_in_t => exact h_nb_notin_visiting h_in_t
      apply ih (node :: visiting) nb
      · exact List.nodup_cons.mpr ⟨h_notin, h_nodup⟩
      · intro v hv
        cases hv with
        | head _ => exact h_node_key
        | tail _ hv_t => exact h_sub v hv_t
      · intro v hv
        cases hv with
        | head _ => exact .single h_nb
        | tail _ hv_t => exact (h_inv v hv_t).trans (.single h_nb)
      · exact h_nb_notin'
      · simp only [List.length_cons]
        omega

/-- Top-level corollary: at fuel ≥ |keys| + 1, DFS from any starting
    node returns true in cycle-free graphs. The fuel `|names|² + 1` used
    by `checkAcyclicity` dominates this bound for any non-trivial graph. -/
private theorem dfsNoCycle_top_level_acyclic
    (graph : List (String × List String))
    (h_acyclic : ∀ a, ¬ Reachable graph a a)
    (node : String) (fuel : Nat)
    (h_fuel : fuel ≥ (graph.map Prod.fst).length + 1) :
    dfsNoCycle graph fuel [] [] node = true := by
  apply dfsNoCycle_acyclic_returns_true graph h_acyclic fuel [] node
  · exact List.nodup_nil
  · intro v hv; exact absurd hv (List.not_mem_nil)
  · intro v hv; exact absurd hv (List.not_mem_nil)
  · exact List.not_mem_nil
  · rw [List.length_nil, Nat.zero_add]; exact h_fuel

/-- **Completeness (REQ-515 part 1, second direction):** if no
    performative is reachable from itself, `checkAcyclicity` returns `[]`. -/
theorem checkAcyclicity_complete (p : ProtocolGraph)
    (h : ¬ p.hasCycle) : p.checkAcyclicity = [] := by
  simp only [ProtocolGraph.checkAcyclicity, List.filterMap_eq_nil_iff]
  intro n _hn
  have h_acyclic : ∀ a, ¬ Reachable p.successorGraph a a := by
    intro a hreach
    exact h ⟨a, hreach⟩
  have h_keys : (p.successorGraph.map Prod.fst) = p.stepNames := by
    simp only [ProtocolGraph.successorGraph, ProtocolGraph.stepNames,
               List.map_map, Function.comp_def]
  have h_fuel_bound : p.stepNames.length * p.stepNames.length + 1
                        ≥ (p.successorGraph.map Prod.fst).length + 1 := by
    rw [h_keys]
    have : p.stepNames.length ≤ p.stepNames.length * p.stepNames.length ∨
           p.stepNames.length = 0 := by
      by_cases hz : p.stepNames.length = 0
      · exact Or.inr hz
      · exact Or.inl (Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hz))
    omega
  have hdfs := dfsNoCycle_top_level_acyclic p.successorGraph h_acyclic n
                 (p.stepNames.length * p.stepNames.length + 1) h_fuel_bound
  simp [hdfs]

/-- **CON-515 — `check_acyclicity_iff_no_cycle`** (full iff).

    Combines `checkAcyclicity_sound` (soundness, `→`) with
    `checkAcyclicity_complete` (completeness, `←`). The completeness
    direction is by induction on the DFS fuel: in cycle-free graphs the
    DFS recursion depth is bounded by `|stepNames|`, so fuel
    `|stepNames|² + 1` is more than sufficient. -/
theorem check_acyclicity_iff_no_cycle (p : ProtocolGraph) :
    p.checkAcyclicity = [] ↔ ¬ p.hasCycle :=
  ⟨checkAcyclicity_sound p, checkAcyclicity_complete p⟩

/-! ## Reachability check (REQ-205) — forward DFS + soundness. -/

/-- Forward DFS searching for `target` reachable from `start` in the
    successor graph. Returns `true` iff `target` is `start` or appears
    along some path within `fuel` steps.

    Semantically equivalent to the Rust BFS in
    `CausalProtocol::check_reachability` for the soundness direction:
    both algorithms visit only nodes reachable from `start`. The DFS
    formulation reuses `Reachable` from `R1NoRecursion.lean` directly,
    avoiding a separate visited-set invariant. -/
def dfsReaches (graph : List (String × List String)) (fuel : Nat)
    (visited : List String) (start target : String) : Bool :=
  if start == target then true
  else if fuel == 0 then false
  else if visited.contains start then false
  else
    let visited' := start :: visited
    let neighbors := graphNeighbors graph start
    neighbors.any (fun nb => dfsReaches graph (fuel - 1) visited' nb target)
termination_by fuel
decreasing_by
  simp_all
  omega

/-- Reachability check (REQ-205) — Lean port of Rust
    `CausalProtocol::check_reachability`. For each declared step name
    other than `"begin"`, runs a forward DFS from `"begin"` and emits
    one `unreachable` violation per step the DFS fails to reach. Fuel
    `|names|² + 1` matches the R5 acyclicity convention. -/
def ProtocolGraph.checkReachability (p : ProtocolGraph) : List ProtocolViolation :=
  let graph := p.successorGraph
  let fuel  := p.stepNames.length * p.stepNames.length + 1
  p.stepNames.filterMap fun n =>
    if n == "begin" then none
    else if dfsReaches graph fuel [] "begin" n then none
    else some (.unreachable n)

/-- "Reachable from begin" predicate: a step is reachable from `begin`
    iff it equals `"begin"` or there is a `Reachable` path in the
    successor graph from `"begin"` to it. Mirrors REQ-205's "every
    step is reachable from begin" semantics. -/
def ProtocolGraph.reachableFromBegin (p : ProtocolGraph) (s : String) : Prop :=
  s = "begin" ∨ Reachable p.successorGraph "begin" s

/-- Property: every declared step is reachable from `begin`. -/
def ProtocolGraph.allStepsReachable (p : ProtocolGraph) : Prop :=
  ∀ s ∈ p.stepNames, p.reachableFromBegin s

/-! ## Soundness — `checkReachability = [] → allStepsReachable`. -/

/-- DFS-reachability soundness: if `dfsReaches` returns true, the target
    is either equal to the start or reachable from it in the graph.

    Proof is by induction on fuel. The `visited` and `start` arguments
    are generalised so the IH applies to recursive calls (which advance
    `start` to a neighbour and grow `visited`). -/
private theorem dfsReaches_sound (graph : List (String × List String)) :
    ∀ (fuel : Nat) (visited : List String) (start target : String),
      dfsReaches graph fuel visited start target = true →
      start = target ∨ Reachable graph start target := by
  intro fuel
  induction fuel with
  | zero =>
    intro visited start target h
    unfold dfsReaches at h
    split at h
    · rename_i heq; exact .inl (beq_iff_eq.mp heq)
    · split at h
      · exact absurd h (by simp)
      · rename_i hfuel
        have : ((0 : Nat) == 0) = true := by simp
        exact absurd this hfuel
  | succ n ih =>
    intro visited start target h
    unfold dfsReaches at h
    split at h
    · rename_i heq; exact .inl (beq_iff_eq.mp heq)
    · split at h
      · rename_i hfuel; exact absurd hfuel (by simp)
      · split at h
        · exact absurd h (by simp)
        · rw [show (n + 1 - 1 : Nat) = n from by omega] at h
          rw [List.any_eq_true] at h
          obtain ⟨nb, hnb_mem, hnb_dfs⟩ := h
          have ih_nb := ih (start :: visited) nb target hnb_dfs
          cases ih_nb with
          | inl hnb_eq =>
            rw [hnb_eq] at hnb_mem
            exact .inr (.single hnb_mem)
          | inr hnb_reach =>
            exact .inr (.cons hnb_mem hnb_reach)

/-- Helper: extract per-step DFS success from `checkReachability = []`.
    Mirrors `dfs_true_of_check_empty` for the acyclicity proof. -/
private theorem dfs_reaches_of_check_empty (p : ProtocolGraph)
    (h : p.checkReachability = []) :
    ∀ n ∈ p.stepNames, n ≠ "begin" →
      dfsReaches p.successorGraph (p.stepNames.length * p.stepNames.length + 1)
        [] "begin" n = true := by
  intro n hn hne
  simp only [ProtocolGraph.checkReachability, List.filterMap_eq_nil_iff] at h
  have hbody := h n hn
  have hbeq : (n == "begin") = false := by simp [hne]
  simp [hbeq] at hbody
  by_cases hdfs : dfsReaches p.successorGraph
      (p.stepNames.length * p.stepNames.length + 1) [] "begin" n = true
  · exact hdfs
  · simp [hdfs] at hbody

/-- **Soundness (REQ-515 part 2):** if `checkReachability` returns `[]`,
    every declared step is reachable from `begin` in the successor graph. -/
theorem checkReachability_sound (p : ProtocolGraph)
    (h : p.checkReachability = []) : p.allStepsReachable := by
  intro s hs
  by_cases hbegin : s = "begin"
  · exact .inl hbegin
  · have hdfs := dfs_reaches_of_check_empty p h s hs hbegin
    have hsound := dfsReaches_sound p.successorGraph _ _ _ _ hdfs
    cases hsound with
    | inl hbeq    => exact absurd hbeq.symm hbegin
    | inr hreach  => exact .inr hreach

/-! ## Completeness — `allStepsReachable → checkReachability = []`.

Path-based reachability machinery is needed because `Reachable` is "too
abstract" for the DFS-completeness proof: a `Reachable` proof can revisit
nodes (e.g. `a → b → a → c`), which would deadlock the forward DFS at
the visited-check. We extract a *simple* path (`Nodup` and avoiding the
DFS's growing `visited` set) and induct on its length. -/

/-- Reachability via an explicit sequence of intermediate nodes.
    `ReachableViaPath graph s t [n₁, …, n_k]` represents the path
    `s → n₁ → … → n_k → t` with `k + 1` edges. The empty path is a
    single edge `s → t`. -/
inductive ReachableViaPath (graph : List (String × List String)) :
    String → String → List String → Prop where
  | direct : b ∈ graphNeighbors graph a → ReachableViaPath graph a b []
  | step   : c ∈ graphNeighbors graph a →
             ReachableViaPath graph c b path →
             ReachableViaPath graph a b (c :: path)

/-- A `Reachable` proof gives an explicit `ReachableViaPath` witness. -/
private theorem reachable_to_via_path {graph : List (String × List String)}
    {s t : String} (h : Reachable graph s t) :
    ∃ path, ReachableViaPath graph s t path := by
  induction h with
  | single hmem => exact ⟨[], .direct hmem⟩
  | cons hmem _ ih =>
      obtain ⟨path, hp⟩ := ih
      exact ⟨_ :: path, .step hmem hp⟩

/-- The source of any `ReachableViaPath` is a graph key (it has outgoing edges). -/
private theorem reachableViaPath_source_in_keys
    {graph : List (String × List String)}
    {s t : String} {path : List String} (h : ReachableViaPath graph s t path) :
    s ∈ graph.map Prod.fst := by
  cases h with
  | direct hmem => exact node_key_of_neighbor_mem graph hmem
  | step hmem _ => exact node_key_of_neighbor_mem graph hmem

/-- Every intermediate node in a `ReachableViaPath` is also a graph key
    (each intermediate is the source of the next edge). -/
private theorem reachableViaPath_path_in_keys
    {graph : List (String × List String)}
    {s t : String} {path : List String} (h : ReachableViaPath graph s t path) :
    ∀ x ∈ path, x ∈ graph.map Prod.fst := by
  induction h with
  | direct _ => intro x hx; exact absurd hx (List.not_mem_nil)
  | step _ hrest ih =>
      intro x hx
      cases hx with
      | head _ => exact reachableViaPath_source_in_keys hrest
      | tail _ hx_t => exact ih x hx_t

/-- Helper: from a `ReachableViaPath` whose path contains a node `v`,
    extract a strictly shorter `ReachableViaPath` starting at `v`. Used
    by path simplification to "shortcut" loops (drop the prefix up to and
    including the visited-again node). -/
private theorem reachableViaPath_suffix_at_node
    {graph : List (String × List String)} :
    ∀ {s t : String} {path : List String} (v : String),
      ReachableViaPath graph s t path → v ∈ path →
      ∃ suff : List String,
        ReachableViaPath graph v t suff ∧ suff.length < path.length := by
  intro s t path v h
  induction path generalizing s with
  | nil => intro h_in; exact absurd h_in List.not_mem_nil
  | cons c rest ih =>
      intro h_in
      cases h with
      | step hmem h_rest =>
          cases h_in with
          | head _ =>
              exact ⟨rest, h_rest, by simp [List.length_cons]⟩
          | tail _ h_in_rest =>
              obtain ⟨suff, hsuff, hlen⟩ := ih h_rest h_in_rest
              exact ⟨suff, hsuff, by simp [List.length_cons]; omega⟩

/-- **Path simplification**: from any `ReachableViaPath`, extract one
    with `Nodup` intermediates that don't include `s`. The proof is by
    strong induction on path length:

    * If `path = c :: rest` with `c = s`: drop the prefix; the suffix
      `rest` is still a `ReachableViaPath graph s t`. Recurse.
    * If `s ∈ rest`: drop the prefix up to the (second) occurrence of `s`;
      the suffix is `ReachableViaPath graph s t` strictly shorter. Recurse.
    * Otherwise (`c ≠ s` and `s ∉ rest`): recurse on `rest`, prepend `c`.
      If after recursion `s` reappears (in the simplified `rest'`),
      shortcut again via `reachableViaPath_suffix_at_node`.

    Each branch strictly reduces path length, so well-founded recursion
    on `path.length` discharges termination. -/
private theorem reachableViaPath_to_simple
    (graph : List (String × List String)) :
    ∀ (path : List String) (s t : String),
      ReachableViaPath graph s t path →
      ∃ path', ReachableViaPath graph s t path' ∧
               path'.Nodup ∧
               s ∉ path' ∧
               path'.length ≤ path.length := by
  intro path
  induction h_n : path.length using Nat.strongRecOn
      generalizing path with
  | ind n ih =>
    intro s t h_path
    subst h_n
    cases h_path with
    | direct hmem =>
        exact ⟨[], .direct hmem, List.nodup_nil, List.not_mem_nil,
               Nat.le_refl _⟩
    | step hmem h_rest =>
        rename_i c rest
        -- path = c :: rest, edge s → c, h_rest : RVP graph c t rest
        by_cases hc_s : c = s
        · -- c = s (self-loop): use h_rest directly.
          subst hc_s
          have hlt : rest.length < (c :: rest).length := by
            simp [List.length_cons]
          obtain ⟨p', hp', hnd, hns, hlen⟩ :=
            ih rest.length hlt rest rfl c t h_rest
          exact ⟨p', hp', hnd, hns, by simp [List.length_cons]; omega⟩
        · by_cases hs_in_rest : s ∈ rest
          · -- s ∈ rest: extract suffix RVP graph s t suff with suff.length < rest.length.
            obtain ⟨suff, hsuff, hlen⟩ :=
              reachableViaPath_suffix_at_node s h_rest hs_in_rest
            have hlt : suff.length < (c :: rest).length := by
              simp [List.length_cons]; omega
            obtain ⟨p', hp', hnd, hns, hlen'⟩ :=
              ih suff.length hlt suff rfl s t hsuff
            exact ⟨p', hp', hnd, hns, by simp [List.length_cons]; omega⟩
          · -- s ∉ rest and c ≠ s. Recurse on rest.
            have hlt_rest : rest.length < (c :: rest).length := by
              simp [List.length_cons]
            obtain ⟨rest', hrp, hrnd, hrns, hrlen⟩ :=
              ih rest.length hlt_rest rest rfl c t h_rest
            -- rest' : RVP graph c t rest', c ∉ rest', rest' Nodup, |rest'| ≤ |rest|.
            by_cases hs_in_rest' : s ∈ rest'
            · -- s appears in rest': shortcut via suffix-at-node.
              obtain ⟨suff', hsuff', hlen'⟩ :=
                reachableViaPath_suffix_at_node s hrp hs_in_rest'
              have hlt : suff'.length < (c :: rest).length := by
                simp [List.length_cons]; omega
              obtain ⟨p', hp', hnd, hns, hlen''⟩ :=
                ih suff'.length hlt suff' rfl s t hsuff'
              exact ⟨p', hp', hnd, hns, by simp [List.length_cons]; omega⟩
            · -- s ∉ rest'. Build c :: rest'.
              refine ⟨c :: rest', .step hmem hrp, ?_, ?_, ?_⟩
              · exact List.nodup_cons.mpr ⟨hrns, hrnd⟩
              · intro h_in
                cases h_in with
                | head _ => exact hc_s rfl
                | tail _ h_in_rest' => exact hs_in_rest' h_in_rest'
              · simp [List.length_cons]; omega

/-- **DFS completeness along a simple path**: if there's a `Nodup` path
    from `s` to `t` (with `s` not on it) that doesn't intersect `visited`,
    then `dfsReaches` finds `t` at fuel ≥ `path.length + 1`. Proof by
    induction on the path: at each step the next path node is in
    `graphNeighbors` of the current node (by `ReachableViaPath`), and
    `Nodup` + disjointness ensure it isn't blocked by `visited`. -/
private theorem dfsReaches_via_path
    (graph : List (String × List String)) :
    ∀ (path : List String) (s t : String) (visited : List String) (fuel : Nat),
      ReachableViaPath graph s t path →
      (∀ x ∈ s :: path, x ∉ visited) →
      path.Nodup →
      s ∉ path →
      fuel ≥ path.length + 1 →
      dfsReaches graph fuel visited s t = true := by
  intro path
  induction path with
  | nil =>
      intro s t visited fuel h_rvp h_visited _ _ h_fuel
      cases h_rvp with
      | direct hmem =>
          unfold dfsReaches
          by_cases hst : s = t
          · simp [hst]
          · have hs_v : s ∉ visited := h_visited s List.mem_cons_self
            have h_fuel' : fuel ≥ 1 := by simp at h_fuel; omega
            have h_st_beq : (s == t) = false := by simp [hst]
            have h_fuel_beq : (fuel == 0) = false := by simp; omega
            have h_vc_beq : visited.contains s = false := by simp [hs_v]
            simp only [h_st_beq, h_fuel_beq, h_vc_beq, ↓reduceIte,
                       Bool.false_eq_true]
            rw [List.any_eq_true]
            refine ⟨t, hmem, ?_⟩
            unfold dfsReaches
            simp
  | cons c rest ih =>
      intro s t visited fuel h_rvp h_visited h_nodup h_s_notin h_fuel
      cases h_rvp with
      | step hmem h_rest =>
          unfold dfsReaches
          by_cases hst : s = t
          · simp [hst]
          · have hs_v : s ∉ visited := h_visited s List.mem_cons_self
            have h_fuel' : fuel ≥ rest.length + 2 := by
              simp [List.length_cons] at h_fuel; omega
            have h_c_neq_s : c ≠ s := by
              intro h_eq
              exact h_s_notin (h_eq ▸ List.mem_cons_self)
            have hc_v : c ∉ visited :=
              h_visited c (List.mem_cons_of_mem _ List.mem_cons_self)
            have h_c_notin_rest : c ∉ rest := (List.nodup_cons.mp h_nodup).1
            have h_rest_nodup : rest.Nodup := (List.nodup_cons.mp h_nodup).2
            have h_s_notin_rest : s ∉ rest := by
              intro h_in; exact h_s_notin (List.mem_cons_of_mem _ h_in)
            have h_st_beq : (s == t) = false := by simp [hst]
            have h_fuel_beq : (fuel == 0) = false := by simp; omega
            have h_vc_beq : visited.contains s = false := by simp [hs_v]
            simp only [h_st_beq, h_fuel_beq, h_vc_beq, ↓reduceIte,
                       Bool.false_eq_true]
            rw [List.any_eq_true]
            refine ⟨c, hmem, ?_⟩
            apply ih c t (s :: visited) (fuel - 1) h_rest
            · -- ∀ x ∈ c :: rest, x ∉ s :: visited
              intro x hx h_in_v'
              cases h_in_v' with
              | head _ =>
                  cases hx with
                  | head _ => exact h_c_neq_s rfl
                  | tail _ h_in_rest => exact h_s_notin_rest h_in_rest
              | tail _ h_in_v =>
                  have hx_in_full : x ∈ s :: c :: rest := by
                    cases hx with
                    | head _ => exact List.mem_cons_of_mem _ List.mem_cons_self
                    | tail _ h => exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)
                  exact h_visited x hx_in_full h_in_v
            · exact h_rest_nodup
            · exact h_c_notin_rest
            · omega

/-- **DFS completeness for the top-level call** (`visited = []`): given
    `Reachable graph s t`, `dfsReaches` at fuel ≥ `|keys| + 1` returns
    true. Composes path extraction (`reachable_to_via_path`),
    simplification (`reachableViaPath_to_simple`), and path-following DFS
    completeness (`dfsReaches_via_path`). -/
private theorem dfsReaches_complete_top_level
    (graph : List (String × List String))
    {s t : String} (h_reach : Reachable graph s t)
    (fuel : Nat)
    (h_fuel : fuel ≥ (graph.map Prod.fst).length + 1) :
    dfsReaches graph fuel [] s t = true := by
  obtain ⟨path, h_rvp⟩ := reachable_to_via_path h_reach
  obtain ⟨path', h_rvp', h_nd, h_sn, _h_len⟩ :=
    reachableViaPath_to_simple graph path s t h_rvp
  have h_path'_keys : ∀ x ∈ path', x ∈ graph.map Prod.fst :=
    reachableViaPath_path_in_keys h_rvp'
  have h_len_bound : path'.length ≤ (graph.map Prod.fst).length :=
    nodup_subset_length_le path' h_nd _ h_path'_keys
  apply dfsReaches_via_path graph path' s t [] fuel h_rvp'
  · intro x _; exact List.not_mem_nil
  · exact h_nd
  · exact h_sn
  · omega

/-- **Completeness (REQ-515 part 2, second direction):** if every step
    is reachable from `begin`, `checkReachability` returns `[]`. -/
theorem checkReachability_complete (p : ProtocolGraph)
    (h : p.allStepsReachable) : p.checkReachability = [] := by
  simp only [ProtocolGraph.checkReachability, List.filterMap_eq_nil_iff]
  intro n hn
  by_cases hbegin : n = "begin"
  · simp [hbegin]
  · have h_reach := h n hn
    rcases h_reach with hbeq | hreach
    · exact absurd hbeq hbegin
    · have h_keys : (p.successorGraph.map Prod.fst) = p.stepNames := by
        simp only [ProtocolGraph.successorGraph, ProtocolGraph.stepNames,
                   List.map_map, Function.comp_def]
      have h_fuel : p.stepNames.length * p.stepNames.length + 1
                      ≥ (p.successorGraph.map Prod.fst).length + 1 := by
        rw [h_keys]
        have : p.stepNames.length ≤ p.stepNames.length * p.stepNames.length ∨
               p.stepNames.length = 0 := by
          by_cases hz : p.stepNames.length = 0
          · exact Or.inr hz
          · exact Or.inl (Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hz))
        omega
      have hdfs := dfsReaches_complete_top_level p.successorGraph hreach
                     (p.stepNames.length * p.stepNames.length + 1) h_fuel
      simp [hbegin, hdfs]

/-- **CON-515 — `check_reachability_iff_all_reachable`** (full iff).

    Combines `checkReachability_sound` (soundness, `→`) with
    `checkReachability_complete` (completeness, `←`). The completeness
    direction extracts a simple path of length ≤ `|stepNames|` from any
    `Reachable` proof, then shows the forward DFS follows it at fuel
    `|stepNames|² + 1`. -/
theorem check_reachability_iff_all_reachable (p : ProtocolGraph) :
    p.checkReachability = [] ↔ p.allStepsReachable :=
  ⟨checkReachability_sound p, checkReachability_complete p⟩

/-! ## Performative-definedness check (REQ-206) — set membership + iff. -/

/-- Performative names referenced by a protocol (mirrors Rust
    `CausalProtocol::all_referenced_performatives` in
    `crates/cbcl-core/src/protocol.rs`). Collects each declared step
    name plus every name appearing in any step's predecessor or
    successor list, with `"begin"` filtered out (REQ-206 treats
    `begin` as always defined).

    Rust uses a `BTreeSet` to dedupe; the Lean version returns a plain
    `List String` since the iff theorem only quantifies over
    membership, not multiplicity. -/
def ProtocolGraph.referencedPerformatives (p : ProtocolGraph) : List String :=
  p.steps.flatMap fun s =>
    (if s.performative = "begin" then [] else [s.performative]) ++
    s.predecessors.filter (· ≠ "begin") ++
    s.successors.filter (· ≠ "begin")

/-- Performative-definedness check (REQ-206) — Lean port of Rust
    `CausalProtocol::check_performative_definedness`. Returns one
    `undefinedPerformative` violation per referenced performative not
    present in the supplied `defined` set (the dialect's
    installed-ancestor closure). -/
def ProtocolGraph.checkPerformativeDefinedness
    (p : ProtocolGraph) (defined : List String) : List ProtocolViolation :=
  p.referencedPerformatives.filterMap fun n =>
    if n ∈ defined then none
    else some (.undefinedPerformative n)

/-- Property: every referenced performative is in the `defined` set. -/
def ProtocolGraph.allReferencedDefined
    (p : ProtocolGraph) (defined : List String) : Prop :=
  ∀ n ∈ p.referencedPerformatives, n ∈ defined

/-- **CON-515 — `check_performative_definedness_iff_all_defined`
    (REQ-515 part 3).**

    Full iff: pure set membership, no fuel, no graph traversal. Reduces
    to `List.filterMap_eq_nil_iff` plus case analysis on `n ∈ defined`. -/
theorem check_performative_definedness_iff_all_defined
    (p : ProtocolGraph) (defined : List String) :
    p.checkPerformativeDefinedness defined = [] ↔
    p.allReferencedDefined defined := by
  simp only [ProtocolGraph.checkPerformativeDefinedness,
             ProtocolGraph.allReferencedDefined,
             List.filterMap_eq_nil_iff]
  refine ⟨fun h n hn => ?_, fun h n hn => ?_⟩
  · have hf := h n hn
    by_cases hd : n ∈ defined
    · exact hd
    · simp [hd] at hf
  · simp [h n hn]

/-! ## Step-uniqueness check (REQ-207, post-fix) — predecessor cardinality
    + successor `Nodup` + iff. -/

/-- Step-uniqueness check (REQ-207, post-fix) — Lean port of Rust
    `CausalProtocol::check_step_uniqueness`. Emits one
    `duplicateStep` violation per `StepDecl` whose predecessor list
    contains a repeated entry, or whose successor list contains a
    repeated entry.

    The Rust `CausalProtocol::steps` is keyed by performative name,
    so the only way for extra predecessor entries to arise is via
    the surface-form `(then …)` parser pushing per-clause
    contributions into the same step. Distinct-alternative
    declarations like `(then begin a) (then b a)` are *intentional* —
    `verify_causal` reads the resulting `[Single "begin", Single "b"]`
    as `begin ∨ b` for the predecessor of `a`, so honest alternations
    keep `Nodup`. What R5 forbids is *literal* repetition, e.g. the
    same `(then begin a)` clause twice, which collapses to
    `[Single "begin", Single "begin"]` and breaks `Nodup`. Legitimate
    fan-in is a single `NodeRef.All …` entry (collapsed to one string
    in this Lean model), so it trivially keeps `Nodup`. The Lean model
    maps every `NodeRef.Single x` to the entry `x`; faithful
    representation of the multi-name `Any`/`All` constructors is out
    of scope for the parity tests (`req515_step_uniqueness_*` use
    `Single` only), and the structured Rust check enforces the
    property on the full `Vec<NodeRef>` form. -/
def ProtocolGraph.checkStepUniqueness (p : ProtocolGraph) : List ProtocolViolation :=
  p.steps.filterMap fun s =>
    if s.predecessors.Nodup ∧ s.successors.Nodup then none
    else some (.duplicateStep s.performative)

/-- Property: every `StepDecl` has duplicate-free predecessor and
    successor lists. -/
def ProtocolGraph.allStepsUnique (p : ProtocolGraph) : Prop :=
  ∀ s ∈ p.steps, s.predecessors.Nodup ∧ s.successors.Nodup

/-- **CON-515 — `check_step_uniqueness_iff_no_duplicates`
    (REQ-515 part 4).**

    Full iff: per-step `Nodup` on both edge lists, no fuel,
    no graph traversal. Mirrors
    `check_performative_definedness_iff_all_defined` structurally;
    reduces to `List.filterMap_eq_nil_iff` plus case analysis on the
    per-step `Nodup ∧ Nodup` conjunction. -/
theorem check_step_uniqueness_iff_no_duplicates (p : ProtocolGraph) :
    p.checkStepUniqueness = [] ↔ p.allStepsUnique := by
  simp only [ProtocolGraph.checkStepUniqueness,
             ProtocolGraph.allStepsUnique,
             List.filterMap_eq_nil_iff]
  refine ⟨fun h s hs => ?_, fun h s hs => ?_⟩
  · have hf := h s hs
    by_cases hu : s.predecessors.Nodup ∧ s.successors.Nodup
    · exact hu
    · simp [hu] at hf
  · simp [h s hs]

end CBCL
