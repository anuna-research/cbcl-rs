import LeanCbcl.R1NoRecursion

/-!
# R5 Sub-check Soundness — Acyclicity + Reachability + Definedness (REQ-515 / CON-515 / TEST-515)

Lean port of three SPEC-002 R5 sub-checks:

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

Acyclicity and reachability reuse the SPEC-001 graph layer
(`graphNeighbors`, `Reachable`) and the underlying DFS algorithm
(`dfsNoCycle`) from `LeanCbcl/R1NoRecursion.lean`. Reachability adds a
new forward-DFS helper (`dfsReaches`) since the Rust BFS visits
*forward* (from `begin` outward) whereas R1's DFS searches *for
cycles*. A forward DFS is equivalent to BFS for soundness — both
visit exactly the reachable set — and yields a smaller proof against
the existing `Reachable` inductive. Definedness is purely a
set-membership check and reduces to `List.filterMap_eq_nil_iff`.

## Theorems

* `checkAcyclicity_sound` / `checkReachability_sound` — soundness
  (`check returns [] → property holds`). This is REQ-515's mandatory
  direction for both graph sub-checks.

* `check_acyclicity_iff_no_cycle` / `check_reachability_iff_all_reachable`
  — the headline iff theorems named in CON-515. **Both currently state
  the soundness direction only**; completeness (`property holds → check
  returns []`) is deferred per ADR-512. For acyclicity the deferred
  direction would require a König-style argument bounding cycle length
  by `|stepNames|`; for reachability the deferred direction would
  require showing that fuel `n² + 1` suffices for BFS to visit every
  reachable node. Both are open work.

* `check_performative_definedness_iff_all_defined` — full iff (no
  fuel, no graph traversal), follows directly from
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
    `ProtocolViolation`). The `cycle`, `unreachable`, and
    `undefinedPerformative` constructors are used by the REQ-204,
    REQ-205, and REQ-206 proofs respectively; the `duplicateStep`
    (REQ-207) violation is introduced by a sibling task. -/
inductive ProtocolViolation where
  | cycle (participants : List String) : ProtocolViolation
  | unreachable (step : String)        : ProtocolViolation
  | undefinedPerformative (name : String) : ProtocolViolation
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

/-- **CON-515 — `check_acyclicity_iff_no_cycle`.**

    Currently proves the soundness direction (`→`) only. Per ADR-512,
    completeness (`←`) is deferred to a follow-on commit; the underlying
    DFS-completeness lemma `dfsNoCycle_complete` in `R1NoRecursion.lean`
    provides the bound-existential ingredient, but lifting it to the
    fixed `|names|² + 1` fuel used by `checkAcyclicity` requires a
    König-style cycle-shortening argument that is not yet mechanised.

    The theorem is named per CON-515; downstream users that only need
    soundness should prefer `checkAcyclicity_sound` directly. -/
theorem check_acyclicity_iff_no_cycle (p : ProtocolGraph) :
    p.checkAcyclicity = [] → ¬ p.hasCycle :=
  checkAcyclicity_sound p

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

/-- **CON-515 — `check_reachability_iff_all_reachable`.**

    Currently proves the soundness direction (`→`) only. Per ADR-512,
    completeness (`←`) is deferred to a follow-on commit. The deferred
    direction would require a BFS-completeness argument: every node
    reachable in the abstract `Reachable` predicate is visited by the
    fuel-bounded forward DFS at fuel `|stepNames|² + 1`. The standard
    bound is `|stepNames|` (every reachable node has a simple path of
    length ≤ |V| - 1), so the fuel is more than sufficient; mechanising
    the bound requires reasoning about `visited`-set growth that is not
    yet in place.

    The theorem is named per CON-515; downstream users that only need
    soundness should prefer `checkReachability_sound` directly. -/
theorem check_reachability_iff_all_reachable (p : ProtocolGraph) :
    p.checkReachability = [] → p.allStepsReachable :=
  checkReachability_sound p

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

end CBCL
