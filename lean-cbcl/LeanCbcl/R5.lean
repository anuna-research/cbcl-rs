import LeanCbcl.R1NoRecursion

/-!
# R5 Sub-check Soundness — Acyclicity (REQ-515 part 1 / CON-515 / TEST-515)

Lean port of SPEC-002 REQ-204's acyclicity check. The Rust implementation
(`crates/cbcl-core/src/protocol.rs::CausalProtocol::check_acyclicity`)
uses a 3-colour DFS over the successor graph and emits one
`ProtocolViolation::Cycle` per back-edge encountered.

This module mirrors the SPEC-001 R1 DFS proof structure
(`LeanCbcl/R1NoRecursion.lean`): the underlying graph DFS (`dfsNoCycle`),
graph-reachability predicate (`Reachable`), and DFS soundness theorem
(`dfsNoCycle_no_cycle`) are reused unchanged. Only the surface layer
(`StepDecl` / `ProtocolGraph` / `ProtocolViolation` / `checkAcyclicity`)
is new.

## Theorems

* `checkAcyclicity_sound` — soundness (`check returns [] → no cycle`).
  This is REQ-515 part 1's mandatory direction.

* `check_acyclicity_iff_no_cycle` — the headline iff theorem named in
  CON-515. **Currently states the soundness direction only**;
  completeness (`no cycle → check returns []`) is deferred per ADR-512.
  The deferred direction would require a König-style argument bounding
  cycle length by `|stepNames|`, which is not yet mechanised. The
  existing companion `dfsNoCycle_complete` in `R1NoRecursion.lean`
  provides the underlying DFS-completeness lemma; lifting it to the
  fixed `n² + 1` fuel used here is the open work.
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
    `ProtocolViolation`). Only the `cycle` constructor is needed for the
    acyclicity proof; reachability/definedness/uniqueness violations are
    introduced by sibling tasks. -/
inductive ProtocolViolation where
  | cycle (participants : List String) : ProtocolViolation
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

end CBCL
