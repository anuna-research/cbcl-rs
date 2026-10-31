import LeanCbcl.SealedCheckpoint

/-!
SPEC-023 local identity-journal / activation / abort transition model.
An arbitrary honest core follows these steps; Byzantine nodes are unrestricted.
The composed quorum theorem uses actual activation state and published snapshots.
Prepare-certificate uniqueness and external recovery consensus remain separate.
No full Python lifecycle correspondence or Abstract ordered-history theorem.
-/
namespace CBCL.AbortableHandoff
open CBCL.ValidatorBudget CBCL.SealedCheckpoint

/-- Local journal and abort/export state for the handoff abstraction. -/
structure Node where
  /-- Transactions durably signed by this node. -/
  signed : Nat → Bool
  /-- Checkpoint activated by this node, if any. -/
  activated : Option Nat
  /-- Whether this node has irreversibly stopped normal execution. -/
  stopped : Bool
  /-- Frozen signature journal and activated checkpoint exported on abort. -/
  exported : Option ((Nat → Bool) × Option Nat)

/-- One permitted protocol transition, labelled only when an operation becomes final. -/
inductive Step : Node → Node → Prop where
  | sign (s : Node) (tx : Nat) (openPhase : s.stopped = false) :
      Step s { s with signed := fun t => if t = tx then true else s.signed t }
  | activate (s : Node) (cp : Nat) (openPhase : s.stopped = false)
      (once : s.activated = none ∨ s.activated = some cp) :
      Step s { s with activated := some cp }
  | abort (s : Node) : Step s { s with stopped := true, exported := some (s.signed, s.activated) }
  | replay (s : Node) : Step s s

/-- States reachable by finitely many permitted transitions. -/
inductive Reach (initial : Node) : Node → Prop where
  | start : Reach initial initial
  | next : Reach initial s → Step s t → Reach initial t

/-- Every exported snapshot matches the node's stopped, immutable state. -/
def SnapshotValid (s : Node) : Prop :=
  ∀ ops choice, s.exported = some (ops, choice) →
    s.stopped = true ∧ s.signed = ops ∧ s.activated = choice

theorem step_snapshot (valid : SnapshotValid s) (h : Step s t) : SnapshotValid t := by
  cases h with
  | sign tx openPhase =>
      intro ops choice exported
      have old := valid ops choice exported
      simp [openPhase] at old
  | activate cp openPhase once =>
      intro ops choice exported
      have old := valid ops choice exported
      simp [openPhase] at old
  | abort =>
      intro ops choice exported
      change some (s.signed, s.activated) = some (ops, choice) at exported
      simp only [Option.some.injEq, Prod.mk.injEq] at exported
      exact ⟨rfl, exported.1, exported.2⟩
  | replay => exact valid

theorem reachable_snapshot (empty : initial.exported = none) (h : Reach initial s) :
    SnapshotValid s := by
  induction h with
  | start => intro ops choice impossible; simp [empty] at impossible
  | next _ step ih => exact step_snapshot ih step

/-- Covers operation identities even when their resource cost is zero. -/
theorem stopped_step (stopped : s.stopped = true) (h : Step s t) :
    t.stopped = true ∧ t.signed = s.signed ∧ t.activated = s.activated := by
  cases h with
  | sign tx openPhase => simp [stopped] at openPhase
  | activate cp openPhase once => simp [stopped] at openPhase
  | abort => exact ⟨rfl, rfl, rfl⟩
  | replay => exact ⟨stopped, rfl, rfl⟩

theorem stopped_reach (stopped : initial.stopped = true) (h : Reach initial s) :
    s.stopped = true ∧ s.signed = initial.signed ∧ s.activated = initial.activated := by
  induction h with
  | start => exact ⟨stopped, rfl, rfl⟩
  | next _ step ih =>
      obtain ⟨hs, ho, hc⟩ := stopped_step ih.1 step
      exact ⟨hs, ho.trans ih.2.1, hc.trans ih.2.2⟩

/-- A hidden activation quorum cannot disappear across a quorum handoff.
The core's snapshot invariant is obtained from reachable_snapshot. -/
theorem activation_preserved_in_handoff (c : Committee f) (nodes : Nat → Node) (cp : Nat)
    (valid : ∀ w ∈ c.core, SnapshotValid (nodes w))
    (activated : 2*f+1 ≤ voteCount (c.core ++ c.others)
      (fun w => decide ((nodes w).activated = some cp)))
    (handoff : Nat → Bool)
    (selected : ∀ w ∈ c.core, handoff w = true → (nodes w).exported.isSome = true)
    (aborted : 2*f+1 ≤ voteCount (c.core ++ c.others) handoff) :
    ∃ w ∈ c.core, handoff w = true ∧ ∃ ops, (nodes w).exported = some (ops, some cp) := by
  obtain ⟨w, hw, ha, included⟩ := honest_intersection c _ _ activated aborted
  have hb := selected w hw included
  have choice : (nodes w).activated = some cp := of_decide_eq_true ha
  cases he : (nodes w).exported with
  | none => simp [he] at hb
  | some snapshot =>
      obtain ⟨ops, recorded⟩ := snapshot
      have hv := valid w hw ops recorded he
      have same : recorded = some cp := hv.2.2.symm.trans choice
      exact ⟨w, hw, included, ops, same ▸ he⟩

/-- Fast prepare vote-once plus quorum intersection gives unique prepare QC. -/
theorem prepare_unique (c : Committee f) (votes : Nat → Nat → Bool) (a b : Nat)
    (once : ∀ w ∈ c.core, votes a w = true → votes b w = true → a = b)
    (qa : 2*f+1 ≤ voteCount (c.core ++ c.others) (votes a))
    (qb : 2*f+1 ≤ voteCount (c.core ++ c.others) (votes b)) : a = b := by
  obtain ⟨w, hw, ha, hb⟩ := honest_intersection c _ _ qa qb
  exact once w hw ha hb

/-- Compose transition induction with quorum intersection, rather than assuming
snapshot validity independently of the local execution. -/
theorem reachable_activation_preserved (c : Committee f) (initial nodes : Nat → Node)
    (empty : ∀ w ∈ c.core, (initial w).exported = none)
    (runs : ∀ w ∈ c.core, Reach (initial w) (nodes w)) (cp : Nat)
    (activated : 2*f+1 ≤ voteCount (c.core ++ c.others)
      (fun w => decide ((nodes w).activated = some cp)))
    (handoff : Nat → Bool)
    (selected : ∀ w ∈ c.core, handoff w = true → (nodes w).exported.isSome = true)
    (aborted : 2*f+1 ≤ voteCount (c.core ++ c.others) handoff) :
    ∃ w ∈ c.core, handoff w = true ∧ ∃ ops, (nodes w).exported = some (ops, some cp) := by
  apply activation_preserved_in_handoff c nodes cp _ activated handoff selected aborted
  intro w hw
  exact reachable_snapshot (empty w hw) (runs w hw)

/-- External recovery selection must honor certified prepare evidence. This
selection validity is an interface premise; agreement is not implemented here. -/
theorem recovery_preserves_activation (c : Committee f) (initial nodes : Nat → Node)
    (empty : ∀ w ∈ c.core, (initial w).exported = none)
    (runs : ∀ w ∈ c.core, Reach (initial w) (nodes w)) (cp chosen : Nat)
    (activated : 2*f+1 ≤ voteCount (c.core ++ c.others)
      (fun w => decide ((nodes w).activated = some cp)))
    (handoff : Nat → Bool)
    (selected : ∀ w ∈ c.core, handoff w = true → (nodes w).exported.isSome = true)
    (aborted : 2*f+1 ≤ voteCount (c.core ++ c.others) handoff)
    (honors : ∀ w ∈ c.core, handoff w = true → ∀ ops candidate,
      (nodes w).exported = some (ops, some candidate) → chosen = candidate) : chosen = cp := by
  obtain ⟨w, hw, included, ops, report⟩ := reachable_activation_preserved c initial nodes empty runs cp activated handoff selected aborted
  exact honors w hw included ops cp report

end CBCL.AbortableHandoff
