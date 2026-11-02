import LeanCbcl.ConsensusFree.OwnedLifecycle
import LeanCbcl.ConsensusFree.Scheduler

/-! SPEC-034: derive dependency readiness from a finite acyclic catalogue and
executable retry queue. Retirement uses owner observation, never hidden votes.
This is not the owner-product capstone or Rust source refinement. -/
namespace CBCL.ConsensusFree.OwnedProgress
open CBCL.ConsensusFree.MultiParent.Liveness
namespace Retry
/-- Concrete FIFO retry queue used for retained dependency work. -/
abbrev Queue := Scheduler.QueueTrace
variable {N : Nat}
/-- Finite verified dependency objects with strictly decreasing dependency height. -/
structure Catalogue (N : Nat) where
  /-- Objects that must be known before importing each object. -/
  dependencies : Fin N → List (Fin N)
  /-- Well-founded height ordering each object's dependencies. -/
  height : Fin N → Nat
  earlier : ∀ i j, j ∈ dependencies i → height j < height i
  /-- Authentication result for each retained public object. -/
  verified : Fin N → Bool

/-- Import an authenticated object only after all its dependencies are known. -/
def importOne (c : Catalogue N) (known : Fin N → Bool) (i : Fin N) : Fin N → Bool :=
  if c.verified i && (c.dependencies i).all known then setAt known i true else known

theorem import_preserves (c : Catalogue N) (known : Fin N → Bool) (i j : Fin N)
    (old : known j = true) : importOne c known i j = true := by
  unfold importOne
  split
  · by_cases ji : j = i <;> simp_all [setAt]
  · exact old

theorem import_ready (c : Catalogue N) (known : Fin N → Bool) (i : Fin N)
    (verified : c.verified i = true) (dependencies : ∀ j ∈ c.dependencies i, known j = true) :
    importOne c known i i = true := by
  have all : (c.dependencies i).all known = true := List.all_eq_true.mpr dependencies
  simp [importOne, verified, all, setAt]

/-- Newly imported data cannot bypass authentication or unresolved prerequisites. -/
theorem import_requires (c : Catalogue N) (known : Fin N → Bool) (i : Fin N)
    (absent : known i = false) (imported : importOne c known i i = true) :
    c.verified i = true ∧ ∀ j ∈ c.dependencies i, known j = true := by
  unfold importOne at imported
  split at imported
  next allowed =>
    have parts := Bool.and_eq_true_iff.mp allowed
    exact ⟨parts.1, List.all_eq_true.mp parts.2⟩
  next disabled => simp [absent] at imported

/-- The executable queue tries its head, then retains it behind finite arrivals. -/
structure Execution (c : Catalogue N) where
  /-- Concrete retained retry jobs and finite arrivals. -/
  queue : Queue (Fin N)
  /-- Objects successfully imported at each completed worker tick. -/
  known : Nat → Fin N → Bool
  step : ∀ n, known (n+1) = match (queue.pending n).head? with
    | none => known n
    | some i => importOne c (known n) i

theorem Execution.monotone (e : Execution c) (n : Nat) (i : Fin N)
    (old : e.known n i = true) : e.known (n+1) i = true := by
  rw [e.step]
  cases head : (e.queue.pending n).head? with
  | none => exact old
  | some j => exact import_preserves c (e.known n) j i old

private theorem finite_ready (xs : List α) (p : Nat → α → Prop)
    (each : ∀ x ∈ xs, ∃ t, ∀ n, t ≤ n → p n x) :
    ∃ t, ∀ n, t ≤ n → ∀ x ∈ xs, p n x := by
  induction xs with
  | nil => exact ⟨0, by simp⟩
  | cons x xs ih =>
    obtain ⟨a, ha⟩ := each x (by simp)
    obtain ⟨b, hb⟩ := ih (fun y hy => each y (by simp [hy]))
    refine ⟨max a b, ?_⟩
    intro n hn y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ha n (by omega)
    · exact hb n (by omega) y hy

/-- Lower dependencies become known by induction; the actual retry algorithm
then services the ready node. No opaque ready-action premise is assumed. -/
theorem eventually_known (e : Execution c)
    (verified : ∀ i, c.verified i = true)
    (admitted : ∀ i, ∃ n, i ∈ e.queue.pending n) (i : Fin N) :
    ∃ t, ∀ n, t ≤ n → e.known n i = true := by
  have byHeight : ∀ h i, c.height i = h → ∃ t, ∀ n, t ≤ n → e.known n i = true := by
    intro h
    induction h using Nat.strongRecOn with
    | ind h ih =>
      intro i hi
      have deps : ∀ j ∈ c.dependencies i, ∃ t, ∀ n, t ≤ n → e.known n j = true := by
        intro j hj
        exact ih (c.height j) (by have lt := c.earlier i j hj; omega) j rfl
      obtain ⟨start, ready⟩ := finite_ready (c.dependencies i) (fun n j => e.known n j = true) deps
      obtain ⟨n, hn, head⟩ := Scheduler.admitted_revisited e.queue i (admitted i) start
      have imported : e.known (n+1) i = true := by
        rw [e.step, head]
        exact import_ready c (e.known n) i (verified i) (ready n hn)
      exact ⟨n+1, persists _ (fun n => e.monotone n i) imported⟩
  exact byHeight (c.height i) i rfl

theorem finite_closure {c : Catalogue N} (e : Execution c)
    (verified : ∀ i, c.verified i = true)
    (admitted : ∀ i, ∃ n, i ∈ e.queue.pending n) :
    ∃ t, ∀ n, t ≤ n → ∀ i, e.known n i = true := by
  obtain ⟨t, ht⟩ := finite_ready (List.finRange N) (fun n i => e.known n i = true)
    (fun i _ => eventually_known e verified admitted i)
  exact ⟨t, fun n hn i => ht n hn i (by simp)⟩

/-- Observed completion may retire stale work; an unreceived quorum may not. -/
structure RetiringExecution (c : Catalogue N) where
  /-- Retained dependency work scheduled before observed completion. -/
  queue : Queue (Fin N)
  /-- Objects actually imported before work may retire. -/
  known : Nat → Fin N → Bool
  /-- Whether the owner has received and verified completion evidence. -/
  observedDone : Nat → Bool
  retained : ∀ n, observedDone n = true → observedDone (n+1) = true
  step : ∀ n, known (n+1) = if observedDone n then known n else
    match (queue.pending n).head? with
    | none => known n
    | some i => importOne c (known n) i

theorem observed_or_closure (e : RetiringExecution c)
    (verified : ∀ i, c.verified i = true)
    (admitted : ∀ i, ∃ n, i ∈ e.queue.pending n) :
    ∃ t, ∀ n, t ≤ n → e.observedDone n = true ∨ ∀ i, e.known n i = true := by
  classical
  by_cases done : ∃ n, e.observedDone n = true
  · obtain ⟨t, ht⟩ := done
    exact ⟨t, fun n hn => Or.inl (persists _ e.retained ht n hn)⟩
  · have absent : ∀ n, e.observedDone n = false := by
      intro n; cases h : e.observedDone n <;> simp_all
    let ongoing : Execution c := ⟨e.queue, e.known, by intro n; simpa [absent n] using e.step n⟩
    obtain ⟨t, ht⟩ := finite_closure ongoing verified admitted
    exact ⟨t, fun n hn => Or.inr (ht n hn)⟩
end Retry

/-- These are owner-received authenticated signatures. Honest delivery nodes
suffice, with no assumption that Byzantine signatures are delivered. -/
theorem eventually_observed_quorum
    (protocol : MultiParent.Config V T R f)
    (catalogue : Retry.Catalogue N) (e : Retry.RetiringExecution catalogue)
    (received : Nat → Nat → Bool) (voteNode : Nat → Fin N)
    (verified : ∀ i, catalogue.verified i = true)
    (admitted : ∀ i, ∃ n, i ∈ e.queue.pending n)
    (observation : ∀ n, e.observedDone n = MultiParent.quorum protocol (received n))
    (delivered : ∀ n w, w ∈ protocol.committee.core → e.known n (voteNode w) = true → received n w = true) :
    ∃ t, ∀ n, t ≤ n → MultiParent.quorum protocol (received n) = true := by
  obtain ⟨t, ht⟩ := Retry.observed_or_closure e verified admitted
  refine ⟨t, fun n hn => ?_⟩
  rcases ht n hn with observed | complete
  · simpa [observation n] using observed
  · exact core_forms_quorum protocol (received n) (fun w hw => delivered n w hw (complete _))


namespace Witness
open Retry
/-- Reversed evidence order: root prerequisite, child, then dependent vote delivery. -/
def chain : Retry.Catalogue 3 where
  dependencies i := if i.val = 0 then [] else if i.val = 1 then [0] else [1]
  height := Fin.val
  earlier := by
    intro i j hj
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hi with rfl | rfl | rfl <;> simp at hj
    · subst j; decide
    · subst j; decide
  verified := fun _ => true

/-- Pending reversed-chain retry jobs at each witness tick. -/
def pendingAt : Nat → List (Fin 3) :=
  Nat.rec [2, 1, 0] (fun _ pending => Scheduler.advance pending [])
/-- Objects imported by the reversed-chain witness at each tick. -/
def knownAt : Nat → Fin 3 → Bool :=
  Nat.rec (fun _ => false) (fun n previous => match (pendingAt n).head? with
    | none => previous
    | some i => importOne chain previous i)

/-- Executable retry trace that imports the reversed dependency chain. -/
def retry : Retry.Execution chain where
  queue := ⟨pendingAt, fun _ => [], fun _ => rfl⟩
  known := knownAt
  step := by
    intro n
    funext i
    cases h : (pendingAt n).head? <;> simp [knownAt, h]

example : knownAt 6 2 = false ∧ knownAt 7 2 = true := by decide
example : ∀ i, knownAt 7 i = true := by decide
example : ∃ t, ∀ n, t ≤ n → ∀ i, retry.known n i = true := by
  apply finite_closure retry (by decide)
  intro i
  refine ⟨0, ?_⟩
  have casesI : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases casesI with rfl | rfl | rfl <;> decide

/-- A real observed early QC may retire stale jobs without an honest third vote.
The global/private and owner-received vote sets are explicitly different. -/
def protocol := OwnedLifecycle.Witness.unit.old
/-- Early quorum votes from two honest validators and one Byzantine validator. -/
def earlyVotes (w : Nat) : Bool := decide (w = 0 ∨ w = 1 ∨ w = 3)
/-- A globally formed quorum whose signatures need not reach the owner. -/
def privateVotes (w : Nat) : Bool := decide (w = 0 ∨ w = 1 ∨ w = 3)
/-- Owner receipt of only the two honest signatures from a private quorum. -/
def onlyTwoReceived (w : Nat) : Bool := decide (w = 0 ∨ w = 1)
example : MultiParent.quorum protocol privateVotes = true ∧
    MultiParent.quorum protocol onlyTwoReceived = false := by decide
example : MultiParent.quorum protocol earlyVotes = true ∧ earlyVotes 2 = false := by decide
example : MultiParent.quorum protocol (fun w => decide (w ≤ 2)) = true := by decide

/-- Retry trace in which observed completion legitimately retires old work. -/
def earlyRetirement : Retry.RetiringExecution chain where
  queue := retry.queue
  known := fun _ _ => false
  observedDone := fun n => decide (1 ≤ n)
  retained := by intro n h; exact decide_eq_true (by have := of_decide_eq_true h; omega)
  step := by
    intro n
    cases n with
    | zero => rfl
    | succ n => simp

example : earlyRetirement.observedDone 1 = true ∧ earlyRetirement.known 100 2 = false := by decide
example : ∃ t, ∀ n, t ≤ n → earlyRetirement.observedDone n = true ∨
    ∀ i, earlyRetirement.known n i = true := by
  apply observed_or_closure earlyRetirement (by decide)
  intro i
  refine ⟨0, ?_⟩
  have casesI : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases casesI with rfl | rfl | rfl <;> decide
end Witness

end CBCL.ConsensusFree.OwnedProgress
