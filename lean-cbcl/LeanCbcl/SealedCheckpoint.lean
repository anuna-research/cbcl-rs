import LeanCbcl.ValidatorBudget

/-! SPEC-022 local transition and accounting core. No extraction or complete
asynchronous refinement is claimed. Quorum/report premises remain explicit. -/
namespace CBCL.SealedCheckpoint

open CBCL.ValidatorBudget

theorem disjoint_vote_bound (ws : List Nat) (a b : Nat → Bool)
    (disjoint : ∀ w ∈ ws, ¬ (a w = true ∧ b w = true)) :
    voteCount ws a + voteCount ws b ≤ ws.length := by
  induction ws with
  | nil => simp [voteCount, sumOn]
  | cons w ws ih =>
      have hw := disjoint w (by simp)
      have tailBound := ih (fun x hx => disjoint x (by simp [hx]))
      simp only [voteCount, sumOn_cons, List.length_cons] at *
      cases ha : a w <;> cases hb : b w <;> simp_all <;> omega

/-- Both quorums share a witness in the arbitrary honest core. -/
theorem honest_intersection (c : Committee f) (a b : Nat → Bool)
    (qa : 2*f+1 ≤ voteCount (c.core ++ c.others) a)
    (qb : 2*f+1 ≤ voteCount (c.core ++ c.others) b) :
    ∃ w ∈ c.core, a w = true ∧ b w = true := by
  classical
  apply Classical.byContradiction
  intro absent
  have disjoint : ∀ w ∈ c.core, ¬ (a w = true ∧ b w = true) := by
    intro w hw both
    exact absent ⟨w, hw, both⟩
  have bound := disjoint_vote_bound c.core a b disjoint
  have ha := quorum_coverage c a qa
  have hb := quorum_coverage c b qb
  rw [c.core_size] at bound
  omega

structure Journal where
  spent : Nat
  capacity : Nat
  frozen : Bool

inductive Step : Journal → Journal → Prop where
  | sign (s : Journal) (amount : Nat) (openEpoch : s.frozen = false)
      (affordable : s.spent + amount ≤ s.capacity) :
      Step s { s with spent := s.spent + amount }
  | freeze (s : Journal) : Step s { s with frozen := true }
  | replay (s : Journal) : Step s s

inductive Reach (initial : Journal) : Journal → Prop where
  | start : Reach initial initial
  | next : Reach initial s → Step s t → Reach initial t

theorem step_capacity (h : Step s t) : t.capacity = s.capacity := by
  cases h <;> rfl

theorem step_bounded (bounded : s.spent ≤ s.capacity) (h : Step s t) :
    t.spent ≤ t.capacity := by
  cases h with
  | sign _ _ affordable => exact affordable
  | freeze => exact bounded
  | replay => exact bounded

theorem reachable_bounded (bounded : initial.spent ≤ initial.capacity)
    (h : Reach initial s) : s.spent ≤ initial.capacity := by
  have aux : ∀ t, Reach initial t → t.spent ≤ t.capacity ∧ t.capacity = initial.capacity := by
    intro t ht
    induction ht with
    | start => exact ⟨bounded, rfl⟩
    | next _ step ih => exact ⟨step_bounded ih.1 step, (step_capacity step).trans ih.2⟩
  obtain ⟨hb, hc⟩ := aux s h
  omega

theorem frozen_step (frozen : s.frozen = true) (h : Step s t) :
    t.frozen = true ∧ t.spent = s.spent := by
  cases h with
  | sign _ openEpoch _ => simp [frozen] at openEpoch
  | freeze => exact ⟨rfl, rfl⟩
  | replay => exact ⟨frozen, rfl⟩

theorem frozen_journal (frozen : initial.frozen = true) (h : Reach initial s) :
    s.frozen = true ∧ s.spent = initial.spent := by
  induction h with
  | start => exact ⟨frozen, rfl⟩
  | next _ step ih =>
      obtain ⟨hf, hs⟩ := frozen_step ih.1 step
      exact ⟨hf, hs.trans ih.2⟩

/-- Applies separately to rights and headroom. The capacity and complete-cut
premises must still be derived for the full distributed lifecycle. -/
theorem finalized_nonnegative
    (initial actualCredits checkpointCredits charged priorCost currentCost allocation : Int)
    (credits : checkpointCredits ≤ actualCredits)
    (carried : priorCost ≤ charged)
    (books : allocation = initial + checkpointCredits - charged)
    (epochBound : currentCost ≤ allocation) :
    0 ≤ initial + actualCredits - priorCost - currentCost := by omega

theorem unique_successor {Witness Statement : Type}
    (votes : Witness → Statement → Prop) (honest : Witness → Prop)
    (once : ∀ w, honest w → ∀ a b, votes w a → votes w b → a = b)
    (a b : Statement)
    (intersection : ∃ w, honest w ∧ votes w a ∧ votes w b) : a = b := by
  obtain ⟨w, hw, ha, hb⟩ := intersection
  exact once w hw a b ha hb

theorem late_certificate_carried {Witness Tx : Type}
    (signed report : Witness → Tx → Prop) (held : Tx → Prop) (tx : Tx)
    (shared : ∃ w, signed w tx ∧ (∀ t, signed w t → report w t) ∧
      (∀ t, report w t → held t)) : held tx := by
  obtain ⟨w, hs, complete, included⟩ := shared
  exact included tx (complete tx hs)

example : (30 : Int) - (10 + 10 + 10) = 0 := by decide
example : ¬ ((3 : Int) ≤ 30 - (10 + 10 + 10)) := by decide

end CBCL.SealedCheckpoint
