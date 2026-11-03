import LeanCbcl.ConsensusFree.Core

namespace CBCL.ConsensusFree
open CBCL.ValidatorBudget CBCL.SealedCheckpoint
variable {A T P R f : Nat}

theorem two_mono [DecidableEq α] [DecidableEq β] (fn : α → β → Bool) (a : α) (b : β) :
    ∀ x y, fn x y = true → two fn a b true x y = true := by
  intro x y h
  by_cases ha : x = a <;> by_cases hb : y = b <;> simp_all [two, setAt]

theorem quorum_mono (c : Config A T P R f) (a b : Nat → Bool)
    (extension : ∀ w, a w = true → b w = true) : quorum c a = true → quorum c b = true := by
  intro ha
  have count : voteCount (c.committee.core ++ c.committee.others) a ≤
      voteCount (c.committee.core ++ c.committee.others) b := by
    apply sumOn_mono
    intro w _
    cases ha : a w <;> cases hb : b w <;> simp_all
  have qa := of_decide_eq_true ha
  apply decide_eq_true
  omega

theorem quorum_has_core (c : Config A T P R f) (votes : Nat → Bool) (hq : quorum c votes = true) :
    ∃ w ∈ c.committee.core, votes w = true := by
  have coverage := quorum_coverage c.committee votes (of_decide_eq_true hq)
  apply Classical.byContradiction
  intro absent
  have zero : voteCount c.committee.core votes = 0 := by
    have same : ∀ w ∈ c.committee.core, votes w = false := by
      intro w hw
      cases he : votes w with
      | false => rfl
      | true => exact False.elim (absent ⟨w, hw, he⟩)
    have bound := sumOn_bound c.committee.core (fun w => if votes w then 1 else 0) 0
      (fun w hw => by simp [same w hw])
    simpa [voteCount] using Nat.le_zero.mp (by simpa using bound)
  omega

/-- Persistent signature, effect and cancellation evidence grows monotonically. -/
structure JournalExtension (s t : State A T P R) : Prop where
  signatures : ∀ tx w, s.signatures tx w = true → t.signatures tx w = true
  effects : ∀ tx w, s.effects tx w = true → t.effects tx w = true
  fences : ∀ tx w, s.fences tx w = true → t.fences tx w = true
  votes : ∀ p w, s.votes p w = true → t.votes p w = true
  seals : ∀ e w, s.sealed e w = true → t.sealed e w = true

private theorem extension_refl (s : State A T P R) : JournalExtension s s :=
  ⟨fun _ _ h => h, fun _ _ h => h, fun _ _ h => h, fun _ _ h => h, fun _ _ h => h⟩

theorem step_journals {c : Config A T P R f} {s t : State A T P R} {label}
    (step : Step c s label t) : JournalExtension s t := by
  cases step with
  | sign tx w member fresh allowed =>
      exact ⟨two_mono _ tx w, fun _ _ h => h, fun _ _ h => h, fun _ _ h => h, fun _ _ h => h⟩
  | freeze e w member =>
      exact ⟨fun _ _ h => h, fun _ _ h => h, fun _ _ h => h, fun _ _ h => h, two_mono _ e w⟩
  | release => exact ⟨fun _ _ h => h, fun _ _ h => h, fun _ _ h => h, fun _ _ h => h, fun _ _ h => h⟩
  | endorse p w member allowed =>
      exact ⟨fun _ _ h => h, fun _ _ h => h, fun _ _ h => h, two_mono _ p w, fun _ _ h => h⟩
  | record => exact ⟨fun _ _ h => h, fun _ _ h => h, fun _ _ h => h, fun _ _ h => h, fun _ _ h => h⟩
  | install => exact ⟨fun _ _ h => h, fun _ _ h => h, fun _ _ h => h, fun _ _ h => h, fun _ _ h => h⟩
  | receiveOperation => exact ⟨fun _ _ h => h, fun _ _ h => h, fun _ _ h => h, fun _ _ h => h, fun _ _ h => h⟩
  | receiveFinal => exact ⟨fun _ _ h => h, fun _ _ h => h, fun _ _ h => h, fun _ _ h => h, fun _ _ h => h⟩
  | fence tx w member allowed =>
      exact ⟨fun _ _ h => h, fun _ _ h => h, two_mono _ tx w, fun _ _ h => h, fun _ _ h => h⟩
  | effect tx w member allowed =>
      have raw : JournalExtension s (emit s tx w) :=
        ⟨fun _ _ h => h, two_mono _ tx w, fun _ _ h => h, fun _ _ h => h, fun _ _ h => h⟩
      unfold effect
      split <;> exact ⟨raw.signatures, raw.effects, raw.fences, raw.votes, raw.seals⟩
  | replay => exact ⟨fun _ _ h => h, fun _ _ h => h, fun _ _ h => h, fun _ _ h => h, fun _ _ h => h⟩

/-- Sealing prevents all future fresh signatures in that exact epoch, including
zero-cost operations. No assumption about global resource balances. -/
theorem step_sealed_stable {c : Config A T P R f} {s t : State A T P R} {label}
    (step : Step c s label t) (e : Epoch A P) (w : Nat) (hw : w ∈ c.committee.core)
    (frozen : s.sealed e w = true) (tx : Fin T) (context : c.opEpoch tx = e) :
    t.signatures tx w = s.signatures tx w := by
  cases step with
  | sign u v member fresh allowed =>
      by_cases sameTx : tx = u
      · subst u
        by_cases sameW : w = v
        · subst v
          have openEpoch := (allowed hw).2.2.1
          simp [context, frozen] at openEpoch
        · simp [signed, two, setAt, sameW]
      · simp [signed, two, setAt, sameTx]
  | effect u v member allowed => unfold effect; split <;> rfl
  | freeze => rfl
  | release => rfl
  | endorse => rfl
  | record => rfl
  | install => rfl
  | receiveOperation => rfl
  | receiveFinal => rfl
  | fence => rfl
  | replay => rfl

theorem reporter_persistent {c : Config A T P R f} {s t : State A T P R} {label}
    (step : Step c s label t) (p : Fin P) (w : Nat) : reporter c s p w = true → reporter c t p w = true := by
  intro old
  have pair : s.sealed (c.checkpoints p).parent w = true ∧
      (w ∈ c.committee.core → Fits c s p w) := by
    have decomposed : s.sealed (c.checkpoints p).parent w = true ∧
        decide (w ∈ c.committee.core → Fits c s p w) = true := by
      simpa only [reporter, Bool.and_eq_true_iff] using old
    exact ⟨decomposed.1, of_decide_eq_true decomposed.2⟩
  have newer := (step_journals step).seals _ _ pair.1
  simp only [reporter, newer, Bool.true_and, decide_eq_true_eq]
  intro hw tx context signature
  apply pair.2 hw tx context
  rw [← step_sealed_stable step _ w hw pair.1 tx context]
  exact signature

/-- Honest journals obey authentication, epoch knowledge and vote exclusion. -/
structure Evidence (c : Config A T P R f) (s : State A T P R) : Prop where
  discipline : ∀ tx w, w ∈ c.committee.core → ¬ (s.effects tx w = true ∧ s.fences tx w = true)
  signature_known : ∀ tx w, w ∈ c.committee.core → s.signatures tx w = true → Known c s (c.opEpoch tx)
  signature_auth : ∀ tx w, w ∈ c.committee.core → s.signatures tx w = true → c.authorized tx = true
  effect_operation : ∀ tx w, w ∈ c.committee.core → s.effects tx w = true → operationCert c s tx = true
  received_operation : ∀ tx w, s.seenOperation tx w = true → operationCert c s tx = true
  received_final : ∀ tx w, s.seenFinal tx w = true → finalCert c s tx = true
  released_cancel : ∀ tx w, w ∈ c.committee.core → s.released tx w = true → cancelCert c s tx = true
  voted_choice : ∀ p w, w ∈ c.committee.core → s.votes p w = true →
    s.choices (c.checkpoints p).parent w = some p

theorem final_cancel_exclusive {c : Config A T P R f} {s : State A T P R}
    (h : Evidence c s) (tx : Fin T) : ¬ (finalCert c s tx = true ∧ cancelCert c s tx = true) := by
  intro ⟨he, hf⟩
  obtain ⟨w, hw, vote, fenced⟩ := honest_intersection c.committee _ _
    (of_decide_eq_true he) (of_decide_eq_true hf)
  exact h.discipline tx w hw ⟨vote, fenced⟩

theorem final_operation {c : Config A T P R f} {s : State A T P R}
    (h : Evidence c s) (tx : Fin T) (finalized : finalCert c s tx = true) : operationCert c s tx = true := by
  obtain ⟨w, hw, vote⟩ := quorum_has_core c _ finalized
  exact h.effect_operation tx w hw vote

theorem operation_known {c : Config A T P R f} {s : State A T P R}
    (h : Evidence c s) (tx : Fin T) (cert : operationCert c s tx = true) : Known c s (c.opEpoch tx) := by
  obtain ⟨w, hw, vote⟩ := quorum_has_core c _ cert
  exact h.signature_known tx w hw vote

theorem checkpoint_unique {c : Config A T P R f} {s : State A T P R} (h : Evidence c s)
    (p q : Fin P) (first : checkpointCert c s p = true) (second : checkpointCert c s q = true)
    (sameParent : (c.checkpoints p).parent = (c.checkpoints q).parent) : p = q := by
  obtain ⟨w, hw, vp, vq⟩ := honest_intersection c.committee _ _
    (of_decide_eq_true first) (of_decide_eq_true second)
  have a := h.voted_choice p w hw vp
  have b := h.voted_choice q w hw vq
  rw [sameParent] at a
  exact Option.some.inj (a.symm.trans b)

end CBCL.ConsensusFree
