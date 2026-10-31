import LeanCbcl.ConsensusFree.Capacity

namespace CBCL.ConsensusFree
open CBCL.ValidatorBudget CBCL.SealedCheckpoint
variable {A T P R f : Nat}

/-- Ghost balances equal genesis plus credits minus debits of final operations. -/
def Observed (c : Config A T P R f) (s : State A T P R) : Prop :=
  ∀ d, s.balance d = (c.initial d : Int) +
    isum (List.finRange T) (fun tx => if finalCert c s tx then (c.credit tx d : Int) else 0) -
    isum (List.finRange T) (fun tx => if finalCert c s tx then (c.cost tx d : Int) else 0)

theorem effect_final_other (c : Config A T P R f) (s : State A T P R) (tx u : Fin T) (w : Nat)
    (different : u ≠ tx) : finalCert c (emit s tx w) u = finalCert c s u := by
  simp [finalCert, emit, two, setAt, different]

theorem effect_final_mono (c : Config A T P R f) (s : State A T P R) (tx : Fin T) (w : Nat) :
    finalCert c s tx = true → finalCert c (emit s tx w) tx = true :=
  quorum_mono c _ _ (two_mono s.effects tx w tx)

theorem newly_final_data {c : Config A T P R f} {s : State A T P R} {tx : Fin T} {w : Nat}
    (h : newlyFinal c s tx w = true) :
    finalCert c s tx = false ∧ finalCert c (emit s tx w) tx = true := by simpa [newlyFinal] using h

theorem final_rows_new {c : Config A T P R f} {s : State A T P R} {tx : Fin T} {w : Nat}
    (new : newlyFinal c s tx w = true) (weight : Fin T → Int) :
    (fun u => if finalCert c (emit s tx w) u then weight u else 0) =
      setAt (fun u => if finalCert c s u then weight u else 0) tx (weight tx) := by
  funext u
  by_cases same : u = tx
  · subst u; simp [(newly_final_data new).2, setAt]
  · simp [effect_final_other c s tx u w same, setAt, same]

theorem final_rows_same {c : Config A T P R f} {s : State A T P R} {tx : Fin T} {w : Nat}
    (notNew : newlyFinal c s tx w ≠ true) : ∀ u, finalCert c (emit s tx w) u = finalCert c s u := by
  intro u
  by_cases same : u = tx
  · subst u
    have mono := effect_final_mono c s tx w
    cases old : finalCert c s tx <;> cases new : finalCert c (emit s tx w) tx <;>
      simp_all [newlyFinal]
  · exact effect_final_other c s tx u w same

theorem step_observed {c : Config A T P R f} {s t : State A T P R} {label}
    (h : Observed c s) (step : Step c s label t) : Observed c t := by
  cases step with
  | effect tx w member allowed =>
      by_cases new : newlyFinal c s tx w = true
      · intro d
        rw [effect, if_pos new]
        change s.balance d + (c.credit tx d : Int) - (c.cost tx d : Int) = (c.initial d : Int) +
          isum (List.finRange T) (fun u => if finalCert c (emit s tx w) u then (c.credit u d : Int) else 0) -
          isum (List.finRange T) (fun u => if finalCert c (emit s tx w) u then (c.cost u d : Int) else 0)
        rw [final_rows_new new, final_rows_new new]
        rw [isum_update _ _ _ _ (finRange_unique T) (List.mem_finRange tx)]
        rw [isum_update _ _ _ _ (finRange_unique T) (List.mem_finRange tx)]
        simp only [(newly_final_data new).1, Bool.false_eq_true, ↓reduceIte]
        have old := h d
        omega
      · intro d
        rw [effect, if_neg new]
        change s.balance d = (c.initial d : Int) +
          isum (List.finRange T) (fun u => if finalCert c (emit s tx w) u then (c.credit u d : Int) else 0) -
          isum (List.finRange T) (fun u => if finalCert c (emit s tx w) u then (c.cost u d : Int) else 0)
        simp only [final_rows_same new]
        exact h d
  | sign => exact h
  | freeze => exact h
  | release => exact h
  | endorse => exact h
  | record => exact h
  | install => exact h
  | receiveOperation => exact h
  | receiveFinal => exact h
  | fence => exact h
  | replay => exact h

theorem quorum_empty (c : Config A T P R f) : quorum c (fun _ => false) = false := by
  have zero : ∀ xs : List Nat, voteCount xs (fun _ => false) = 0 := by
    intro xs
    induction xs with
    | nil => rfl
    | cons x xs ih => simpa [voteCount, sumOn] using ih
  simp [quorum, zero]

theorem sumOn_zero (xs : List α) : sumOn xs (fun _ => 0) = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [sumOn, ih]

theorem isum_zero (xs : List α) : isum xs (fun _ => 0) = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [isum, ih]

/-- Joint journal, archive, local-state, capacity and observation invariant. -/
structure Invariant (c : Config A T P R f) (s : State A T P R) : Prop where
  evidence : Evidence c s
  catalogue : Catalogue c s
  locals : Locals c s
  capacity : Capacity c s
  observed : Observed c s

theorem initial_invariant (c : Config A T P R f) : Invariant c (initial c) := by
  have slots : ∀ a n e, (initial c).archive a n = some e → n = 0 ∧ e = .root a := by
    intro a n e slot
    by_cases zero : n = 0
    · subst n; exact ⟨rfl, by simpa [initial] using slot.symm⟩
    · simp [initial, zero] at slot
  have noCheckpoint : ∀ p, ¬ Known c (initial c) (.checkpoint p) := by
    intro p known
    have data := slots _ _ _ known
    have eq := data.2
    cases eq
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · intro tx w _; simp [initial]
    · intro tx w _ impossible; simp [initial] at impossible
    · intro tx w _ impossible; simp [initial] at impossible
    · intro tx w _ impossible; simp [initial] at impossible
    · intro tx w impossible; simp [initial] at impossible
    · intro tx w impossible; simp [initial] at impossible
    · intro tx w _ impossible; simp [initial] at impossible
    · intro p w _ impossible; simp [initial] at impossible
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro a n e slot; rw [(slots a n e slot).2]; rfl
    · intro a n e slot; rw [(slots a n e slot).2, (slots a n e slot).1]; rfl
    · intro p known; exact False.elim (noCheckpoint p known)
    · intro p known; exact False.elim (noCheckpoint p known)
    · intro a n below
      have zero : n = 0 := by simpa [initial] using Nat.le_zero.mp below
      subst n; exact ⟨.root a, by simp [initial]⟩
    · intro a n e slot; rw [(slots a n e slot).1]; exact Nat.zero_le _
  · refine ⟨?_, ?_, ?_⟩
    · intro w a; simp [Known, initial, owner, depth, epochOwner, epochDepth]
    · intro w a; rfl
    · intro p w impossible; simp [initial] at impossible
  · intro e w _ d
    simp [charge, initial, sumOn_zero]
  · intro d
    simp [initial, finalCert, quorum_empty, isum_zero]

theorem step_invariant {c : Config A T P R f} {s t : State A T P R} {label}
    (h : Invariant c s) (step : Step c s label t) : Invariant c t :=
  ⟨step_evidence h.evidence h.locals h.catalogue step,
   step_catalogue h.evidence h.catalogue step,
   step_locals h.locals h.evidence h.catalogue step,
   step_capacity h.capacity step, step_observed h.observed step⟩

end CBCL.ConsensusFree
