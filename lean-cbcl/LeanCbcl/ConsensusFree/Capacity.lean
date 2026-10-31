import LeanCbcl.ConsensusFree.Evidence

namespace CBCL.ConsensusFree
open CBCL.ValidatorBudget CBCL.SealedCheckpoint
variable {A T P R f : Nat}

/-- Every honest validator's scaled outstanding charge fits its epoch allocation. -/
def Capacity (c : Config A T P R f) (s : State A T P R) : Prop :=
  ∀ e w, w ∈ c.committee.core → ∀ d, charge c s e w d ≤ (f+1) * allowance c e d

theorem step_capacity {c : Config A T P R f} {s t : State A T P R} {label}
    (h : Capacity c s) (step : Step c s label t) : Capacity c t := by
  cases step with
  | sign tx w member fresh allowed =>
      intro e v hv d
      by_cases vw : v = w
      · subst v
        by_cases context : e = c.opEpoch tx
        · subst e; exact (allowed hv).2.2.2.2 d
        · apply Nat.le_trans _ (h e w hv d)
          apply sumOn_mono
          intro u _
          by_cases ut : u = tx
          · subst u
            have different : c.opEpoch tx ≠ e := Ne.symm context
            simp [signed, two, setAt, different]
          · simp [signed, two, setAt, ut]
      · apply Nat.le_trans _ (h e v hv d)
        apply sumOn_mono
        intro u _
        by_cases ut : u = tx <;> simp_all [signed, two, setAt]
  | release tx w member reserved certificate =>
      intro e v hv d
      apply Nat.le_trans _ (h e v hv d)
      apply sumOn_mono
      intro u _
      by_cases ut : u = tx
      · subst u
        by_cases vw : v = w <;> simp_all [release, two, setAt]
      · simp [release, two, setAt, ut]
  | effect tx w member allowed => unfold effect; split <;> exact h
  | freeze => exact h
  | endorse => exact h
  | record => exact h
  | install => exact h
  | receiveOperation => exact h
  | receiveFinal => exact h
  | fence => exact h
  | replay => exact h

theorem sumOn_filter (xs : List α) (predicate : α → Bool) (weight : α → Nat) :
    sumOn (xs.filter predicate) weight = sumOn xs (fun x => if predicate x then weight x else 0) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      cases hp : predicate x <;> simp [List.filter, hp, sumOn, ih]

/-- The earlier fixed-epoch theorem, generalized to typed transaction IDs. -/
theorem certified_bound (committee : Committee f) (txs : List α)
    (amount : α → Nat) (votes : α → Nat → Bool) (allocation : Nat)
    (quorums : ∀ tx ∈ txs, 2*f+1 ≤ voteCount (committee.core ++ committee.others) (votes tx))
    (columns : ∀ w ∈ committee.core, sumOn txs
      (fun tx => if votes tx w then (2*f+1) * amount tx else 0) ≤ (f+1) * allocation) :
    sumOn txs amount ≤ allocation := by
  let charged := fun tx w => if votes tx w then (2*f+1) * amount tx else 0
  have rows : (f+1) * ((2*f+1) * sumOn txs amount) ≤
      sumOn txs (fun tx => sumOn committee.core (charged tx)) := by
    rw [← sumOn_mul, ← sumOn_mul]
    exact sumOn_mono _ _ _ (fun tx ht => certificate_charge committee (votes tx) (amount tx) (quorums tx ht))
  rw [sumOn_swap] at rows
  have bound := sumOn_bound committee.core (fun w => sumOn txs (fun tx => charged tx w))
    ((f+1) * allocation) columns
  rw [committee.core_size] at bound
  have total : (f+1) * ((2*f+1) * sumOn txs amount) ≤ (f+1) * ((2*f+1) * allocation) := by
    calc
      _ ≤ _ := rows
      _ ≤ _ := bound
      _ = _ := by ac_rfl
  exact Nat.le_of_mul_le_mul_left (Nat.le_of_mul_le_mul_left total (by omega)) (by omega)

/-- Whether an operation is final and originates in the specified epoch. -/
def currentFinal (c : Config A T P R f) (s : State A T P R) (e : Epoch A P) (tx : Fin T) : Bool :=
  finalCert c s tx && decide (c.opEpoch tx = e)

theorem epoch_final_consumption {c : Config A T P R f} {s : State A T P R}
    (ev : Evidence c s) (capacity : Capacity c s) (e : Epoch A P) (d : Fin R) :
    sumOn ((List.finRange T).filter (currentFinal c s e)) (fun tx => c.cost tx d) ≤ allowance c e d := by
  apply certified_bound c.committee _ _ s.signatures
  · intro tx member
    have filtered := (List.mem_filter.mp member).2
    have final : finalCert c s tx = true := by simpa [currentFinal] using (Bool.and_eq_true_iff.mp filtered).1
    exact of_decide_eq_true (final_operation ev tx final)
  · intro w hw
    apply Nat.le_trans _ (capacity e w hw d)
    rw [sumOn_filter]
    apply sumOn_mono
    intro tx _
    by_cases relevant : currentFinal c s e tx = true
    · have data : finalCert c s tx = true ∧ c.opEpoch tx = e := by simpa [currentFinal] using relevant
      have neverReleased : s.released tx w = false := by
        cases released : s.released tx w with
        | false => rfl
        | true => exact False.elim (final_cancel_exclusive ev tx ⟨data.1, ev.released_cancel tx w hw released⟩)
      simp [relevant, data.2, neverReleased]
    · simp [relevant]

end CBCL.ConsensusFree
