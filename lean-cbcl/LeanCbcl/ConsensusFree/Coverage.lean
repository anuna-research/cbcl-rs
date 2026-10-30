import LeanCbcl.ConsensusFree.Observation

namespace CBCL.ConsensusFree
open CBCL.ValidatorBudget CBCL.SealedCheckpoint
variable {A T P R f : Nat}

/-- Every old operation that can still form an operation certificate is carried
in every later known epoch. Includes released signatures and delayed assembly. -/
theorem old_operation_held {c : Config A T P R f} {s : State A T P R}
    (ev : Evidence c s) (cat : Catalogue c s) (tx : Fin T) (cert : operationCert c s tx = true)
    (e : Epoch A P) (known : Known c s e) (source : owner c (c.opEpoch tx) = owner c e)
    (older : depth c (c.opEpoch tx) < depth c e) : held c e tx = true := by
  have main : ∀ n (g : Epoch A P), depth c g = n → Known c s g →
      owner c (c.opEpoch tx) = owner c g → depth c (c.opEpoch tx) < n → held c g tx = true := by
    intro n
    induction n with
    | zero => intro g height _ _ impossible; omega
    | succ n ih =>
        intro g height current sameOwner less
        cases g with
        | root a => have zero : depth c (.root a) = 0 := rfl; omega
        | checkpoint p =>
            have valid := cat.checkpoint_valid p current
            have shape := static_facts valid.1
            have parentHeight : depth c (c.checkpoints p).parent = n := by
              have ds := shape.parent_depth
              change (c.checkpoints p).depth = n+1 at height
              omega
            have parentOwner : owner c (c.opEpoch tx) = owner c (c.checkpoints p).parent := by
              rw [shape.parent_owner]; exact sameOwner
            by_cases earlier : depth c (c.opEpoch tx) < n
            · exact shape.inherit_held tx (ih _ parentHeight valid.2.1 parentOwner earlier)
            · have equalDepth : depth c (c.opEpoch tx) = n := by omega
              have parentEq := known_unique (operation_known ev tx cert) valid.2.1 parentOwner
                (equalDepth.trans parentHeight.symm)
              have reports := valid.2.2.1
              obtain ⟨w, hw, signed, reported⟩ := honest_intersection c.committee _ _
                (of_decide_eq_true cert) (of_decide_eq_true reports)
              have data : s.sealed (c.checkpoints p).parent w = true ∧
                  decide (w ∈ c.committee.core → Fits c s p w) = true := by
                simpa only [reporter, Bool.and_eq_true_iff] using reported
              exact (of_decide_eq_true data.2) hw tx parentEq signed
  exact main (depth c e) e rfl known source older

theorem known_refund_cancel {c : Config A T P R f} {s : State A T P R} (cat : Catalogue c s)
    (e : Epoch A P) (known : Known c s e) (tx : Fin T) (refund : refunded c e tx = true) : cancelCert c s tx = true := by
  cases e with
  | root a => simp [refunded] at refund
  | checkpoint p => exact (cat.checkpoint_valid p known).2.2.2.2 tx refund

theorem known_credit_final {c : Config A T P R f} {s : State A T P R} (cat : Catalogue c s)
    (e : Epoch A P) (known : Known c s e) (tx : Fin T) (credit : credited c e tx = true) : finalCert c s tx = true := by
  cases e with
  | root a => simp [credited] at credit
  | checkpoint p => exact (cat.checkpoint_valid p known).2.2.2.1 tx credit

def markedNat (mark : Fin T → Bool) (weight : Fin T → Nat) : Nat :=
  sumOn (List.finRange T) (fun tx => if mark tx then weight tx else 0)

def netHeld (c : Config A T P R f) (e : Epoch A P) (d : Fin R) : Nat :=
  markedNat (fun tx => held c e tx && !refunded c e tx) (fun tx => c.cost tx d)
def epochDebit (c : Config A T P R f) (s : State A T P R) (e : Epoch A P) (d : Fin R) : Nat :=
  sumOn ((List.finRange T).filter (currentFinal c s e)) (fun tx => c.cost tx d)
def totalDebit (c : Config A T P R f) (s : State A T P R) (d : Fin R) : Nat :=
  markedNat (finalCert c s) (fun tx => c.cost tx d)
def totalCredit (c : Config A T P R f) (s : State A T P R) (d : Fin R) : Nat :=
  markedNat (finalCert c s) (fun tx => c.credit tx d)
def manifestCredit (c : Config A T P R f) (e : Epoch A P) (d : Fin R) : Nat :=
  markedNat (credited c e) (fun tx => c.credit tx d)

theorem isum_cast (xs : List α) (weight : α → Nat) :
    isum xs (fun x => (weight x : Int)) = (sumOn xs weight : Int) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [isum, sumOn, ih]

theorem marked_cast (mark : Fin T → Bool) (weight : Fin T → Nat) :
    isum (List.finRange T) (fun tx => if mark tx then (weight tx : Int) else 0) = (markedNat mark weight : Int) := by
  have eq : (fun tx => if mark tx then (weight tx : Int) else 0) =
      (fun tx => ((if mark tx then weight tx else 0 : Nat) : Int)) := by
    funext tx; cases mark tx <;> rfl
  rw [eq, isum_cast]
  rfl

theorem held_net_identity {c : Config A T P R f} {s : State A T P R}
    (cat : Catalogue c s) (e : Epoch A P) (known : Known c s e) (d : Fin R) :
    markedNat (held c e) (fun tx => c.cost tx d) =
      netHeld c e d + markedNat (refunded c e) (fun tx => c.cost tx d) := by
  have subset : ∀ tx, refunded c e tx = true → held c e tx = true := by
    cases e with
    | root a => intro tx impossible; simp [refunded] at impossible
    | checkpoint p => exact (static_facts (cat.checkpoint_valid p known).1).refund_held
  simp only [netHeld, markedNat]
  rw [← sumOn_add]
  apply Nat.le_antisymm
  · apply sumOn_mono
    intro tx _
    have sub := subset tx
    cases ha : held c e tx <;> cases hb : refunded c e tx <;> simp_all
  · apply sumOn_mono
    intro tx _
    have sub := subset tx
    cases ha : held c e tx <;> cases hb : refunded c e tx <;> simp_all

theorem epoch_books {c : Config A T P R f} {s : State A T P R} (cat : Catalogue c s)
    (e : Epoch A P) (known : Known c s e) (d : Fin R) (owned : c.resourceOwner d = owner c e) :
    (allowance c e d : Int) = (c.initial d : Int) + (manifestCredit c e d : Int) - (netHeld c e d : Int) := by
  have heldEq := held_net_identity cat e known d
  cases e with
  | root a =>
      have own : c.resourceOwner d = a := owned
      simp [allowance, manifestCredit, netHeld, held, refunded, credited, markedNat, sumOn_zero, own]
  | checkpoint p =>
      have books := (static_facts (cat.checkpoint_valid p known).1).books d owned
      rw [marked_cast, marked_cast, marked_cast] at books
      change (allowance c (.checkpoint p) d : Int) = (c.initial d : Int) +
        (manifestCredit c (.checkpoint p) d : Int) -
        (markedNat (held c (.checkpoint p)) (fun tx => c.cost tx d) : Int) +
        (markedNat (refunded c (.checkpoint p)) (fun tx => c.cost tx d) : Int) at books
      omega

theorem manifest_credit_bounded {c : Config A T P R f} {s : State A T P R} (cat : Catalogue c s)
    (e : Epoch A P) (known : Known c s e) (d : Fin R) : manifestCredit c e d ≤ totalCredit c s d := by
  apply sumOn_mono
  intro tx _
  by_cases listed : credited c e tx = true
  · have finalized := known_credit_final cat e known tx listed
    simp [listed, finalized]
  · simp [listed]

/-- All past cost is covered by non-refunded manifests; current cost is left
for the independent fixed-epoch double-counting theorem. -/
theorem final_cost_partition {c : Config A T P R f} {s : State A T P R}
    (ev : Evidence c s) (cat : Catalogue c s) (e : Epoch A P) (known : Known c s e)
    (frontier : depth c e = s.frontier (owner c e)) (d : Fin R) (owned : c.resourceOwner d = owner c e) :
    totalDebit c s d ≤ netHeld c e d + epochDebit c s e d := by
  unfold totalDebit netHeld epochDebit markedNat
  rw [sumOn_filter, ← sumOn_add]
  apply sumOn_mono
  intro tx _
  by_cases finalized : finalCert c s tx = true
  · by_cases here : c.opEpoch tx = e
    · simp [currentFinal, finalized, here]
    · by_cases source : c.resourceOwner d = owner c (c.opEpoch tx)
      · have sameOwner : owner c (c.opEpoch tx) = owner c e := source.symm.trans owned
        have cert := final_operation ev tx finalized
        have opKnown := operation_known ev tx cert
        have below := cat.frontier_bound _ _ _ opKnown
        rw [sameOwner, ← frontier] at below
        have earlier : depth c (c.opEpoch tx) < depth c e := by
          by_cases equal : depth c (c.opEpoch tx) = depth c e
          · exact False.elim (here (known_unique opKnown known sameOwner equal))
          · omega
        have carried := old_operation_held ev cat tx cert e known sameOwner earlier
        have notRefunded : refunded c e tx = false := by
          cases flag : refunded c e tx with
          | false => rfl
          | true => exact False.elim (final_cancel_exclusive ev tx
              ⟨finalized, known_refund_cancel cat e known tx flag⟩)
        simp [finalized, carried, notRefunded]
      · have zero := c.cost_local tx d source
        simp [zero]
  · simp [finalized, currentFinal]

theorem resource_nonnegative {c : Config A T P R f} {s : State A T P R} (h : Invariant c s) (d : Fin R) :
    0 ≤ s.balance d := by
  obtain ⟨e, slot⟩ := h.catalogue.hole_free (c.resourceOwner d) (s.frontier (c.resourceOwner d)) (Nat.le_refl _)
  have known := slot_known h.catalogue _ _ e slot
  have ownerEq := h.catalogue.slot_owner _ _ e slot
  have depthEq := h.catalogue.slot_depth _ _ e slot
  have frontier : depth c e = s.frontier (owner c e) := by rw [ownerEq]; exact depthEq
  have owned : c.resourceOwner d = owner c e := ownerEq.symm
  have partition := final_cost_partition h.evidence h.catalogue e known frontier d owned
  have cap := epoch_final_consumption h.evidence h.capacity e d
  have credits := manifest_credit_bounded h.catalogue e known d
  have books := epoch_books h.catalogue e known d owned
  have obs := h.observed d
  rw [marked_cast, marked_cast] at obs
  change s.balance d = (c.initial d : Int) + (totalCredit c s d : Int) - (totalDebit c s d : Int) at obs
  change epochDebit c s e d ≤ allowance c e d at cap
  omega

end CBCL.ConsensusFree
