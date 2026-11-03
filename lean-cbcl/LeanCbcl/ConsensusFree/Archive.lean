import LeanCbcl.ConsensusFree.Journals

namespace CBCL.ConsensusFree
open CBCL.ValidatorBudget CBCL.SealedCheckpoint
variable {A T P R f : Nat}

/-- Static manifest properties extracted from live validity. -/
structure StaticFacts (c : Config A T P R f) (p : Fin P) : Prop where
  authorized : (c.checkpoints p).authorized = true
  parent_owner : owner c (c.checkpoints p).parent = (c.checkpoints p).owner
  parent_depth : (c.checkpoints p).depth = depth c (c.checkpoints p).parent + 1
  inherit_held : ∀ tx, held c (c.checkpoints p).parent tx = true → (c.checkpoints p).held tx = true
  inherit_refunded : ∀ tx, refunded c (c.checkpoints p).parent tx = true → (c.checkpoints p).refunded tx = true
  inherit_credited : ∀ tx, credited c (c.checkpoints p).parent tx = true → (c.checkpoints p).credited tx = true
  refund_held : ∀ tx, (c.checkpoints p).refunded tx = true → (c.checkpoints p).held tx = true
  held_context : ∀ tx, (c.checkpoints p).held tx = true →
    owner c (c.opEpoch tx) = (c.checkpoints p).owner ∧ depth c (c.opEpoch tx) < (c.checkpoints p).depth
  off_source : ∀ d, c.resourceOwner d ≠ (c.checkpoints p).owner → (c.checkpoints p).allocation d = 0
  books : ∀ d, c.resourceOwner d = (c.checkpoints p).owner → ((c.checkpoints p).allocation d : Int) =
    (c.initial d : Int) +
    isum (List.finRange T) (fun tx => if (c.checkpoints p).credited tx then (c.credit tx d : Int) else 0) -
    isum (List.finRange T) (fun tx => if (c.checkpoints p).held tx then (c.cost tx d : Int) else 0) +
    isum (List.finRange T) (fun tx => if (c.checkpoints p).refunded tx then (c.cost tx d : Int) else 0)

theorem static_facts {c : Config A T P R f} {p : Fin P} (h : ManifestStatic c p) : StaticFacts c p := by
  rcases h with ⟨ha, ho, hd, hh, hr, hc, hs, hx, hz, hb⟩
  exact ⟨ha, ho, hd, hh, hr, hc, hs, hx, hz, hb⟩

/-- Every previously recorded archive entry is preserved. -/
def ArchiveExtension (s t : State A T P R) : Prop :=
  ∀ a n e, s.archive a n = some e → t.archive a n = some e

theorem known_extension {c : Config A T P R f} {s t : State A T P R}
    (extension : ArchiveExtension s t) (e : Epoch A P) (known : Known c s e) : Known c t e :=
  extension _ _ e known

theorem known_unique {c : Config A T P R f} {s : State A T P R} {e g : Epoch A P}
    (he : Known c s e) (hg : Known c s g) (ho : owner c e = owner c g) (hd : depth c e = depth c g) : e = g := by
  unfold Known at he hg
  rw [ho, hd] at he
  exact Option.some.inj (he.symm.trans hg)

theorem manifest_persistent {c : Config A T P R f} {s t : State A T P R} {label}
    (step : Step c s label t) (archive : ArchiveExtension s t) (p : Fin P)
    (old : ManifestLive c s p) : ManifestLive c t p := by
  rcases old with ⟨static, parent, reports, credits, refunds⟩
  refine ⟨static, known_extension archive _ parent, ?_, ?_, ?_⟩
  · exact quorum_mono c _ _ (reporter_persistent step p) reports
  · intro tx credited
    exact quorum_mono c _ _ ((step_journals step).effects tx) (credits tx credited)
  · intro tx refunded
    exact quorum_mono c _ _ ((step_journals step).fences tx) (refunds tx refunded)

/-- Archive entries have consistent ownership, depth and live validity. -/
structure Catalogue (c : Config A T P R f) (s : State A T P R) : Prop where
  slot_owner : ∀ a n e, s.archive a n = some e → owner c e = a
  slot_depth : ∀ a n e, s.archive a n = some e → depth c e = n
  checkpoint_valid : ∀ p, Known c s (.checkpoint p) → ManifestLive c s p
  checkpoint_quorum : ∀ p, Known c s (.checkpoint p) → checkpointCert c s p = true
  hole_free : ∀ a n, n ≤ s.frontier a → ∃ e, s.archive a n = some e
  frontier_bound : ∀ a n e, s.archive a n = some e → n ≤ s.frontier a

theorem slot_known {c : Config A T P R f} {s : State A T P R} (h : Catalogue c s)
    (a : Fin A) (n : Nat) (e : Epoch A P) (slot : s.archive a n = some e) : Known c s e := by
  unfold Known
  rw [h.slot_owner a n e slot, h.slot_depth a n e slot]
  exact slot

/-- No first-writer assumption: two certificate-backed records at one slot
must agree, as derived from parent certificates and honest vote-once. -/
theorem certificate_same_slot {c : Config A T P R f} {s : State A T P R}
    (ev : Evidence c s) (cat : Catalogue c s) (e : Epoch A P) (p : Fin P)
    (old : Known c s e) (owners : owner c e = (c.checkpoints p).owner)
    (depths : depth c e = (c.checkpoints p).depth)
    (cert : checkpointCert c s p = true) (valid : ManifestLive c s p) : e = .checkpoint p := by
  have newShape := static_facts valid.1
  cases e with
  | root a =>
      have zero : depth c (.root a) = 0 := rfl
      have successor := newShape.parent_depth
      omega
  | checkpoint q =>
      have oldCert := cat.checkpoint_quorum q old
      have oldValid := cat.checkpoint_valid q old
      have oldShape := static_facts oldValid.1
      have ownerEq : (c.checkpoints q).owner = (c.checkpoints p).owner := owners
      have depthEq : (c.checkpoints q).depth = (c.checkpoints p).depth := depths
      have parentOwner : owner c (c.checkpoints q).parent = owner c (c.checkpoints p).parent := by
        rw [oldShape.parent_owner, newShape.parent_owner, ownerEq]
      have parentDepth : depth c (c.checkpoints q).parent = depth c (c.checkpoints p).parent := by
        have a := oldShape.parent_depth
        have b := newShape.parent_depth
        omega
      have parents := known_unique oldValid.2.1 valid.2.1 parentOwner parentDepth
      exact congrArg Epoch.checkpoint (checkpoint_unique ev q p oldCert cert parents)

theorem record_extension {c : Config A T P R f} {s : State A T P R}
    (ev : Evidence c s) (cat : Catalogue c s) (p : Fin P) (w : Nat)
    (cert : checkpointCert c s p = true) (valid : ManifestLive c s p) : ArchiveExtension s (record c s p w) := by
  intro a n e old
  by_cases account : a = (c.checkpoints p).owner
  · subst a
    by_cases height : n = (c.checkpoints p).depth
    · subst n
      have same := certificate_same_slot ev cat e p (slot_known cat _ _ e old)
        (cat.slot_owner _ _ e old) (cat.slot_depth _ _ e old) cert valid
      subst e
      simp [record, two, setAt]
    · simpa [record, two, setAt, height] using old
  · simpa [record, two, setAt, account] using old

/-- Every other protocol event leaves the archive unchanged. -/
theorem step_archive_extension {c : Config A T P R f} {s t : State A T P R} {label}
    (ev : Evidence c s) (cat : Catalogue c s) (step : Step c s label t) : ArchiveExtension s t := by
  cases step with
  | record p w member cert valid => exact record_extension ev cat p w cert valid
  | effect tx w member allowed => unfold effect; split <;> exact fun _ _ _ h => h
  | sign => exact fun _ _ _ h => h
  | freeze => exact fun _ _ _ h => h
  | release => exact fun _ _ _ h => h
  | endorse => exact fun _ _ _ h => h
  | install => exact fun _ _ _ h => h
  | receiveOperation => exact fun _ _ _ h => h
  | receiveFinal => exact fun _ _ _ h => h
  | fence => exact fun _ _ _ h => h
  | replay => exact fun _ _ _ h => h


theorem record_slot_cases {c : Config A T P R f} {s : State A T P R} (p : Fin P) (w : Nat)
    (a : Fin A) (n : Nat) (e : Epoch A P) (slot : (record c s p w).archive a n = some e) :
    (a = (c.checkpoints p).owner ∧ n = (c.checkpoints p).depth ∧ e = .checkpoint p) ∨ s.archive a n = some e := by
  by_cases account : a = (c.checkpoints p).owner
  · subst a
    by_cases height : n = (c.checkpoints p).depth
    · subst n
      have same : Epoch.checkpoint p = e := by simpa [record, two, setAt] using slot
      exact Or.inl ⟨rfl, rfl, same.symm⟩
    · exact Or.inr (by simpa [record, two, setAt, height] using slot)
  · exact Or.inr (by simpa [record, two, setAt, account] using slot)

theorem record_frontier_mono (c : Config A T P R f) (s : State A T P R) (p : Fin P) (w : Nat) (a : Fin A) :
    s.frontier a ≤ (record c s p w).frontier a := by
  by_cases same : a = (c.checkpoints p).owner
  · subst a; simp only [record, setAt_same]; exact Nat.le_max_left _ _
  · simp [record, setAt, same]

theorem record_catalogue {c : Config A T P R f} {s : State A T P R}
    (ev : Evidence c s) (cat : Catalogue c s) (p : Fin P) (w : Nat) (member : Member c w)
    (cert : checkpointCert c s p = true) (valid : ManifestLive c s p) : Catalogue c (record c s p w) := by
  have extension := record_extension ev cat p w cert valid
  have step := Step.record s p w member cert valid
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a n e slot
    rcases record_slot_cases p w a n e slot with ⟨account, height, same⟩ | old
    · subst e; exact account.symm
    · exact cat.slot_owner a n e old
  · intro a n e slot
    rcases record_slot_cases p w a n e slot with ⟨account, height, same⟩ | old
    · subst e; exact height.symm
    · exact cat.slot_depth a n e old
  · intro q known
    rcases record_slot_cases p w _ _ _ known with ⟨account, height, same⟩ | old
    · have eq := Epoch.checkpoint.inj same
      subst q
      exact manifest_persistent step extension p valid
    · exact manifest_persistent step extension q (cat.checkpoint_valid q old)
  · intro q known
    rcases record_slot_cases p w _ _ _ known with ⟨account, height, same⟩ | old
    · have eq := Epoch.checkpoint.inj same
      subst q; exact cert
    · exact cat.checkpoint_quorum q old
  · intro a n below
    by_cases prior : n ≤ s.frontier a
    · obtain ⟨e, slotProof⟩ := cat.hole_free a n prior
      exact ⟨e, extension a n e slotProof⟩
    · by_cases same : a = (c.checkpoints p).owner
      · subst a
        have parent := valid.2.1
        have shape := static_facts valid.1
        have parentBelow := cat.frontier_bound _ _ _ parent
        rw [shape.parent_owner] at parentBelow
        have upper : (c.checkpoints p).depth ≤ s.frontier (c.checkpoints p).owner + 1 := by
          have ds := shape.parent_depth
          omega
        have bn : n ≤ max (s.frontier (c.checkpoints p).owner) (c.checkpoints p).depth := by
          simpa [record] using below
        have atNew : n = (c.checkpoints p).depth := by omega
        subst n
        exact ⟨.checkpoint p, by simp [record, two, setAt]⟩
      · have old : n ≤ s.frontier a := by simpa [record, setAt, same] using below
        exact False.elim (prior old)
  · intro a n e slot
    rcases record_slot_cases p w a n e slot with ⟨account, height, same⟩ | old
    · subst a; subst n
      simp only [record, setAt_same]
      exact Nat.le_max_right _ _
    · exact Nat.le_trans (cat.frontier_bound a n e old) (record_frontier_mono c s p w a)

theorem catalogue_transport {c : Config A T P R f} {s t : State A T P R} {label}
    (cat : Catalogue c s) (step : Step c s label t) (extension : ArchiveExtension s t)
    (archive : t.archive = s.archive) (frontier : t.frontier = s.frontier) : Catalogue c t := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [archive] using cat.slot_owner
  · simpa [archive] using cat.slot_depth
  · intro p known
    have old : Known c s (.checkpoint p) := by simpa [Known, archive] using known
    exact manifest_persistent step extension p (cat.checkpoint_valid p old)
  · intro p known
    have old : Known c s (.checkpoint p) := by simpa [Known, archive] using known
    exact quorum_mono c _ _ ((step_journals step).votes p) (cat.checkpoint_quorum p old)
  · simpa [archive, frontier] using cat.hole_free
  · simpa [archive, frontier] using cat.frontier_bound

theorem step_catalogue {c : Config A T P R f} {s t : State A T P R} {label}
    (ev : Evidence c s) (cat : Catalogue c s) (step : Step c s label t) : Catalogue c t := by
  have extension := step_archive_extension ev cat step
  cases step with
  | record p w member cert valid => exact record_catalogue ev cat p w member cert valid
  | effect tx w member allowed =>
      apply catalogue_transport cat (Step.effect s tx w member allowed) extension
      · unfold effect; split <;> rfl
      · unfold effect; split <;> rfl
  | sign tx w member fresh allowed => exact catalogue_transport cat (Step.sign s tx w member fresh allowed) extension rfl rfl
  | freeze e w member => exact catalogue_transport cat (Step.freeze s e w member) extension rfl rfl
  | release tx w member reserved certificate => exact catalogue_transport cat (Step.release s tx w member reserved certificate) extension rfl rfl
  | endorse p w member allowed => exact catalogue_transport cat (Step.endorse s p w member allowed) extension rfl rfl
  | install p w member received parent credits => exact catalogue_transport cat (Step.install s p w member received parent credits) extension rfl rfl
  | receiveOperation tx w member certificate => exact catalogue_transport cat (Step.receiveOperation s tx w member certificate) extension rfl rfl
  | receiveFinal tx w member certificate => exact catalogue_transport cat (Step.receiveFinal s tx w member certificate) extension rfl rfl
  | fence tx w member allowed => exact catalogue_transport cat (Step.fence s tx w member allowed) extension rfl rfl
  | replay => exact cat

end CBCL.ConsensusFree
