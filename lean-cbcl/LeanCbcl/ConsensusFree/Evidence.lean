import LeanCbcl.ConsensusFree.Archive

namespace CBCL.ConsensusFree
open CBCL.ValidatorBudget CBCL.SealedCheckpoint
variable {A T P R f : Nat}

/-- Local installations and delivered checkpoints refer to known archive entries. -/
structure Locals (c : Config A T P R f) (s : State A T P R) : Prop where
  installed_known : ∀ w a, Known c s (s.active w a)
  installed_owner : ∀ w a, owner c (s.active w a) = a
  received_checkpoint : ∀ p w, s.seenCheckpoint p w = true → Known c s (.checkpoint p)

private theorem unchanged_evidence {c : Config A T P R f} {s t : State A T P R}
    (h : Evidence c s) (extension : ArchiveExtension s t)
    (sig : t.signatures = s.signatures) (eff : t.effects = s.effects) (fen : t.fences = s.fences)
    (op : t.seenOperation = s.seenOperation) (fin : t.seenFinal = s.seenFinal)
    (rel : t.released = s.released) (vot : t.votes = s.votes) (cho : t.choices = s.choices) : Evidence c t := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [eff, fen] using h.discipline
  · intro tx w hw vote
    exact known_extension extension _ (h.signature_known tx w hw (by simpa [sig] using vote))
  · simpa [sig] using h.signature_auth
  · simpa [eff, operationCert, sig] using h.effect_operation
  · simpa [op, operationCert, sig] using h.received_operation
  · simpa [fin, finalCert, eff] using h.received_final
  · simpa [rel, cancelCert, fen] using h.released_cancel
  · simpa [vot, cho] using h.voted_choice

theorem step_evidence {c : Config A T P R f} {s t : State A T P R} {label}
    (h : Evidence c s) (localState : Locals c s) (cat : Catalogue c s)
    (step : Step c s label t) : Evidence c t := by
  have archive := step_archive_extension h cat step
  have journals := step_journals step
  cases step with
  | replay => exact h
  | freeze e w member => exact unchanged_evidence h archive rfl rfl rfl rfl rfl rfl rfl rfl
  | record p w member cert valid => exact unchanged_evidence h archive rfl rfl rfl rfl rfl rfl rfl rfl
  | install p w member received parent credits => exact unchanged_evidence h archive rfl rfl rfl rfl rfl rfl rfl rfl
  | sign tx w member fresh allowed =>
      refine ⟨h.discipline, ?_, ?_, ?_, ?_, h.received_final, h.released_cancel, h.voted_choice⟩
      · intro u v hv vote
        by_cases ut : u = tx
        · subst u
          by_cases vw : v = w
          · subst v
            have known := localState.installed_known w (owner c (c.opEpoch tx))
            rw [(allowed hv).2.1] at known
            exact known
          · exact h.signature_known tx v hv (by simpa [signed, two, setAt, vw] using vote)
        · exact h.signature_known u v hv (by simpa [signed, two, setAt, ut] using vote)
      · intro u v hv vote
        by_cases ut : u = tx
        · subst u
          by_cases vw : v = w
          · subst v; exact (allowed hv).1
          · exact h.signature_auth tx v hv (by simpa [signed, two, setAt, vw] using vote)
        · exact h.signature_auth u v hv (by simpa [signed, two, setAt, ut] using vote)
      · intro u v hv vote
        exact quorum_mono c _ _ (journals.signatures u) (h.effect_operation u v hv vote)
      · intro u v receipt
        exact quorum_mono c _ _ (journals.signatures u) (h.received_operation u v receipt)
  | release tx w member reserved certificate =>
      refine ⟨h.discipline, h.signature_known, h.signature_auth, h.effect_operation,
        h.received_operation, h.received_final, ?_, h.voted_choice⟩
      intro u v hv released
      by_cases ut : u = tx
      · subst u
        by_cases vw : v = w
        · subst v; exact certificate
        · exact h.released_cancel tx v hv (by simpa [release, two, setAt, vw] using released)
      · exact h.released_cancel u v hv (by simpa [release, two, setAt, ut] using released)
  | endorse p w member allowed =>
      refine ⟨h.discipline, h.signature_known, h.signature_auth, h.effect_operation,
        h.received_operation, h.received_final, h.released_cancel, ?_⟩
      intro q v hv vote
      by_cases vw : v = w
      · subst v
        by_cases qp : q = p
        · subst q; simp [endorse, two, setAt]
        · have oldVote : s.votes q w = true := by simpa [endorse, two, setAt, qp] using vote
          have oldChoice := h.voted_choice q w hv oldVote
          by_cases parents : (c.checkpoints q).parent = (c.checkpoints p).parent
          · rw [parents] at oldChoice
            have once := (allowed hv).2.2.2
            have same : q = p := by
              rcases once with empty | chosen
              · rw [empty] at oldChoice; cases oldChoice
              · exact Option.some.inj (oldChoice.symm.trans chosen)
            exact False.elim (qp same)
          · simpa [endorse, two, setAt, parents] using oldChoice
      · have oldVote : s.votes q v = true := by
          by_cases qp : q = p <;> simp_all [endorse, two, setAt]
        have oldChoice := h.voted_choice q v hv oldVote
        by_cases parents : (c.checkpoints q).parent = (c.checkpoints p).parent <;>
          simpa [endorse, two, setAt, vw, parents] using oldChoice
  | receiveOperation tx w member certificate =>
      refine ⟨h.discipline, h.signature_known, h.signature_auth, h.effect_operation,
        ?_, h.received_final, h.released_cancel, h.voted_choice⟩
      intro u v receipt
      by_cases ut : u = tx
      · subst u
        by_cases vw : v = w
        · subst v; exact certificate
        · exact h.received_operation tx v (by simpa [receiveOperation, two, setAt, vw] using receipt)
      · exact h.received_operation u v (by simpa [receiveOperation, two, setAt, ut] using receipt)
  | receiveFinal tx w member certificate =>
      refine ⟨h.discipline, h.signature_known, h.signature_auth, h.effect_operation,
        h.received_operation, ?_, h.released_cancel, h.voted_choice⟩
      intro u v receipt
      by_cases ut : u = tx
      · subst u
        by_cases vw : v = w
        · subst v; exact certificate
        · exact h.received_final tx v (by simpa [receiveFinal, two, setAt, vw] using receipt)
      · exact h.received_final u v (by simpa [receiveFinal, two, setAt, ut] using receipt)
  | fence tx w member allowed =>
      refine ⟨?_, h.signature_known, h.signature_auth, h.effect_operation,
        h.received_operation, h.received_final, ?_, h.voted_choice⟩
      · intro u v hv ⟨effectVote, fenceVote⟩
        by_cases ut : u = tx
        · subst u
          by_cases vw : v = w
          · subst v; have noEffect := allowed hv; simp [fence, noEffect] at effectVote
          · exact h.discipline tx v hv ⟨effectVote, by simpa [fence, two, setAt, vw] using fenceVote⟩
        · exact h.discipline u v hv ⟨effectVote, by simpa [fence, two, setAt, ut] using fenceVote⟩
      · intro u v hv released
        exact quorum_mono c _ _ (journals.fences u) (h.released_cancel u v hv released)
  | effect tx w member allowed =>
      have raw : Evidence c (emit s tx w) := by
        refine ⟨?_, h.signature_known, h.signature_auth, ?_, h.received_operation, ?_, h.released_cancel, h.voted_choice⟩
        · intro u v hv ⟨effectVote, fenceVote⟩
          by_cases ut : u = tx
          · subst u
            by_cases vw : v = w
            · subst v; have noFence := (allowed hv).2; simp [emit, noFence] at fenceVote
            · exact h.discipline tx v hv ⟨by simpa [emit, two, setAt, vw] using effectVote, fenceVote⟩
          · exact h.discipline u v hv ⟨by simpa [emit, two, setAt, ut] using effectVote, fenceVote⟩
        · intro u v hv vote
          by_cases ut : u = tx
          · subst u
            by_cases vw : v = w
            · subst v; exact h.received_operation tx w (allowed hv).1
            · exact h.effect_operation tx v hv (by simpa [emit, two, setAt, vw] using vote)
          · exact h.effect_operation u v hv (by simpa [emit, two, setAt, ut] using vote)
        · intro u v receipt
          exact quorum_mono c _ _ (two_mono s.effects tx w u) (h.received_final u v receipt)
      unfold effect
      split <;> exact ⟨raw.discipline, raw.signature_known, raw.signature_auth, raw.effect_operation,
        raw.received_operation, raw.received_final, raw.released_cancel, raw.voted_choice⟩

theorem step_locals {c : Config A T P R f} {s t : State A T P R} {label}
    (h : Locals c s) (ev : Evidence c s) (cat : Catalogue c s) (step : Step c s label t) : Locals c t := by
  have extension := step_archive_extension ev cat step
  have knowns : ∀ w a, Known c t (s.active w a) := fun w a => known_extension extension _ (h.installed_known w a)
  have received : ∀ p w, s.seenCheckpoint p w = true → Known c t (.checkpoint p) :=
    fun p w receipt => known_extension extension _ (h.received_checkpoint p w receipt)
  cases step with
  | record p w member cert valid =>
      refine ⟨knowns, h.installed_owner, ?_⟩
      intro q v receipt
      by_cases qp : q = p
      · subst q
        by_cases vw : v = w
        · subst v; simp [Known, record, two, setAt, owner, depth, epochOwner, epochDepth]
        · exact received p v (by simpa [record, two, setAt, vw] using receipt)
      · exact received q v (by simpa [record, two, setAt, qp] using receipt)
  | install p w member receipt parent credits =>
      refine ⟨?_, ?_, received⟩
      · intro v a
        by_cases vw : v = w
        · subst v
          by_cases account : a = (c.checkpoints p).owner
          · subst a; simpa [install, two, setAt] using received p w receipt
          · simpa [install, two, setAt, account] using knowns w a
        · simpa [install, two, setAt, vw] using knowns v a
      · intro v a
        by_cases vw : v = w
        · subst v
          by_cases account : a = (c.checkpoints p).owner
          · subst a; simp [install, two, setAt, owner, epochOwner]
          · simpa [install, two, setAt, account] using h.installed_owner w a
        · simpa [install, two, setAt, vw] using h.installed_owner v a
  | effect tx w member allowed =>
      by_cases newly : newlyFinal c s tx w = true
      · simp only [effect, if_pos newly] at knowns received ⊢
        exact ⟨knowns, h.installed_owner, received⟩
      · simp only [effect, if_neg newly] at knowns received ⊢
        exact ⟨knowns, h.installed_owner, received⟩
  | sign => exact ⟨knowns, h.installed_owner, received⟩
  | freeze => exact ⟨knowns, h.installed_owner, received⟩
  | release => exact ⟨knowns, h.installed_owner, received⟩
  | endorse => exact ⟨knowns, h.installed_owner, received⟩
  | receiveOperation => exact ⟨knowns, h.installed_owner, received⟩
  | receiveFinal => exact ⟨knowns, h.installed_owner, received⟩
  | fence => exact ⟨knowns, h.installed_owner, received⟩
  | replay => exact h

end CBCL.ConsensusFree
