import LeanCbcl.ConsensusFree.OwnerProduct

namespace CBCL.ConsensusFree.OwnerProduct
open CBCL.ValidatorBudget
variable {N W R f : Nat} {c : Config N W R f}

@[simp] theorem pin_version (c : Config N W R f) (s : State N W R) (i j : Fin N) :
    (pin c s j).bits (.u .version i) = (decide (i = j) || s.bits (.u .version i)) := by
  by_cases h : ∃ k, s.bits (.u .version k) = true <;>
    simp [pin, add_bits, snapshots, h]

/-- The published allocation is sufficient by admission conservation, not by a
readiness premise or an assumed successful signing check. Later income cannot
mutate this immutable version's books. -/
theorem version_budget_apply (c : Config N W R f) (s : State N W R) (a : Action N W)
    (funding : OwnerFunding.Invariant c.costs (funds s))
    (prior : ∀ i, s.bits (.u .version i) = true → ∀ d, (c.costs.debit i d : Int) ≤ s.allocation i d)
    (en : Enabled c s a) : ∀ i, (applyAction c s a).bits (.u .version i) = true →
      ∀ d, (c.costs.debit i d : Int) ≤ (applyAction c s a).allocation i d := by
  intro i hv d
  cases a with
  | manifest j =>
    by_cases ij : i = j
    · subst i
      have req : head s j := en.1.1
      simpa only [applyAction, pin, setAt_same] using
        (OwnerFunding.unissued_head_funded funding j req.1 req.2.1 d)
    · have old : s.bits (.u .version i) = true := by
        simpa [applyAction, pin_version, ij] using hv
      simpa only [applyAction, pin, setAt_other _ _ _ _ ij] using prior i old d
  | _ =>
    all_goals
      simp only [applyAction, target] at hv ⊢
      have old : s.bits (.u .version i) = true := by simpa [add_bits] using hv
      simpa only [add] using prior i old d

theorem version_budget (e : Execution c) (n : Nat) : ∀ i,
    (e.state n).bits (.u .version i) = true →
    ∀ d, (c.costs.debit i d : Int) ≤ (e.state n).allocation i d := by
  induction n with
  | zero => simp [e.starts, initial]
  | succ n ih =>
    rw [e.step]; unfold perform; split
    next en => exact version_budget_apply _ _ _ (OwnerFunding.run_invariant (funding_run e n)) ih en
    next disabled => exact ih

@[simp] theorem pin_batch (c : Config N W R f) (s : State N W R) (i j : Fin N) :
    (pin c s i).bits (.u .batch j) = s.bits (.u .batch j) := by
  by_cases h : ∃ k, s.bits (.u .version k) = true <;>
    simp [pin, add_bits, snapshots, h]

theorem batch_issue_total (c : Config N W R f) (s : State N W R) (i : Fin N) (d : Fin R)
    (fresh : s.bits (.u .batch i) = false) :
    batchTotal c (add s [.u .issued i, .u .batch i]) d = batchTotal c s d + c.costs.debit i d := by
  have mask : (fun j => (add s [.u .issued i, .u .batch i]).bits (.u .batch j)) =
      setAt (fun j => s.bits (.u .batch j)) i true := by
    funext j; by_cases ji : j = i <;> simp [add_bits, setAt, ji]
  unfold batchTotal
  rw [mask, OwnerFunding.marked_set]
  simp [fresh]

theorem batch_envelope_apply (c : Config N W R f) (s : State N W R) (a : Action N W)
    (causal : Causal c s) (prior : ∀ d, batchTotal c s d ≤ c.limit d)
    (en : Enabled c s a) : ∀ d, batchTotal c (applyAction c s a) d ≤ c.limit d := by
  intro d
  cases a with
  | issueBatch i =>
    have req : head s i ∧ s.bits (.g .frozen) = false ∧ batchFits c s i := en.1
    have fresh : s.bits (.u .batch i) = false := by
      cases h : s.bits (.u .batch i)
      · rfl
      · have := causal.batchIssued i h; simp [req.1.2.1] at this
    simpa only [applyAction, batch_issue_total _ _ _ _ fresh] using (req.2.2 d).2
  | _ =>
    all_goals simpa [batchTotal, applyAction, target, add_bits] using prior d

theorem batch_envelope (e : Execution c) (n : Nat) : ∀ d, batchTotal c (e.state n) d ≤ c.limit d := by
  induction n with
  | zero => simp [e.starts, batchTotal, initial]
  | succ n ih =>
    rw [e.step]; unfold perform; split
    next en => exact batch_envelope_apply _ _ _ (causal_run e n) ih en
    next disabled => exact ih

private theorem sum_mono (xs : List α) (a b : α → Int)
    (bound : ∀ i ∈ xs, a i ≤ b i) : isum xs a ≤ isum xs b := by
  induction xs with
  | nil => simp [isum]
  | cons i xs ih =>
    have head := bound i (by simp)
    have tail := ih (fun j hj => bound j (by simp [hj]))
    simp only [isum]; omega

/-- Any subset of the entire owner-issued batch leaves enough envelope for an
unsigned member, irrespective of validator arrival order. -/
theorem unsigned_batch_fits (c : Config N W R f) (s : State N W R) (i : Fin N) (w : Fin W)
    (issued : s.bits (.u .batch i) = true) (unsigned : s.bits (.l .vote i w) = false)
    (envelope : ∀ d, batchTotal c s d ≤ c.limit d) :
    ∀ d, OwnerFunding.marked (fun j => s.bits (.l .vote j w) && s.bits (.u .batch j))
      (fun j => c.costs.debit j d) + c.costs.debit i d ≤ c.limit d := by
  intro d
  have bound : isum (List.finRange N) (fun j =>
      (if s.bits (.l .vote j w) && s.bits (.u .batch j) then (c.costs.debit j d : Int) else 0) +
      (if j = i then (c.costs.debit i d : Int) else 0)) ≤ batchTotal c s d := by
    apply sum_mono
    intro j _
    by_cases ji : j = i
    · subst j; simp [issued, unsigned]
    · cases hv : s.bits (.l .vote j w) <;> cases hb : s.bits (.u .batch j) <;> simp [hb, ji]
  have single : isum (List.finRange N) (fun j => if j = i then (c.costs.debit i d : Int) else 0) = c.costs.debit i d := by
    change isum (List.finRange N) (setAt (fun _ => 0) i (c.costs.debit i d)) = c.costs.debit i d
    rw [isum_update _ _ i _ (finRange_unique N) (by simp)]
    have zero : isum (List.finRange N) (fun _ : Fin N => (0 : Int)) = 0 := by
      induction List.finRange N <;> simp_all [isum]
    simp [zero]
  rw [isum_add, single] at bound
  exact Int.le_trans bound (envelope d)

theorem core_quorum (c : Config N W R f) (mask : Fin W → Bool)
    (all : ∀ w ∈ c.core, mask w = true) : quorum c mask = true := by
  apply decide_eq_true
  have full := List.countP_eq_length.mpr all
  simp only [List.countP_append, full, c.coreSize]
  omega


theorem Saturated.close {s : State N W R} (sat : Saturated c s) (a : Action N W)
    (ha : honest c a) (hr : requires c s a) (k : Flag N W) (hk : target a = some k)
    (needed : Needed s a := by
      simp only [Needed, Unfinal, HeldDependency, rootExists] at *
      all_goals grind) : s.bits k = true := sat a ha hr needed k hk

/-- The integer envelope used by the product implies the native fractional
validator inequality. Checked machine overflow is a separate representation bound. -/
theorem batch_native_guard (c : Config N W R f) (s : State N W R) (i : Fin N) (w : Fin W)
    (ready : signReady c s i w) (batch : s.bits (.u .batch i) = true) (d : Fin R) :
    (OwnerFunding.marked (fun j => s.bits (.l .vote j w) && s.bits (.u .batch j))
      (fun j => c.costs.debit j d) + c.costs.debit i d) * ((2*f+1 : Nat) : Int) ≤
      (c.costs.initial d : Int) * ((f+1 : Nat) : Int) := by
  have h := ready.2.2.2
  rw [if_pos batch] at h
  have used := h.2.2.2 d
  have multiplied := Int.mul_le_mul_of_nonneg_right used (Int.natCast_nonneg (2*f+1))
  have safe : (c.limit d : Int) * ((2*f+1 : Nat) : Int) ≤
      (c.costs.initial d : Int) * ((f+1 : Nat) : Int) := by
    simpa only [Int.natCast_mul] using (Int.ofNat_le.mpr (c.safeLimit d))
  exact Int.le_trans multiplied safe


/-- Existing external proof objects are imported by their acyclic dependencies;
owner authentication alone does not make them magically local. -/
theorem saturated_income {s : State N W R} (sat : Saturated c s) (pending : Pending s)
    (auth : ∀ i, s.bits (.u .income i) = true → c.costs.incomingAuthenticated i = true)
    (i : Fin N) (used : ∃ j, s.bits (.u .version j) = true ∧ s.bits (.snapshot j i) = true) (hi : s.bits (.u .income i) = true) (w : Fin W) (hw : w ∈ c.core) :
    s.bits (.l .income i w) = true := by
  have nodes : ∀ h node, (c.external i).height node = h → s.bits (.external i node w) = true := by
    intro h
    induction h using Nat.strongRecOn with
    | ind h ih =>
      intro node hn
      apply sat.close (.external i node w) hw
        ⟨hi, c.externalVerified i (auth i hi) node, ?_⟩ _ rfl
      intro dep hd
      exact ih ((c.external i).height dep)
        (by have := (c.external i).earlier node dep hd; omega) dep rfl
  exact sat.close (.deliverIncome i w) hw ⟨hi, fun node => nodes _ node rfl⟩ _ rfl

/-- Normal candidate -> OperationQC -> EffectsQC imports, in dependency order.
Earlier owner versions and incoming proof closures are established recursively. -/
theorem saturated_evidence {s : State N W R} (h : Causal c s)
    (funding : OwnerFunding.Invariant c.costs (funds s)) (sat : Saturated c s) (pending : Pending s)
    (auth : ∀ i, s.bits (.u .income i) = true → c.costs.incomingAuthenticated i = true)
    (w : Fin W) (hw : w ∈ c.core) : ∀ i,
      (s.bits (.u .version i) = true → s.bits (.l .metadata i w) = true) ∧
      (HeldDependency s i → s.bits (.u .complete i) = true → s.bits (.l .final i w) = true) := by
  have byRank : ∀ rank i, i.val = rank →
      (s.bits (.u .version i) = true → s.bits (.l .metadata i w) = true) ∧
      (HeldDependency s i → s.bits (.u .complete i) = true → s.bits (.l .final i w) = true) := by
    intro rank
    induction rank using Nat.strongRecOn with
    | ind rank ih =>
      intro i hi
      have metadataReady : s.bits (.u .version i) = true → s.bits (.l .metadata i w) = true := by
        intro hv
        apply sat.close (.metadata i w) hw ⟨hv, ?_⟩ _ rfl
        refine ⟨?_, ?_, ?_⟩
        · intro j ji vj
          exact (ih j.val (by have : j.val < i.val := ji; omega) j rfl).1 vj
        · intro j ji
          exact (ih j.val (by have : j.val < i.val := ji; omega) j rfl).2 ⟨i, hv, ji⟩ (h.versionPrior i hv j ji)
        · intro j hj
          exact saturated_income sat pending auth j ⟨i, hv, hj⟩ (h.snapshotIncome i j hj) w hw
      refine ⟨metadataReady, ?_⟩
      intro used done
      have final := h.completedFinal i done
      have issued : s.bits (.u .issued i) = true := funding.final_issued i final
      have candidate : s.bits (.l .act i w) = true := by
        apply sat.close (.act i w) hw ⟨issued, ?_⟩ _ rfl
        rcases h.issuedMode i issued with batch | active
        · exact Or.inl batch
        · exact Or.inr (metadataReady (h.activeVersion i active))
      have op := sat.close (.deliverOperation i w) hw ⟨h.finalOperation i final, candidate⟩ _ rfl
      exact sat.close (.deliverFinal i w) hw ⟨final, candidate, op⟩ _ rfl
  intro i; exact byRank i.val i rfl

/-- With no owner-observed root QC, honest sealed votes (or genuine QC feedback)
remain available. No Byzantine signature is needed. -/
theorem saturated_seal {s : State N W R} (h : Causal c s) (sat : Saturated c s) (pending : Pending s)
    (evidence : ∀ w ∈ c.core, ∀ i,
      (s.bits (.u .version i) = true → s.bits (.l .metadata i w) = true) ∧
      (HeldDependency s i → s.bits (.u .complete i) = true → s.bits (.l .final i w) = true))
    (root : rootExists s) : s.bits (.g .seal) = true := by
  by_cases done : s.bits (.g .seal) = true
  · exact done
  · have localAbsent : ∀ w ∈ c.core, s.bits (.p .root w) = false := by
      intro w hw
      cases hr : s.bits (.p .root w)
      · rfl
      · exact False.elim (done (sat.close (.feedbackRoot w) hw ⟨root, hr⟩ _ rfl))
    have sealVotes : ∀ w ∈ c.core, s.bits (.p .sealVote w) = true := by
      intro w hw
      obtain ⟨i, hi⟩ := root
      apply sat.close (.seal w) hw ⟨⟨i, hi, (evidence w hw i).1 (h.rootVersion i hi)⟩, ?_⟩ _ rfl
      simp only [if_pos hw]
      refine ⟨localAbsent w hw, ?_, ?_⟩
      · intro j hj
        exact (evidence w hw j).2 ⟨i, h.rootVersion i hi, h.batchEarlier i j (h.rootVersion i hi) hj⟩ (h.rootDrained i j hi hj)
      · intro j hj
        rcases h.issuedMode j (h.voteIssued j w hj) with batch | active
        · exact batch
        · exact False.elim (done (h.activeSeal j active))
    have received : ∀ w ∈ c.core, s.bits (.p .sealReceived w) = true :=
      fun w hw => sat.close (.receiveSeal w) hw (sealVotes w hw) _ rfl
    exact sat.close .formSeal trivial ⟨root, core_quorum c _ received⟩ _ rfl

/-- Missing old adoptions cannot be forgotten. A later retained adoption implies
all its owner-created parents were visited; otherwise the missing parent remains
eligible for ordinary direct-parent catch-up. -/
theorem saturated_adoption {s : State N W R} (h : Causal c s) (sat : Saturated c s) (pending : Pending s)
    (metadata : ∀ w ∈ c.core, ∀ i, s.bits (.u .version i) = true → s.bits (.l .metadata i w) = true)
    (sealed : s.bits (.g .seal) = true) (w : Fin W) (hw : w ∈ c.core) :
    ∀ i, s.bits (.u .version i) = true → s.bits (.l .adopted i w) = true := by
  have rootPresent : rootExists s := h.sealRoot sealed
  obtain ⟨rootIndex, rootPublished⟩ := rootPresent
  have rootKnown := sat.close (.deliverRoot w) hw
    ⟨sealed, ⟨rootIndex, rootPublished, metadata w hw rootIndex (h.rootVersion rootIndex rootPublished)⟩⟩ _ rfl
  have byRank : ∀ rank i, i.val = rank → s.bits (.u .version i) = true → s.bits (.l .adopted i w) = true := by
    intro rank
    induction rank using Nat.strongRecOn with
    | ind rank ih =>
      intro i hi hv
      by_cases adopted : s.bits (.l .adopted i w) = true
      · exact adopted
      · have absent : s.bits (.l .adopted i w) = false := by cases hh : s.bits (.l .adopted i w) <;> simp_all
        have laterAbsent : ∀ j, i < j → s.bits (.l .adopted j w) = false := by
          intro j ij
          cases hj : s.bits (.l .adopted j w)
          · rfl
          · exact False.elim (adopted (h.adoptedParents j w hj i ij hv))
        apply sat.close (.adopt i w) hw ⟨metadata w hw i hv, rootKnown, ?_, laterAbsent, ?_⟩ _ rfl
        · intro j ji vj
          exact ih j.val (by have : j.val < i.val := ji; omega) j rfl vj
        · intro j hj
          rcases h.voteMode j w hw hj with batch | own
          · exact h.batchEarlier i j hv batch
          · apply Classical.byContradiction
            intro notEarlier
            have ge : i ≤ j := by omega
            by_cases eq : i = j
            · subst j; exact adopted own
            · have ij : i < j := by omega
              have := laterAbsent j ij; simp [own] at this
  intro i; exact byRank i.val i rfl

/-- A still-pending issued request has either a supplied certificate to return,
or honest signing work enabled by derived envelope/history/full-allocation facts. -/
theorem saturated_issued {s : State N W R} (h : Causal c s) (sat : Saturated c s) (pending : Pending s)
    (budget : ∀ i, s.bits (.u .version i) = true → ∀ d, (c.costs.debit i d : Int) ≤ s.allocation i d)
    (envelope : ∀ d, batchTotal c s d ≤ c.limit d)
    (metadata : ∀ w ∈ c.core, ∀ i, s.bits (.u .version i) = true → s.bits (.l .metadata i w) = true)
    (adoptions : ∀ w ∈ c.core, ∀ i, s.bits (.u .version i) = true → s.bits (.l .adopted i w) = true)
    (i : Fin N) (issued : s.bits (.u .issued i) = true) : s.bits (.u .complete i) = true := by
  by_cases complete : s.bits (.u .complete i) = true
  · exact complete
  · by_cases ownerFinal : s.bits (.u .final i) = true
    · exact sat.close (.complete i) trivial ownerFinal _ rfl
    · have unfinal : Unfinal s i := ⟨issued, by cases hf : s.bits (.u .final i) <;> simp_all⟩
      have laterVersion : ∀ j, i < j → s.bits (.u .version j) = false := by
        intro j ij
        cases hj : s.bits (.u .version j)
        · rfl
        · exact False.elim (complete (h.versionPrior j hj i ij))
      have laterAdoption : ∀ w j, i < j → s.bits (.l .adopted j w) = false := by
        intro w j ij
        cases hj : s.bits (.l .adopted j w)
        · rfl
        · have vj := h.metadataVersion j w (h.adoptedMetadata j w hj)
          have := laterVersion j ij; simp [vj] at this
      have candidates : ∀ w ∈ c.core, s.bits (.l .act i w) = true := by
        intro w hw
        apply sat.close (.act i w) hw ⟨issued, ?_⟩ _ rfl
        rcases h.issuedMode i issued with batch | active
        · exact Or.inl batch
        · exact Or.inr (metadata w hw i (h.activeVersion i active))
      have operation : s.bits (.u .operation i) = true := by
        by_cases formed : s.bits (.u .operation i) = true
        · exact formed
        · have noLocal : ∀ w ∈ c.core, s.bits (.l .operation i w) = false := by
            intro w hw
            cases hl : s.bits (.l .operation i w)
            · rfl
            · exact False.elim (formed (sat.close (.feedbackOperation i w) hw ⟨issued, hl⟩ _ rfl))
          have votes : ∀ w ∈ c.core, s.bits (.l .vote i w) = true := by
            intro w hw
            by_cases voted : s.bits (.l .vote i w) = true
            · exact voted
            · have absent : s.bits (.l .vote i w) = false := by cases hh : s.bits (.l .vote i w) <;> simp_all
              apply sat.close (.sign i w) hw ?_ _ rfl
              simp only [requires, if_pos hw]
              refine ⟨issued, candidates w hw, noLocal w hw, ?_⟩
              cases batch : s.bits (.u .batch i)
              · simp only [Bool.false_eq_true, if_false]
                have active : s.bits (.u .activated i) = true := by
                  rcases h.issuedMode i issued with hb | ha
                  · simp [batch] at hb
                  · exact ha
                have vi := h.activeVersion i active
                refine ⟨⟨adoptions w hw i vi, laterAdoption w⟩, ?_, budget i vi⟩
                intro j hj
                apply Classical.byContradiction
                intro gt
                have ij : i < j := by omega
                rcases h.voteMode j w hw hj with bj | aj
                · have := h.batchEarlier i j vi bj; omega
                · have := laterAdoption w j ij; simp [aj] at this
              · simp only [if_true]
                have noRoot : ¬ rootExists s := by
                  rintro ⟨j, hj⟩
                  exact complete (h.rootDrained j i hj batch)
                have noSeal : s.bits (.p .sealVote w) = false := by
                  cases hs : s.bits (.p .sealVote w)
                  · rfl
                  · exact False.elim (noRoot (h.sealVoteRoot w hs))
                have noKnownRoot : s.bits (.p .root w) = false := by
                  cases hr : s.bits (.p .root w)
                  · rfl
                  · exact False.elim (noRoot (h.localRoot w hr))
                have noAdopt : ∀ j, s.bits (.l .adopted j w) = false := by
                  intro j
                  cases ha : s.bits (.l .adopted j w)
                  · rfl
                  · exact False.elim (noRoot (h.versionRoot j (h.metadataVersion j w (h.adoptedMetadata j w ha))))
                exact ⟨noSeal, noKnownRoot, noAdopt, unsigned_batch_fits c s i w batch absent envelope⟩
          have received : ∀ w ∈ c.core, s.bits (.l .voteReceived i w) = true :=
            fun w hw => sat.close (.receiveVote i w) hw (votes w hw) _ rfl
          exact sat.close (.formOperation i) trivial ⟨issued, core_quorum c _ received⟩ _ rfl
      have final : s.bits (.u .final i) = true := by
        by_cases formed : s.bits (.u .final i) = true
        · exact formed
        · have noLocal : ∀ w ∈ c.core, s.bits (.l .final i w) = false := by
            intro w hw
            cases hl : s.bits (.l .final i w)
            · rfl
            · exact False.elim (formed (sat.close (.feedbackFinal i w) hw ⟨issued, hl, operation⟩ _ rfl))
          have effects : ∀ w ∈ c.core, s.bits (.l .effect i w) = true := by
            intro w hw
            have localOp := sat.close (.deliverOperation i w) hw ⟨operation, candidates w hw⟩ _ rfl
            apply sat.close (.effect i w) hw ?_ _ rfl
            simp only [requires, if_pos hw]
            exact ⟨localOp, candidates w hw, noLocal w hw⟩
          have received : ∀ w ∈ c.core, s.bits (.l .effectReceived i w) = true :=
            fun w hw => sat.close (.receiveEffect i w) hw (effects w hw) _ rfl
          exact sat.close (.formFinal i) trivial ⟨issued, operation, core_quorum c _ received⟩ _ rfl
      exact sat.close (.complete i) trivial final _ rfl




/-- Essential closure lemma. All financial, history and phase premises below
are inductive theorems of the initialized product, not environment assumptions. -/
theorem saturated_complete {s : State N W R} (h : Causal c s)
    (funding : OwnerFunding.Invariant c.costs (funds s)) (sat : Saturated c s) (pending : Pending s)
    (auth : ∀ i, s.bits (.u .income i) = true → c.costs.incomingAuthenticated i = true)
    (budget : ∀ i, s.bits (.u .version i) = true → ∀ d, (c.costs.debit i d : Int) ≤ s.allocation i d)
    (envelope : ∀ d, batchTotal c s d ≤ c.limit d) :
    ∀ i, s.bits (.u .accepted i) = true → s.bits (.u .complete i) = true := by
  have evidence := fun w hw => saturated_evidence h funding sat pending auth w hw
  have metadataReady := fun w hw i hv => (evidence w hw i).1 hv
  have adoptions : ∀ w ∈ c.core, ∀ i,
      s.bits (.u .version i) = true → s.bits (.l .adopted i w) = true := by
    intro w hw i hv
    have sealed := saturated_seal h sat pending evidence (h.versionRoot i hv)
    exact saturated_adoption h sat pending metadataReady sealed w hw i hv
  have byRank : ∀ rank i, i.val = rank → s.bits (.u .accepted i) = true → s.bits (.u .complete i) = true := by
    intro rank
    induction rank using Nat.strongRecOn with
    | ind rank ih =>
      intro i hi accepted
      have lower : ∀ j, j < i → s.bits (.u .complete j) = true := by
        intro j ji
        exact ih j.val (by have : j.val < i.val := ji; omega) j rfl (h.admittedPrefix i accepted j ji)
      cases issued : s.bits (.u .issued i)
      · have hd : head s i := ⟨accepted, issued, fun j ji => funding.final_issued j (h.completedFinal j (lower j ji))⟩
        have drainedNow : drained s := by
          intro j hj
          by_cases ji : j < i
          · exact lower j ji
          · by_cases eq : i = j
            · subst j; simp [issued] at hj
            · have ij : i < j := by omega
              have := h.issuedPrefix j hj i ij; simp [issued] at this
        have frozen : s.bits (.g .frozen) = true := by
          cases hf : s.bits (.g .frozen)
          · by_cases fits : batchFits c s i
            · have := sat.close (.issueBatch i) trivial ⟨hd, hf, fits⟩ _ rfl
              simp [issued] at this
            · have := sat.close (.freeze i) trivial ⟨hd, hf, fits⟩ _ rfl
              simp [hf] at this
          · rfl
        have version := sat.close (.manifest i) trivial ⟨hd, frozen, drainedNow⟩ _ rfl
        have sealed := saturated_seal h sat pending evidence (h.versionRoot i version)
        have currentOwner : current s i c.ownerValidator := by
          refine ⟨adoptions _ c.ownerHonest i version, ?_⟩
          intro j ij
          cases hj : s.bits (.l .adopted j c.ownerValidator)
          · rfl
          · have vj := h.metadataVersion j _ (h.adoptedMetadata j _ hj)
            have ci := h.versionPrior j vj i ij
            have ii := funding.final_issued i (h.completedFinal i ci)
            change s.bits (.u .issued i) = true at ii
            simp [issued] at ii
        have activated := sat.close (.activate i) trivial ⟨version, sealed, currentOwner⟩ _ rfl
        have ii := sat.close (.issueOwned i) trivial ⟨hd, activated, drainedNow, budget i version⟩ _ rfl
        simp [issued] at ii
      · exact saturated_issued h sat pending budget envelope metadataReady adoptions i issued
  intro i; exact byRank i.val i rfl

/-- Full initialized finite-capacity product completion: accepted FIFO requests
reach the owner's durable Complete with observed EffectsQC. No final certificate,
SignAllowed, head affordability, drain, root uniqueness or readiness premise is
supplied to this theorem. Byzantine handlers and private certificate disclosure
need no fairness. Completed worker turns abstract successful atomic journal IO. -/
theorem admitted_eventually_complete (e : Execution c) (i : Fin N) (start : Nat)
    (accepted : (e.state start).bits (.u .accepted i) = true) :
    ∃ finish, start ≤ finish ∧ (e.state finish).bits (.u .complete i) = true := by
  obtain ⟨t, fixed⟩ := eventually_stationary e
  have sat := stationary_saturated e t fixed
  have allDone : ∀ j, (e.state t).bits (.u .accepted j) = true → (e.state t).bits (.u .complete j) = true := by
    intro j hj
    by_cases complete : (e.state t).bits (.u .complete j) = true
    · exact complete
    · have pending : Pending (e.state t) := ⟨j, hj, by cases hh : (e.state t).bits (.u .complete j) <;> simp_all⟩
      exact saturated_complete (causal_run e t)
        (OwnerFunding.run_invariant (funding_run e t)) sat pending
        (fun k hk => OwnerFunding.received_income_authenticated (funding_run e t) k hk)
        (version_budget e t) (batch_envelope e t) j hj
  have keep := MultiParent.Liveness.persists _ (fun n => step_mono e n (.u .accepted i)) accepted
  have admitted : (e.state t).bits (.u .accepted i) = true := by
    have atMax := keep (max start t) (by omega)
    simpa only [fixed (max start t) (by omega)] using atMax
  exact ⟨max start t, by omega, by simpa only [fixed (max start t) (by omega)] using allDone i admitted⟩

/-- Once completed, the same immutable request remains completed forever. -/
theorem admitted_eventually_always_complete (e : Execution c) (i : Fin N) (start : Nat)
    (accepted : (e.state start).bits (.u .accepted i) = true) :
    ∃ finish, start ≤ finish ∧ ∀ n, finish ≤ n → (e.state n).bits (.u .complete i) = true := by
  obtain ⟨finish, hf, hc⟩ := admitted_eventually_complete e i start accepted
  exact ⟨finish, hf, MultiParent.Liveness.persists _ (fun n => step_mono e n (.u .complete i)) hc⟩


/-- No reachable pending request is a protocol deadlock: some necessary honest
or owner action is enabled. This is separate from the stronger fair termination
result above. Native IO outages are represented by postponed/stuttering turns. -/
theorem pending_has_enabled_job (e : Execution c) (n : Nat) (i : Fin N)
    (accepted : (e.state n).bits (.u .accepted i) = true)
    (incomplete : (e.state n).bits (.u .complete i) = false) :
    ∃ a, honest c a ∧ Needed (e.state n) a ∧ Enabled c (e.state n) a := by
  apply Classical.byContradiction
  intro stuck
  have sat : Saturated c (e.state n) := by
    intro a ha hr hn k hk
    cases absent : (e.state n).bits k
    · have en : Enabled c (e.state n) a := ⟨hr, by simp [hk, absent]⟩
      exact False.elim (stuck ⟨a, ha, hn, en⟩)
    · rfl
  have pending : Pending (e.state n) := ⟨i, accepted, incomplete⟩
  have done := saturated_complete (causal_run e n)
    (OwnerFunding.run_invariant (funding_run e n)) sat pending
    (fun j hj => OwnerFunding.received_income_authenticated (funding_run e n) j hj)
    (version_budget e n) (batch_envelope e n) i accepted
  simp [incomplete] at done


end CBCL.ConsensusFree.OwnerProduct
