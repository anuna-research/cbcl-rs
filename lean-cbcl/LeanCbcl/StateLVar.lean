import LeanCbcl.StateLift
import LeanCbcl.StateKernelDelivery

/-! SPEC-038: conflict-aware thresholds over the join order. Evidence may grow;
dissemination preserves finite witnesses, not equality at unequal histories. -/
namespace CBCL.StateLVar
open State StateLift

section Threshold
variable {L : Type u} [BoundedJoinSemilattice L]

/-- The carrier order is derived from join. -/
def Below (a b : L) : Prop := a ⊔ b = b

theorem below_refl (a : L) : Below a a := join_idem a

theorem below_trans {a b c : L} (ab : Below a b) (bc : Below b c) : Below a c := by
  unfold Below at *
  calc a ⊔ c = a ⊔ (b ⊔ c) := by rw [bc]
       _ = (a ⊔ b) ⊔ c := (join_assoc a b c).symm
       _ = c := by rw [ab, bc]

theorem below_left (a b : L) : Below a (a ⊔ b) := by
  unfold Below
  rw [← join_assoc, join_idem]

theorem below_right (a b : L) : Below b (a ⊔ b) := by
  rw [join_comm]
  exact below_left b a

theorem join_below {a b c : L} (ac : Below a c) (bc : Below b c) :
    Below (a ⊔ b) c := by
  unfold Below at *
  rw [join_assoc, bc, ac]

theorem top_below {a : L} (h : Below (⊤ : L) a) : a = ⊤ := by
  unfold Below at h
  rw [top_join] at h
  exact h.symm

def Incompatible (Q : L → Prop) : Prop :=
  ∀ a b, Q a → Q b → a ≠ b → a ⊔ b = ⊤

/-- Fault-first success: conflict is never a threshold alternative. -/
def Successful (Q : L → Prop) (state result : L) : Prop :=
  state ≠ ⊤ ∧ Q result ∧ Below result state

/-- Distinct reached alternatives force the combined history to conflict. -/
theorem distinct_successes_force_conflict {Q : L → Prop} (incompatible : Incompatible Q)
    {x y a b : L} (left : Successful Q x a) (right : Successful Q y b) (different : a ≠ b) :
    x ⊔ y = ⊤ := by
  apply top_below
  rw [← incompatible a b left.2.1 right.2.1 different]
  exact join_below (below_trans left.2.2 (below_left x y))
    (below_trans right.2.2 (below_right x y))

theorem threshold_quasi_determinism {Q : L → Prop} (incompatible : Incompatible Q)
    {x y a b : L} (left : Successful Q x a) (right : Successful Q y b) :
    a = b ∨ x ⊔ y = ⊤ := by
  by_cases equal : a = b
  · exact Or.inl equal
  · exact Or.inr (distinct_successes_force_conflict incompatible left right equal)

/-- Growth preserves the successful fact unless the new state faults. -/
theorem success_persists {Q : L → Prop} {x y a : L} (success : Successful Q x a)
    (growth : Below x y) (ordinary : y ≠ ⊤) : Successful Q y a :=
  ⟨ordinary, success.2.1, below_trans success.2.2 growth⟩
/-- Runtime-style read result: faults carry a separate evidence channel. -/
inductive ThresholdRead (L : Type u) where
  | pending
  | reached (element : L)
  | fault (evidence : FinSet Act)

/-- Dependency faults are checked before selecting any successful alternative.
Here `L` is the business carrier with its semantic conflict class as top;
evidence-carrying `Sole` is not a threshold carrier in the Rust type checker. -/
noncomputable def thresholdRead (Q : List L) (state : L) (dependencyFault : Bool)
    (evidence : FinSet Act) : ThresholdRead L := by
  classical
  exact if dependencyFault = true ∨ state = ⊤ then .fault evidence else
    match Q.find? (fun q => decide (Below q state)) with
    | none => .pending
    | some q => .reached q

theorem thresholdRead_fault_first (Q : List L) (state : L) (evidence : FinSet Act) :
    thresholdRead Q state true evidence = .fault evidence := by
  classical
  simp [thresholdRead]

theorem thresholdRead_sound {Q : List L} {state result : L} {fault : Bool} {evidence : FinSet Act}
    (read : thresholdRead Q state fault evidence = .reached result) :
    Successful (fun q => q ∈ Q) state result := by
  classical
  unfold thresholdRead at read
  split at read
  · contradiction
  · rename_i ordinary
    cases found : Q.find? (fun q => decide (Below q state)) with
    | none => simp [found] at read
    | some q =>
      simp only [found, ThresholdRead.reached.injEq] at read
      subst q
      have reached : decide (Below result state) = true := List.find?_some (p := fun q : L => decide (Below q state)) found
      exact ⟨fun top => ordinary (Or.inr top), List.mem_of_find?_eq_some found,
        of_decide_eq_true reached⟩

/-- Concrete threshold reads inherit agreement from the actual join order. -/
theorem thresholdRead_agreement {Q : List L}
    (incompatible : Incompatible (fun q => q ∈ Q))
    {x y a b : L} {fx fy : Bool} {ex ey : FinSet Act}
    (left : thresholdRead Q x fx ex = .reached a)
    (right : thresholdRead Q y fy ey = .reached b) : a = b ∨ x ⊔ y = ⊤ :=
  threshold_quasi_determinism incompatible (thresholdRead_sound left) (thresholdRead_sound right)

end Threshold

/-- Domain filtering is a display of full accepted evidence. -/
def rawHistory (A : List Act) : FinSet Act := lift (fun a => FinSet.mk [a]) A

theorem rawHistory_eq (A : List Act) : rawHistory A = FinSet.mk A := by
  rw [rawHistory, lift_mk_single]
  simp

theorem rawHistory_union (A B : List Act) :
    rawHistory (A ++ B) = rawHistory A ⊔ rawHistory B := lift_append _ A B

theorem rawHistory_setEq {A B : List Act} (same : SetEq A B) :
    rawHistory A = rawHistory B := lift_setEq _ same

/-- The identity carrier forgets ordering and duplicates, and nothing else. -/
theorem rawHistory_faithful {A B : List Act} (equal : rawHistory A = rawHistory B) : SetEq A B := by
  rw [rawHistory_eq, rawHistory_eq] at equal
  intro a
  have membership : a ∈ FinSet.mk A ↔ a ∈ FinSet.mk B := by rw [equal]
  exact FinSet.mem_mk.symm.trans (membership.trans FinSet.mem_mk)

/-- Fault-aware domain display. Raw carrier equality includes excluded acts. -/
inductive DomainRead where
  | value (selected : FinSet Act)
  | fault (evidence : Lattice.Set Nat)

def domainRead (verb key opener field : String) (A : List Act) : DomainRead :=
  match initialCarrier opener field A with
  | .top evidence => .fault evidence
  | _ => .value (FinSet.mk (initialDomain verb key opener field A))

theorem domainRead_setEq {A B : List Act} (same : SetEq A B)
    (verb key opener field : String) :
    domainRead verb key opener field A = domainRead verb key opener field B := by
  unfold domainRead
  rw [initialCarrier_invariant same opener field]
  have selected : FinSet.mk (initialDomain verb key opener field A) =
      FinSet.mk (initialDomain verb key opener field B) := FinSet.ext fun a =>
    FinSet.mem_mk.trans ((initialDomain_invariant same verb key opener field a).trans FinSet.mem_mk.symm)
  rw [selected]


/-- Domain filtering is well-defined on the raw finite-set quotient. -/
def displayDomain (verb key opener field : String) : FinSet Act → DomainRead :=
  Quotient.lift (domainRead verb key opener field)
    (fun _ _ same => domainRead_setEq same verb key opener field)

theorem display_rawHistory (verb key opener field : String) (A : List Act) :
    displayDomain verb key opener field (rawHistory A) = domainRead verb key opener field A := by
  rw [rawHistory_eq]
  rfl

/-- Initializer evidence is exactly the accepted opener addresses. -/
theorem sole_evidence_join (a b : Sole) (address : Nat) :
    address ∈ Sole.evidence (a ⊔ b) ↔
      address ∈ Sole.evidence a ∨ address ∈ Sole.evidence b := by
  change address ∈ Sole.evidence (Sole.join a b) ↔ _
  cases a <;> cases b <;> simp only [Sole.join]
  case one.one a va b vb =>
    by_cases h : a = b ∧ va = vb
    · rw [if_pos h]; simp [Sole.evidence, h.1]
    · rw [if_neg h]; simp [Sole.evidence]
  all_goals simp [Sole.evidence]

theorem opener_evidence (opener field : String) (A : List Act) (address : Nat) :
    address ∈ Sole.evidence (initialCarrier opener field A) ↔
      ∃ a ∈ A, a.verb = opener ∧ a.addr = address := by
  have general (T : List Act) : address ∈ Sole.evidence (lift (sole field) T) ↔
      ∃ a ∈ T, a.addr = address := by
    induction T with
    | nil => simp [lift_nil, Sole.evidence, JoinSemilatticeBot.bot]
    | cons a rest ih =>
      rw [lift_cons, sole_evidence_join, ih]
      simp [sole, Sole.evidence]
      grind
  rw [initialCarrier, general]
  simp [acts]
  grind

/-- Two different accepted opener addresses are a concrete conflict witness. -/
theorem opener_fork_fault {A : List Act} {a b : Act} (opener field : String)
    (ha : a ∈ A) (hb : b ∈ A) (va : a.verb = opener) (vb : b.verb = opener)
    (different : a.addr ≠ b.addr) :
    ∃ evidence, initialCarrier opener field A = .top evidence ∧
      a.addr ∈ evidence ∧ b.addr ∈ evidence := by
  have ea := (opener_evidence opener field A a.addr).mpr ⟨a, ha, va, rfl⟩
  have eb := (opener_evidence opener field A b.addr).mpr ⟨b, hb, vb, rfl⟩
  cases h : initialCarrier opener field A with
  | bot => simp [h, Sole.evidence] at ea
  | one addr value => simp [h, Sole.evidence] at ea eb; exact False.elim (different (ea.trans eb.symm))
  | top evidence => exact ⟨evidence, rfl, by simpa [h, Sole.evidence] using ea, by simpa [h, Sole.evidence] using eb⟩

/-- Any extension containing the fork faults its dependent domain, preserving
both witness addresses even if further conflicts enlarge the evidence. -/
theorem domain_fork_fault {A : List Act} {a b : Act} (verb key opener field : String)
    (ha : a ∈ A) (hb : b ∈ A) (va : a.verb = opener) (vb : b.verb = opener)
    (different : a.addr ≠ b.addr) :
    ∃ evidence, domainRead verb key opener field A = .fault evidence ∧
      a.addr ∈ evidence ∧ b.addr ∈ evidence := by
  obtain ⟨e, conflict, ea, eb⟩ := opener_fork_fault opener field ha hb va vb different
  exact ⟨e, by simp [domainRead, conflict], ea, eb⟩

/-- A nonnegative admitted amount can only increase an event sum. -/
theorem nonnegative_sum_sublist (key : String) {A B : List Act} (sub : A.Sublist B)
    (nonnegative : ∀ a ∈ B, 0 ≤ amount key a) : sumField key A ≤ sumField key B := by
  induction sub with
  | slnil => exact Int.le_refl 0
  | @cons A B a sub ih =>
    rw [sumField_cons]
    have tail := ih (fun x hx => nonnegative x (by simp [hx]))
    have head := nonnegative a (by simp)
    omega
  | @cons₂ A B a sub ih =>
    rw [sumField_cons, sumField_cons]
    have tail := ih (fun x hx => nonnegative x (by simp [hx]))
    omega

/-- Permutation does not affect the numerical sum, so inclusion suffices;
unique accepted addresses ensure the old history does not duplicate amounts. -/
theorem nonnegative_events_monotone (verb key : String) {A B : List Act}
    (unique : NodupAddr A) (growth : ∀ a ∈ A, a ∈ B)
    (nonnegative : ∀ a ∈ acts verb B, 0 ≤ amount key a) :
    sumField key (acts verb A) ≤ sumField key (acts verb B) := by
  have subset : acts verb A ⊆ acts verb B := by
    intro a ha
    simp only [acts, List.mem_filter, beq_iff_eq] at ha ⊢
    exact ⟨growth a ha.1, ha.2⟩
  obtain ⟨C, perm, sub⟩ := List.subperm_of_subset (List.Pairwise.of_map Act.addr (fun _ _ h equal => h (congrArg Act.addr equal)) (unique.acts verb)) subset
  have sums : sumField key C = sumField key (acts verb A) :=
    perm.foldl_eq' (fun _ _ _ _ z => by simp only [Int.add_right_comm]) 0
  rw [← sums]
  exact nonnegative_sum_sublist key sub nonnegative

/-- Reflexive transitive predecessor reachability in the immutable valid world.
The freezing act itself belongs to its cut. -/
inductive Ancestor (world : Act → Prop) : Act → Act → Prop where
  | self {a} : world a → Ancestor world a a
  | step {a p f} : world a → a.addr ∈ p.preds → Ancestor world p f → Ancestor world a f

/-- Accepted histories contain the immutable causal predecessors they cite. -/
def CausallyClosed (world : Act → Prop) (A : List Act) : Prop :=
  ∀ child ∈ A, ∀ parent, world parent → parent.addr ∈ child.preds → parent ∈ A

theorem ancestor_accepted {world : Act → Prop} {A : List Act}
    (closed : CausallyClosed world A) {a f : Act} (path : Ancestor world a f)
    (freezer : f ∈ A) : a ∈ A := by
  induction path with
  | self _ => exact freezer
  | @step a p f valid edge path ih => exact closed p (ih freezer) a valid edge

noncomputable def causalCut (world : Act → Prop) (A : List Act) (f : Act) : List Act := by
  classical
  exact A.filter (fun a => decide (Ancestor world a f))

/-- Closed histories containing the same freezer contain exactly the same cut. -/
theorem causalCut_agreement {world : Act → Prop} {A B : List Act} {f : Act}
    (leftClosed : CausallyClosed world A) (rightClosed : CausallyClosed world B)
    (leftFreezer : f ∈ A) (rightFreezer : f ∈ B) :
    SetEq (causalCut world A f) (causalCut world B f) := by
  classical
  intro a
  simp only [causalCut, List.mem_filter, decide_eq_true_eq]
  exact ⟨fun h => ⟨ancestor_accepted rightClosed h.2 rightFreezer, h.2⟩,
    fun h => ⟨ancestor_accepted leftClosed h.2 leftFreezer, h.2⟩⟩

theorem freezer_in_cut {world : Act → Prop} {A : List Act} {f : Act}
    (valid : world f) (accepted : f ∈ A) : f ∈ causalCut world A f := by
  classical
  simp [causalCut, accepted, Ancestor.self valid]

/-- The earliest freezer is causal, not a winner chosen by content address. -/
def Earliest (world : Act → Prop) (verb : String) (A : List Act) (f : Act) : Prop :=
  f ∈ A ∧ f.verb = verb ∧ ∀ earlier ∈ A, earlier.verb = verb →
    Ancestor world earlier f → earlier = f

/-- A later delivery cannot reveal an earlier freezer behind an already closed
cut. Concurrent freezers may still make the observation a terminal fault. -/
theorem earliest_persists {world : Act → Prop} {verb : String} {A B : List Act} {f : Act}
    (closed : CausallyClosed world A) (growth : ∀ a ∈ A, a ∈ B)
    (first : Earliest world verb A f) : Earliest world verb B f := by
  refine ⟨growth f first.1, first.2.1, ?_⟩
  intro earlier _ verbIs path
  exact first.2.2 earlier (ancestor_accepted closed path first.1) verbIs path

/-- Any set-extensional field evaluator gives the same frozen underlying value
at the same earliest freezer, even if excluded-contribution metadata grows. -/
theorem frozen_value_agreement {world : Act → Prop} {A B : List Act} {f : Act}
    (leftClosed : CausallyClosed world A) (rightClosed : CausallyClosed world B)
    (leftFreezer : f ∈ A) (rightFreezer : f ∈ B) {V : Type}
    (evaluate : List Act → V) (invariant : ∀ {X Y}, SetEq X Y → evaluate X = evaluate Y) :
    evaluate (causalCut world A f) = evaluate (causalCut world B f) :=
  invariant (causalCut_agreement leftClosed rightClosed leftFreezer rightFreezer)

/-- A closed source proves that a freezer has no hidden causal predecessor
freezer, so the same root remains earliest wherever that act is accepted. -/
theorem earliest_transfer {world : Act → Prop} {verb : String} {A B : List Act} {f : Act}
    (closed : CausallyClosed world A) (first : Earliest world verb A f) (accepted : f ∈ B) :
    Earliest world verb B f := by
  refine ⟨accepted, first.2.1, ?_⟩
  intro earlier _ verbIs path
  exact first.2.2 earlier (ancestor_accepted closed path first.1) verbIs path

/-- Concrete finite witnesses of freeze conflict. The late-write case is only
available under the fault policy; supersede merely records exclusion. -/
inductive FreezeConflict (world : Act → Prop) (verb : String) (contributes : Act → Prop)
    (faultPolicy : Bool) (A : List Act) : Act → Act → Prop where
  | concurrent {a b} : Earliest world verb A a → Earliest world verb A b →
      a.addr ≠ b.addr → FreezeConflict world verb contributes faultPolicy A a b
  | late {f a} : Earliest world verb A f → a ∈ A → contributes a →
      ¬ Ancestor world a f → faultPolicy = true →
      FreezeConflict world verb contributes faultPolicy A f a

/-- Evidence includes the freezing act and excluded contributor, or both
concurrent earliest freezing acts. It names only accepted acts. -/
def freezeEvidence (world : Act → Prop) (verb : String) (contributes : Act → Prop)
    (faultPolicy : Bool) (A : List Act) : Lattice.Set Nat := fun address =>
  ∃ a b, FreezeConflict world verb contributes faultPolicy A a b ∧
    (address = a.addr ∨ address = b.addr)

theorem freeze_witness_accepted {world : Act → Prop} {verb : String} {contributes : Act → Prop}
    {policy : Bool} {A : List Act} {a b : Act}
    (conflict : FreezeConflict world verb contributes policy A a b) : a ∈ A ∧ b ∈ A := by
  cases conflict with
  | concurrent left right _ => exact ⟨left.1, right.1⟩
  | late first accepted _ _ _ => exact ⟨first.1, accepted⟩

theorem freeze_evidence_sound {world : Act → Prop} {verb : String} {contributes : Act → Prop}
    {policy : Bool} {A : List Act} {address : Nat}
    (evidence : address ∈ freezeEvidence world verb contributes policy A) :
    ∃ a ∈ A, a.addr = address := by
  obtain ⟨a, b, conflict, equal⟩ := evidence
  have accepted := freeze_witness_accepted conflict
  rcases equal with equal | equal
  · exact ⟨a, accepted.1, equal.symm⟩
  · exact ⟨b, accepted.2, equal.symm⟩

/-- The same finite pair remains a conflict in any closed replica containing
both acts; this does not require its entire current history to be equal. -/
theorem freeze_witness_transfer {world : Act → Prop} {verb : String} {contributes : Act → Prop}
    {policy : Bool} {A B : List Act} {a b : Act} (closed : CausallyClosed world A)
    (conflict : FreezeConflict world verb contributes policy A a b) (ha : a ∈ B) (hb : b ∈ B) :
    FreezeConflict world verb contributes policy B a b := by
  cases conflict with
  | concurrent left right different =>
      exact .concurrent (earliest_transfer closed left ha) (earliest_transfer closed right hb) different
  | late first _ contribution outside policy =>
      exact .late (earliest_transfer closed first ha) hb contribution outside policy

theorem earliest_setEq {world : Act → Prop} {verb : String} {A B : List Act}
    (same : SetEq A B) (f : Act) : Earliest world verb A f ↔ Earliest world verb B f := by
  constructor
  · intro ⟨accepted, verbIs, first⟩
    exact ⟨(same f).mp accepted, verbIs, fun a ha hv path => first a ((same a).mpr ha) hv path⟩
  · intro ⟨accepted, verbIs, first⟩
    exact ⟨(same f).mpr accepted, verbIs, fun a ha hv path => first a ((same a).mp ha) hv path⟩

theorem freezeConflict_setEq {world : Act → Prop} {verb : String} {contributes : Act → Prop}
    {policy : Bool} {A B : List Act} (same : SetEq A B) (a b : Act) :
    FreezeConflict world verb contributes policy A a b ↔ FreezeConflict world verb contributes policy B a b := by
  have transfer {X Y : List Act} (h : SetEq X Y) :
      FreezeConflict world verb contributes policy X a b → FreezeConflict world verb contributes policy Y a b := by
    intro conflict
    cases conflict with
    | concurrent left right different =>
        exact .concurrent ((earliest_setEq h a).mp left) ((earliest_setEq h b).mp right) different
    | late first accepted contribution outside policy =>
        exact .late ((earliest_setEq h a).mp first) ((h b).mp accepted) contribution outside policy
  exact ⟨transfer same, transfer same.symm⟩

theorem freezeEvidence_setEq {world : Act → Prop} {verb : String} {contributes : Act → Prop}
    {policy : Bool} {A B : List Act} (same : SetEq A B) :
    freezeEvidence world verb contributes policy A = freezeEvidence world verb contributes policy B := by
  funext address
  apply propext
  simp only [freezeEvidence, freezeConflict_setEq same]

theorem causalCut_setEq {world : Act → Prop} {A B : List Act} (same : SetEq A B) (f : Act) :
    SetEq (causalCut world A f) (causalCut world B f) := by
  classical
  intro a
  simp only [causalCut, List.mem_filter, same a]

/-- Without a concurrent-freezer conflict the chosen root is unique, so its
selection is independent of the representative's enumeration order. -/
theorem earliest_find_setEq {world : Act → Prop} {verb : String} {A B : List Act}
    (same : SetEq A B) (unique : NodupAddr A)
    (noConcurrent : ∀ a b, Earliest world verb A a → Earliest world verb A b → a.addr = b.addr) :
    (by classical exact A.find? (fun f => decide (Earliest world verb A f))) =
    (by classical exact B.find? (fun f => decide (Earliest world verb B f))) := by
  classical
  cases left : A.find? (fun f => decide (Earliest world verb A f)) with
  | none =>
      cases right : B.find? (fun f => decide (Earliest world verb B f)) with
      | none => rfl
      | some b =>
          have firstB : Earliest world verb B b := of_decide_eq_true
            (List.find?_some (p := fun f => decide (Earliest world verb B f)) right)
          have firstA := (earliest_setEq same b).mpr firstB
          have absent := List.find?_eq_none.mp left b firstA.1
          exact False.elim (absent (by simpa using firstA))
  | some a =>
      have firstA : Earliest world verb A a := of_decide_eq_true
        (List.find?_some (p := fun f => decide (Earliest world verb A f)) left)
      cases right : B.find? (fun f => decide (Earliest world verb B f)) with
      | none =>
          have firstB := (earliest_setEq same a).mp firstA
          have absent := List.find?_eq_none.mp right a firstB.1
          exact False.elim (absent (by simpa using firstB))
      | some b =>
          have firstB : Earliest world verb A b := (earliest_setEq same b).mpr
            (of_decide_eq_true (List.find?_some (p := fun f => decide (Earliest world verb B f)) right))
          exact congrArg some (unique.eq_of_addr firstA.1 firstB.1 (noConcurrent a b firstA firstB))

/-- Frozen reads separate exact values, current snapshots, and terminal faults. -/
inductive FreezeRead (V : Type) where
  | snapshot (value : V)
  | frozen (freezer : Nat) (value : V) (excluded : FinSet Act)
  | fault (evidence : Lattice.Set Nat)

/-- Read raw faults before a historical cut, unioning their evidence with all
freeze witnesses. The cut is exact; excluded metadata remains a current view. -/
noncomputable def freezeRead {V : Type} (world : Act → Prop) (verb : String)
    (contributes : Act → Prop) (policy : Bool) (rawFault : Option (Lattice.Set Nat))
    (evaluate : List Act → V) (A : List Act) : FreezeRead V := by
  classical
  let witnesses := freezeEvidence world verb contributes policy A
  exact if rawFault.isSome ∨ (∃ a b, FreezeConflict world verb contributes policy A a b) then
      .fault (rawFault.getD ∅ ∪ witnesses)
    else match A.find? (fun f => decide (Earliest world verb A f)) with
    | none => .snapshot (evaluate A)
    | some f => .frozen f.addr (evaluate (causalCut world A f))
        (FinSet.mk (A.filter (fun a => decide (contributes a ∧ ¬ Ancestor world a f))))

/-- A concrete conflict forces a fault observation and retains both addresses,
including when an independent raw fault appears as well. -/
theorem freezeRead_conflict {V : Type} {world : Act → Prop} {verb : String}
    {contributes : Act → Prop} {policy : Bool} {A : List Act} {a b : Act}
    (rawFault : Option (Lattice.Set Nat)) (evaluate : List Act → V)
    (conflict : FreezeConflict world verb contributes policy A a b) :
    ∃ evidence, freezeRead world verb contributes policy rawFault evaluate A = .fault evidence ∧
      a.addr ∈ evidence ∧ b.addr ∈ evidence := by
  classical
  refine ⟨rawFault.getD ∅ ∪ freezeEvidence world verb contributes policy A, ?_, ?_, ?_⟩
  · simp [freezeRead, show ∃ x y, FreezeConflict world verb contributes policy A x y from ⟨a,b,conflict⟩]
  · exact Or.inr ⟨a, b, conflict, Or.inl rfl⟩
  · exact Or.inr ⟨a, b, conflict, Or.inr rfl⟩

/-- Complete freeze observations, including exclusion metadata and all fault
evidence, are equal at equal accepted sets. -/
theorem freezeRead_setEq {V : Type} {world : Act → Prop} {verb : String}
    {contributes : Act → Prop} {policy : Bool} {A B : List Act}
    (same : SetEq A B) (unique : NodupAddr A)
    (evaluate : List Act → V) (invariant : ∀ {X Y}, SetEq X Y → evaluate X = evaluate Y)
    (rawA rawB : Option (Lattice.Set Nat)) (rawSame : rawA = rawB) :
    freezeRead world verb contributes policy rawA evaluate A =
      freezeRead world verb contributes policy rawB evaluate B := by
  classical
  have conflicts : (∃ a b, FreezeConflict world verb contributes policy A a b) ↔
      (∃ a b, FreezeConflict world verb contributes policy B a b) := by
    simp only [freezeConflict_setEq same]
  unfold freezeRead
  simp only [rawSame, conflicts, freezeEvidence_setEq same]
  by_cases fault : rawB.isSome ∨ ∃ a b, FreezeConflict world verb contributes policy B a b
  · simp only [if_pos fault]
  · simp only [if_neg fault]
    have noConcurrent : ∀ a b, Earliest world verb A a → Earliest world verb A b → a.addr = b.addr := by
      intro a b left right
      by_cases equal : a.addr = b.addr
      · exact equal
      · exact False.elim (fault (Or.inr ⟨a, b, .concurrent
          ((earliest_setEq same a).mp left) ((earliest_setEq same b).mp right) equal⟩))
    rw [earliest_find_setEq same unique noConcurrent]
    cases found : B.find? (fun f => decide (Earliest world verb B f)) with
    | none => exact congrArg FreezeRead.snapshot (invariant same)
    | some f =>
      have excluded : FinSet.mk (A.filter (fun a => decide (contributes a ∧ ¬ Ancestor world a f))) =
          FinSet.mk (B.filter (fun a => decide (contributes a ∧ ¬ Ancestor world a f))) := by
        apply FinSet.ext
        intro a
        simp only [FinSet.mem_mk, List.mem_filter, same a]
      simp only
      rw [invariant (causalCut_setEq (world := world) same f), excluded]

section Delivery
open StateKernelDelivery AdmissionStratification StateRefinement

/-- The causal admission boundary: an accepted candidate's recognized immutable
predecessors must already be accepted. This is an admission property, not a
consequence of ValidHistory's sufficient enabling condition. -/
def PredecessorAdmission (adm : Admission) (world : Act → Prop) : Prop :=
  ∀ A child, adm.admit A child = .accepted →
    ∀ parent, world parent → parent.addr ∈ child.preds → parent ∈ A

theorem step_causal_closed {adm : Admission} {auth world : Act → Prop}
    (admission : PredecessorAdmission adm world) {s t : Execution} {event : Option Act}
    (closed : CausallyClosed world s.accepted) (step : Step adm auth s event t) :
    CausallyClosed world t.accepted := by
  cases step with
  | accept a pending admitted =>
      intro child member parent valid edge
      apply (insertAct_setEq a _ parent).mpr
      rcases List.mem_cons.mp ((insertAct_setEq a _ child).mp member) with equal | old
      · subst child
        exact List.mem_cons.mpr (Or.inr (admission _ a admitted parent valid edge))
      · exact List.mem_cons.mpr (Or.inr (closed _ old _ valid edge))
  | _ => exact closed

/-- Causal closure is established from the actual receive/accept execution. -/
theorem replica_causal_closed {adm : Admission} {auth : Act → Prop} {H : ValidHistory adm}
    (R : Replica adm auth H) (admission : PredecessorAdmission adm H.contains) (n : Nat) :
    CausallyClosed H.contains (R.run n).accepted := by
  induction n with
  | zero => rw [R.behavior.1]; intro child member; contradiction
  | succ n ih => exact step_causal_closed admission ih (R.behavior.2 n)

/-- Every member of an actual accepted finite conflict witness eventually
belongs permanently to the other replica, including in infinite histories. -/
theorem witness_dissemination {adm : Admission} {auth : Act → Prop} {H : ValidHistory adm}
    (left right : Replica adm auth H) (witness : List Act) (atTime : Nat)
    (accepted : ∀ a ∈ witness, a ∈ (left.run atTime).accepted) :
    ∃ t, ∀ n, t ≤ n → ∀ a ∈ witness, a ∈ (right.run n).accepted :=
  eventually_all witness _ (fun a ha => eventual_dissemination left right a atTime (accepted a ha))

/-- A concrete initializer fork eventually faults every replica's dependent
read, with the original addresses present in its evidence on every suffix. -/
theorem eventual_domain_fork {adm : Admission} {auth : Act → Prop} {H : ValidHistory adm}
    (left right : Replica adm auth H) (atTime : Nat) (a b : Act)
    (verb key opener field : String)
    (ha : a ∈ (left.run atTime).accepted) (hb : b ∈ (left.run atTime).accepted)
    (va : a.verb = opener) (vb : b.verb = opener) (different : a.addr ≠ b.addr) :
    ∃ t, ∀ n, t ≤ n → ∃ evidence,
      domainRead verb key opener field (right.run n).accepted = .fault evidence ∧
      a.addr ∈ evidence ∧ b.addr ∈ evidence := by
  obtain ⟨t, all⟩ := witness_dissemination left right [a, b] atTime (by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb)
  refine ⟨t, fun n hn => ?_⟩
  exact domain_fork_fault verb key opener field (all n hn a (by simp))
    (all n hn b (by simp)) va vb different

/-- Concrete freeze conflict evidence eventually appears at every compliant
replica. The closed-cut premise comes from causal admission, not arithmetic. -/
theorem eventual_freeze_conflict {adm : Admission} {auth : Act → Prop} {H : ValidHistory adm}
    (left right : Replica adm auth H) (atTime : Nat)
    (verb : String) (contributes : Act → Prop) (policy : Bool) (a b : Act)
    (closed : CausallyClosed H.contains (left.run atTime).accepted)
    (conflict : FreezeConflict H.contains verb contributes policy (left.run atTime).accepted a b) :
    ∃ t, ∀ n, t ≤ n →
      a.addr ∈ freezeEvidence H.contains verb contributes policy (right.run n).accepted ∧
      b.addr ∈ freezeEvidence H.contains verb contributes policy (right.run n).accepted := by
  have accepted := freeze_witness_accepted conflict
  obtain ⟨t, all⟩ := witness_dissemination left right [a, b] atTime (by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact accepted.1
    · exact accepted.2)
  refine ⟨t, fun n hn => ?_⟩
  have transferred := freeze_witness_transfer closed conflict (all n hn a (by simp)) (all n hn b (by simp))
  exact ⟨⟨a, b, transferred, Or.inl rfl⟩, ⟨a, b, transferred, Or.inr rfl⟩⟩

/-- Freeze witnesses produce actual terminal read outcomes after dissemination,
even if independent raw conflicts enlarge the returned evidence. -/
theorem eventual_freeze_fault {adm : Admission} {auth : Act → Prop} {H : ValidHistory adm}
    (left right : Replica adm auth H) (atTime : Nat)
    (admission : PredecessorAdmission adm H.contains)
    (verb : String) (contributes : Act → Prop) (policy : Bool) (a b : Act)
    (conflict : FreezeConflict H.contains verb contributes policy (left.run atTime).accepted a b)
    {V : Type} (evaluate : List Act → V) (rawFault : List Act → Option (Lattice.Set Nat)) :
    ∃ t, ∀ n, t ≤ n → ∃ evidence,
      freezeRead H.contains verb contributes policy (rawFault (right.run n).accepted)
        evaluate (right.run n).accepted = .fault evidence ∧ a.addr ∈ evidence ∧ b.addr ∈ evidence := by
  have accepted := freeze_witness_accepted conflict
  obtain ⟨t, all⟩ := witness_dissemination left right [a, b] atTime (by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact accepted.1
    · exact accepted.2)
  refine ⟨t, fun n hn => ?_⟩
  exact freezeRead_conflict _ evaluate (freeze_witness_transfer
    (replica_causal_closed left admission atTime) conflict
    (all n hn a (by simp)) (all n hn b (by simp)))

/-- A set-extensional observation (including its evidence) converges after
finite completion under the existing acceptance and fairness premises. -/
theorem finite_observation_agreement {adm : Admission} {auth : Act → Prop}
    {H : ValidHistory adm} (left right : Replica adm auth H)
    {O : Type} (observe : List Act → O)
    (invariant : ∀ {A B}, SetEq A B → observe A = observe B)
    (history : List Act) (complete : ∀ a, H.contains a ↔ a ∈ history) :
    ∃ t, ∀ n m, t ≤ n → t ≤ m →
      observe (left.run n).accepted = observe (right.run m).accepted := by
  obtain ⟨tl, hl⟩ := finite_history_stabilizes left history complete
  obtain ⟨tr, hr⟩ := finite_history_stabilizes right history complete
  refine ⟨max tl tr, ?_⟩
  intro n m hn hm
  apply invariant
  intro a
  exact (hl n (by omega) a).trans (hr m (by omega) a).symm
/-- Instantiate finite-history convergence with the complete freeze read,
including canonical set evidence and exclusion metadata. -/
theorem finite_freeze_agreement {adm : Admission} {auth : Act → Prop} {H : ValidHistory adm}
    (left right : Replica adm auth H) {V : Type}
    (verb : String) (contributes : Act → Prop) (policy : Bool)
    (evaluate : List Act → V) (invariant : ∀ {A B}, SetEq A B → evaluate A = evaluate B)
    (rawFault : List Act → Option (Lattice.Set Nat))
    (rawInvariant : ∀ {A B}, SetEq A B → rawFault A = rawFault B)
    (history : List Act) (complete : ∀ a, H.contains a ↔ a ∈ history) :
    ∃ t, ∀ n m, t ≤ n → t ≤ m →
      freezeRead H.contains verb contributes policy (rawFault (left.run n).accepted)
        evaluate (left.run n).accepted =
      freezeRead H.contains verb contributes policy (rawFault (right.run m).accepted)
        evaluate (right.run m).accepted := by
  obtain ⟨tl, hl⟩ := finite_history_stabilizes left history complete
  obtain ⟨tr, hr⟩ := finite_history_stabilizes right history complete
  refine ⟨max tl tr, ?_⟩
  intro n m hn hm
  have same : SetEq (left.run n).accepted (right.run m).accepted :=
    fun a => (hl n (by omega) a).trans (hr m (by omega) a).symm
  exact freezeRead_setEq same
    (reachable_wellFormed (behavior_reachable left.behavior n)).accepted_unique
    evaluate invariant _ _ (rawInvariant same)

/-- Concrete fault-aware domain display converges without any abstract
observation-extensionality premise supplied by the caller. -/
theorem finite_domain_agreement {adm : Admission} {auth : Act → Prop} {H : ValidHistory adm}
    (left right : Replica adm auth H) (verb key opener field : String)
    (history : List Act) (complete : ∀ a, H.contains a ↔ a ∈ history) :
    ∃ t, ∀ n m, t ≤ n → t ≤ m →
      domainRead verb key opener field (left.run n).accepted =
        domainRead verb key opener field (right.run m).accepted :=
  finite_observation_agreement left right (domainRead verb key opener field)
    (fun same => domainRead_setEq same verb key opener field) history complete

end Delivery
section LegacyClause
open StateKernel StateKernelClause StateKernelSEC StateKernelSemantics

/-- Metadata retained from the installed rule, including delegated resource
verbs that the older closure port represented only by a configuration name. -/
def selectionVerbs : Selection → List String
  | .verb v | .own v => [v]
  | .current v _ delete => v :: delete.toList
  | .byKey source _ _ | .bySigner source _ | .withField source _ => selectionVerbs source

def expressionVerbs (resourceVerbs : String → List String) : Expr → List String
  | .initial _ _ => []
  | .progress v => [v]
  | .scalar source _ _ | .existsRule source | .count source | .distinct source _
  | .valuesBy source _ _ => selectionVerbs source
  | .counter inc dec _ => selectionVerbs inc ++ selectionVerbs dec
  | .mapped plan | .histogram plan | .sum plan => selectionVerbs plan.source
  | .bounded name => resourceVerbs name

/-- Own initializer and all domain dependencies survive compilation of derived
map operations: histogram/sum retain their source's selection. -/
def initializerSources (resourceVerbs : String → List String) (domains : List Domain)
    (expression : Expr) : List (String × String) :=
  (match expression with | .initial v f => [(v, f)] | _ => []) ++
    ((domains.filter (fun d => (expressionVerbs resourceVerbs expression).contains d.verb)).map
      (fun d => (d.opener, d.field)))

def initializerConflict (sources : List (String × String)) (A : List Act) : Prop :=
  ∃ source ∈ sources, ∃ e, initialCarrier source.1 source.2 A = .top e

def initializerEvidence (sources : List (String × String)) (A : List Act) : Lattice.Set Nat :=
  fun address => ∃ source ∈ sources, ∃ e,
    initialCarrier source.1 source.2 A = .top e ∧ address ∈ e

inductive FieldObservation where
  | value (observation : Observation)
  | fault (evidence : Lattice.Set Nat)

def FieldEquivalent : FieldObservation → FieldObservation → Prop
  | .value a, .value b => Equivalent a b
  | .fault a, .fault b => a = b
  | _, _ => False

/-- Resource failures are explicit terminal observations, not absent numbers.
The verifier remains the existing typed closure port. -/
def resourceFailure (context : Context) (expression : Expr) (A : List Act) : Option (Lattice.Set Nat) :=
  match expression with
  | .bounded name => match context.resource A name with
      | .fault _ evidence => some (fun address => address ∈ evidence)
      | _ => none
  | _ => none

theorem resourceFailure_setEq (context : Context) (expression : Expr) {A B : List Act}
    (same : SetEq A B) : resourceFailure context expression A = resourceFailure context expression B := by
  cases expression <;> simp only [resourceFailure]
  rw [context.resource_ext A B same]

/-- Conflict-aware compiled display checks raw initializers before the legacy
selector can turn a conflicting domain into an empty successful collection. -/
noncomputable def evaluateField (context : Context) (resourceVerbs : String → List String)
    (domains : List Domain) (expression : Expr) (A : List Act) : FieldObservation := by
  classical
  let sources := initializerSources resourceVerbs domains expression
  let resource := resourceFailure context expression A
  exact if initializerConflict sources A ∨ resource.isSome then
      .fault (initializerEvidence sources A ∪ resource.getD ∅)
    else .value (evaluate (context.input A) domains expression)

theorem initializerConflict_setEq {sources : List (String × String)} {A B : List Act}
    (same : SetEq A B) : initializerConflict sources A ↔ initializerConflict sources B := by
  unfold initializerConflict
  simp only [initialCarrier_invariant same]

theorem initializerEvidence_setEq {sources : List (String × String)} {A B : List Act}
    (same : SetEq A B) : initializerEvidence sources A = initializerEvidence sources B := by
  funext address
  apply propext
  unfold initializerEvidence
  simp only [initialCarrier_invariant same]

/-- Compiled primitive, closure and derived dependencies all propagate an
initializer fork with its original finite witness addresses. -/
theorem evaluateField_fork (context : Context) (resourceVerbs : String → List String)
    (domains : List Domain) (expression : Expr) {A : List Act} {a b : Act}
    (opener field : String)
    (source : (opener, field) ∈ initializerSources resourceVerbs domains expression)
    (ha : a ∈ A) (hb : b ∈ A) (va : a.verb = opener) (vb : b.verb = opener)
    (different : a.addr ≠ b.addr) :
    ∃ evidence, evaluateField context resourceVerbs domains expression A = .fault evidence ∧
      a.addr ∈ evidence ∧ b.addr ∈ evidence := by
  classical
  obtain ⟨e, conflict, ea, eb⟩ := opener_fork_fault opener field ha hb va vb different
  have fault : initializerConflict (initializerSources resourceVerbs domains expression) A :=
    ⟨(opener, field), source, e, conflict⟩
  refine ⟨initializerEvidence (initializerSources resourceVerbs domains expression) A ∪
    (resourceFailure context expression A).getD ∅, ?_, ?_, ?_⟩
  · simp [evaluateField, fault]
  · exact Or.inl ⟨(opener, field), source, e, conflict, ea⟩
  · exact Or.inl ⟨(opener, field), source, e, conflict, eb⟩

theorem evaluateField_setEq (context : Context) (resourceVerbs : String → List String)
    (domains : List Domain) (expression : Expr) {A B : List Act}
    (ua : NodupAddr A) (ub : NodupAddr B) (same : SetEq A B) :
    FieldEquivalent (evaluateField context resourceVerbs domains expression A)
      (evaluateField context resourceVerbs domains expression B) := by
  classical
  unfold evaluateField
  dsimp only
  rw [resourceFailure_setEq context expression same]
  rw [show initializerConflict (initializerSources resourceVerbs domains expression) A ↔
      initializerConflict (initializerSources resourceVerbs domains expression) B from initializerConflict_setEq same]
  split
  · change _ ∪ _ = _ ∪ _
    rw [initializerEvidence_setEq same]
  · exact strong_convergence context domains expression ua ub same

/-- Conflict-free erasure is exactly the previous evaluator. -/
theorem evaluateField_forget (context : Context) (resourceVerbs : String → List String)
    (domains : List Domain) (expression : Expr) (A : List Act)
    (ordinary : ¬ initializerConflict (initializerSources resourceVerbs domains expression) A)
    (resourceOrdinary : resourceFailure context expression A = none) :
    evaluateField context resourceVerbs domains expression A =
      .value (evaluate (context.input A) domains expression) := by
  classical
  simp [evaluateField, ordinary, resourceOrdinary]

/-- A legacy compiled field has the full accepted-set carrier. The summarizing
per-head lifts in StateLift refine this identity carrier where possible. -/
structure CompiledTerm where
  expression : Expr
  carrier : FinSet Act

/-- Interpretation is independent of which unique accepted-history
representative is chosen for the carrier. Uses the existing kernel evaluator,
including HLC, derived fields and delegated closure/resource semantics. -/
def TermMeaning (context : Context) (resourceVerbs : String → List String)
    (domains : List Domain) (term : CompiledTerm) (output : FieldObservation) : Prop :=
  ∀ A, NodupAddr A → rawHistory A = term.carrier →
    FieldEquivalent (evaluateField context resourceVerbs domains term.expression A) output

/-- Whole-clause lift, in the original declaration order. -/
def compileTerms (clause : Compiled) (A : List Act) : List (String × CompiledTerm) :=
  clause.fields.map (fun (name, expression) => (name, ⟨expression, rawHistory A⟩))

/-- Whole compiled observation after raw faults have propagated. -/
noncomputable def observeFields (context : Context) (resourceVerbs : String → List String)
    (clause : Compiled) (A : List Act) : List (String × FieldObservation) :=
  clause.fields.map (fun (name, expression) =>
    (name, evaluateField context resourceVerbs clause.domains expression A))

/-- Componentwise union for the full clause product, with names and expressions
fixed. The carrier is independent of its display and dependency faults. -/
theorem compileTerms_union (clause : Compiled) (A B : List Act) :
    compileTerms clause (A ++ B) = (compileTerms clause A).map (fun (name, term) =>
      (name, {term with carrier := term.carrier ⊔ rawHistory B})) := by
  simp [compileTerms, rawHistory_union, List.map_map]

theorem compileTerms_put (clause : Compiled) (a : Act) (A : List Act) :
    compileTerms clause (a :: A) = (compileTerms clause A).map (fun (name, term) =>
      (name, {term with carrier := FinSet.mk [a] ⊔ term.carrier})) := by
  simp [compileTerms, rawHistory, lift_cons, List.map_map]

/-- Fault-aware compiled observations interpret the product of raw lifts,
including initializer faults propagated to primitive, closure and derived fields. -/
theorem compiled_clause_correspondence (context : Context)
    (resourceVerbs : String → List String) (clause : Compiled)
    (A : List Act) (unique : NodupAddr A) :
    List.Forall₂ (fun term output => term.1 = output.1 ∧
      TermMeaning context resourceVerbs clause.domains term.2 output.2)
      (compileTerms clause A) (observeFields context resourceVerbs clause A) := by
  unfold compileTerms observeFields
  induction clause.fields with
  | nil => exact .nil
  | cons field rest ih =>
      refine .cons ⟨rfl, ?_⟩ ih
      intro B uniqueB equal
      exact evaluateField_setEq context resourceVerbs clause.domains field.2 uniqueB unique
        (rawHistory_faithful equal)

/-- Finite delivery converges on the whole conflict-aware legacy clause,
including propagated initializer and resource-port faults. This uses the typed
resource port's extensionality; it does not prove that verifier's witness
classification or persistence under strict history growth. -/
theorem fault_aware_strong_eventual_consistency {adm : AdmissionStratification.Admission}
    {auth : Act → Prop} {H : StateKernelDelivery.ValidHistory adm}
    (left right : StateKernelDelivery.Replica adm auth H) (context : Context)
    (resourceVerbs : String → List String) (clause : Compiled)
    (history : List Act) (complete : ∀ a, H.contains a ↔ a ∈ history) :
    ∃ t, ∀ n m, t ≤ n → t ≤ m →
      List.Forall₂ (fun a b => a.1 = b.1 ∧ FieldEquivalent a.2 b.2)
        (observeFields context resourceVerbs clause (left.run n).accepted)
        (observeFields context resourceVerbs clause (right.run m).accepted) := by
  obtain ⟨tl, hl⟩ := StateKernelDelivery.finite_history_stabilizes left history complete
  obtain ⟨tr, hr⟩ := StateKernelDelivery.finite_history_stabilizes right history complete
  refine ⟨max tl tr, ?_⟩
  intro n m hn hm
  have same : SetEq (left.run n).accepted (right.run m).accepted :=
    fun a => (hl n (by omega) a).trans (hr m (by omega) a).symm
  have uniqueLeft := (StateRefinement.reachable_wellFormed (StateRefinement.behavior_reachable left.behavior n)).accepted_unique
  have uniqueRight := (StateRefinement.reachable_wellFormed (StateRefinement.behavior_reachable right.behavior m)).accepted_unique
  unfold observeFields
  induction clause.fields with
  | nil => exact .nil
  | cons field rest ih =>
    exact .cons ⟨rfl, evaluateField_setEq context resourceVerbs clause.domains
      field.2 uniqueLeft uniqueRight same⟩ ih

/-- The no-new-observation fragment recovers the existing SEC theorem over
actual compiled clauses and the original observation equivalence. -/
theorem legacy_strong_eventual_consistency {adm : AdmissionStratification.Admission}
    {auth : Act → Prop} {H : StateKernelDelivery.ValidHistory adm}
    (left right : StateKernelDelivery.Replica adm auth H) (context : Context) (clause : Compiled)
    (history : List Act) (complete : ∀ a, H.contains a ↔ a ∈ history) :
    ∃ t, ∀ n m, t ≤ n → t ≤ m →
      List.Forall₂ (fun a b => a.1 = b.1 ∧ Equivalent a.2 b.2)
        (evaluateFields (context.input (left.run n).accepted) clause.domains clause.fields)
        (evaluateFields (context.input (right.run m).accepted) clause.domains clause.fields) :=
  StateKernelDelivery.strong_eventual_consistency left right context clause history complete
end LegacyClause

end CBCL.StateLVar
