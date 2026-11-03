import LeanCbcl.State
import LeanCbcl.AdmissionStratification

/-!
# State execution refinement (SPEC-019 CON-1906)

A typed, single-thread execution model with fixed dialect, admission and
immutable authentication context. It is not a Rust or cryptographic refinement
proof. Scheduling has no fairness assumption. Business specifications are
supplied independently; the counter instance defines labelled arithmetic
without referring to the concrete machine or its observation.
-/

namespace CBCL.StateRefinement

open State AdmissionStratification

/-- Bookkeeping for one pinned thread; only `accepted` contributes to business state. -/
structure Execution where
  /-- Authenticated, address-consistent acts received so far. -/
  received : List Act := []
  /-- Received candidates awaiting a terminal scheduling decision. -/
  pending : List Act := []
  /-- Accepted history, with duplicate insertion suppressed. -/
  accepted : List Act := []
  /-- Candidates rejected by the fixed admission function. -/
  rejected : List Act := []
  deriving DecidableEq

/-- The empty execution state before receipt of the opener. -/
def initial : Execution := ⟨[], [], [], []⟩

/-- Receipt and scheduling are separate. Only acceptance carries a business label.
Unknown candidates stay pending. A duplicate receipt never reapplies an act. -/
inductive Step (adm : Admission) (authenticated : Act → Prop) :
    Execution → Option Act → Execution → Prop where
  | receive (s : Execution) (a : Act) (ha : authenticated a)
      (fresh : ∀ b ∈ s.received, b.addr ≠ a.addr) :
      Step adm authenticated s none
        { s with received := a :: s.received, pending := a :: s.pending }
  | duplicate (s : Execution) (a : Act) (ha : a ∈ s.received) :
      Step adm authenticated s none s
  | accept (s : Execution) (a : Act) (hp : a ∈ s.pending)
      (hv : adm.admit s.accepted a = .accepted) :
      Step adm authenticated s (some a)
        { s with accepted := insertAct a s.accepted, pending := s.pending.erase a }
  | reject (s : Execution) (a : Act) (hp : a ∈ s.pending)
      (hv : adm.admit s.accepted a = .rejected) :
      Step adm authenticated s none
        { s with pending := s.pending.erase a, rejected := insertAct a s.rejected }
  | wait (s : Execution) (a : Act) (hp : a ∈ s.pending)
      (hv : adm.admit s.accepted a = .pending) :
      Step adm authenticated s none s
  | idle (s : Execution) : Step adm authenticated s none s

/-- The invariants are established from the empty initial state, not assumed
anew at each reachable state. Authentication is a typed boundary premise. -/
structure WellFormed (authenticated : Act → Prop) (s : Execution) : Prop where
  received_unique : NodupAddr s.received
  accepted_unique : NodupAddr s.accepted
  pending_received : ∀ a ∈ s.pending, a ∈ s.received
  accepted_received : ∀ a ∈ s.accepted, a ∈ s.received
  received_authenticated : ∀ a ∈ s.received, authenticated a

theorem initial_wellFormed (authenticated : Act → Prop) :
    WellFormed authenticated initial := by
  constructor <;> simp [initial, NodupAddr]

private theorem insert_mem {a b : Act} {A : List Act}
    (hb : b ∈ insertAct a A) : b = a ∨ b ∈ A := by
  exact List.mem_cons.mp ((insertAct_setEq a A b).mp hb)

private theorem insert_unique_of_received {R A : List Act} {a : Act}
    (hR : NodupAddr R) (hA : NodupAddr A)
    (hsub : ∀ b ∈ A, b ∈ R) (ha : a ∈ R) : NodupAddr (insertAct a A) := by
  by_cases hin : a ∈ A
  · simpa [insertAct, hin] using hA
  · apply hA.insertAct
    intro b hb he
    have hba := hR.eq_of_addr (hsub b hb) ha he
    exact hin (hba ▸ hb)

theorem step_wellFormed {adm : Admission} {auth : Act → Prop}
    {s t : Execution} {e : Option Act} (hs : WellFormed auth s)
    (h : Step adm auth s e t) : WellFormed auth t := by
  cases h with
  | receive a ha fresh =>
    refine ⟨?_, hs.accepted_unique, ?_, ?_, ?_⟩
    · simp only [NodupAddr, List.map_cons, List.nodup_cons, List.mem_map]
      exact ⟨fun ⟨b, hb, he⟩ => fresh b hb he, hs.received_unique⟩
    · intro b hb
      rcases List.mem_cons.mp hb with he | hb
      · exact List.mem_cons.mpr (Or.inl he)
      · exact List.mem_cons.mpr (Or.inr (hs.pending_received b hb))
    · intro b hb; exact List.mem_cons.mpr (Or.inr (hs.accepted_received b hb))
    · intro b hb
      rcases List.mem_cons.mp hb with he | hb
      · exact he ▸ ha
      · exact hs.received_authenticated b hb
  | accept a hp _ =>
    refine ⟨hs.received_unique, ?_, ?_, ?_, hs.received_authenticated⟩
    · exact insert_unique_of_received hs.received_unique hs.accepted_unique
        hs.accepted_received (hs.pending_received a hp)
    · intro b hb; exact hs.pending_received b (List.mem_of_mem_erase hb)
    · intro b hb
      rcases insert_mem hb with he | hb
      · exact he ▸ hs.pending_received a hp
      · exact hs.accepted_received b hb
  | reject a _ _ =>
    exact ⟨hs.received_unique, hs.accepted_unique,
      fun b hb => hs.pending_received b (List.mem_of_mem_erase hb),
      hs.accepted_received, hs.received_authenticated⟩
  | duplicate => exact hs
  | wait => exact hs
  | idle => exact hs

/-- Finite reachability under the concrete transition relation. -/
inductive Reachable (adm : Admission) (auth : Act → Prop) : Execution → Prop where
  | start : Reachable adm auth initial
  | advance {s t : Execution} {e : Option Act} :
      Reachable adm auth s → Step adm auth s e t → Reachable adm auth t

theorem reachable_wellFormed {adm : Admission} {auth : Act → Prop} {s : Execution}
    (h : Reachable adm auth s) : WellFormed auth s := by
  induction h with
  | start => exact initial_wellFormed auth
  | advance _ hstep ih => exact step_wellFormed ih hstep

theorem accepted_authenticated {adm : Admission} {auth : Act → Prop} {s : Execution}
    (h : Reachable adm auth s) {a : Act} (ha : a ∈ s.accepted) : auth a := by
  have hw := reachable_wellFormed h
  exact hw.received_authenticated a (hw.accepted_received a ha)

/-- No fresh acceptance can originate outside the received candidate set. -/
theorem new_accepted_received {adm : Admission} {auth : Act → Prop}
    {s t : Execution} {e : Option Act} (hs : WellFormed auth s)
    (h : Step adm auth s e t) {a : Act}
    (ha : a ∈ t.accepted) (hnew : a ∉ s.accepted) : a ∈ s.received := by
  cases h with
  | accept b hp _ =>
    rcases insert_mem ha with he | ha
    · exact he ▸ hs.pending_received b hp
    · exact False.elim (hnew ha)
  | receive => exact False.elim (hnew ha)
  | duplicate => exact False.elim (hnew ha)
  | reject => exact False.elim (hnew ha)
  | wait => exact False.elim (hnew ha)
  | idle => exact False.elim (hnew ha)

theorem accepted_address_conflict_impossible {adm : Admission} {auth : Act → Prop}
    {s : Execution} (h : Reachable adm auth s) {a b : Act}
    (ha : a ∈ s.accepted) (hb : b ∈ s.accepted) (he : a.addr = b.addr) : a = b :=
  (reachable_wellFormed h).accepted_unique.eq_of_addr ha hb he

theorem accept_requires_pending {adm : Admission} {auth : Act → Prop}
    {s t : Execution} {a : Act} (h : Step adm auth s (some a) t) :
    a ∈ s.pending ∧ adm.admit s.accepted a = .accepted := by
  cases h with
  | accept _ hp hv => exact ⟨hp, hv⟩

theorem internal_preserves_accepted {adm : Admission} {auth : Act → Prop}
    {s t : Execution} (h : Step adm auth s none t) : t.accepted = s.accepted := by
  cases h <;> rfl

/-- Labelled business transitions are independent of execution bookkeeping. -/
structure Business (β : Type) where
  /-- Independently specified initial business states. -/
  init : β → Prop
  /-- Independently specified effect of one accepted action. -/
  next : Act → β → β → Prop

/-- Stuttering preserves time indices and permits infinite internal activity. -/
def AbstractStep {β : Type} (B : Business β) (e : Option Act) (x y : β) : Prop :=
  x = y ∨ ∃ a, e = some a ∧ B.next a x y

/-- Obligations connecting an observation to an independent business machine. -/
structure Simulation {β : Type} (B : Business β) (adm : Admission)
    (auth : Act → Prop) (observe : List Act → β) : Prop where
  initial : B.init (observe [])
  acceptance : ∀ s a, WellFormed auth s → a ∈ s.pending →
    adm.admit s.accepted a = .accepted → a ∉ s.accepted →
    B.next a (observe s.accepted) (observe (insertAct a s.accepted))

theorem step_simulation {β : Type} {B : Business β} {adm : Admission}
    {auth : Act → Prop} {observe : List Act → β}
    (sim : Simulation B adm auth observe) {s t : Execution} {e : Option Act}
    (hs : WellFormed auth s) (h : Step adm auth s e t) :
    AbstractStep B e (observe s.accepted) (observe t.accepted) := by
  cases h with
  | accept a hp hv =>
    by_cases ha : a ∈ s.accepted
    · exact Or.inl (by simp [insertAct, ha])
    · exact Or.inr ⟨a, rfl, sim.acceptance s a hs hp hv ha⟩
  | receive => exact Or.inl rfl
  | duplicate => exact Or.inl rfl
  | reject => exact Or.inl rfl
  | wait => exact Or.inl rfl
  | idle => exact Or.inl rfl

/-- Fresh accepted events cannot bypass the independent business transition. -/
theorem fresh_acceptance_effect {β : Type} {B : Business β} {adm : Admission}
    {auth : Act → Prop} {observe : List Act → β}
    (sim : Simulation B adm auth observe) {s t : Execution} {a : Act}
    (hs : WellFormed auth s) (h : Step adm auth s (some a) t)
    (fresh : a ∉ s.accepted) : B.next a (observe s.accepted) (observe t.accepted) := by
  cases h with
  | accept _ hp hv => exact sim.acceptance s a hs hp hv fresh

/-- Finite business reachability with explicit stuttering. -/
inductive BusinessReachable {β : Type} (B : Business β) : β → Prop where
  | start {x : β} : B.init x → BusinessReachable B x
  | advance {x y : β} {e : Option Act} : BusinessReachable B x →
      AbstractStep B e x y → BusinessReachable B y

theorem reachable_simulation {β : Type} {B : Business β} {adm : Admission}
    {auth : Act → Prop} {observe : List Act → β}
    (sim : Simulation B adm auth observe) {s : Execution}
    (h : Reachable adm auth s) : BusinessReachable B (observe s.accepted) := by
  induction h with
  | start => exact .start sim.initial
  | advance hs ht ih =>
    exact .advance ih (step_simulation sim (reachable_wellFormed hs) ht)

/-- Infinite time-indexed execution, without delivery or scheduling fairness. -/
def Behavior (adm : Admission) (auth : Act → Prop)
    (run : Nat → Execution) (events : Nat → Option Act) : Prop :=
  run 0 = initial ∧ ∀ n, Step adm auth (run n) (events n) (run (n + 1))

/-- Infinite business behavior retaining each concrete time index. -/
def BusinessBehavior {β : Type} (B : Business β)
    (run : Nat → β) (events : Nat → Option Act) : Prop :=
  B.init (run 0) ∧ ∀ n, AbstractStep B (events n) (run n) (run (n + 1))

theorem behavior_reachable {adm : Admission} {auth : Act → Prop}
    {run : Nat → Execution} {events : Nat → Option Act}
    (h : Behavior adm auth run events) (n : Nat) : Reachable adm auth (run n) := by
  induction n with
  | zero => rw [h.1]; exact .start
  | succ n ih => exact .advance ih (h.2 n)

/-- The forward simulation capstone: all mapped behaviors satisfy the abstract
initial predicate and labelled transition relation, with stuttering retained. -/
theorem behavior_refinement {β : Type} {B : Business β} {adm : Admission}
    {auth : Act → Prop} {observe : List Act → β}
    (sim : Simulation B adm auth observe) {run : Nat → Execution}
    {events : Nat → Option Act} (h : Behavior adm auth run events) :
    BusinessBehavior B (fun n => observe (run n).accepted) events := by
  refine ⟨?_, ?_⟩
  · change B.init (observe (run 0).accepted)
    rw [h.1]; exact sim.initial
  · intro n
    exact step_simulation sim (reachable_wellFormed (behavior_reachable h n)) (h.2 n)

/-! ## Independent counter machine (REQ-1937) -/

/-- The independent counter specification: labelled arithmetic on a balance. -/
def counterBusiness (inc dec key : String) : Business Int where
  init x := x = 0
  next a x y :=
    (a.verb = inc ∧ y = x + amount key a) ∨
    (a.verb = dec ∧ y = x - amount key a) ∨
    (a.verb ≠ inc ∧ a.verb ≠ dec ∧ y = x)

/-- Arithmetic effect of insertion; the concrete counter is reused, not
redefined to make simulation true by construction. -/
theorem counter_insert_effect (inc dec key : String) (a : Act) (A : List Act) :
    counter inc dec key (insertAct a A) = counter inc dec key A +
      (if a ∈ A then 0 else
        (if a.verb = inc then amount key a else 0) -
        (if a.verb = dec then amount key a else 0)) := by
  by_cases ha : a ∈ A
  · simp [insertAct, ha]
  · simp only [insertAct, if_neg ha, counter, acts, List.filter_cons]
    by_cases hi : a.verb = inc <;> by_cases hd : a.verb = dec <;>
      simp_all [sumField_cons] <;> omega

theorem counter_simulation (inc dec key : String) (distinct : inc ≠ dec)
    (adm : Admission) (auth : Act → Prop) :
    Simulation (counterBusiness inc dec key) adm auth (counter inc dec key) := by
  refine ⟨by simp [counterBusiness, counter, sumField, acts], ?_⟩
  intro s a _ _ _ ha
  have effect := counter_insert_effect inc dec key a s.accepted
  have transition : (counterBusiness inc dec key).next a
      (counter inc dec key s.accepted) (counter inc dec key (insertAct a s.accepted)) := by
    simp only [if_neg ha] at effect
    by_cases hi : a.verb = inc
    · have hd : a.verb ≠ dec := fun he => distinct (hi.symm.trans he)
      exact Or.inl ⟨hi, by simpa only [if_pos hi, if_neg hd, Int.sub_zero] using effect⟩
    · by_cases hd : a.verb = dec
      · exact Or.inr (Or.inl ⟨hd, by simpa only [if_neg hi, if_pos hd,
          Int.zero_sub, Int.zero_add, Int.sub_eq_add_neg] using effect⟩)
      · exact Or.inr (Or.inr ⟨hi, hd, by simpa only [if_neg hi, if_neg hd,
          Int.sub_zero, Int.add_zero] using effect⟩)
  exact transition

theorem counter_behavior_refinement (inc dec key : String) (distinct : inc ≠ dec)
    {adm : Admission} {auth : Act → Prop} {run : Nat → Execution}
    {events : Nat → Option Act} (h : Behavior adm auth run events) :
    BusinessBehavior (counterBusiness inc dec key)
      (fun n => counter inc dec key (run n).accepted) events :=
  behavior_refinement (counter_simulation inc dec key distinct adm auth) h

/-! ## Kernel-checked regression examples (TEST-1954–1958) -/

namespace Examples

/-- An increment of seven with a fresh address. -/
def inc7 : Act := ⟨10, "inc", "alice", [], [("amount", .int 7)], []⟩
/-- A decrement of three citing the increment as predecessor. -/
def dec3 : Act := ⟨20, "dec", "bob", [10], [("amount", .int 3)], []⟩
/-- A different body claiming the increment's address. -/
def conflict : Act := { inc7 with fields := [("amount", .int 99)] }

/-- A small citation-aware gate demonstrates child-before-parent scheduling.
It is an example admission, not a replacement for the deployed R5/R6 checker. -/
def admission : Admission where
  shape _ := true
  causal store a :=
    if a.preds.all (fun p => store.any (fun b => b.addr == p)) then .accepted else .pending

/-- Out-of-order receipt with no accepted predecessor. -/
def childReceived : Execution := { initial with received := [dec3], pending := [dec3] }
/-- Both candidates received but neither accepted. -/
def bothReceived : Execution :=
  { childReceived with received := [inc7, dec3], pending := [inc7, dec3] }
/-- Accepting the parent unblocks the pending child. -/
def parentAccepted : Execution :=
  { bothReceived with accepted := [inc7], pending := [dec3] }
/-- The completed example history has balance four. -/
def bothAccepted : Execution :=
  { parentAccepted with accepted := [dec3, inc7], pending := [] }

theorem receive_child : Step admission (fun _ => True) initial none childReceived := by
  apply Step.receive initial dec3 trivial
  simp [initial]

theorem wait_for_parent : Step admission (fun _ => True) childReceived none childReceived := by
  apply Step.wait childReceived dec3
  · decide
  · decide

theorem receive_parent : Step admission (fun _ => True) childReceived none bothReceived := by
  apply Step.receive childReceived inc7 trivial
  decide

theorem accept_parent : Step admission (fun _ => True) bothReceived (some inc7) parentAccepted := by
  exact Step.accept bothReceived inc7 (adm := admission) (authenticated := fun _ => True)
    (by decide) (by decide)

theorem accept_child : Step admission (fun _ => True) parentAccepted (some dec3) bothAccepted := by
  exact Step.accept parentAccepted dec3 (adm := admission) (authenticated := fun _ => True)
    (by decide) (by decide)

/-- A constant observation cannot refine a business that forbids all effects. -/
theorem false_business_cannot_simulate :
    ¬ Simulation (β := Unit) ⟨fun _ => True, fun _ _ _ => False⟩
      admission (fun _ => True) (fun _ => ()) := by
  intro sim
  have reachable : Reachable admission (fun _ => True) bothReceived :=
    .advance (.advance .start receive_child) receive_parent
  exact fresh_acceptance_effect sim (reachable_wellFormed reachable) accept_parent
    (by decide)

theorem out_of_order_reachable : Reachable admission (fun _ => True) bothAccepted :=
  .advance (.advance (.advance (.advance (.advance .start receive_child)
    wait_for_parent) receive_parent) accept_parent) accept_child

theorem out_of_order_balance : counter "inc" "dec" "amount" bothAccepted.accepted = 4 := by
  decide

theorem duplicate_does_not_count :
    counter "inc" "dec" "amount" (insertAct inc7 bothAccepted.accepted) = 4 := by
  decide

theorem decrement_not_addition :
    ¬ (counterBusiness "inc" "dec" "amount").next dec3 7 10 := by
  unfold counterBusiness
  decide

theorem receipt_not_acceptance : counter "inc" "dec" "amount" childReceived.accepted = 0 := by
  decide

theorem absent_candidate_cannot_accept :
    ¬ Step admission (fun _ => True) initial (some inc7) parentAccepted := by
  intro h
  have hp := (accept_requires_pending h).1
  simp [initial] at hp

theorem missing_predecessor_cannot_accept :
    ¬ Step admission (fun _ => True) childReceived (some dec3) bothAccepted := by
  intro h
  have hv := (accept_requires_pending h).2
  have hn : admission.admit childReceived.accepted dec3 = .pending := by decide
  rw [hn] at hv
  contradiction

theorem conflicting_history_not_reachable :
    ¬ Reachable admission (fun _ => True)
      { initial with accepted := [inc7, conflict] } := by
  intro h
  have he := accepted_address_conflict_impossible h (a := inc7) (b := conflict)
    (by simp) (by simp) (by rfl)
  have hn : inc7 ≠ conflict := by decide
  exact hn he

end Examples

end CBCL.StateRefinement
