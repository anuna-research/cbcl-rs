import LeanCbcl.ConsensusFree.OwnedProgress

/-! SPEC-034 financial part of owner readiness: derive full-allocation head funding
from checked admission and immutable costs. Observed finalization is an input event,
not a liveness oracle; this file never assumes it eventually happens. -/
namespace CBCL.ConsensusFree.OwnerFunding
variable {N R : Nat}
/-- Immutable request identities and resource effects used by owner admission accounting. -/
structure Costs (N R : Nat) where
  /-- Abstract verified wire identities; incoming catalogue is external-only. -/
  requestId : Fin N → String
  /-- Verified external credit identities, disjoint from owner-issued request identities. -/
  incomingId : Fin N → String
  requestUnique : ∀ i j, requestId i = requestId j → i = j
  incomingUnique : ∀ i j, incomingId i = incomingId j → i = j
  separate : ∀ i j, requestId i ≠ incomingId j
  /-- Initial certified allocation in each resource coordinate. -/
  initial : Fin R → Nat
  /-- Nonnegative resource debit of each admitted request. -/
  debit : Fin N → Fin R → Nat
  /-- Nonnegative resource credit produced by each finalized owner request. -/
  credit : Fin N → Fin R → Nat
  /-- Nonnegative resource credit carried by each external proof. -/
  incomingCredit : Fin N → Fin R → Nat
  /-- Authentication result for each external credit proof. -/
  incomingAuthenticated : Fin N → Bool
/-- Durable admission, issuance and verified-receipt facts for owner accounting. -/
structure State (N R : Nat) where
  /-- Requests durably admitted and reserved by the owner. -/
  accepted : Fin N → Bool
  /-- Requests with an immutable durably issued operation. -/
  issued : Fin N → Bool
  /-- Issued requests whose effects certificates the owner has verified. -/
  final : Fin N → Bool
  /-- External credit proofs imported into the owner's finalized view. -/
  incoming : Fin N → Bool

/-- Owner funding state before admissions, issuance or incoming receipts. -/
def initial : State N R := ⟨fun _ => false, fun _ => false, fun _ => false, fun _ => false⟩
/-- Sum a nonnegative weight over a selected finite identity mask. -/
def marked (mask : Fin N → Bool) (weight : Fin N → Nat) : Int :=
  isum (List.finRange N) (fun i => if mask i then (weight i : Int) else 0)
private theorem isum_zero (xs : List α) : isum xs (fun _ => 0) = 0 := by
  induction xs <;> simp_all [isum]
@[simp] theorem marked_empty (weight : Fin N → Nat) : marked (fun _ => false) weight = 0 := by
  simp [marked, isum_zero]

theorem marked_set (mask : Fin N → Bool) (weight : Fin N → Nat) (i : Fin N) :
    marked (setAt mask i true) weight = marked mask weight - (if mask i then (weight i : Int) else 0) + weight i := by
  have eq : (fun j => if setAt mask i true j then (weight j : Int) else 0) =
      setAt (fun j => if mask j then (weight j : Int) else 0) i (weight i) := by
    funext j; by_cases ji : j = i <;> simp_all [setAt]
  unfold marked
  rw [eq, isum_update _ _ i _ (finRange_unique N) (by simp)]

/-- Certified funds minus all admitted request debits, counting only verified credits. -/
def available (c : Costs N R) (s : State N R) (d : Fin R) : Int :=
  c.initial d + marked s.incoming (fun i => c.incomingCredit i d) + marked s.final (fun i => c.credit i d) - marked s.accepted (fun i => c.debit i d)
/-- Finalized balance before subtracting outstanding admission reservations. -/
def view (c : Costs N R) (s : State N R) (d : Fin R) : Int :=
  c.initial d + marked s.incoming (fun i => c.incomingCredit i d) + marked s.final (fun i => c.credit i d) - marked s.final (fun i => c.debit i d)
/-- Debits reserved by admitted requests that are not yet finalized. -/
def reserved (c : Costs N R) (s : State N R) (d : Fin R) : Int :=
  marked (fun i => s.accepted i && !s.final i) (fun i => c.debit i d)
/-- Full resource allocation after debits of all issued requests. -/
def allocation (c : Costs N R) (s : State N R) (d : Fin R) : Int :=
  c.initial d + marked s.incoming (fun i => c.incomingCredit i d) + marked s.final (fun i => c.credit i d) - marked s.issued (fun i => c.debit i d)

/-- Reserve a fresh admitted request in the funding state. -/
def enqueue (s : State N R) (i : Fin N) : State N R := {s with accepted := setAt s.accepted i true}
/-- Mark an admitted request as durably issued. -/
def issue (s : State N R) (i : Fin N) : State N R := {s with issued := setAt s.issued i true}
/-- Record the owner's first verified effects receipt for an issued request. -/
def finalize (s : State N R) (i : Fin N) : State N R := {s with final := setAt s.final i true}
/-- Record the owner's first verified receipt of an external credit. -/
def income (s : State N R) (i : Fin N) : State N R := {s with incoming := setAt s.incoming i true}

/-- Checked admission, issuance, receipt and replay transitions for owner funding. -/
inductive Step (c : Costs N R) : State N R → State N R → Prop where
  | enqueue (s i) (fresh : s.accepted i = false) (funded : ∀ d, (c.debit i d : Int) ≤ available c s d) : Step c s (enqueue s i)
  | issue (s i) (admitted : s.accepted i = true) : Step c s (issue s i)
  | finalize (s i) (issued : s.issued i = true) (fresh : s.final i = false) : Step c s (finalize s i)
  | income (s i) (verified : c.incomingAuthenticated i = true) (fresh : s.incoming i = false) : Step c s (income s i)
  | replay (s) : Step c s s
/-- Admission coverage and nonnegative available funds preserved by funding steps. -/
structure Invariant (c : Costs N R) (s : State N R) : Prop where
  issued_admitted : ∀ i, s.issued i = true → s.accepted i = true
  final_issued : ∀ i, s.final i = true → s.issued i = true
  funding : ∀ d, 0 ≤ available c s d

theorem initial_invariant (c : Costs N R) : Invariant c initial := by
  refine ⟨by intros; contradiction, by intros; contradiction, ?_⟩
  intro d; simp [available, initial]

/-- A final effects receipt changes spendable-minus-reserved funds by its credit,
not minus its debit a second time. This applies separately to every coordinate. -/
theorem finalization_conservation (c : Costs N R) (s : State N R) (i : Fin N)
    (fresh : s.final i = false) (d : Fin R) :
    available c (finalize s i) d = available c s d + c.credit i d := by
  simp only [available, finalize, marked_set, fresh, Bool.false_eq_true, ite_false]
  omega

theorem step_invariant (h : Invariant c s) (st : Step c s t) : Invariant c t := by
  cases st with
  | enqueue i fresh funded =>
    refine ⟨?_, h.final_issued, ?_⟩
    · intro j hj
      by_cases ji : j = i
      · subst j; simp [enqueue, setAt]
      · simpa [enqueue, setAt, ji] using h.issued_admitted j hj
    · intro d
      have bound := funded d
      simp only [available, enqueue, marked_set, fresh, Bool.false_eq_true, ite_false]
      unfold available at bound
      omega
  | issue i admitted =>
    refine ⟨?_, ?_, h.funding⟩
    · intro j hj
      by_cases ji : j = i
      · subst j; exact admitted
      · exact h.issued_admitted j (by simpa [issue, setAt, ji] using hj)
    · intro j hj
      by_cases ji : j = i
      · subst j; simp [issue, setAt]
      · simpa [issue, setAt, ji] using h.final_issued j hj
  | finalize i issued fresh =>
    refine ⟨h.issued_admitted, ?_, ?_⟩
    · intro j hj
      by_cases ji : j = i
      · subst j; exact issued
      · exact h.final_issued j (by simpa [finalize, setAt, ji] using hj)
    · intro d
      rw [finalization_conservation c _ _ fresh d]
      have := h.funding d
      omega
  | income i verified fresh =>
    refine ⟨h.issued_admitted, h.final_issued, ?_⟩
    intro d
    have := h.funding d
    simp only [available, income, marked_set, fresh, Bool.false_eq_true, ite_false] at *
    omega
  | replay => exact h

/-- Connect the normalized proof expression to the driver's actual finalized-view
minus outstanding-reservation calculation. No serialized capacity cache is trusted. -/
theorem view_minus_reservations (h : Invariant c s) (d : Fin R) :
    view c s d - reserved c s d = available c s d := by
  have costs : marked s.accepted (fun i => c.debit i d) - marked s.final (fun i => c.debit i d) = reserved c s d := by
    unfold marked reserved
    rw [← isum_sub]
    apply isum_congr
    intro i _
    have subset : s.final i = true → s.accepted i = true := fun hf => h.issued_admitted i (h.final_issued i hf)
    cases ha : s.accepted i <;> cases hf : s.final i <;> simp_all
  unfold view available
  omega

private theorem isum_mono (xs : List α) (a b : α → Int)
    (bound : ∀ i ∈ xs, a i ≤ b i) : isum xs a ≤ isum xs b := by
  induction xs with
  | nil => simp [isum]
  | cons i xs ih =>
    have head := bound i (by simp)
    have tail := ih (fun j hj => bound j (by simp [hj]))
    simp only [isum]; omega

/-- Full-capacity head funding is derived from admission/reservation invariants
and exact held books; it is not an assumed SignAllowed/funding premise. -/
theorem unissued_head_funded {c : Costs N R} {s : State N R}
    (h : Invariant c s) (i : Fin N) (admitted : s.accepted i = true)
    (unissued : s.issued i = false) (d : Fin R) : (c.debit i d : Int) ≤ allocation c s d := by
  have pointwise : marked s.issued (fun j => c.debit j d) + c.debit i d ≤ marked s.accepted (fun j => c.debit j d) := by
    have bound : isum (List.finRange N) (fun j =>
        (if s.issued j then (c.debit j d : Int) else 0) + (if j = i then (c.debit i d : Int) else 0)) ≤ marked s.accepted (fun j => c.debit j d) := by
      apply isum_mono
      intro j _
      by_cases ji : j = i
      · subst j; simp [admitted, unissued]
      · have subset := h.issued_admitted j
        cases hi : s.issued j <;> cases ha : s.accepted j <;> simp_all
    have single : isum (List.finRange N) (fun j => if j = i then (c.debit i d : Int) else 0) = c.debit i d := by
      change isum (List.finRange N) (setAt (fun _ => 0) i (c.debit i d)) = c.debit i d
      rw [isum_update _ _ i _ (finRange_unique N) (by simp)]
      simp [isum_zero]
    rw [isum_add, single] at bound
    exact bound
  have funds := h.funding d
  unfold available allocation at *
  omega

/-- Finite sequences of funding transitions from a chosen state. -/
inductive Run (c : Costs N R) : State N R → State N R → Prop where
  | refl (s) : Run c s s
  | next : Run c s t → Step c t u → Run c s u

theorem run_invariant (run : Run c initial s) : Invariant c s := by
  induction run with
  | refl => exact initial_invariant c
  | next _ step ih => exact step_invariant ih step

theorem received_income_authenticated (run : Run c initial s) (i : Fin N)
    (received : s.incoming i = true) : c.incomingAuthenticated i = true := by
  induction run with
  | refl => simp [initial] at received
  | next prior step ih =>
    cases step with
    | income j verified fresh =>
      by_cases ij : i = j
      · subst j; exact verified
      · exact ih (by simpa [income, setAt, ij] using received)
    | enqueue => exact ih received
    | issue => exact ih received
    | finalize => exact ih received
    | replay => exact ih received

theorem admitted_head_funded (run : Run c initial s) (i : Fin N)
    (accepted : s.accepted i = true) (unissued : s.issued i = false) (d : Fin R) :
    (c.debit i d : Int) ≤ allocation c s d :=
  unissued_head_funded (run_invariant run) i accepted unissued d

namespace Witness
/-- Two reserved debits of seven hundred and three hundred from one thousand. -/
def costs : Costs 2 1 where
  requestId := fun i => "request-" ++ toString i.val
  incomingId := fun i => "external-" ++ toString i.val
  requestUnique := by decide
  incomingUnique := by decide
  separate := by decide
  initial := fun _ => 1000
  debit := fun i _ => if i.val = 0 then 700 else 300
  credit := fun _ _ => 0
  incomingCredit := fun _ _ => 0
  incomingAuthenticated := fun _ => false

/-- Funding state with both witness requests admitted. -/
def queue : State 2 1 := enqueue (enqueue initial 0) 1
/-- Funding state after issuing and finalizing the first witness request. -/
def drained : State 2 1 := finalize (issue queue 0) 0

theorem drained_run : Run costs initial drained := by
  have a : Run costs initial (enqueue initial 0) := .next (.refl _) (.enqueue _ _ rfl (by decide))
  have b : Run costs initial queue := .next a (.enqueue _ _ (by decide) (by decide))
  have i : Run costs initial (issue queue 0) := .next b (.issue _ _ (by decide))
  exact .next i (.finalize _ _ (by decide) (by decide))
example : view costs drained 0 = 300 ∧ reserved costs drained 0 = 300 ∧ available costs drained 0 = 0 := by decide
example : (costs.debit 1 0 : Int) ≤ allocation costs drained 0 :=
  admitted_head_funded drained_run 1 (by decide) (by decide) 0
example : allocation costs drained 0 = 300 := by decide

/-- One resource unit reserved for one full-allocation request. -/
def unit : Costs 1 1 where
  requestId := fun i => "request-" ++ toString i.val
  incomingId := fun i => "external-" ++ toString i.val
  requestUnique := by decide
  incomingUnique := by decide
  separate := by decide
  initial := fun _ => 1
  debit := fun _ _ => 1
  credit := fun _ _ => 0
  incomingCredit := fun _ _ => 0
  incomingAuthenticated := fun _ => false
example : allocation unit (enqueue initial 0) 0 = 1 := by decide
example : (unit.debit 0 0 : Int) ≤ allocation unit (enqueue initial 0) 0 := by
  apply admitted_head_funded (.next (.refl _) (.enqueue _ _ rfl (by decide))) 0 (by decide) (by decide)

/-- Rights and headroom accounting for a burn followed by a mint. -/
def cycle : Costs 2 2 where
  requestId := fun i => "request-" ++ toString i.val
  incomingId := fun i => "external-" ++ toString i.val
  requestUnique := by decide
  incomingUnique := by decide
  separate := by decide
  initial := fun d => if d.val = 0 then 1 else 0
  debit := fun i d => if i.val = d.val then 1 else 0
  credit := fun i d => if i.val ≠ d.val then 1 else 0
  incomingCredit := fun _ _ => 0
  incomingAuthenticated := fun _ => false

/-- Funding state after admitting, issuing and finalizing the burn. -/
def afterBurn : State 2 2 := finalize (issue (enqueue initial 0) 0) 0
example : ¬ (∀ d, (cycle.debit 1 d : Int) ≤ available cycle (enqueue initial 0) d) := by decide
example : ∀ d, (cycle.debit 1 d : Int) ≤ available cycle afterBurn d := by decide
example : available cycle afterBurn 1 = 1 ∧ allocation cycle (enqueue afterBurn 1) 1 = 1 := by decide
end Witness

end CBCL.ConsensusFree.OwnerFunding
