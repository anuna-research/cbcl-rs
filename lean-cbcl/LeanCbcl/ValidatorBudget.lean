import Std
import LeanCbcl.BoundedCounter

/-!
SPEC-021: parametric signing-capacity and finality safety core.
Cryptographic identity, durable storage and the asynchronous version-DAG refinement
are assumptions outside this module. In particular, local reconciliation identities
are NOT an induction proof of the full Stingray/CBCL lifecycle.
-/
namespace CBCL.ValidatorBudget

/-- A transparent finite sum, usable for transaction rows and witness columns. -/
def sumOn (xs : List α) (f : α → Nat) : Nat :=
  match xs with
  | [] => 0
  | x :: rest => f x + sumOn rest f

@[simp] theorem sumOn_nil (f : α → Nat) : sumOn [] f = 0 := rfl
@[simp] theorem sumOn_cons (x : α) (xs : List α) (f : α → Nat) :
    sumOn (x :: xs) f = f x + sumOn xs f := rfl

theorem sumOn_append (xs ys : List α) (f : α → Nat) :
    sumOn (xs ++ ys) f = sumOn xs f + sumOn ys f := by
  induction xs with
  | nil => simp [sumOn]
  | cons x xs ih => simp [sumOn, ih, Nat.add_assoc]

theorem sumOn_add (xs : List α) (f g : α → Nat) :
    sumOn xs (fun x => f x + g x) = sumOn xs f + sumOn xs g := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [sumOn_cons, ih]; omega

theorem sumOn_mul (xs : List α) (f : α → Nat) (k : Nat) :
    sumOn xs (fun x => k * f x) = k * sumOn xs f := by
  induction xs with
  | nil => simp [sumOn]
  | cons x xs ih => simp only [sumOn_cons, ih, Nat.mul_add]

theorem sumOn_mono (xs : List α) (f g : α → Nat)
    (h : ∀ x ∈ xs, f x ≤ g x) : sumOn xs f ≤ sumOn xs g := by
  induction xs with
  | nil => exact Nat.le_refl 0
  | cons x xs ih =>
    have hx := h x (by simp)
    have hr := ih (fun y hy => h y (by simp [hy]))
    simp only [sumOn_cons]
    omega

theorem sumOn_bound (xs : List α) (f : α → Nat) (bound : Nat)
    (h : ∀ x ∈ xs, f x ≤ bound) : sumOn xs f ≤ xs.length * bound := by
  induction xs with
  | nil => simp [sumOn]
  | cons x xs ih =>
    have hx := h x (by simp)
    have hr := ih (fun y hy => h y (by simp [hy]))
    simp only [sumOn_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- The accounting identity underlying the capacity argument. -/
theorem sumOn_swap (xs : List α) (ys : List β) (f : α → β → Nat) :
    sumOn xs (fun x => sumOn ys (f x)) =
      sumOn ys (fun y => sumOn xs (fun x => f x y)) := by
  induction xs with
  | nil =>
    induction ys with
    | nil => rfl
    | cons y ys ih => simpa [sumOn] using ih
  | cons x xs ih =>
    simp only [sumOn_cons]
    rw [ih, ← sumOn_add]

/-- One bit per authenticated witness. Repeated identity aliases are not slots. -/
def voteCount (ws : List Nat) (voted : Nat → Bool) : Nat :=
  sumOn ws (fun w => if voted w then 1 else 0)

theorem voteCount_le_length (ws : List Nat) (voted : Nat → Bool) :
    voteCount ws voted ≤ ws.length := by
  have h := sumOn_bound ws (fun w => if voted w then 1 else 0) 1
    (by intro w _; dsimp; split <;> omega)
  simpa [voteCount] using h

/-- Select 2f+1 honest witnesses as a proof device; remaining f slots can include
additional honest witnesses. Validators do not know which witnesses form the core. -/
structure Committee (f : Nat) where
  core : List Nat
  others : List Nat
  distinct : (core ++ others).Nodup
  core_size : core.length = 2 * f + 1
  other_size : others.length = f

/-- A 2f+1 certificate necessarily contains at least f+1 core votes. -/
theorem quorum_coverage (c : Committee f) (voted : Nat → Bool)
    (quorum : 2 * f + 1 ≤ voteCount (c.core ++ c.others) voted) :
    f + 1 ≤ voteCount c.core voted := by
  have outside := voteCount_le_length c.others voted
  rw [c.other_size] at outside
  unfold voteCount at quorum outside ⊢
  rw [sumOn_append] at quorum
  omega

theorem weighted_votes (ws : List Nat) (voted : Nat → Bool) (weight : Nat) :
    sumOn ws (fun w => if voted w then weight else 0) = voteCount ws voted * weight := by
  induction ws with
  | nil => simp [sumOn, voteCount]
  | cons w ws ih =>
    simp only [sumOn_cons, voteCount, Nat.add_mul] at *
    cases voted w <;> simp [ih]

/-- Each certificate's amount is charged to enough distinct honest witnesses. -/
theorem certificate_charge (c : Committee f) (votes : Nat → Bool) (amount : Nat)
    (quorum : 2 * f + 1 ≤ voteCount (c.core ++ c.others) votes) :
    (f + 1) * ((2 * f + 1) * amount) ≤
      sumOn c.core (fun w => if votes w then (2 * f + 1) * amount else 0) := by
  rw [weighted_votes]
  exact Nat.mul_le_mul_right _ (quorum_coverage c votes quorum)

/-- Parametric double-counting theorem. Per-witness capacity and actual certificate
votes imply a bound on the UNION of certified consumption, not just one quorum. -/
theorem certified_consumption_bound (c : Committee f) (txs : List Nat)
    (amount : Nat → Nat) (votes : Nat → Nat → Bool) (initial : Nat)
    (quorums : ∀ t ∈ txs, 2 * f + 1 ≤ voteCount (c.core ++ c.others) (votes t))
    (witness_capacity : ∀ w ∈ c.core,
      sumOn txs (fun t => if votes t w then (2 * f + 1) * amount t else 0)
        ≤ (f + 1) * initial) :
    sumOn txs amount ≤ initial := by
  let charge := fun t w => if votes t w then (2 * f + 1) * amount t else 0
  have rows : (f + 1) * ((2 * f + 1) * sumOn txs amount) ≤
      sumOn txs (fun t => sumOn c.core (charge t)) := by
    rw [← sumOn_mul, ← sumOn_mul]
    exact sumOn_mono _ _ _ (fun t ht => certificate_charge c (votes t) (amount t) (quorums t ht))
  rw [sumOn_swap] at rows
  have columns := sumOn_bound c.core (fun w => sumOn txs (fun t => charge t w))
    ((f + 1) * initial) witness_capacity
  rw [c.core_size] at columns
  have total : (f + 1) * ((2 * f + 1) * sumOn txs amount) ≤
      (f + 1) * ((2 * f + 1) * initial) := by
    calc
      _ ≤ sumOn c.core (fun w => sumOn txs (fun t => charge t w)) := rows
      _ ≤ (2 * f + 1) * ((f + 1) * initial) := columns
      _ = _ := by ac_rfl
  exact Nat.le_of_mul_le_mul_left
    (Nat.le_of_mul_le_mul_left total (by omega)) (by omega)

/-- Apply the same certificate, with both independently enforced capacity guards,
to rights and headroom. No independent combination of incompatible certificates. -/
theorem both_consumption_bounds (c : Committee f) (txs : List Nat)
    (rightsCost headroomCost : Nat → Nat) (votes : Nat → Nat → Bool) (r h : Nat)
    (quorums : ∀ t ∈ txs, 2 * f + 1 ≤ voteCount (c.core ++ c.others) (votes t))
    (rights : ∀ w ∈ c.core, sumOn txs
      (fun t => if votes t w then (2 * f + 1) * rightsCost t else 0) ≤ (f + 1) * r)
    (headroom : ∀ w ∈ c.core, sumOn txs
      (fun t => if votes t w then (2 * f + 1) * headroomCost t else 0) ≤ (f + 1) * h) :
    sumOn txs rightsCost ≤ r ∧ sumOn txs headroomCost ≤ h :=
  ⟨certified_consumption_bound c txs rightsCost votes r quorums rights,
   certified_consumption_bound c txs headroomCost votes h quorums headroom⟩

/-- Fixed-checkpoint mint/burn batch: no speculative use of credits produced inside
that batch. Transfers conserve global totals by BoundedCounter.transfer_conserves. -/
theorem fixed_checkpoint_bounds (floor : Int) (r h mints burns : Nat)
    (rights : burns ≤ r) (headroom : mints ≤ h) :
    floor ≤ floor + r + mints - burns ∧
    floor + r + mints - burns ≤ floor + r + h := by omega

/-- Business tags determine consumption. Authorization and recipient credit
provenance remain lifecycle premises, not properties of these tags. -/
inductive Kind where
  | mint | burn | pay | headroom
  deriving DecidableEq, Repr

structure Operation where
  kind : Kind
  amount : Nat
  deriving DecidableEq, Repr

def rightsCost (op : Operation) : Nat :=
  match op.kind with
  | .burn | .pay => op.amount
  | _ => 0

def headroomCost (op : Operation) : Nat :=
  match op.kind with
  | .mint | .headroom => op.amount
  | _ => 0

def minted (op : Operation) : Nat := if op.kind == .mint then op.amount else 0
def burned (op : Operation) : Nat := if op.kind == .burn then op.amount else 0

theorem burn_le_rightsCost (op : Operation) : burned op ≤ rightsCost op := by
  cases op with
  | mk kind amount => cases kind <;> simp [burned, rightsCost]

theorem mint_le_headroomCost (op : Operation) : minted op ≤ headroomCost op := by
  cases op with
  | mk kind amount => cases kind <;> simp [minted, headroomCost]

/-- Connect certificate capacity to floor/ceiling arithmetic for one aggregate
checkpoint. Transfers consume source rights but conserve global value. New credits
cannot be reused within this fixed-checkpoint theorem. -/
theorem certified_batch_bounds (c : Committee f) (txs : List Nat)
    (ops : Nat → Operation) (votes : Nat → Nat → Bool) (r h : Nat) (floor : Int)
    (quorums : ∀ t ∈ txs, 2 * f + 1 ≤ voteCount (c.core ++ c.others) (votes t))
    (rights : ∀ w ∈ c.core, sumOn txs
      (fun t => if votes t w then (2 * f + 1) * rightsCost (ops t) else 0) ≤ (f + 1) * r)
    (headroom : ∀ w ∈ c.core, sumOn txs
      (fun t => if votes t w then (2 * f + 1) * headroomCost (ops t) else 0) ≤ (f + 1) * h) :
    let m := sumOn txs (fun t => minted (ops t))
    let b := sumOn txs (fun t => burned (ops t))
    floor ≤ floor + r + m - b ∧ floor + r + m - b ≤ floor + r + h := by
  have bounds := both_consumption_bounds c txs
    (fun t => rightsCost (ops t)) (fun t => headroomCost (ops t)) votes r h quorums rights headroom
  have rb := sumOn_mono txs (fun t => burned (ops t)) (fun t => rightsCost (ops t))
    (fun t _ => burn_le_rightsCost (ops t))
  have hm := sumOn_mono txs (fun t => minted (ops t)) (fun t => headroomCost (ops t))
    (fun t _ => mint_le_headroomCost (ops t))
  exact fixed_checkpoint_bounds floor r h _ _ (Nat.le_trans rb bounds.1) (Nat.le_trans hm bounds.2)

structure LocalBudget where
  rights : Int
  headroom : Int
  deriving DecidableEq, Repr

/-- No partially applied reservation can escape an insufficient second guard. -/
def reserve (b : LocalBudget) (scale rightsCost headroomCost : Nat) : Option LocalBudget :=
  if (scale * rightsCost : Nat) ≤ b.rights ∧ (scale * headroomCost : Nat) ≤ b.headroom then
    some ⟨b.rights - scale * rightsCost, b.headroom - scale * headroomCost⟩
  else none

theorem reserve_nonnegative (b : LocalBudget) (scale r h : Nat) (after : LocalBudget)
    (accepted : reserve b scale r h = some after) :
    0 ≤ after.rights ∧ 0 ≤ after.headroom := by
  unfold reserve at accepted
  split at accepted
  · rename_i enough
    cases accepted
    dsimp
    omega
  · contradiction

/-- All operation IDs here denote already bound authenticated complete statements. -/
def reserveOnce (ids : List Nat) (b : LocalBudget) (id scale r h : Nat) :
    Option (List Nat × LocalBudget) :=
  if id ∈ ids then some (ids, b)
  else (reserve b scale r h).map (fun after => (id :: ids, after))

theorem reservation_replay (ids : List Nat) (b : LocalBudget) (id scale r h : Nat)
    (seen : id ∈ ids) : reserveOnce ids b id scale r h = some (ids, b) := by
  simp [reserveOnce, seen]

/-- A version applies finalized deltas and refunds only its OWN covered signatures. -/
def reconcile (free : Int) (k scale : Nat) (delta : Int) (ownCovered : Nat) : Int :=
  free + (k : Int) * delta + (scale : Int) * ownCovered

/-- Retained omitted reservations are algebraically necessary. No nonnegative
assumption is made on the reconciled free budget: exposure can make it negative. -/
theorem reconciliation_preserves_exposure (free balance delta : Int)
    (k scale covered omitted : Nat)
    (before : free + (scale : Int) * ((covered : Int) + omitted) = (k : Int) * balance) :
    reconcile free k scale delta covered + (scale : Int) * omitted =
      (k : Int) * (balance + delta) := by
  simp only [Int.mul_add] at before ⊢
  unfold reconcile
  omega

theorem empty_reconciliation (free : Int) (k scale : Nat) :
    reconcile free k scale 0 0 = free := by simp [reconcile]

/-- Flags concern one candidate account/version. Byzantine witnesses may set both. -/
structure Witness where
  faulty : Bool
  executed : Bool
  fenced : Bool
  deriving DecidableEq, Repr

def disciplined (w : Witness) : Prop :=
  w.faulty = false → ¬ (w.executed = true ∧ w.fenced = true)

def executions (ws : List Witness) : Nat := sumOn ws (fun w => if w.executed then 1 else 0)
def fences (ws : List Witness) : Nat := sumOn ws (fun w => if w.fenced then 1 else 0)
def faults (ws : List Witness) : Nat := sumOn ws (fun w => if w.faulty then 1 else 0)

theorem disciplined_count_bound (ws : List Witness)
    (honest : ∀ w ∈ ws, disciplined w) :
    executions ws + fences ws ≤ ws.length + faults ws := by
  induction ws with
  | nil => simp [executions, fences, faults, sumOn]
  | cons w ws ih =>
    have hw := honest w (by simp)
    have hr := ih (fun x hx => honest x (by simp [hx]))
    have single : (if w.executed then 1 else 0) + (if w.fenced then 1 else 0) ≤
        1 + (if w.faulty then 1 else 0) := by
      cases w with
      | mk faulty executed fenced =>
        cases faulty <;> cases executed <;> cases fenced <;> simp [disciplined] at hw ⊢
    simp only [executions, fences, faults, sumOn_cons, List.length_cons] at *
    omega

/-- A finalized effects quorum and a no-commit recovery quorum cannot coexist.
No consensus oracle or globally trusted owner is assumed for this exclusion. -/
theorem finality_excludes_no_commit (ws : List Witness) (f : Nat)
    (roster : ws.length = 3 * f + 1) (fault_bound : faults ws ≤ f)
    (honest : ∀ w ∈ ws, disciplined w)
    (final : 2 * f + 1 ≤ executions ws) : ¬ (2 * f + 1 ≤ fences ws) := by
  have capacity := disciplined_count_bound ws honest
  omega

/-- An honest witness fences before voting and never executes through that fence. -/
def execute (w : Witness) : Option Witness :=
  if w.faulty || !w.fenced then some { w with executed := true } else none

def fence (w : Witness) : Option Witness :=
  if w.faulty || !w.executed then some { w with fenced := true } else none

theorem execute_preserves_discipline (w after : Witness) (hw : disciplined w)
    (step : execute w = some after) : disciplined after := by
  cases w with
  | mk faulty executed fenced =>
    cases faulty <;> cases executed <;> cases fenced <;>
      simp [execute, disciplined] at hw step ⊢ <;> subst after <;> simp

theorem fence_preserves_discipline (w after : Witness) (hw : disciplined w)
    (step : fence w = some after) : disciplined after := by
  cases w with
  | mk faulty executed fenced =>
    cases faulty <;> cases executed <;> cases fenced <;>
      simp [fence, disciplined] at hw step ⊢ <;> subst after <;> simp

inductive ReceiptEvent where
  | internal
  | finalize (id : Nat)
  deriving DecidableEq

/-- The abstraction exposes final receipts; all internal events stutter. -/
def receiptStep (receipts : List Nat) : ReceiptEvent → List Nat
  | .internal => receipts
  | .finalize id => if id ∈ receipts then receipts else id :: receipts

theorem receipt_monotone (receipts : List Nat) (event : ReceiptEvent) :
    ∀ id ∈ receipts, id ∈ receiptStep receipts event := by
  intro id hi
  cases event with
  | internal => exact hi
  | finalize new => simp only [receiptStep]; split <;> simp_all

theorem receipt_replay (receipts : List Nat) (id : Nat) :
    receiptStep (receiptStep receipts (.finalize id)) (.finalize id) =
      receiptStep receipts (.finalize id) := by
  simp only [receiptStep]
  split <;> simp_all

/-- A concrete distinct roster used for positive and adversarial examples. -/
def four : Committee 1 := ⟨[0, 1, 2], [3], by decide, by decide, by decide⟩

def splitVotes (tx witness : Nat) : Bool :=
  witness == 3 || match tx with
    | 0 => witness == 0 || witness == 1
    | 1 => witness == 0 || witness == 2
    | _ => witness == 1 || witness == 2

/-- Three separately certified units fit B=3 with conservative local capacity. -/
example : ∀ t ∈ ([0, 1, 2] : List Nat),
    3 ≤ voteCount (four.core ++ four.others) (splitVotes t) := by decide
example : ∀ w ∈ four.core,
    sumOn [0, 1, 2] (fun t => if splitVotes t w then 3 else 0) ≤ 2 * 3 := by decide

/-- Full local budgets (instead of the conservative fraction) permit B=2 to certify
three units. This is the semantic counterexample behind the bound mutation. -/
example : ∀ w ∈ four.core,
    sumOn [0, 1, 2] (fun t => if splitVotes t w then 3 else 0) ≤ 3 * 2 := by decide
example : ¬ sumOn [0, 1, 2] (fun _ => 1) ≤ 2 := by decide

example : reserve ⟨6, 0⟩ 3 1 1 = none := by decide
example : reserve ⟨6, 6⟩ 3 1 1 = some ⟨3, 3⟩ := by decide
example : reconcile 3 2 3 (-1) 0 = 1 := by decide
example : reconcile 0 2 3 (-1) 0 = -2 := by decide
example : execute ⟨false, false, true⟩ = none := by decide
example : fence ⟨false, true, false⟩ = none := by decide
example : execute ⟨true, false, true⟩ = some ⟨true, true, true⟩ := by decide

#print axioms certified_consumption_bound
#print axioms both_consumption_bounds
#print axioms fixed_checkpoint_bounds
#print axioms certified_batch_bounds
#print axioms reconciliation_preserves_exposure
#print axioms finality_excludes_no_commit
#print axioms receipt_monotone

end CBCL.ValidatorBudget
