import Std

/-!
Independent two-budget arithmetic model for SPEC-019 CON-1909.

This proves local conservation and bounds for abstract escrow operations.
It does NOT prove Rust correspondence, resource-DAG validation, compatible-union
safety, authentication, durable issuance, or external effect delivery.
-/
namespace CBCL.BoundedCounter

/-- One account owns decrement rights and increment headroom. -/
structure Budget where
  /-- Units this account may consume or transfer. -/
  rights : Nat
  /-- Units this account may issue or transfer as headroom. -/
  headroom : Nat
  deriving DecidableEq

/-- Combined capacity carried by an account. -/
def capacity (b : Budget) : Nat := b.rights + b.headroom

/-- Issuance consumes headroom and creates rights; its theorem requires budget. -/
def increment (b : Budget) (n : Nat) : Budget :=
  ⟨b.rights + n, b.headroom - n⟩

/-- Consumption destroys rights and restores headroom. -/
def decrement (b : Budget) (n : Nat) : Budget :=
  ⟨b.rights - n, b.headroom + n⟩

/-- Move rights between two accounts, preserving their headroom. -/
def transfer (a b : Budget) (n : Nat) : Budget × Budget :=
  (⟨a.rights - n, a.headroom⟩, ⟨b.rights + n, b.headroom⟩)

/-- Move headroom between two accounts, preserving their rights. -/
def transferHeadroom (a b : Budget) (n : Nat) : Budget × Budget :=
  (⟨a.rights, a.headroom - n⟩, ⟨b.rights, b.headroom + n⟩)

/-- Sufficient local headroom makes issuance conserve capacity. -/
theorem increment_conserves (b : Budget) (n : Nat) (enough : n ≤ b.headroom) :
    capacity (increment b n) = capacity b := by
  simp only [capacity, increment]
  omega

/-- Sufficient local rights make consumption conserve capacity. -/
theorem decrement_conserves (b : Budget) (n : Nat) (enough : n ≤ b.rights) :
    capacity (decrement b n) = capacity b := by
  simp only [capacity, decrement]
  omega

/-- Rights transfer conserves both rights and combined capacity. -/
theorem transfer_conserves (a b : Budget) (n : Nat) (enough : n ≤ a.rights) :
    let result := transfer a b n
    result.1.rights + result.2.rights = a.rights + b.rights ∧
    capacity result.1 + capacity result.2 = capacity a + capacity b := by
  simp only [transfer, capacity]
  omega

/-- Headroom transfer conserves rights, headroom and combined capacity. -/
theorem transfer_headroom_conserves (a b : Budget) (n : Nat)
    (enough : n ≤ a.headroom) :
    let result := transferHeadroom a b n
    result.1.headroom + result.2.headroom = a.headroom + b.headroom ∧
    result.1.rights + result.2.rights = a.rights + b.rights ∧
    capacity result.1 + capacity result.2 = capacity a + capacity b := by
  dsimp [transferHeadroom, capacity]
  constructor
  · omega
  constructor
  · rfl
  · omega

/-- Sum of all account decrement budgets. -/
def rightsTotal (accounts : List Budget) : Nat := (accounts.map Budget.rights).sum
/-- Sum of all account increment budgets. -/
def headroomTotal (accounts : List Budget) : Nat := (accounts.map Budget.headroom).sum

/-- Observable integer value includes the protected floor. -/
def value (floor : Int) (accounts : List Budget) : Int := floor + rightsTotal accounts

/-- Natural account rights imply the lower bound. -/
theorem floor_preserved (floor : Int) (accounts : List Budget) :
    floor ≤ value floor accounts := by
  unfold value
  omega

/-- The capacity allocation equation and natural headroom imply the upper bound. -/
theorem ceiling_preserved (floor ceiling : Int) (accounts : List Budget)
    (allocation : (rightsTotal accounts : Int) + headroomTotal accounts = ceiling - floor) :
    value floor accounts ≤ ceiling := by
  unfold value
  have nonnegative : (0 : Int) ≤ headroomTotal accounts := Int.natCast_nonneg _
  omega

/-- Both bounds follow from correctly allocated nonnegative budgets. -/
theorem both_bounds (floor ceiling : Int) (accounts : List Budget)
    (allocation : (rightsTotal accounts : Int) + headroomTotal accounts = ceiling - floor) :
    floor ≤ value floor accounts ∧ value floor accounts ≤ ceiling :=
  ⟨floor_preserved floor accounts, ceiling_preserved floor ceiling accounts allocation⟩

-- Removing a local budget guard is observable: saturated subtraction would
-- create rights and destroy conservation.
example : capacity (increment ⟨2, 0⟩ 1) ≠ capacity ⟨2, 0⟩ := by decide
example : capacity (decrement ⟨0, 2⟩ 1) ≠ capacity ⟨0, 2⟩ := by decide

#print axioms increment_conserves
#print axioms decrement_conserves
#print axioms transfer_conserves
#print axioms transfer_headroom_conserves
#print axioms both_bounds

end CBCL.BoundedCounter
