import LeanCbcl.ConsensusFree.Execution

namespace CBCL.ConsensusFree.Currency
open CBCL.ValidatorBudget
open CBCL.ConsensusFree
variable {A T P f : Nat}

abbrev rights (a : Fin A) : Fin (A+A) := Fin.castAdd A a
abbrev headroom (a : Fin A) : Fin (A+A) := Fin.natAdd A a

def resourceOwner (d : Fin (A+A)) : Fin A := Fin.addCases (fun a => a) (fun a => a) d

@[simp] theorem owner_rights (a : Fin A) : resourceOwner (rights a) = a := by simp [resourceOwner]
@[simp] theorem owner_headroom (a : Fin A) : resourceOwner (headroom a) = a := by exact Fin.addCases_right a

theorem rights_ne_headroom (a b : Fin A) : rights a ≠ headroom b := by
  intro eq
  have values := congrArg Fin.val eq
  have bound := a.isLt
  change a.val = A + b.val at values
  omega

theorem rights_injective {a b : Fin A} (eq : rights a = rights b) : a = b := by
  apply Fin.ext
  exact congrArg (fun d : Fin (A+A) => d.val) eq

theorem headroom_injective {a b : Fin A} (eq : headroom a = headroom b) : a = b := by
  apply Fin.ext
  have values := congrArg Fin.val eq
  change A + a.val = A + b.val at values
  omega

def atom (key : Fin R) (amount : Nat) (d : Fin R) : Nat := if d = key then amount else 0

theorem atoms_disjoint (a b : Fin R) (amount : Nat) (different : a ≠ b) (d : Fin R) :
    atom a amount d = 0 ∨ atom b amount d = 0 := by
  by_cases same : d = a
  · subst d; exact Or.inr (by simp [atom, different])
  · exact Or.inl (by simp [atom, same])

structure Operation (A P : Nat) where
  epoch : Epoch A P
  kind : Kind
  amount : Nat
  recipient : Fin A

structure Context (A T P : Nat) where
  checkpoints : Fin P → Checkpoint A T P (A+A)
  operations : Fin T → Operation A P
  initialRights : Fin A → Nat
  initialHeadroom : Fin A → Nat
  capped : Bool
  issuers : Fin A → Bool
  ownerSigned : Fin T → Bool
  nonself : ∀ tx, ((operations tx).kind = .pay ∨ (operations tx).kind = .headroom) →
    (operations tx).recipient ≠ epochOwner checkpoints (operations tx).epoch

abbrev source (c : Context A T P) (tx : Fin T) := epochOwner c.checkpoints (c.operations tx).epoch

def cost (c : Context A T P) (tx : Fin T) : Fin (A+A) → Nat :=
  match (c.operations tx).kind with
  | .pay | .burn => atom (rights (source c tx)) (c.operations tx).amount
  | .mint => if c.capped then atom (headroom (source c tx)) (c.operations tx).amount else fun _ => 0
  | .headroom => atom (headroom (source c tx)) (c.operations tx).amount

def credit (c : Context A T P) (tx : Fin T) : Fin (A+A) → Nat :=
  match (c.operations tx).kind with
  | .pay => atom (rights (c.operations tx).recipient) (c.operations tx).amount
  | .mint => atom (rights (source c tx)) (c.operations tx).amount
  | .burn => if c.capped then atom (headroom (source c tx)) (c.operations tx).amount else fun _ => 0
  | .headroom => atom (headroom (c.operations tx).recipient) (c.operations tx).amount

def authorized (c : Context A T P) (tx : Fin T) : Bool :=
  c.ownerSigned tx && decide (0 < (c.operations tx).amount) &&
    (if (c.operations tx).kind = .mint then c.issuers (source c tx) else true) &&
    (if (c.operations tx).kind = .headroom then c.capped else true)

theorem cost_local (c : Context A T P) (tx : Fin T) (d : Fin (A+A))
    (other : resourceOwner d ≠ source c tx) : cost c tx d = 0 := by
  have rightOther : d ≠ rights (source c tx) := by intro same; subst d; exact other (owner_rights _)
  have headOther : d ≠ headroom (source c tx) := by intro same; subst d; exact other (owner_headroom _)
  have rz : atom (rights (source c tx)) (c.operations tx).amount d = 0 := by simp only [atom, if_neg rightOther]
  have hz : atom (headroom (source c tx)) (c.operations tx).amount d = 0 := by simp only [atom, if_neg headOther]
  cases kind : (c.operations tx).kind with
  | pay => simpa only [cost, kind] using rz
  | burn => simpa only [cost, kind] using rz
  | headroom => simpa only [cost, kind] using hz
  | mint =>
      simp only [cost, kind]
      split
      · exact hz
      · rfl

theorem vectors_disjoint (c : Context A T P) (tx : Fin T) (d : Fin (A+A)) :
    cost c tx d = 0 ∨ credit c tx d = 0 := by
  cases kind : (c.operations tx).kind with
  | pay =>
      have different : rights (source c tx) ≠ rights (c.operations tx).recipient := by
        intro eq
        exact c.nonself tx (Or.inl kind) (rights_injective eq).symm
      simpa only [cost, credit, kind] using atoms_disjoint _ _ (c.operations tx).amount different d
  | headroom =>
      have different : headroom (source c tx) ≠ headroom (c.operations tx).recipient := by
        intro eq
        exact c.nonself tx (Or.inr kind) (headroom_injective eq).symm
      simpa only [cost, credit, kind] using atoms_disjoint _ _ (c.operations tx).amount different d
  | mint =>
      cases capped : c.capped with
      | false => exact Or.inl (by simp [cost, kind, capped])
      | true =>
          have dis := atoms_disjoint (headroom (source c tx)) (rights (source c tx))
            (c.operations tx).amount (Ne.symm (rights_ne_headroom _ _)) d
          simpa [cost, credit, kind, capped] using dis
  | burn =>
      cases capped : c.capped with
      | false => exact Or.inr (by simp [credit, kind, capped])
      | true =>
          have dis := atoms_disjoint (rights (source c tx)) (headroom (source c tx))
            (c.operations tx).amount (rights_ne_headroom _ _) d
          simpa [cost, credit, kind, capped] using dis

def config (c : Context A T P) (committee : Committee f) : Config A T P (A+A) f where
  committee := committee
  initial := Fin.addCases c.initialRights (fun a => if c.capped then c.initialHeadroom a else 0)
  checkpoints := c.checkpoints
  opEpoch := fun tx => (c.operations tx).epoch
  resourceOwner := resourceOwner
  cost := cost c
  credit := credit c
  authorized := authorized c
  cost_local := cost_local c
  disjoint := vectors_disjoint c

theorem mint_requires_issuer (c : Context A T P) (tx : Fin T) (mint : (c.operations tx).kind = .mint)
    (auth : authorized c tx = true) : c.issuers (source c tx) = true := by
  simp [authorized, mint] at auth
  exact auth.2

theorem headroom_requires_cap (c : Context A T P) (tx : Fin T) (move : (c.operations tx).kind = .headroom)
    (auth : authorized c tx = true) : c.capped = true := by
  simp [authorized, move] at auth
  exact auth.2

theorem atom_total (key : Fin R) (amount : Nat) :
    isum (List.finRange R) (fun d => (atom key amount d : Int)) = (amount : Int) := by
  have eq : (fun d => (atom key amount d : Int)) = setAt (fun _ => 0) key (amount : Int) := by
    funext d; by_cases same : d = key <;> simp [atom, setAt, same]
  rw [eq, isum_update _ _ _ _ (finRange_unique R) (List.mem_finRange key)]
  simp [isum_zero]

theorem capped_conservation (c : Context A T P) (cap : c.capped = true) (tx : Fin T) :
    isum (List.finRange (A+A)) (fun d => (credit c tx d : Int)) =
      isum (List.finRange (A+A)) (fun d => (cost c tx d : Int)) := by
  cases kind : (c.operations tx).kind <;> simp [credit, cost, kind, cap, atom_total]


theorem business_conservation {c : Config A T P R f} {before after : Fin R → Int} {tx : Fin T}
    (step : BusinessStep c before tx after) (dims : List (Fin R))
    (conserved : isum dims (fun d => (c.credit tx d : Int)) = isum dims (fun d => (c.cost tx d : Int))) :
    isum dims after = isum dims before := by
  rw [step.2.2, isum_sub, isum_add, conserved]
  omega

theorem business_run_conservation {c : Config A T P R f} {before after : Fin R → Int} {txs}
    (trace : BusinessRun c before txs after) (dims : List (Fin R))
    (conserved : ∀ tx, isum dims (fun d => (c.credit tx d : Int)) = isum dims (fun d => (c.cost tx d : Int))) :
    isum dims after = isum dims before := by
  induction trace with
  | nil => rfl
  | cons step tail ih => exact ih.trans (business_conservation step dims (conserved _))

def rightsTotal (balance : Fin (A+A) → Int) : Int :=
  isum (List.finRange (A+A)) (fun d => if d.val < A then balance d else 0)
def headroomTotal (balance : Fin (A+A) → Int) : Int :=
  isum (List.finRange (A+A)) (fun d => if d.val < A then 0 else balance d)

theorem total_split (balance : Fin (A+A) → Int) :
    rightsTotal balance + headroomTotal balance = isum (List.finRange (A+A)) balance := by
  rw [rightsTotal, headroomTotal, ← isum_add]
  apply isum_congr
  intro d _
  split <;> simp

theorem currency_floor (c : Context A T P) (committee : Committee f) (commands : List (Command A T P)) (floor : Int) :
    floor ≤ floor + rightsTotal (run (config c committee) (initial (config c committee)) commands).2.balance := by
  have positive := all_schedules_nonnegative (config c committee) commands
  have total : 0 ≤ rightsTotal (run (config c committee) (initial (config c committee)) commands).2.balance := by
    apply isum_nonneg
    intro d _
    split
    · exact positive d
    · omega
  omega

theorem currency_ceiling (c : Context A T P) (committee : Committee f) (cap : c.capped = true)
    (commands : List (Command A T P)) (floor : Int) :
    floor + rightsTotal (run (config c committee) (initial (config c committee)) commands).2.balance ≤
      floor + isum (List.finRange (A+A)) (initial (config c committee)).balance := by
  have positive := all_schedules_nonnegative (config c committee) commands
  have total := business_run_conservation (full_async_refinement (config c committee) commands)
    (List.finRange (A+A)) (capped_conservation c cap)
  have headPositive : 0 ≤ headroomTotal (run (config c committee) (initial (config c committee)) commands).2.balance := by
    apply isum_nonneg
    intro d _
    split
    · omega
    · exact positive d
  have split := total_split (run (config c committee) (initial (config c committee)) commands).2.balance
  omega

end CBCL.ConsensusFree.Currency
