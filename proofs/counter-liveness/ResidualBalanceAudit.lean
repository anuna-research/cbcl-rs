import LeanCbcl.ConsensusFree.Liveness

/-! Research counterexample for the CURRENT protocol, not a replacement.
One authorized unit debit and unit initial capacity, with arbitrary finite DAG,
no incoming credits and no authorized cancellation. Every version has exact unit
books. Even ideal version advancement cannot enable the debit. -/
namespace CBCL.ConsensusFree.MultiParent.ResidualAudit
open CBCL.ValidatorBudget CBCL.SealedCheckpoint Liveness

private def committee : Committee 1 where
  core := [0, 1, 2]
  others := [3]
  distinct := by decide
  core_size := by decide
  other_size := by decide

def unitPool (g : Graph V) (target : Version V) : Config V 1 1 1 where
  graph := g
  committee := committee
  manifest := fun _ => ⟨fun _ => false, fun _ => false, fun _ => false, fun _ => 1, true⟩
  initial := fun _ => 1
  opVersion := fun _ => target
  cost := fun _ _ => 1
  credit := fun _ _ => 0
  authorized := fun _ => true
  cancelAuthorized := fun _ => false
  disjoint := by intros; exact Or.inr rfl

@[simp] theorem allowance_one (g : Graph V) (target v : Version V) (d : Fin 1) :
    allowance (unitPool g target) v d = 1 := by
  simp [allowance, unitPool]

/-- Positive balance is not the same as usable signing capacity. -/
theorem no_honest_sign (g : Graph V) (target : Version V) (s : State V 1)
    (w : Nat) (honest : w ∈ (unitPool g target).committee.core) :
    ¬ SignAllowed (unitPool g target) s 0 w := by
  intro allowed
  obtain ⟨_, _, unreleased, capacity⟩ := allowed honest
  have bound := capacity (0 : Fin 1)
  have range : List.finRange 1 = [0] := by decide
  simp [charge, unitPool, allowance, range, sumOn, signed,
    CBCL.ConsensusFree.two, CBCL.ConsensusFree.setAt, unreleased] at bound

/-- Every execution retains no honest signature, regardless of DAG operations. -/
theorem no_honest_signature (g : Graph V) (target : Version V)
    (e : Execution (unitPool g target)) (n w : Nat)
    (honest : w ∈ (unitPool g target).committee.core) :
    (e.state n).signatures 0 w = false := by
  have inv := e.invariant n
  have noRelease : (e.state n).released 0 w = false := by
    cases released : (e.state n).released 0 w with
    | false => rfl
    | true =>
      have qc := inv.release_cancel 0 w honest released
      rw [no_cancel_certificate e 0 (by rfl) n] at qc
      contradiction
  cases hs : (e.state n).signatures 0 w with
  | false => rfl
  | true =>
    have bound := inv.capacity target w honest (0 : Fin 1)
    have range : List.finRange 1 = [0] := by decide
    simp [charge, unitPool, allowance, range, sumOn, hs, noRelease] at bound

/-- Even f Byzantine signatures cannot make a quorum without an honest signer. -/
theorem no_operation_certificate (g : Graph V) (target : Version V)
    (e : Execution (unitPool g target)) (n : Nat) :
    operationCert (unitPool g target) (e.state n) 0 = false := by
  cases h : operationCert (unitPool g target) (e.state n) 0 with
  | false => rfl
  | true =>
    obtain ⟨w, hw, signed, _⟩ := honest_intersection
      (unitPool g target).committee _ _ (of_decide_eq_true h) (of_decide_eq_true h)
    rw [no_honest_signature g target e n w hw] at signed
    contradiction

/-- Safety-preserving version adoption cannot spend the final unit in this model. -/
theorem no_final_certificate (g : Graph V) (target : Version V)
    (e : Execution (unitPool g target)) (n : Nat) :
    finalCert (unitPool g target) (e.state n) 0 = false := by
  cases h : finalCert (unitPool g target) (e.state n) 0 with
  | false => rfl
  | true =>
    have qc := final_operation (e.invariant n) h
    rw [no_operation_certificate g target e n] at qc
    contradiction

/-- Nonvacuous witness: a valid successor exists, is recorded, and all honest
validators actually adopt it. The debit remains disabled there. -/
def twoVersions : Graph 1 where
  lower := fun v => if h : 0 < v.val then [⟨0, h⟩] else []

def advanced : State 1 1 :=
  (execute (unitPool twoVersions 1) initial
    [.record 1, .adopt 1 0, .adopt 1 1, .adopt 1 2]).getD initial

example : Static (unitPool twoVersions 1) 1 := by decide
example : advanced.known 1 = true ∧ advanced.active 0 = 1 ∧
    advanced.active 1 = 1 ∧ advanced.active 2 = 1 := by decide
example : ¬ SignAllowed (unitPool twoVersions 1) advanced 0 0 := by decide

/-- There is an actual infinite target-fair execution. Fairness cannot enable
an action rejected by the arithmetic guard. -/
def quiet : Execution (unitPool twoVersions 0) where
  state := fun _ => initial
  command := fun _ => .replay
  starts := rfl
  accepted := fun _ => rfl

theorem quiet_sign_fair (w : Nat)
    (honest : w ∈ (unitPool twoVersions 0).committee.core) :
    WeakFair quiet.command
      (fun n => SignEnabled (unitPool twoVersions 0) (quiet.state n) 0 w) (.sign 0 w) := by
  intro start enabled
  exact False.elim (no_honest_sign twoVersions 0 _ w honest
    ((enabled start (Nat.le_refl start)).2))

theorem quiet_effect_fair (w : Nat) :
    WeakFair quiet.command
      (fun n => EffectEnabled (unitPool twoVersions 0) (quiet.state n) 0 w) (.effect 0 w) := by
  intro start enabled
  have qc := (enabled start (Nat.le_refl start)).2.1
  rw [no_operation_certificate twoVersions 0 quiet start] at qc
  contradiction

#print axioms no_honest_sign
#print axioms no_honest_signature
#print axioms no_operation_certificate
#print axioms no_final_certificate
#print axioms quiet_sign_fair
#print axioms quiet_effect_fair
end CBCL.ConsensusFree.MultiParent.ResidualAudit
