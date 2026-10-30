import LeanCbcl.ConsensusFree.Currency

/-! Collective pools separate the transaction actor from the single resource
account. Authorization is an input predicate established by signature/role checks;
no Rust extraction, cryptographic correctness or multi-parent merge is asserted. -/
namespace CBCL.ConsensusFree.Collective
open CBCL.ValidatorBudget
open CBCL.ConsensusFree

structure Context (K T P : Nat) where
  checkpoints : Fin P → Checkpoint 1 T P 2
  epoch : Fin T → Epoch 1 P
  actor : Fin T → Fin K
  isMint : Fin T → Bool
  amount : Fin T → Nat
  signatureValid : Fin T → Bool
  roleAdmitted : Fin T → Bool
  isIssuer : Fin K → Bool
  initialRights : Nat
  initialHeadroom : Nat
  capped : Bool

def actorAuthorized (c : Context K T P) (tx : Fin T) : Bool :=
  c.signatureValid tx && c.roleAdmitted tx &&
    (if c.isMint tx then c.isIssuer (c.actor tx) else true)

def currency (c : Context K T P) : Currency.Context 1 T P where
  checkpoints := c.checkpoints
  operations := fun tx => {
    epoch := c.epoch tx
    kind := if c.isMint tx then .mint else .burn
    amount := c.amount tx
    recipient := 0
  }
  initialRights := fun _ => c.initialRights
  initialHeadroom := fun _ => c.initialHeadroom
  capped := c.capped
  issuers := fun _ => true
  ownerSigned := actorAuthorized c
  nonself := by
    intro tx h
    cases hm : c.isMint tx <;> simp [hm] at h

def config (c : Context K T P) (committee : Committee f) : Config 1 T P 2 f :=
  Currency.config (currency c) committee

theorem same_resource_source (c : Context K T P) (a b : Fin T) :
    Currency.source (currency c) a = Currency.source (currency c) b :=
  Subsingleton.elim _ _

theorem authorization_checks_actor (c : Context K T P) (tx : Fin T)
    (h : Currency.authorized (currency c) tx = true) :
    c.signatureValid tx = true ∧ c.roleAdmitted tx = true := by
  have pair := Bool.and_eq_true_iff.mp h
  have pair := Bool.and_eq_true_iff.mp pair.1
  have pair := Bool.and_eq_true_iff.mp pair.1
  have owner : actorAuthorized c tx = true := pair.1
  simp only [actorAuthorized, Bool.and_eq_true_iff] at owner
  exact owner.1

theorem mint_checks_actual_issuer (c : Context K T P) (tx : Fin T)
    (mint : c.isMint tx = true)
    (h : Currency.authorized (currency c) tx = true) :
    c.isIssuer (c.actor tx) = true := by
  have pair := Bool.and_eq_true_iff.mp h
  have pair := Bool.and_eq_true_iff.mp pair.1
  have pair := Bool.and_eq_true_iff.mp pair.1
  have owner : actorAuthorized c tx = true := pair.1
  simpa [actorAuthorized, mint] using (Bool.and_eq_true_iff.mp owner).2

theorem collective_async_refinement (c : Context K T P) (committee : Committee f)
    (commands : List (Command 1 T P)) :
    BusinessRun (config c committee) (initial (config c committee)).balance
      ((run (config c committee) (initial (config c committee)) commands).1.filterMap id)
      (run (config c committee) (initial (config c committee)) commands).2.balance :=
  full_async_refinement (config c committee) commands

theorem collective_resources_nonnegative (c : Context K T P) (committee : Committee f)
    (commands : List (Command 1 T P)) :
    ∀ d, 0 ≤ (run (config c committee) (initial (config c committee)) commands).2.balance d :=
  all_schedules_nonnegative (config c committee) commands

theorem collective_floor (c : Context K T P) (committee : Committee f)
    (commands : List (Command 1 T P)) (floor : Int) :
    floor ≤ floor + Currency.rightsTotal (A := 1)
      (run (config c committee) (initial (config c committee)) commands).2.balance :=
  Currency.currency_floor (currency c) committee commands floor

theorem collective_ceiling (c : Context K T P) (committee : Committee f)
    (cap : c.capped = true) (commands : List (Command 1 T P)) (floor : Int) :
    floor + Currency.rightsTotal (A := 1) (run (config c committee) (initial (config c committee)) commands).2.balance ≤
      floor + CBCL.ConsensusFree.isum (List.finRange 2) (initial (config c committee)).balance :=
  Currency.currency_ceiling (currency c) committee cap commands floor

end CBCL.ConsensusFree.Collective
