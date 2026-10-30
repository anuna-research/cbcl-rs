import LeanCbcl.ConsensusFree.Collective
open CBCL.ConsensusFree CBCL.ConsensusFree.Collective CBCL.ValidatorBudget

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def sellers : Collective.Context 2 2 0 where
  checkpoints := Fin.elim0
  epoch := fun _ => .root 0
  actor := id
  isMint := fun _ => false
  amount := fun tx => if tx.val = 0 then 3 else 2
  signatureValid := fun _ => true
  roleAdmitted := fun _ => true
  isIssuer := fun _ => false
  initialRights := 100
  initialHeadroom := 0
  capped := false

def committee : Committee 1 := ⟨[0,1,2], [3], by decide, rfl, rfl⟩
def cfg := Collective.config sellers committee

def commands : List (Command 1 2 0) :=
  [0,1].flatMap (fun tx => [0,1,2].map (Command.sign tx)) ++
  [0,1].flatMap (fun tx => [0,1,2].map (Command.receiveOperation tx)) ++
  [1,0].flatMap (fun tx => [0,1,2].map (Command.effect tx))

example : sellers.actor 0 ≠ sellers.actor 1 := by decide
example : Currency.source (currency sellers) 0 = Currency.source (currency sellers) 1 :=
  same_resource_source sellers 0 1
example : (run cfg (initial cfg) commands).2.balance 0 = 95 := by decide
example : Currency.authorized (currency {sellers with roleAdmitted := fun _ => false}) 0 = false := by decide
example : Currency.authorized (currency {sellers with isMint := fun _ => true}) 0 = false := by decide

#print axioms Collective.same_resource_source
#print axioms Collective.authorization_checks_actor
#print axioms Collective.mint_checks_actual_issuer
#print axioms Collective.collective_async_refinement
#print axioms Collective.collective_resources_nonnegative
#print axioms Collective.collective_floor
#print axioms Collective.collective_ceiling

def main : IO Unit := do
  if (run cfg (initial cfg) commands).2.balance 0 != 95 then
    throw (IO.userError "collective actor trace mismatch")
  IO.println "collective two-actor trace: 100 - 3 - 2 = 95; role and issuer checks kernel-verified"
