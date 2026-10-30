import LeanCbcl.ConsensusFree.CollectiveProtocol
open CBCL.ConsensusFree CBCL.ValidatorBudget
open CollectiveActors
namespace CollectiveActorAudit
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def committee : Committee 1 := ⟨[0,1,2], [3], by decide, rfl, rfl⟩

def ctx : CollectiveActors.Context 3 3 2 1 where
  domain := 41
  policy := {
    cast := fun _ => true
    role := fun a r =>
      (r.val == 0 && a.val == 0) ||
      (r.val == 1 && (a.val == 1 || a.val == 2)) ||
      (r.val == 2 && (a.val == 0 || a.val == 1))
    initializer := 0
    increment := 1
    decrement := 1
    issuer := some 2
  }
  authenticated := fun _ _ _ => true
  opener := 0
  floor := -10
  ceiling := some 100
  initialRights := 100
  manifests := fun _ => {
    parent := .root 0
    depth := 1
    held := fun tx => tx.val == 0
    refunded := fun tx => tx.val == 0
    credited := fun _ => false
    allocation := fun d => if d.val == 0 then 100 else 10
  }
  epoch := fun _ => .root 0
  actor := fun tx => if tx.val == 0 then 1 else 2
  isMint := fun _ => false
  amount := fun tx => if tx.val == 0 then 3 else 2

def genesis := canonical ctx .genesis 0
def start := initialState ctx committee genesis

def owner (c : CollectiveActors.Context 3 3 2 1) (tx : Fin 2) := canonical c (.operation tx) (c.actor tx)
def cancel (c : CollectiveActors.Context 3 3 2 1) (tx : Fin 2) := canonical c (.cancellation tx) (c.actor tx)
def deliver (packet : Packet 3 2 1) : List (Event 3 2 1) := [0,1,2].map (fun w => .deliver w packet)
def signs (tx : Fin 2) : List (Event 3 2 1) := [0,1,2].map (fun w => .protocol (.sign tx w))
def finish (tx : Fin 2) : List (Event 3 2 1) :=
  [0,1,2].map (fun w => .protocol (.receiveOperation tx w)) ++
  [0,1,2].map (fun w => .protocol (.effect tx w))
def sales := deliver (owner ctx 0) ++ deliver (owner ctx 1) ++ signs 0 ++ signs 1 ++ finish 1 ++ finish 0

example : admitGenesis ctx committee genesis = some start := rfl
example : (run ctx committee start sales).2.core.balance 0 = 95 := by decide
example : ctx.floor + (run ctx committee start sales).2.core.balance 0 = 85 := by decide
example : (run ctx committee start sales).2.core.balance 1 = 15 := by decide
example : verify {ctx with isMint := fun _ => true} (owner ctx 0) = true := by decide
-- Both actors have the increment role; only actor 1 has issuer role 2.
example : verify {ctx with isMint := fun _ => true} (owner ctx 1) = false := by decide
example : verify {ctx with policy := {ctx.policy with issuer := none}, isMint := fun _ => true} (owner ctx 0) = false := by decide
example : verify ctx (canonical ctx (.cancellation 0) 2) = false := by decide
example : verify ctx ⟨42,.actor 1,.cancellation 0⟩ = false := by decide
example : verify ctx ⟨41,.pool,.cancellation 0⟩ = false := by decide
example : verify ctx (canonical ctx (.checkpoint 0) 0) = false := by decide
example : verify ctx (canonical ctx (.checkpoint 0) 1) = true := by decide
example : verify ctx (canonical ctx (.checkpoint 0) 2) = true := by decide
example : admitGenesis {ctx with ceiling := some 89} committee genesis = none := by decide
example : headroom {ctx with initialRights := 5, ceiling := some (-2)} = 3 := by decide
example : verify {ctx with initialRights := 5, ceiling := some (-2)} genesis = true := by decide
example : verify {ctx with initialRights := 0, ceiling := some (-12)} genesis = false := by decide
example : (execute ctx committee start (.protocol (.sign 0 0))).2.core.signatures 0 0 = false := by decide
example : (execute ctx committee start (.protocol (.sign 0 3))).2.core.signatures 0 3 = true := by decide

def reclaimed : CollectiveActors.Context 3 3 2 1 := {ctx with
  epoch := fun tx => if tx.val == 0 then .root 0 else .checkpoint 0
  amount := fun _ => 60
}
def released : List (Event 3 2 1) :=
  deliver (owner reclaimed 0) ++ signs 0 ++ deliver (cancel reclaimed 0) ++
  [0,1,2].map (fun w => .protocol (.fence 0 w)) ++
  [0,1,2].map (fun w => .protocol (.release 0 w))
def checkpointed : List (Event 3 2 1) := released ++
  [0,1,2].map (fun w => .protocol (.freeze (.root 0) w)) ++
  deliver (canonical reclaimed (.checkpoint 0) 2) ++
  [0,1,2].map (fun w => .protocol (.endorse 0 w)) ++
  [0,1,2].map (fun w => .protocol (.record 0 w)) ++
  [0,1,2].map (fun w => .protocol (.install 0 w))
def recoveredSales := checkpointed ++ deliver (owner reclaimed 1) ++ signs 1 ++ finish 1 ++ finish 0

def reclaimStart := initialState reclaimed committee (canonical reclaimed .genesis 0)
example : (run reclaimed committee reclaimStart checkpointed).2.core.active 0 0 = .checkpoint 0 := by decide
example : (run reclaimed committee reclaimStart recoveredSales).2.core.balance 0 = 40 := by decide
example : (run reclaimed committee reclaimStart recoveredSales).2.core.balance 1 = 70 := by decide
example : finalCert (config reclaimed committee) (run reclaimed committee reclaimStart recoveredSales).2.core 0 = false := by decide
example : (run reclaimed committee reclaimStart recoveredSales).2.receipts 0 (.cancellation 0) 1 = true := by decide
example : (run reclaimed committee reclaimStart recoveredSales).2.receipts 0 (.checkpoint 0) 2 = true := by decide
example : (recover reclaimed committee (canonical reclaimed .genesis 0) recoveredSales).isSome = true := by decide

#print axioms execute_erases
#print axioms control_step
#print axioms control_run
#print axioms operation_quorum_has_authorized_actor
#print axioms finality_has_authorized_actor
#print axioms minted_finality_checks_issuer
#print axioms cancel_quorum_has_original_request
#print axioms checkpoint_quorum_has_eligible_request
#print axioms declared_cap_bound
#print axioms declared_floor
#print axioms declared_ceiling
#print axioms admitted_run
#print axioms infinite_refinement
#print axioms released_cannot_finalize
#print axioms receipt_run_mono
#print axioms honest_successor_choice_persists
#print axioms recover_control

end CollectiveActorAudit

open CollectiveActorAudit
def main : IO Unit := do
  if (run ctx committee start sales).2.core.balance 0 != 95 then
    throw (IO.userError "collective actor sale trace failed")
  if (run reclaimed committee reclaimStart recoveredSales).2.core.balance 0 != 40 then
    throw (IO.userError "collective actor reclamation trace failed")
  IO.println "collective actor audit: authenticated sales, shared pool, cancellation, cross-actor checkpoint, late finality and recovery passed"
