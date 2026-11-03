import LeanCbcl.ConsensusFree.CollectiveProtocol
open CBCL.ConsensusFree CBCL.ValidatorBudget
namespace CollectiveActorReview
open CollectiveActors
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
def committee : Committee 1 := ⟨[0,1,2], [3], by decide, rfl, rfl⟩
def ctx : CollectiveActors.Context 3 3 2 1 where
  domain := 7
  policy := {
    cast := fun _ => true
    role := fun a r => a.val = r.val || (r.val = 2 && a.val = 1)
    initializer := 0, increment := 1, decrement := 2, issuer := some 1 }
  authenticated := fun _ _ _ => true
  opener := 0
  floor := -10
  ceiling := some 100
  initialRights := 100
  manifests := fun _ => {
    parent := .root 0, depth := 1
    held := fun _ => false, refunded := fun _ => false, credited := fun _ => false
    allocation := fun d => if d.val = 0 then 100 else 10 }
  epoch := fun _ => .root 0
  actor := fun tx => if tx.val = 0 then 1 else 2
  isMint := fun _ => false
  amount := fun tx => if tx.val = 0 then 3 else 2
def start := initialState ctx committee (canonical ctx .genesis 0)
def op (tx : Fin 2) : Packet 3 2 1 := canonical ctx (.operation tx) (ctx.actor tx)
def cancel (tx : Fin 2) : Packet 3 2 1 := canonical ctx (.cancellation tx) (ctx.actor tx)
def deliverOp (tx : Fin 2) : List (Event 3 2 1) := [0,1,2].map (fun w => .deliver w (op tx))
def finalTx (tx : Fin 2) : List (Event 3 2 1) :=
  deliverOp tx ++ [0,1,2].map (fun w => .protocol (.sign tx w)) ++
  [0,1,2].map (fun w => .protocol (.receiveOperation tx w)) ++
  [0,1,2].map (fun w => .protocol (.effect tx w))
example : (run ctx committee start (finalTx 0 ++ finalTx 1)).2.core.balance 0 = 95 := by decide
example : (execute ctx committee start (.protocol (.sign 0 0))).2.core.signatures 0 0 = false := by decide
example : (execute ctx committee start (.protocol (.sign 0 3))).2.core.signatures 0 3 = true := by decide
example : verify ctx ⟨7, .pool, .operation 0⟩ = false := by decide
example : verify ctx ⟨8, .actor 1, .operation 0⟩ = false := by decide
example : verify ctx (canonical ctx (.cancellation 0) 2) = false := by decide
example : verify ctx (canonical ctx (.checkpoint 0) 0) = false := by decide
example : verify ctx (canonical ctx (.checkpoint 0) 1) = true := by decide
example : verify ctx (canonical ctx (.checkpoint 0) 2) = true := by decide
example : verify {ctx with authenticated := fun _ _ p => p == .operation 0}
  (canonical ctx (.cancellation 0) 1) = false := by decide
example : verify {ctx with policy := {ctx.policy with cast := fun _ => false}} (op 0) = false := by decide
example : verify {ctx with isMint := fun _ => true} (op 1) = false := by decide
example : verify {ctx with ceiling := some 89} (canonical ctx .genesis 0) = false := by decide
example : verify {ctx with ceiling := some 90} (canonical ctx .genesis 0) = true := by decide
example : headroom ctx = 10 := by decide
example : (run ctx committee start [.deliver 0 (op 0), .protocol (.fence 0 0)]).2.core.fences 0 0 = false := by decide
example : (run ctx committee start [.deliver 0 (cancel 0), .protocol (.sign 0 0)]).2.core.signatures 0 0 = false := by decide
example : (run ctx committee start [.deliver 0 (op 0), .deliver 0 (cancel 0), .protocol (.fence 0 0)]).2.core.fences 0 0 = true := by decide
example : (run ctx committee start [
  .deliver 0 (canonical ctx (.checkpoint 0) 1),
  .deliver 0 (canonical ctx (.checkpoint 0) 2),
  .deliver 0 (canonical ctx (.checkpoint 0) 0)]).2.receipts 0 (.checkpoint 0) 1 = true := by decide
example : (run ctx committee start [
  .deliver 0 (canonical ctx (.checkpoint 0) 1),
  .deliver 0 (canonical ctx (.checkpoint 0) 2)]).2.receipts 0 (.checkpoint 0) 2 = true := by decide
example : (run ctx committee start (finalTx 0 ++ [.deliver 0 (canonical ctx .genesis 0)])).2.core.balance 0 = 97 := by decide
def sealRoot : List (Event 3 2 1) := [0,1,2].map (fun w => .protocol (.freeze (.root 0) w))
example : (run ctx committee start (sealRoot ++ [.protocol (.endorse 0 0)])).2.core.votes 0 0 = false := by decide
example : (run ctx committee start (sealRoot ++ [.deliver 0 (canonical ctx (.checkpoint 0) 2), .protocol (.endorse 0 0)])).2.core.votes 0 0 = true := by decide
def cancelled : List (Event 3 2 1) := deliverOp 0 ++
  [0,1,2].map (fun w => .protocol (.sign 0 w)) ++
  [0,1,2].map (fun w => .deliver w (cancel 0)) ++
  [0,1,2].map (fun w => .protocol (.fence 0 w)) ++
  [0,1,2].map (fun w => .protocol (.release 0 w))
example : (run ctx committee start cancelled).2.core.released 0 0 = true := by decide
example : (run ctx committee start (cancelled ++ finalTx 0)).2.core.balance 0 = 100 := by decide
example : finalCert (config ctx committee) (run ctx committee start (cancelled ++ finalTx 0)).2.core 0 = false := by decide
end CollectiveActorReview
