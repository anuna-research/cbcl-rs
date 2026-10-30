import LeanCbcl.ConsensusFree.Currency

namespace CBCL.ConsensusFree.Tests
open CBCL.ValidatorBudget
open CBCL.ConsensusFree.Currency
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

abbrev Cmd := Command 2 14 10

def cp (p : Fin 10) : Checkpoint 2 14 10 4 where
  owner := if p.val = 7 then 1 else 0
  parent := match p.val with
    | 1 => .checkpoint 0
    | 2 => .checkpoint 1
    | 5 => .checkpoint 4
    | 6 => .checkpoint 3
    | 7 => .root 1
    | _ => .root 0
  depth := match p.val with | 1 | 5 | 6 => 2 | 2 => 3 | _ => 1
  held := fun tx => match p.val with
    | 0 | 1 | 2 => tx.val < 3
    | 3 | 6 => tx.val = 2
    | 4 | 5 => tx.val = 5 || tx.val = 6
    | 8 => tx.val = 6
    | _ => false
  refunded := fun tx => match p.val with
    | 1 | 2 => tx.val = 0
    | 4 | 5 => tx.val = 5
    | _ => false
  credited := fun tx => p.val = 7 && tx.val = 2
  allocation := fun d =>
    if p.val = 7 then (if d.val = 1 then 10 else 0)
    else if d.val = 2 then 10
    else if d.val = 0 then
      match p.val with | 0 => 0 | 3 | 6 => 20 | 9 => 30 | _ => 10
    else 0
  authorized := p.val != 9

def op (tx : Fin 14) : Currency.Operation 2 10 where
  epoch := match tx.val with
    | 3 => .checkpoint 0
    | 4 => .checkpoint 1
    | 10 => .checkpoint 7
    | 11 => .root 1
    | _ => .root 0
  kind := match tx.val with
    | 7 | 11 | 12 => .mint
    | 8 => .burn
    | 9 => .headroom
    | _ => .pay
  amount := match tx.val with
    | 0 | 1 | 2 => 10
    | 3 | 4 => 3
    | 5 | 6 => 20
    | 7 | 9 | 11 => 2
    | 8 | 12 => 1
    | 10 => 5
    | _ => 0
  recipient := if tx.val = 10 || tx.val = 11 then 0 else 1

def context : Context 2 14 10 where
  checkpoints := cp
  operations := op
  initialRights := fun a => if a.val = 0 then 30 else 0
  initialHeadroom := fun a => if a.val = 0 then 10 else 0
  capped := true
  issuers := fun a => a.val = 0
  ownerSigned := fun _ => true
  nonself := by decide

def committee : Committee 1 := ⟨[0,1,2], [3], by decide, rfl, rfl⟩
def cfg := Currency.config context committee

def after (commands : List Cmd) := (run cfg (initial cfg) commands).2

def signWith (tx : Fin 14) (witnesses : List Nat) : List Cmd := witnesses.map (Command.sign tx)
def signs (tx : Fin 14) : List Cmd := signWith tx [0,1,3]
def finish (tx : Fin 14) : List Cmd :=
  [.receiveOperation tx 0, .receiveOperation tx 1, .receiveOperation tx 2,
   .receiveOperation tx 3, .effect tx 0, .effect tx 1, .effect tx 2]
def cancel (tx : Fin 14) : List Cmd := [.fence tx 0, .fence tx 1, .fence tx 2]
def releases (tx : Fin 14) : List Cmd := [.release tx 0, .release tx 1, .release tx 2, .release tx 3]
def seals (e : Epoch 2 10) : List Cmd := [0,1,2,3].map (Command.freeze e)
def endorseWith (p : Fin 10) : List Cmd := [0,1,2].map (Command.endorse p)
def deliverAndInstall (p : Fin 10) : List Cmd := [0,1,2,3].flatMap (fun w => [.record p w, .install p w])

def triangle : List Cmd := signWith 0 [0,1,3] ++ signWith 1 [0,2,3] ++ signWith 2 [1,2,3] ++ finish 2

def closedTriangle := triangle ++ seals (.root 0) ++ endorseWith 0 ++ deliverAndInstall 0

def oldFinals := closedTriangle ++ signs 3 ++ finish 3 ++ finish 0 ++ finish 1

def refundedDescendant := closedTriangle ++ cancel 0 ++ releases 0 ++
  seals (.checkpoint 0) ++ endorseWith 1 ++ deliverAndInstall 1

def refundThenSpend := refundedDescendant ++ signs 4 ++ finish 4 ++ finish 1 ++ finish 0

def repeatRefund := refundedDescendant ++ seals (.checkpoint 1) ++ endorseWith 2 ++ deliverAndInstall 2 ++
  [.record 1 0, .install 1 0, .release 0 0, .release 0 0] ++ finish 1 ++ finish 0

def reusedRoot := signs 5 ++ signs 6 ++ cancel 5 ++ releases 5 ++ signs 6 ++ finish 6

def closedReused := reusedRoot ++ seals (.root 0) ++ endorseWith 4 ++ deliverAndInstall 4 ++
  seals (.checkpoint 4) ++ endorseWith 5 ++ deliverAndInstall 5 ++ releases 5 ++ finish 5

def splitVotes : List Cmd := signs 2 ++ seals (.root 0) ++ [.endorse 0 0, .endorse 3 1, .endorse 3 2,
  .record 0 0, .record 3 1, .endorse 3 0, .endorse 0 1, .record 0 0, .record 3 1]

def firstBranch := signs 2 ++ seals (.root 0) ++ [.endorse 0 0, .endorse 0 1, .endorse 0 3] ++
  deliverAndInstall 0 ++ [.endorse 3 2, .endorse 3 3, .record 3 2, .endorse 6 0, .record 6 0]

def cappedFlow := signs 7 ++ finish 7 ++ signs 8 ++ finish 8 ++ signs 9 ++ finish 9

def incoming := signs 2 ++ finish 2 ++ seals (.root 1) ++ endorseWith 7 ++
  [0,1,2,3].flatMap (fun w => [.record 7 w, .receiveFinal 2 w, .install 7 w]) ++ signs 10 ++ finish 10

def lagging := triangle ++ seals (.root 0) ++ endorseWith 0 ++
  [.record 0 0, .install 0 0, .record 0 1, .install 0 1, .record 0 3, .install 0 3] ++
  cancel 0 ++ releases 0 ++ seals (.checkpoint 0) ++ endorseWith 1 ++
  [.record 1 2, .install 1 2, .record 0 2, .install 0 2, .install 1 2]

def uncappedContext : Context 2 14 10 := { context with capped := false }
def uncapped := Currency.config uncappedContext committee

def budgetBefore := (after (signs 5)).signatures 6 0
def currentLabel (commands : List Cmd) := ((run cfg (initial cfg) commands).1.filterMap id).map Fin.val

def checks : List (String × Bool) := [
  ("triangle complete checkpoint", decide ((after closedTriangle).active 0 0 = .checkpoint 0)),
  ("triangle partial renewal rejected", (perform cfg (after (triangle ++ seals (.root 0))) (.endorse 3 0)).isNone),
  ("30-rights delayed A/B safe", decide ((after oldFinals).balance 0 = 0 ∧ (after oldFinals).balance 1 = 30)),
  ("D cannot certify zero allocation", !(operationCert cfg (after oldFinals) 3)),
  ("refund descendant installs", decide ((after refundedDescendant).active 0 0 = .checkpoint 1)),
  ("refund allocation exactly ten", decide (allowance cfg (.checkpoint 1) 0 = 10)),
  ("refund then E and late B", decide ((after refundThenSpend).balance 0 = 7 ∧ (after refundThenSpend).balance 1 = 23)),
  ("cancelled old A never finalizes", !(finalCert cfg (after refundThenSpend) 0)),
  ("cumulative refund not repeated", decide ((after repeatRefund).balance 0 = 10 ∧ allowance cfg (.checkpoint 2) 0 = 10)),
  ("old record does not lower frontier", decide ((after repeatRefund).frontier 0 = 3)),
  ("old install does not roll back", decide ((after repeatRefund).active 0 0 = .checkpoint 2)),
  ("release really restores independent budget", decide ((after (signs 5 ++ signs 6)).signatures 6 0 = false ∧
    (after reusedRoot).signatures 6 0 = true)),
  ("un-erased released signature", decide ((after closedReused).signatures 5 0 = true ∧ (after closedReused).released 5 0 = true)),
  ("released signature still belongs in report", (perform cfg (after (reusedRoot ++ seals (.root 0))) (.endorse 8 0)).isNone),
  ("root release plus two checkpoints no inflation", decide ((after closedReused).balance 0 = 10 ∧ (after closedReused).frontier 0 = 2)),
  ("late released root certificate harmless", !(finalCert cfg (after closedReused) 5)),
  ("split votes stall without oracle", !(checkpointCert cfg (after splitVotes) 0) && !(checkpointCert cfg (after splitVotes) 3)),
  ("split votes leave root installed", decide ((after splitVotes).active 0 0 = .root 0)),
  ("same-depth fork cannot certify", !(checkpointCert cfg (after firstBranch) 3)),
  ("unrecognised cousin cannot install", decide ((after firstBranch).frontier 0 = 1)),
  ("lagging install catches up sequentially", decide ((after lagging).active 2 0 = .checkpoint 1)),
  ("mint burn and headroom semantics", decide ((after cappedFlow).balance 0 = 31 ∧ (after cappedFlow).balance 2 = 7 ∧
    (after cappedFlow).balance 3 = 2)),
  ("capped supply conservation", decide (isum (List.finRange 4) (after cappedFlow).balance = 40)),
  ("incoming final credit usable after proof delivery", decide ((after incoming).balance 0 = 25 ∧ (after incoming).balance 1 = 5)),
  ("installation cannot reset charged journal", decide (charge cfg (after (incoming ++ [.install 7 0])) (.checkpoint 7) 0 1 = 15)),
  ("unauthorized issuer rejected", (perform cfg (initial cfg) (.sign 11 0)).isNone),
  ("zero amount rejected", (perform cfg (initial cfg) (.sign 13 0)).isNone),
  ("unrecognized witness rejected", (perform cfg (initial cfg) (.sign 0 99)).isNone),
  ("unauthorized checkpoint rejected", (perform cfg (after (seals (.root 0))) (.endorse 9 0)).isNone),
  ("release needs a real cancellation quorum", (perform cfg (after (signs 5 ++ [.fence 5 0, .fence 5 1])) (.release 5 0)).isNone),
  ("final effects cannot be cancelled", !(cancelCert cfg (after (signs 2 ++ finish 2 ++ cancel 2)) 2)),
  ("release cannot erase final charge", (perform cfg (after (signs 2 ++ finish 2 ++ cancel 2)) (.release 2 0)).isNone),
  ("release requires own existing charge", (perform cfg (after (signs 5 ++ cancel 5)) (.release 5 2)).isNone),
  ("zero-cost fresh signing stopped by seal", (perform uncapped
    (run uncapped (initial uncapped) [.freeze (.root 0) 0]).2 (.sign 12 0)).isNone),
  ("uncapped mint costs no headroom", decide (uncapped.cost 7 2 = 0)),
  ("uncapped mint executes", decide ((run uncapped (initial uncapped) (signs 7 ++ finish 7)).2.balance 0 = 32)),
  ("headroom moves disabled in uncapped mode", (perform uncapped (initial uncapped) (.sign 9 0)).isNone),
  ("final labels are immutable operation identities", decide (currentLabel oldFinals = [2,0,1])),
  ("replay release does not erase signature", decide ((after (reusedRoot ++ releases 5 ++ releases 5)).signatures 5 0 = true))
]

example : cfg.authorized 11 = false := by decide
example : cfg.cost 7 2 = 2 ∧ cfg.credit 7 0 = 2 := by decide
example : BusinessRun cfg (initial cfg).balance ((run cfg (initial cfg) refundThenSpend).1.filterMap id)
    (after refundThenSpend).balance := full_async_refinement cfg refundThenSpend
example : (5 : Int) ≤ 5 + rightsTotal (after refundThenSpend).balance := currency_floor context committee refundThenSpend 5
example : 5 + rightsTotal (after refundThenSpend).balance ≤
    5 + isum (List.finRange 4) (initial cfg).balance := currency_ceiling context committee rfl refundThenSpend 5

end CBCL.ConsensusFree.Tests
