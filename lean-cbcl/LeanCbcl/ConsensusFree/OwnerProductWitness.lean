import LeanCbcl.ConsensusFree.OwnerTermination

namespace CBCL.ConsensusFree.OwnerProduct
open CBCL.ValidatorBudget
variable {N W R f : Nat}

/-- Run a finite action script for a bounded number of service turns, then retain its result. -/
def play (c : Config N W R f) (s : State N W R) : List (Action N W) → Nat → State N W R
  | [], _ => s
  | _ :: _, 0 => s
  | a :: rest, n+1 => play c (perform c s a) rest n

@[simp] theorem play_zero (c : Config N W R f) (s : State N W R) (actions : List (Action N W)) :
    play c s actions 0 = s := by cases actions <;> rfl

/-- Select a script's next action, using replay after its last entry. -/
def scriptAction (actions : List (Action N W)) (n : Nat) : Action N W :=
  (actions[n]?).getD .replay

theorem play_step (c : Config N W R f) (s : State N W R) (actions : List (Action N W)) (n : Nat) :
    play c s actions (n+1) = perform c (play c s actions n) (scriptAction actions n) := by
  induction actions generalizing s n with
  | nil => simp [play, scriptAction, perform, Enabled, requires, target, applyAction]
  | cons a rest ih =>
    cases n with
    | zero => simp [play, scriptAction]
    | succ n => simpa [play, scriptAction] using ih (perform c s a) n

theorem play_terminal (c : Config N W R f) (s : State N W R) (actions : List (Action N W))
    (n : Nat) (after : actions.length ≤ n) : play c s actions n = play c s actions actions.length := by
  induction actions generalizing s n with
  | nil => rfl
  | cons a rest ih =>
    cases n with
    | zero => simp at after
    | succ n => simpa [play] using ih (perform c s a) n (by simpa using after)

/-- A finite successful trace followed by replay is a real fair infinite run
when no honest necessary work remains at its terminal state. -/
def scripted (c : Config N W R f) (actions : List (Action N W))
    (terminal : ∀ a, honest c a → ¬ (Enabled c (play c initial actions actions.length) a ∧
      Needed (play c initial actions actions.length) a)) : Execution c where
  state := play c initial actions
  action := scriptAction actions
  starts := by cases actions <;> rfl
  step := play_step c initial actions
  fair := by
    intro a ha start continuous
    have hn : actions.length ≤ max start actions.length := by omega
    have atEnd := continuous (max start actions.length) (by omega)
    rw [play_terminal c initial actions _ hn] at atEnd
    exact False.elim (terminal a ha atEnd)

namespace Witness
private def costs : OwnerFunding.Costs 2 1 where
  requestId := fun i => if i.val = 0 then "pay-four" else "pay-last-unit"
  incomingId := fun i => if i.val = 0 then "external-zero" else "external-one"
  requestUnique := by decide
  incomingUnique := by decide
  separate := by decide
  initial := fun _ => 5
  debit := fun i _ => if i.val = 0 then 4 else 1
  credit := fun _ _ => 0
  incomingCredit := fun _ _ => 0
  incomingAuthenticated := fun _ => false
private def external : OwnedProgress.Retry.Catalogue 2 where
  dependencies := fun _ => []
  height := fun _ => 0
  earlier := by simp
  verified := fun _ => false

/-- Two funded requests and a four-validator committee with one Byzantine member. -/
def config : Config 2 4 1 1 where
  costs := costs
  core := [0,1,2]
  others := [3]
  distinct := by decide
  coreSize := by decide
  otherSize := by decide
  ownerValidator := 0
  ownerHonest := by decide
  external := fun _ => external
  externalVerified := by intros; contradiction
  limit := fun _ => 3
  safeLimit := by decide

/-- Owner first freezes because 4 exceeds the concurrent envelope 3. Validator 2
misses the entire first root/operation/effects exchange. Byzantine validator 3
helps form early QCs, then takes no further action. -/
def sealEarly : List (Action 2 4) :=
  [.admit 0, .admit 1, .freeze 0, .manifest 0,
   .metadata 0 0, .metadata 0 1, .metadata 0 3,
   .seal 0, .seal 1, .seal 3,
   .receiveSeal 0, .receiveSeal 1, .receiveSeal 3, .formSeal]
/-- Early operation certification while honest validator two still lags. -/
def opEarly : List (Action 2 4) := sealEarly ++
  [.deliverRoot 0, .deliverRoot 1, .adopt 0 0, .adopt 0 1, .activate 0, .issueOwned 0,
   .act 0 0, .act 0 1, .sign 0 0, .sign 0 1, .sign 0 3,
   .receiveVote 0 0, .receiveVote 0 1, .receiveVote 0 3, .formOperation 0]
/-- First-request completion using two honest validators and Byzantine assistance. -/
def firstDone : List (Action 2 4) := opEarly ++
  [.deliverOperation 0 0, .deliverOperation 0 1, .effect 0 0, .effect 0 1, .effect 0 3,
   .receiveEffect 0 0, .receiveEffect 0 1, .receiveEffect 0 3, .formFinal 0, .complete 0]
/-- Lagging-validator catch-up and final-unit completion after Byzantine silence. -/
def allDone : List (Action 2 4) := firstDone ++
  [.manifest 1,
   .deliverFinal 0 0, .deliverFinal 0 1,
   .metadata 0 2, .act 0 2, .deliverOperation 0 2, .deliverFinal 0 2,
   .metadata 1 0, .metadata 1 1, .metadata 1 2,
   .deliverRoot 2, .adopt 0 2, .adopt 1 0, .adopt 1 1, .adopt 1 2, .activate 1, .issueOwned 1,
   .act 1 0, .act 1 1, .act 1 2, .sign 1 0, .sign 1 1, .sign 1 2,
   .receiveVote 1 0, .receiveVote 1 1, .receiveVote 1 2, .formOperation 1,
   .deliverOperation 1 0, .deliverOperation 1 1, .deliverOperation 1 2,
   .effect 1 0, .effect 1 1, .effect 1 2,
   .receiveEffect 1 0, .receiveEffect 1 1, .receiveEffect 1 2, .formFinal 1, .complete 1]
/-- State with an owner-observed root certificate before validator two catches up. -/
def sealedEarly := play config initial sealEarly sealEarly.length
/-- State with an observed operation QC but no vote from validator two. -/
def operationEarly := play config initial opEarly opEarly.length
/-- State after the first request's durable owner completion. -/
def firstComplete := play config initial firstDone firstDone.length
/-- State after both witness requests durably complete. -/
def terminal := play config initial allDone allDone.length

set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

example : sealedEarly.bits (.g .seal) = true ∧ sealedEarly.bits (.p .sealVote 2) = false := by decide
example : ¬ Needed sealedEarly (.seal 2) := by unfold Needed Pending; decide
example : (perform config sealedEarly (.deliverRoot 2)).bits (.p .root 2) = false := by decide
example : operationEarly.bits (.u .operation 0) = true ∧ operationEarly.bits (.l .vote 0 2) = false := by decide
example : Pending operationEarly ∧ ¬ Needed operationEarly (.sign 0 2) := by unfold Needed Pending Unfinal; decide
example : firstComplete.bits (.u .complete 0) = true ∧ firstComplete.bits (.l .effect 0 2) = false := by decide
example : ∀ i, terminal.bits (.u .complete i) = true := by decide
example : terminal.bits (.l .vote 1 3) = false ∧ terminal.bits (.l .effect 1 3) = false := by decide
example : terminal.allocation 1 0 = 1 := by decide

private theorem terminal_no_work : ∀ a, honest config a → ¬ (Enabled config terminal a ∧ Needed terminal a) := by
  have noPending : ¬ Pending terminal := by unfold Pending; decide
  have issued : ∀ i, terminal.bits (.u .issued i) = true := by decide
  have versions : ∀ i, terminal.bits (.u .version i) = true := by decide
  have activated : ∀ i, terminal.bits (.u .activated i) = true := by decide
  have operations : ∀ i, terminal.bits (.u .operation i) = true := by decide
  have finals : ∀ i, terminal.bits (.u .final i) = true := by decide
  have completed : ∀ i, terminal.bits (.u .complete i) = true := by decide
  have frozen : terminal.bits (.g .frozen) = true := by decide
  have sealed : terminal.bits (.g .seal) = true := by decide
  intro a ha
  cases a <;> simp [honest, Enabled, Needed, target, noPending, issued, versions, activated,
    operations, finals, completed, frozen, sealed] at *

/-- A non-vacuous fair infinite execution ending in replay after both requests finish. -/
def fairWitness : Execution config := scripted config allDone terminal_no_work
example : (fairWitness.state allDone.length).bits (.u .complete 1) = true := by decide
example : ∃ t, (fairWitness.state t).bits (.u .complete 1) = true := by
  obtain ⟨t, _, ht⟩ := admitted_eventually_complete fairWitness 1 2 (by decide)
  exact ⟨t, ht⟩

/-- Arbitrarily late admission is permitted; it cannot change the previously
selected root or consume the previous request's immutable slot. -/
def lateAdmission : List (Action 2 4) :=
  firstDone.filter (fun a => a != .admit 1) ++ [.admit 1] ++ allDone.drop firstDone.length
example : (play config initial (firstDone.filter (fun a => a != .admit 1)) firstDone.length).bits (.u .accepted 1) = false := by decide
example : ∀ i, (play config initial lateAdmission lateAdmission.length).bits (.u .complete i) = true := by decide

private def externalChain : OwnedProgress.Retry.Catalogue 2 where
  dependencies := fun node => if node.val = 0 then [] else [0]
  height := Fin.val
  earlier := by decide
  verified := fun _ => true

/-- Zero initial funds with authenticated external credit and an acyclic proof chain. -/
def incomeConfig : Config 2 4 1 1 := {config with
  costs := {costs with
    initial := fun _ => 0
    incomingCredit := fun i _ => if i.val = 0 then 5 else 7
    incomingAuthenticated := fun _ => true}
  external := fun _ => externalChain
  externalVerified := by decide
  limit := fun _ => 0
  safeLimit := by decide}
/-- Receive funding, admit both requests and pin the first owned version. -/
def pinIncome : List (Action 2 4) := [.income 0, .admit 0, .admit 1, .freeze 0, .manifest 0]
/-- Version state whose incoming identity snapshot is already immutable. -/
def pinnedIncome := play incomeConfig initial pinIncome pinIncome.length
example : pinnedIncome.bits (.snapshot 0 0) = true ∧ pinnedIncome.bits (.snapshot 0 1) = false := by decide
example : (perform incomeConfig pinnedIncome (.metadata 0 0)).bits (.l .metadata 0 0) = false := by decide
example : (perform incomeConfig pinnedIncome (.external 0 1 0)).bits (.external 0 1 0) = false := by decide
example : (perform incomeConfig pinnedIncome (.income 1)).allocation 0 0 = 5 ∧
    (perform incomeConfig pinnedIncome (.income 1)).bits (.snapshot 0 1) = false := by decide

/-- Dependency-ordered external imports followed by both funded witness payments. -/
def incomeTrace : List (Action 2 4) := pinIncome ++
  [0,1,2,3].flatMap (fun w => [.external 0 1 w, .external 0 0 w, .external 0 1 w, .deliverIncome 0 w]) ++
  allDone.drop 4
example : ∀ i, (play incomeConfig initial incomeTrace incomeTrace.length).bits (.u .complete i) = true := by decide
example : (play incomeConfig initial incomeTrace incomeTrace.length).allocation 1 0 = 1 := by decide

end Witness
end CBCL.ConsensusFree.OwnerProduct
