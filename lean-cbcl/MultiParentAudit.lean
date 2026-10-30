import LeanCbcl.ConsensusFree.MultiParent

/-! Executable SPEC-029 scenarios. Every accepted script is passed through the
same perform guards whose soundness is kernel checked, not a second simulator. -/
namespace CBCL.ConsensusFree.MultiParent.Audit
open CBCL.ValidatorBudget
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def graph : Graph 4 where
  lower v := if h : v.val = 1 then [⟨0,by omega⟩]
    else if h : v.val = 2 then [⟨0,by omega⟩]
    else if h : v.val = 3 then [⟨1,by omega⟩,⟨2,by omega⟩]
    else if h : v.val = 4 then [⟨3,by omega⟩]
    else []

def committee : Committee 1 where
  core := [0,1,2]
  others := [3]
  core_size := by decide
  other_size := by decide
  distinct := by decide

def config (a b m genesis : Nat) (hold refund : Version 4 → Fin 4 → Bool)
    (alloc : Version 4 → Nat) : Config 4 4 1 1 where
  graph := graph
  committee := committee
  initial := fun _ => genesis
  manifest v := {
    held := hold v
    refunded := refund v
    credited := fun _ => false
    allocation := fun _ => alloc v
    authorized := true }
  opVersion tx := if tx.val = 0 then 1 else if tx.val = 1 then 2 else if tx.val = 2 then 3 else 0
  cost tx _ := if tx.val = 0 then a else if tx.val = 1 then b else if tx.val = 2 then m else 0
  credit := fun _ _ => 0
  authorized := fun _ => true
  cancelAuthorized := fun _ => true
  disjoint := by intros; exact Or.inr rfl

def clean : Config 4 4 1 1 := config 0 0 60 100 (fun _ _ => false) (fun _ _ => false) (fun _ => 100)

def split : List (Command 4 4) := [.record 1,.record 2,.adopt 1 0,.adopt 1 1,.adopt 2 2,.adopt 2 3]
def join : List (Command 4 4) := [.record 3,.adopt 3 0,.adopt 3 1,.adopt 3 2,.adopt 3 3]
def spend : List (Command 4 4) := [.sign 2 0,.sign 2 1,.sign 2 2,.effect 2 0,.effect 2 1,.effect 2 2]

def snapshot (c : Config 4 4 1 1) (s : State 4 4) : Nat × Nat × Bool × Bool × Int :=
  (s.active 0 |>.val,s.active 2 |>.val,operationCert c s 2,finalCert c s 2,balance c s 0)

-- Honest nodes 0 and 2 start on different branches; both really adopt M.
example : (execute clean initial split).map (fun s => (s.active 0 |>.val,s.active 2 |>.val)) = some (1,2) := by decide
example : (execute clean initial (split ++ join ++ spend)).map (snapshot clean) = some (3,3,true,true,40) := by decide

-- Pending A and B are each held exactly once. Neither initially has a QC.
def hold (v : Version 4) (tx : Fin 4) : Bool :=
  (v.val = 3 && (tx.val = 0 || tx.val = 1)) || (v.val = 4 && tx.val ≤ 2)
def refund (v : Version 4) (tx : Fin 4) : Bool := v.val = 4 && tx.val = 1
def pending : Config 4 4 1 1 := config 30 30 20 100 hold refund
  (fun v => if v.val = 3 then 40 else if v.val = 4 then 50 else 100)
def partials : List (Command 4 4) := [.sign 0 0,.sign 0 1,.sign 1 2,.sign 1 3]
def late : List (Command 4 4) := [.sign 0 3,.effect 0 0,.effect 0 1,.effect 0 3]
def cancel : List (Command 4 4) := [.fence 1 0,.fence 1 1,.fence 1 2,.release 1 2]
def reclaim : List (Command 4 4) := [.record 4,.adopt 4 0,.adopt 4 1,.adopt 4 2]

example : (execute pending initial (split ++ partials)).map (fun s =>
    (operationCert pending s 0,operationCert pending s 1)) = some (false,false) := by decide
example : (execute pending initial (split ++ partials ++ join ++ spend ++ late)).map (snapshot pending) =
    some (3,3,true,true,50) := by decide
example : (execute pending initial (split ++ partials ++ join ++ spend ++ late ++ cancel ++ reclaim)).map
    (fun s => (s.active 0 |>.val,allowance pending (s.active 0) 0,balance pending s 0,s.signatures 1 2,s.released 1 2)) =
    some (4,50,50,true,true) := by decide

-- Partial signatures CANNOT be forgotten by adoption, even after release.
def forget : Config 4 4 1 1 := config 30 30 20 100 (fun _ _ => false) (fun _ _ => false) (fun _ => 100)
example : execute forget initial (split ++ partials ++ join) = none := by decide
example : execute forget initial (split ++ partials ++ cancel ++ join) = none := by decide

-- Parent books must be recomputed, not summed; allocation 200 is rejected.
def summed : Config 4 4 1 1 := config 0 0 120 100 (fun _ _ => false) (fun _ _ => false)
  (fun v => if v.val = 3 then 200 else 100)
example : execute summed initial (split ++ join) = none := by decide

-- Correctly held costs with an incorrect allocation are also rejected.
def wrongBooks : Config 4 4 1 1 := config 30 30 20 100 hold refund
  (fun v => if v.val = 3 then 41 else if v.val = 4 then 50 else 100)
example : execute wrongBooks initial (split ++ partials ++ join) = none := by decide

-- A refund cannot precede its cancellation certificate.
example : execute pending initial (split ++ partials ++ join ++ spend ++ late ++ [.record 4]) = none := by decide
-- A cancellation for finalized A is refused by every honest effect signer.
example : execute pending initial (split ++ partials ++ join ++ spend ++ late ++ [.fence 0 0]) = none := by decide
-- Releasing without a cancellation certificate is refused.
example : execute pending initial (split ++ partials ++ [.release 0 0]) = none := by decide
-- Effect acknowledgements without an operation certificate are refused.
example : execute pending initial (split ++ [.effect 0 0]) = none := by decide
-- A sibling is not a forward successor of the active branch.
example : execute clean initial (split ++ [.adopt 2 0]) = none := by decide
-- Signing the wrong active version is refused.
example : execute summed initial (split ++ [.sign 2 0]) = none := by decide
-- Isolated capacity rejection: valid M, correct active version, charge240>200.
def tooMuch : Config 4 4 1 1 := config 0 0 80 100 (fun _ _ => false) (fun _ _ => false) (fun _ => 100)
example : (execute tooMuch initial (split ++ join)).map (fun s => s.active 0 |>.val) = some 3 := by decide
example : execute tooMuch initial (split ++ join ++ [.sign 2 0]) = none := by decide

-- Both parents carry the SAME root debit. The join charges its ID once.
def duplicate : Config 4 4 1 1 := {
  (config 0 0 60 100 (fun v tx => v.val ≠ 0 && tx.val = 3) (fun _ _ => false) (fun _ => 90)) with
  cost := fun tx _ => if tx.val = 3 then 10 else if tx.val = 2 then 60 else 0
  disjoint := by intros; exact Or.inr rfl }
def rootVotes : List (Command 4 4) := [.sign 3 0,.sign 3 1,.sign 3 2]
def rootEffects : List (Command 4 4) := [.effect 3 0,.effect 3 1,.effect 3 2]
example : (execute duplicate initial (rootVotes ++ split ++ join ++ spend ++ rootEffects)).map
    (fun s => (allowance duplicate 3 0,balance duplicate s 0)) = some (90,30) := by decide

-- Credits enter a manifest only after a real effects QC, and only once.
def creditedCoin : Config 4 4 1 1 := {
  (config 0 0 60 100 (fun _ _ => false) (fun _ _ => false) (fun _ => 100)) with
  manifest := fun v => {
    held := fun tx => v.val ≠ 0 && tx.val = 3
    refunded := fun _ => false
    credited := fun tx => v.val ≠ 0 && tx.val = 3
    allocation := fun _ => 150
    authorized := true }
  credit := fun tx _ => if tx.val = 3 then 50 else 0
  disjoint := by intro tx d; by_cases ht : tx.val = 3
                 · exact Or.inl (by simp [config,ht])
                 · exact Or.inr (by simp [ht]) }
example : execute creditedCoin initial split = none := by decide
example : (execute creditedCoin initial (rootVotes ++ rootEffects ++ split ++ join ++ spend)).map
    (fun s => (allowance creditedCoin 3 0,balance creditedCoin s 0)) = some (150,90) := by decide

-- The old partial-renewal counterexample: A/B/C root operations each reserve10.
-- A later manifest recognizes only C; A/B signatures are NOT renewable rights.
def oldPattern : Config 4 4 1 1 := {
  (config 0 0 0 30 (fun v tx => v.val = 1 && tx.val = 2) (fun _ _ => false) (fun _ => 20)) with
  opVersion := fun _ => 0
  cost := fun tx _ => if tx.val ≤ 2 then 10 else 0
  disjoint := by intros; exact Or.inr rfl }
def oldVotes : List (Command 4 4) := [
  .sign 0 0,.sign 0 1,.sign 0 3,
  .sign 1 0,.sign 1 2,.sign 1 3,
  .sign 2 1,.sign 2 2,.sign 2 3]
example : (execute oldPattern initial oldVotes).map (fun s =>
    (operationCert oldPattern s 0,operationCert oldPattern s 1,operationCert oldPattern s 2)) = some (true,true,true) := by decide
example : execute oldPattern initial (oldVotes ++ [.record 1,.adopt 1 1]) = none := by decide
example : execute oldPattern initial (oldVotes ++ [.record 1,.adopt 1 2]) = none := by decide

-- Over-reserved branches need owner-authorized cancellation before a join.
def crowdedHold (v : Version 4) (tx : Fin 4) : Bool := v.val = 3 && tx.val ≤ 1
def crowded : Config 4 4 1 1 := config 20 20 0 30 crowdedHold (fun _ _ => false)
  (fun v => if v.val = 3 then 0 else 30)
def crowdedRefund : Config 4 4 1 1 := config 20 20 0 30 crowdedHold
  (fun v tx => v.val = 3 && tx.val = 1) (fun v => if v.val = 3 then 10 else 30)
example : execute crowded initial (split ++ partials ++ join) = none := by decide
example : (execute crowdedRefund initial (split ++ partials ++ cancel ++ join)).map
    (fun s => (s.active 0 |>.val,s.active 2 |>.val,allowance crowdedRefund 3 0,s.signatures 1 2,s.released 1 2)) =
    some (3,3,10,true,true) := by decide

def unauthenticated : Config 4 4 1 1 := {clean with authorized := fun _ => false}
def unauthorizedCancellation : Config 4 4 1 1 := {pending with cancelAuthorized := fun _ => false}
example : execute unauthenticated initial (split ++ join ++ [.sign 2 0]) = none := by decide
example : execute unauthorizedCancellation initial (split ++ partials ++ [.fence 1 0]) = none := by decide

-- Run/refinement theorem applies to the actual accepted script.
theorem joined_refines {s} (ok : execute pending initial
    (split ++ partials ++ join ++ spend ++ late ++ cancel ++ reclaim) = some s) :
    BusinessRun pending initial s ∧ ∀ d, 0 ≤ balance pending s d := by
  have run := execute_sound ok
  exact ⟨finite_refinement run,resource_nonnegative (run_invariant (initial_invariant pending) run)⟩

#print axioms resource_nonnegative
#print axioms finite_refinement
#print axioms infinite_refinement
#print axioms release_future_safe

end CBCL.ConsensusFree.MultiParent.Audit

def main : IO Unit := do
  IO.println "MultiParentAudit: kernel-checked split/join, late certificates, cancellation/refund and rejection scenarios"
