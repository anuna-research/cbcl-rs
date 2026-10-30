import LeanCbcl.ValidatorBudget

/-!
SPEC-021 BUG-2100: a guarded finite trace refutes asynchronous resource safety.

This is the payment-only, fixed-roster fragment of the Python reference model.
All symbolic payments have source Alice, recipient Bob, genesis bound and positive
amounts. Witness3 is Byzantine. No recovery, corrupted identity or mutation is used.
The functions below check the actual node signing/version/execution guards; they
do not assume business safety. A separate theorem excludes refinement to a funded
abstract payment machine. Mapping this fragment to Python is independently audited,
not an extraction/cross-language correspondence theorem.
-/
namespace CBCL.ValidatorBudgetRefutation
open CBCL.ValidatorBudget (sumOn)

inductive Payment where
  | a | b | c | d
  deriving DecidableEq, Repr, Inhabited

def amount : Payment → Nat
  | .a | .b | .c => 10
  | .d => 3

def version : Payment → Nat
  | .a | .b | .c => 0
  | .d => 1

structure Local where
  version : Nat := 0
  free : Int := 60
  signed : List Payment := []
  executed : List Payment := []
  deriving DecidableEq, Repr, Inhabited

structure State where
  nodes : List Local := List.replicate 4 {}
  ballots : List (Nat × Payment) := []
  final : List Payment := []
  versionKnown : Bool := false
  deriving DecidableEq, Repr, Inhabited

def initial : State := {}

def signatures (s : State) (tx : Payment) : Nat :=
  sumOn [0, 1, 2, 3] (fun w => if (w, tx) ∈ s.ballots then 1 else 0)

def effects (s : State) (tx : Payment) : Nat :=
  sumOn s.nodes (fun w => if tx ∈ w.executed then 1 else 0)

/-- Signatures are idempotent, positive amounts are fixed above, member indices
are bounded, and honest signatures charge the actual scaled amount. -/
def sign (s : State) (w : Nat) (tx : Payment) : Option State := do
  if w ≥ 4 then none else do
    let node ← s.nodes[w]?
    if (w, tx) ∈ s.ballots then some s else do
      if tx == .d && !s.versionKnown then none else do
        if w != 3 && (node.version != version tx || node.free < 3 * (amount tx : Int)) then
          none
        else
          let after := if w == 3 then node else
            { node with free := node.free - 3 * amount tx, signed := tx :: node.signed }
          some { s with nodes := s.nodes.set w after, ballots := (w, tx) :: s.ballots }

/-- The owner-signed partial request has the current genesis parent and names
only C. C must already be final and certified. Negative results are retained. -/
def update (s : State) (w : Nat) : Option State := do
  if w ≥ 4 then none else do
    let node ← s.nodes[w]?
    if node.version != 0 || !decide (Payment.c ∈ s.final) || signatures s .c < 3 then none
    else
      let refund : Int := if Payment.c ∈ node.signed then 30 else 0
      let after := { node with version := 1, free := node.free - 20 + refund }
      some { s with nodes := s.nodes.set w after, versionKnown := true }

/-- The covered history is empty for old payments and {C} for new payment D.
No execution fence exists in this trace. Effects are distinct roster slots. -/
def execute (s : State) (w : Nat) (tx : Payment) : Option State := do
  if w ≥ 4 || signatures s tx < 3 then none else do
    let node ← s.nodes[w]?
    if tx == .d && !decide (Payment.c ∈ node.executed) then none else do
      if tx ∈ node.executed then some s else do
        let after := { node with executed := tx :: node.executed }
        let next := { s with nodes := s.nodes.set w after }
        if effects next tx ≥ 3 && !decide (tx ∈ s.final) then
          some { next with final := tx :: s.final }
        else some next

inductive Command where
  | sign (w : Nat) (tx : Payment)
  | update (w : Nat)
  | execute (w : Nat) (tx : Payment)
  deriving DecidableEq, Repr

def step (s : State) : Command → Option State
  | .sign w tx => sign s w tx
  | .update w => update s w
  | .execute w tx => execute s w tx

def run : State → List Command → Option State
  | s, [] => some s
  | s, cmd :: rest => (step s cmd).bind (fun next => run next rest)

theorem positive_amounts :
    ∀ tx ∈ ([.a, .b, .c, .d] : List Payment), 0 < amount tx := by decide

/-- The certificate has a different honest pair for each old payment. -/
def oldSignatures : List Command := [
  .sign 0 .a, .sign 1 .a, .sign 3 .a,
  .sign 0 .b, .sign 2 .b, .sign 3 .b,
  .sign 1 .c, .sign 2 .c, .sign 3 .c]

def finalize (tx : Payment) : List Command :=
  [.execute 0 tx, .execute 1 tx, .execute 2 tx]

def renew (updateZero : Bool) : List Command :=
  (if updateZero then [.update 0] else []) ++ [.update 1, .update 2, .update 3]

def checkpointPrefix (updateZero : Bool) : List Command := oldSignatures ++ finalize .c ++ renew updateZero

def trace (updateZero : Bool) : List Command := checkpointPrefix updateZero ++
  [.sign 1 .d, .sign 2 .d, .sign 3 .d] ++ finalize .d ++ finalize .a ++ finalize .b

def result (updateZero : Bool) : State := (run initial (trace updateZero)).getD initial

def observed (s : State) : Int := 30 - (sumOn s.final amount : Int)

/-- Kernel reduction checks EVERY command returned success, rather than admitting
an invalid transition because an expected final state was supplied. -/
theorem guarded_trace : run initial (trace true) = some (result true) := by decide

theorem old_certificates :
    ∃ s, run initial oldSignatures = some s ∧ signatures s .a = 3 ∧
      signatures s .b = 3 ∧ signatures s .c = 3 ∧
      (s.nodes.map Local.free).take 3 = [0, 0, 0] := by
  decide

theorem partial_update_budgets :
    ∃ s, run initial (checkpointPrefix true) = some s ∧
      (s.nodes.map Local.free).take 3 = [-20, 10, 10] := by decide

theorem all_final : (result true).final = [.b, .a, .d, .c] := by decide

theorem overspent : observed (result true) = -3 := by decide

theorem final_quorums :
    ∀ tx ∈ ([.a, .b, .c, .d] : List Payment),
      signatures (result true) tx = 3 ∧ effects (result true) tx = 3 := by decide

/-- Refusing the negative update at witness0 and accepting only the version's
quorum {1,2,3} still permits exactly the same overspend. -/
theorem nonnegative_adopters_trace : run initial (trace false) = some (result false) := by decide

theorem nonnegative_adopters_budgets :
    ∃ s, run initial (checkpointPrefix false) = some s ∧
      (s.nodes.map Local.free).take 3 = [0, 10, 10] := by decide

theorem quorum_adopted_partial_update :
    ∃ s, run initial (checkpointPrefix false) = some s ∧
      sumOn s.nodes (fun w => if w.version == 1 then 1 else 0) = 3 := by decide

theorem nonnegative_adopters_overspent : observed (result false) = -3 := by decide

/-- Independent funded-payment specification, allowing internal stuttering. -/
inductive BusinessStep : Int → Int → Prop where
  | stutter (balance : Int) : BusinessStep balance balance
  | pay (balance : Int) (n : Nat) (positive : 0 < n) (funded : (n : Int) ≤ balance) :
      BusinessStep balance (balance - n)

inductive BusinessReachable : Int → Prop where
  | start : BusinessReachable 30
  | next {a b : Int} : BusinessReachable a → BusinessStep a b → BusinessReachable b

theorem business_nonnegative {balance : Int} (h : BusinessReachable balance) :
    0 ≤ balance := by
  induction h with
  | start => omega
  | next _ step ih => cases step <;> omega

/-- The actual guarded trace cannot map to any legal funded-payment behavior
under the intended finalized-balance observation. No refinement premise is assumed. -/
theorem no_funded_refinement : ¬ BusinessReachable (observed (result true)) := by
  intro reachable
  have nonnegative := business_nonnegative reachable
  rw [overspent] at nonnegative
  omega

#print axioms guarded_trace
#print axioms overspent
#print axioms final_quorums
#print axioms nonnegative_adopters_trace
#print axioms nonnegative_adopters_overspent
#print axioms no_funded_refinement

end CBCL.ValidatorBudgetRefutation
