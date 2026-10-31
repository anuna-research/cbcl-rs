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

/-- Four fixed payments used by the unsafe renewal counterexample. -/
inductive Payment where
  | a | b | c | d
  deriving DecidableEq, Repr, Inhabited

/-- Nonnegative amount carried by an operation. -/
def amount : Payment → Nat
  | .a | .b | .c => 10
  | .d => 3

/-- Source version assigned to each counterexample payment. -/
def version : Payment → Nat
  | .a | .b | .c => 0
  | .d => 1

/-- One validator's version, remaining budget and persistent journals. -/
structure Local where
  /-- Version currently installed by this validator. -/
  version : Nat := 0
  /-- Remaining scaled budget in the counterexample validator. -/
  free : Int := 60
  /-- Payments durably reserved by this validator. -/
  signed : List Payment := []
  /-- Payments for which this validator emitted effects. -/
  executed : List Payment := []
  deriving DecidableEq, Repr, Inhabited

-- Lean generates a precedence parameter that these record printers do not use.
attribute [nolint unusedArguments] instReprLocal.repr

/-- Counterexample validator states, reservation ballots and final effects. -/
structure State where
  /-- Four validator-local states. -/
  nodes : List Local := List.replicate 4 {}
  /-- Persistent reservation signatures, indexed by validator and payment. -/
  ballots : List (Nat × Payment) := []
  /-- Payments with a completed effect certificate. -/
  final : List Payment := []
  /-- Whether the counterexample's replacement version has been announced. -/
  versionKnown : Bool := false
  deriving DecidableEq, Repr, Inhabited

-- Lean generates a precedence parameter that these record printers do not use.
attribute [nolint unusedArguments] instReprState.repr

/-- Four validators at version zero with sixty scaled budget units each. -/
def initial : State := {}

/-- Count distinct reservation signers for a payment. -/
def signatures (s : State) (tx : Payment) : Nat :=
  sumOn [0, 1, 2, 3] (fun w => if (w, tx) ∈ s.ballots then 1 else 0)

/-- Count validator effect votes for a payment. -/
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

/-- Executable protocol requests with explicit transaction and validator identities. -/
inductive Command where
  | sign (w : Nat) (tx : Payment)
  | update (w : Nat)
  | execute (w : Nat) (tx : Payment)
  deriving DecidableEq, Repr

/-- Execute one counterexample command, rejecting an invalid local action. -/
def step (s : State) : Command → Option State
  | .sign w tx => sign s w tx
  | .update w => update s w
  | .execute w tx => execute s w tx

/-- Execute the counterexample schedule, propagating the first rejection. -/
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

/-- Ask three honest validators to emit effects for a payment. -/
def finalize (tx : Payment) : List Command :=
  [.execute 0 tx, .execute 1 tx, .execute 2 tx]

/-- Install the replacement version, optionally including validator zero. -/
def renew (updateZero : Bool) : List Command :=
  (if updateZero then [.update 0] else []) ++ [.update 1, .update 2, .update 3]

/-- Old reservations and one final payment followed by unsafe version renewal. -/
def checkpointPrefix (updateZero : Bool) : List Command := oldSignatures ++ finalize .c ++ renew updateZero

/-- Counterexample schedule: renew, spend again, then deliver delayed old effects. -/
def trace (updateZero : Bool) : List Command := checkpointPrefix updateZero ++
  [.sign 1 .d, .sign 2 .d, .sign 3 .d] ++ finalize .d ++ finalize .a ++ finalize .b

/-- Final counterexample state obtained by executing the complete schedule. -/
def result (updateZero : Bool) : State := (run initial (trace updateZero)).getD initial

/-- Business balance after subtracting all final payment amounts. -/
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

/-- Balances reachable by legal funded business steps from thirty rights. -/
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
