import LeanCbcl.ConsensusFree.MultiParent
import Lean

/-! SPEC-030 shared oracle. API retries stutter; unreserved release is outside the
Rust API. Every accepted adapter command still generates an abstract Step. -/
namespace CBCL.ConsensusFree.MultiParent.RustOracle
open CBCL.ValidatorBudget Lean
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def graph : Graph 8 where
  lower v := if h : v.val = 1 ∨ v.val = 2 ∨ v.val = 7 then [⟨0,by omega⟩]
    else if h : v.val = 3 ∨ v.val = 5 ∨ v.val = 6 ∨ v.val = 8 then [⟨1,by omega⟩,⟨2,by omega⟩]
    else if h : v.val = 4 then [⟨3,by omega⟩]
    else []
def committee : Committee 1 where
  core := [0,1,2]
  others := [3]
  distinct := by decide
  core_size := by decide
  other_size := by decide

def amount (tx : Fin 7) : Nat := [30,30,20,10,30,20,70][tx.val]!
def mint (tx : Fin 7) : Bool := tx.val = 3
def config : Config 8 7 2 1 where
  graph := graph
  committee := committee
  initial := fun _ => 100
  manifest v := {
    held := fun tx => ((v.val = 3 || v.val = 5 || v.val = 8) && tx.val ≤ 1) ||
      (v.val = 4 && tx.val ≤ 2) || (v.val = 7 && tx.val = 3)
    refunded := fun tx => v.val = 4 && tx.val = 1
    credited := fun tx => (v.val = 4 && (tx.val = 0 || tx.val = 2)) || (v.val = 7 && tx.val = 3)
    allocation := fun d => if d.val = 0 then
      (if v.val = 3 || v.val = 8 then 40 else if v.val = 4 then 50 else if v.val = 5 then 41 else if v.val = 7 then 110 else 100)
      else (if v.val = 4 then 150 else if v.val = 7 then 90 else 100)
    authorized := true }
  opVersion tx := if tx.val = 0 then 1 else if tx.val = 1 then 2 else
    if tx.val = 2 || tx.val = 5 then 3 else if tx.val = 4 then 8 else 0
  cost tx d := if (mint tx && d.val = 1) || (!mint tx && d.val = 0) then amount tx else 0
  credit tx d := if (mint tx && d.val = 0) || (!mint tx && d.val = 1) then amount tx else 0
  authorized := fun _ => true
  cancelAuthorized := fun _ => true
  disjoint := by
    intro tx d
    have h := d.isLt
    by_cases hm : mint tx = true <;> have hd : d.val = 0 ∨ d.val = 1 := by omega
    all_goals rcases hd with hd | hd <;> simp_all

/-- Rust admits a candidate only after verifying its source metadata. The numeric
catalogue has no candidate-registration state, so this is an explicit adapter
precondition rather than a change to the proved abstract protocol. -/
def available (s : State 8 7) : Command 8 7 → Bool
  | .sign tx w | .effect tx w | .fence tx w | .release tx w =>
      if w ∈ config.committee.core then s.known (config.opVersion tx) else true
  | .record v => decide (∀ tx, (held config v tx = true ∨ credited config v tx = true) →
      s.known (config.opVersion tx) = true)
  | _ => true

def apiPerform (s : State 8 7) (cmd : Command 8 7) : Option (State 8 7) :=
  if available s cmd then
    match cmd with
    | .sign tx w => if s.signatures tx w then some s else perform config s cmd
    | .adopt v w => if s.active w = v then some s else perform config s cmd
    | .release tx w => if s.signatures tx w then perform config s cmd else none
    | _ => perform config s cmd
  else none

theorem apiPerform_sound {s t cmd} (h : apiPerform s cmd = some t) : Step config s t := by
  unfold apiPerform at h
  split at h
  · cases cmd <;> dsimp only at h
    all_goals first
      | (split at h <;> first | (cases h; exact .replay _) | exact perform_sound h | contradiction)
      | exact perform_sound h
  · contradiction

def nat (n : Nat) : Json := toJson n
def ids (n : Nat) (p : Fin n → Bool) : Json := toJson ((List.finRange n).filter p |>.map Fin.val)
def cmd (kind : String) (id w : Nat) : Json := toJson [toJson kind,nat id,nat w]
def command : Command 8 7 → Json
  | .sign tx w => cmd "sign" tx.val w
  | .effect tx w => cmd "effect" tx.val w
  | .fence tx w => cmd "fence" tx.val w
  | .release tx w => cmd "release" tx.val w
  | .record v => cmd "record" v.val 0
  | .adopt v w => cmd "adopt" v.val w
  | .replay => cmd "replay" 0 0

def snapshot (s : State 8 7) : Json := Json.mkObj [
  ("nodes",toJson ((List.range 3).map fun w => Json.mkObj [
    ("active",nat (s.active w).val),("visited",ids 9 (s.visited w)),("known",ids 9 s.known),
    ("signed",ids 7 (fun tx => s.signatures tx w)),("released",ids 7 (fun tx => s.released tx w)),
    ("effects",ids 7 (fun tx => s.effects tx w)),("fences",ids 7 (fun tx => s.fences tx w))])),
  ("operation",ids 7 (operationCert config s)),("final",ids 7 (finalCert config s)),
  ("cancel",ids 7 (cancelCert config s)),("balance",toJson [balance config s 0,balance config s 1])]

def catalogue : Json := Json.mkObj [
  ("initial",toJson [100,100]),("amount",toJson ((List.finRange 7).map amount)),
  ("mint",toJson ((List.finRange 7).map mint)),
  ("opVersion",toJson ((List.finRange 7).map (fun tx => (config.opVersion tx).val))),
  ("versions",toJson ((List.finRange 8).map fun i =>
    let v : Version 8 := i.succ
    let m := config.manifest v
    Json.mkObj [("id",nat v.val),("rank",nat v.val),("parents",toJson (graph.parents v |>.map Fin.val)),
      ("held",ids 7 m.held),("refunded",ids 7 m.refunded),("credited",ids 7 m.credited),
      ("allocation",toJson [m.allocation 0,m.allocation 1])]))]

def split : List (Command 8 7) := [.record 1,.record 2,.adopt 1 0,.adopt 1 1,.adopt 2 2]
def partials : List (Command 8 7) := [.sign 0 0,.sign 0 1,.sign 1 2,.sign 1 3]
def merge : List (Command 8 7) := [.record 3,.adopt 3 0,.adopt 3 1,.adopt 3 2]
def spend : List (Command 8 7) := [.sign 2 0,.sign 2 1,.sign 2 2,.effect 2 0,.effect 2 1,.effect 2 2]
def late : List (Command 8 7) := [.sign 0 3,.effect 0 0,.effect 0 1,.effect 0 3]
def cancel : List (Command 8 7) := [.fence 1 0,.fence 1 1,.fence 1 2,.release 1 2]
def scenarios : List (String × List (Command 8 7)) := [
  ("join-late-refund",split ++ partials ++ [.adopt 2 0,.record 5,.record 6,.adopt 6 0] ++ merge ++ spend ++ late ++
    [.record 4] ++ cancel ++ [.adopt 6 2,.record 4,.adopt 4 0,.adopt 4 1,.adopt 4 2,.adopt 3 0,.sign 0 0,.release 1 2]),
  ("capacity",split ++ partials ++ [.record 8,.adopt 8 0,.adopt 8 1,.adopt 8 2,.sign 4 0,.effect 4 0,.release 0 0]),
  ("credit",[.record 7,.sign 3 0,.sign 3 1,.sign 3 2,.effect 3 0,.effect 3 1,.effect 3 2,.record 7,
    .adopt 7 0,.adopt 7 1,.adopt 7 2,.sign 3 0,.fence 3 0]),
  ("root-budget",[.sign 6 0,.effect 6 0,.fence 6 0,.fence 6 1,.fence 6 2,.sign 6 0]),
  ("guard-sweep",split ++ partials ++ merge ++ (List.range 180).map fun n =>
    let tx : Fin 7 := ⟨(n*5+1)%7,by omega⟩
    let w := (n/7)%3
    match n%6 with
    | 0 => .sign tx w
    | 1 => .effect tx w
    | 2 => .fence tx w
    | 3 => .release tx w
    | 4 => .adopt ⟨(n%8)+1,by omega⟩ w
    | _ => .record ⟨(n%8)+1,by omega⟩)]

def steps (s : State 8 7) : List (Command 8 7) → List Json
  | [] => []
  | cmd :: rest =>
    let result := apiPerform s cmd
    let next := result.getD s
    Json.mkObj [("command",command cmd),("accepted",toJson result.isSome),("state",snapshot next)] :: steps next rest

def output : Json := Json.mkObj [("schema",nat 1),("catalogue",catalogue),
  ("traces",toJson (scenarios.map fun (name,cmds) => Json.mkObj [("name",toJson name),("steps",toJson (steps initial cmds))]))]
theorem advance_step (s : State 8 7) (cmd : Command 8 7) :
    Step config s ((apiPerform s cmd).getD s) := by
  cases h : apiPerform s cmd with
  | none => exact .replay _
  | some t => exact apiPerform_sound h

theorem run_trans {a b c : State 8 7} (ab : Run config a b) (bc : Run config b c) : Run config a c := by
  induction bc with
  | refl => exact ab
  | next _ st ih => exact .next ih st

theorem oracle_run (s : State 8 7) (cmds : List (Command 8 7)) :
    Run config s (cmds.foldl (fun s cmd => (apiPerform s cmd).getD s) s) := by
  induction cmds generalizing s with
  | nil => exact .refl _
  | cons cmd rest ih =>
    have tail := ih ((apiPerform s cmd).getD s)
    have head := advance_step s cmd
    exact run_trans (.next (.refl _) head) tail

theorem oracle_safe (cmds : List (Command 8 7)) (d : Fin 2) :
    0 ≤ balance config (cmds.foldl (fun s cmd => (apiPerform s cmd).getD s) initial) d :=
  resource_nonnegative (run_invariant (initial_invariant config) (oracle_run initial cmds)) d

#print axioms apiPerform_sound
#print axioms oracle_safe
end CBCL.ConsensusFree.MultiParent.RustOracle

def main : IO Unit := IO.println CBCL.ConsensusFree.MultiParent.RustOracle.output.compress
