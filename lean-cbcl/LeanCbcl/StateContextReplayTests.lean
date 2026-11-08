import LeanCbcl.StateContextReplay

/-! Opener witnesses require causal root context. Arbitrary list restriction
is not a valid substitute for closed accepted histories. -/
set_option autoImplicit false
namespace CBCL.StateContextReplayTests
open State StateLift StateLVar StateObservation StateContextEvidence StateWitnessReplay

/-- Context decoding is irrelevant to this isolated opener-guard test. -/
def input : Input := ⟨fun _ => none,fun _ => none,some "open"⟩

/-- A predecessor-free context root. -/
def root : Act := ⟨0,"root","@a",[],[],[]⟩

/-- One opener branch cites the root. -/
def first : Act := ⟨1,"open","@a",[0],[],[]⟩

/-- A distinct opener branch independently cites the same root. -/
def second : Act := ⟨2,"open","@b",[0],[],[]⟩

/-- Both opener identities are reported once the root context is present. -/
theorem opener_fault : (openerSpec input).read [root,first,second] = some ({1} ∪ {2}) := by
  rfl

/-- Removing the root suppresses this guard despite retaining both openers. -/
theorem rootless_receiver_pending : (openerSpec input).read [first,second] = none := by
  rfl

/-- The reported opener acts alone are indeed present in that receiver. -/
theorem rootless_receiver_accepts_witness : Accepts [root,first,second] ({1} ∪ {2}) [first,second] := by
  intro act member named
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with equal | equal | equal
  · subst act
    simp [root] at named
  · subst act
    simp
  · subst act
    simp

/-- The rootless receiver violates exactly the causal-closure premise. -/
theorem rootless_receiver_not_closed : ¬CausallyClosed
    (fun act => act ∈ [root,first,second]) [first,second] := by
  intro closed
  have present := closed first (by simp) root (by simp) (by simp [first,root])
  simp [root,first,second] at present

end CBCL.StateContextReplayTests
