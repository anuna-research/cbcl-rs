import LeanCbcl.StateWitnessReplay
/-! A supported, monotone guard need not have a sufficient replay witness. -/
namespace CBCL.StateWitnessReplayTests
open State StateObservation StateWitnessReplay
/-- A trigger omitted from the reported conflict evidence. -/
def trigger : Act := ⟨7,"write","@a",[],[],[]⟩
/-- Growth and support admit a guard with insufficient empty evidence. -/
noncomputable def guard : ErrorSpec := by
  classical
  exact {
   read := fun A => if trigger ∈ A then some ∅ else none
   equiv := by intro A B same; simp only [(same trigger)]
   grow := by
    intro A B growth e fault
    split at fault
    · rename_i present
      have equal := Option.some.inj fault
      subst e
      exact ⟨∅,by simp [growth trigger present],fun _ member => member⟩
    · contradiction
   support := by
    intro A e fault
    split at fault
    · have equal := Option.some.inj fault
      subst e
      intro id member
      contradiction
    · contradiction }
/-- The trigger faults despite the reported certificate being empty. -/
theorem support_does_not_imply_replay :
     guard.read [trigger] = some ∅ ∧ guard.read [] = none := by
  classical
  simp [guard]
/-- Requiring replay excludes the trigger guard even though support holds. -/
theorem trigger_guard_not_replayable : ¬ Replays guard.read [trigger] [] := by
  intro replay
  have fault := support_does_not_imply_replay.1
  have accepted : Accepts [trigger] ∅ [] := by
    intro act member evidence
    exact False.elim evidence
  obtain ⟨enlarged,current,_⟩ := replay ∅ fault accepted
  rw [support_does_not_imply_replay.2] at current
  contradiction

/-- An accepted act outside the fault certificate is irrelevant to replay. -/
def unrelated : Act := ⟨8,"tell","@b",[],[],[]⟩

/-- Replay premises transfer the named act without quietly requiring the full
source history. This also distinguishes exact act receipt from address aliases. -/
theorem accepts_only_named_act : Accepts [trigger,unrelated] {trigger.addr} [trigger] := by
  intro act member named
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with equal | equal
  · subst act
    simp
  · subst act
    simp [trigger,unrelated] at named

end CBCL.StateWitnessReplayTests
