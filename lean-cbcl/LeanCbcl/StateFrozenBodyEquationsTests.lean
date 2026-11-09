import LeanCbcl.StateFrozenBodyEquations
import LeanCbcl.StateAuthoredBindingsTests

/-! Concrete indexed-cut metadata and non-vacuous complete cache witnesses. -/
namespace CBCL.StateFrozenBodyEquationsTests
open State StateLift StateObservation StateObservationPlan StateInstalledCompiler StateReaderReachability

/-- Incomparable close/seal cuts share their root and retain different branches. -/
def acts : List Act := [⟨0,"open","@a",[],[],[]⟩,⟨1,"close","@a",[0],[],[]⟩,
  ⟨2,"mark","@b",[0],[],[]⟩,⟨3,"seal","@a",[2],[],[]⟩]

/-- Independent freezes exercise both active and absent-in-this-scope paths. -/
def freezes : List (String × FreezeSpec) :=
  [("source",⟨"close",fun _ => True,false⟩),("derived",⟨"seal",fun _ => True,false⟩)]

/-- Scope callbacks alone are executable even when value leaves are symbolic. -/
noncomputable def metadata : StateMemoizedReader.Operations (StateReaderValues.Result Nat) :=
  StateReaderValues.operations [] acts [] freezes

/-- The source freezer is absent from the incomparable derived cut. -/
theorem incomparable_active_witness :
    (metadata.active (0,"source") && metadata.active (1,"source") && !metadata.active (2,"source")) = true := by decide

/-- Distinct field roots resolve to their exact allocated cuts. -/
theorem allocated_cuts_witness :
    ((StateReaderValues.scope acts freezes (1,"source")).map Act.addr == [0,1] &&
      (StateReaderValues.scope acts freezes (2,"derived")).map Act.addr == [0,2,3]) = true := by decide

/-- A real context/count/threshold/freeze clause constructs a complete compiled
cache transcript, rather than assuming the final body equation or installation. -/
theorem concrete_cache_transcript (context : StateKernelSEC.Context) :
    ∃ clause, StateAuthoredBindings.prepare (StateAuthoredBindingsTests.environment context)
        StateAuthoredBindingsTests.review acts = some clause ∧
      ∃ plans fields, StateAuthoredBindings.compile (StateAuthoredBindingsTests.environment context)
          StateAuthoredBindingsTests.review acts = some plans ∧
        StateInstalledLowering.resolve [] clause.declarations = some fields ∧
        let ops := StateReaderValues.operations StateAuthoredBindingsTests.review acts fields clause.freezes
        let rank := StateMemoizedReader.requestRank (fields.map Prod.fst).idxOf ops.cut
        ∃ after, StateMemoizedReader.reads ops.body rank (initialKeys StateAuthoredBindingsTests.review) [] =
          some ((initialKeys StateAuthoredBindingsTests.review).map
            (StateCompiledFieldEquations.meaning acts clause.freezes plans),after) := by
  have ranked : StateExecutableFreeze.Ranked acts := StateExecutableFreeze.rankedCheck_sound acts (by decide)
  have unique : NodupAddr acts := by unfold NodupAddr acts; decide
  have consistent : ∀ a ∈ acts, ∀ b ∈ acts, a.addr = b.addr → a = b := by
    intro a memberA b memberB same
    exact unique.eq_of_addr memberA memberB same
  cases prepared : StateAuthoredBindings.prepare (StateAuthoredBindingsTests.environment context) StateAuthoredBindingsTests.review acts with
  | none => have exists_ := StateAuthoredBindingsTests.review_prepares context acts; simp [prepared] at exists_
  | some clause =>
    obtain ⟨plans,fields,compiled,resolved,after,ran,_,_⟩ := StateFrozenBodyEquations.prepared_cache_equivalence
      (StateAuthoredBindingsTests.environment context) StateAuthoredBindingsTests.review acts clause prepared ranked consistent
    exact ⟨clause,rfl,plans,fields,compiled,resolved,after,ran⟩

end CBCL.StateFrozenBodyEquationsTests
