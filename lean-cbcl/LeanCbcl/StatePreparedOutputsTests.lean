import LeanCbcl.StatePreparedOutputs
import LeanCbcl.StateFrozenBodyEquationsTests

/-! Non-vacuous authored context/count/threshold/freeze output composition. -/
namespace CBCL.StatePreparedOutputsTests
open State StateInstalledCompiler StateInstalledLowering StateReaderReachability
open StateFrozenBodyEquationsTests

/-- A concrete authored clause constructs an actual cache transcript and
successful output list, rather than assuming either installation or outputs. -/
theorem concrete_cache_outputs (context : StateKernelSEC.Context) :
    ∃ clause plans fields,
      StateAuthoredBindings.prepare (StateAuthoredBindingsTests.environment context)
        StateAuthoredBindingsTests.review StateFrozenBodyEquationsTests.acts = some clause ∧
      StateAuthoredBindings.compile (StateAuthoredBindingsTests.environment context)
        StateAuthoredBindingsTests.review StateFrozenBodyEquationsTests.acts = some plans ∧
      resolve [] clause.declarations = some fields ∧
      let ops := StateReaderValues.operations StateAuthoredBindingsTests.review StateFrozenBodyEquationsTests.acts fields clause.freezes
      let rank := StateMemoizedReader.requestRank (fields.map Prod.fst).idxOf ops.cut
      ∃ values after outputs,
        StateMemoizedReader.reads ops.body rank (initialKeys StateAuthoredBindingsTests.review) [] = some (values,after) ∧
        StatePreparedOutputs.evaluateValues
          (StateThresholdDispatch.rawScope StateAuthoredBindingsTests.review StateFrozenBodyEquationsTests.acts fields clause.freezes)
          [] clause.declarations values = some outputs := by
  have ranked : StateExecutableFreeze.Ranked StateFrozenBodyEquationsTests.acts := StateExecutableFreeze.rankedCheck_sound StateFrozenBodyEquationsTests.acts (by decide)
  have unique : NodupAddr StateFrozenBodyEquationsTests.acts := by unfold NodupAddr StateFrozenBodyEquationsTests.acts; decide
  have consistent : ∀ a ∈ StateFrozenBodyEquationsTests.acts, ∀ b ∈ StateFrozenBodyEquationsTests.acts, a.addr = b.addr → a = b := by
    intro a memberA b memberB same
    exact unique.eq_of_addr memberA memberB same
  cases prepared : StateAuthoredBindings.prepare (StateAuthoredBindingsTests.environment context)
      StateAuthoredBindingsTests.review StateFrozenBodyEquationsTests.acts with
  | none =>
    have exists_ := StateAuthoredBindingsTests.review_prepares context StateFrozenBodyEquationsTests.acts
    simp [prepared] at exists_
  | some clause =>
    obtain ⟨plans,fields,compiled,resolved,values,after,outputs,ran,adapted,_⟩ :=
      StatePreparedOutputs.prepared_cache_outputs (StateAuthoredBindingsTests.environment context)
        StateAuthoredBindingsTests.review StateFrozenBodyEquationsTests.acts clause prepared ranked consistent
    exact ⟨clause,plans,fields,rfl,compiled,resolved,values,after,outputs,ran,adapted⟩

end CBCL.StatePreparedOutputsTests
