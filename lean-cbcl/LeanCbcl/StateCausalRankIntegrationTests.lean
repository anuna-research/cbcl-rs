import LeanCbcl.StateOutputCompiler
import LeanCbcl.StateCausalRank
import LeanCbcl.StateFrozenBodyEquationsTests

/-! Non-vacuous authored context/count/threshold/freeze output composition. -/
namespace CBCL.StateCausalRankIntegrationTests
open State StateInstalledCompiler StateInstalledLowering StateReaderReachability
open StateFrozenBodyEquationsTests

/-- Reverse delivery and duplicate payloads preserve descending semantic addresses. -/
def history : List Act := StateCausalRank.descending.reverse ++ StateCausalRank.descending.reverse

/-- A concrete authored clause constructs an actual cache transcript and
successful output list, rather than assuming either installation or outputs. -/
theorem descending_duplicate_compiled_outputs (context : StateKernelSEC.Context) :
    ∃ clause program fields,
      StateAuthoredBindings.prepare (StateAuthoredBindingsTests.environment context)
        StateAuthoredBindingsTests.review history = some clause ∧
      StateOutputCompiler.compileAuthored (StateAuthoredBindingsTests.environment context)
        StateAuthoredBindingsTests.review history = some program ∧
      resolve [] clause.declarations = some fields ∧
      let ops := StateReaderValues.operations StateAuthoredBindingsTests.review history fields clause.freezes
      let rank := StateMemoizedReader.requestRank (fields.map Prod.fst).idxOf ops.cut
      ∃ values after,
        StateMemoizedReader.reads ops.body rank (initialKeys StateAuthoredBindingsTests.review) [] = some (values,after) ∧
        StatePreparedOutputs.evaluateValues
          (StateThresholdDispatch.rawScope StateAuthoredBindingsTests.review history fields clause.freezes)
          [] clause.declarations values = some (program.observe) := by
  have ranked : StateExecutableFreeze.Ranked history := StateCausalRank.causalCheck_sound history (by decide)
  have unique : NodupAddr StateCausalRank.descending := by
    unfold NodupAddr StateCausalRank.descending
    decide
  have inside : ∀ act ∈ history, act ∈ StateCausalRank.descending := by
    intro act member
    simpa [history] using member
  have consistent : ∀ a ∈ history, ∀ b ∈ history, a.addr = b.addr → a = b := by
    intro a memberA b memberB same
    exact unique.eq_of_addr (inside a memberA) (inside b memberB) same
  cases prepared : StateAuthoredBindings.prepare (StateAuthoredBindingsTests.environment context)
      StateAuthoredBindingsTests.review history with
  | none =>
    have exists_ := StateAuthoredBindingsTests.review_prepares context history
    simp [prepared] at exists_
  | some clause =>
    obtain ⟨program,fields,compiled,resolved,values,after,ran,adapted⟩ :=
      StateOutputCompiler.authored_compiler_refinement (StateAuthoredBindingsTests.environment context)
        StateAuthoredBindingsTests.review history clause prepared ranked consistent
    exact ⟨clause,program,fields,rfl,compiled,resolved,values,after,ran,adapted⟩

end CBCL.StateCausalRankIntegrationTests
