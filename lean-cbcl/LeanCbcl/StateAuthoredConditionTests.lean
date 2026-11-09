import LeanCbcl.StateAuthoredConditionOutputs
import LeanCbcl.StateAuthoredBindingsTests

/-! Full authored condition regressions start at original Entry syntax and
successful preparation; no source plan or read policy is supplied by tests. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace CBCL.StateAuthoredConditionTests
open State StateLift StateLVar StateObservation StateObservationPlan
open StateInstalledLegacy StateAuthoredBindings StateOutputCompiler

/-- A count and an existence source precede a Boolean conjunction. -/
def entries : List Entry := [
  .field "votes" (.legacy (.count "vote")),
  .field "observed" (.legacy (.existsRule "vote")),
  .condition "ready" (.all [.read "votes" (.element (.count 2)),
    .read "observed" (.element (.scalar (.bool true)))])]

/-- Closed source policies are obtained from the installed actual fields. -/
theorem installs (context : StateKernelSEC.Context) :
    (prepareStatic (StateAuthoredBindingsTests.environment context) entries).isSome = true := by rfl

/-- A complete emitted vector includes the condition in authored order. -/
theorem condition_emitted (context : StateKernelSEC.Context) :
    (StateAuthoredConditionOutputs.compileAuthored (StateAuthoredBindingsTests.environment context) entries []).map
      (fun compiled => compiled.program.outputs.length) = some 3 := by
  dsimp [StateAuthoredConditionOutputs.compileAuthored]
  rfl

/-- A source after the original condition is unavailable even if globally known. -/
theorem later_source_rejected (context : StateKernelSEC.Context) :
    prepareStatic (StateAuthoredBindingsTests.environment context)
      [.condition "ready" (.read "votes" (.element (.count 1))),
       .field "votes" (.legacy (.count "vote"))] = none := by rfl

/-- Full assembly preserves original field and condition output order. -/
theorem output_order (context : StateKernelSEC.Context) :
    (StateAuthoredConditionOutputs.compileAuthored (StateAuthoredBindingsTests.environment context) entries []).map
      (fun compiled => compiled.program.outputs.map (fun output => match output with
        | .field name _ | .threshold name _ _ _ | .condition name _ _ => name)) =
      some ["votes","observed","ready"] := by
  dsimp [StateAuthoredConditionOutputs.compileAuthored]
  rfl

/-- Native Boolean condition success is a fixed literal, not a source callback. -/
theorem fixed_true_literal (context : StateKernelSEC.Context) :
    (StateAuthoredConditionOutputs.compileAuthored (StateAuthoredBindingsTests.environment context) entries []).map
      (fun compiled => compiled.program.outputs.filterMap (fun output => match output with
        | .condition _ truth _ => some truth | _ => none)) =
      some [.element (.scalar (.bool true))] := by
  dsimp [StateAuthoredConditionOutputs.compileAuthored]
  rfl

/-- Conditions are not sources for other conditions. -/
theorem condition_output_source_rejected (context : StateKernelSEC.Context) :
    prepareStatic (StateAuthoredBindingsTests.environment context)
      [.field "votes" (.legacy (.count "vote")),
       .condition "first" (.read "votes" (.element (.count 1))),
       .condition "second" (.read "first" (.element (.count 1)))] = none := by rfl

/-- A later freeze declaration cannot bypass source stability validation. -/
theorem later_supersede_rejected (context : StateKernelSEC.Context) :
    prepareStatic (StateAuthoredBindingsTests.environment context)
      [.field "votes" (.legacy (.count "vote")),
       .condition "ready" (.read "votes" (.element (.count 1))),
       .freeze "votes" "close" false] = none := by rfl

/-- A condition cannot itself become a freeze target. -/
theorem condition_freeze_rejected (context : StateKernelSEC.Context) :
    prepareStatic (StateAuthoredBindingsTests.environment context)
      [.field "votes" (.legacy (.count "vote")),
       .condition "ready" (.read "votes" (.element (.count 1))),
       .freeze "ready" "close" true] = none := by rfl

/-- Unary conjunctions reject through real authored preparation. -/
theorem unary_rejected (context : StateKernelSEC.Context) :
    prepareStatic (StateAuthoredBindingsTests.environment context)
      [.field "votes" (.legacy (.count "vote")),
       .condition "ready" (.all [.read "votes" (.element (.count 1))])] = none := by rfl

/-- Compatible fixed bounds remain valid separate conjuncts. -/
theorem compatible_bounds_install (context : StateKernelSEC.Context) :
    (prepareStatic (StateAuthoredBindingsTests.environment context)
      [.field "votes" (.legacy (.count "vote")),
       .condition "ready" (.all [.read "votes" (.element (.count 1)),
         .read "votes" (.element (.count 2))])]).isSome = true := by rfl

/-- Authored scalar limits also constrain singleton condition reads. -/
theorem oversized_bound_rejected (context : StateKernelSEC.Context) :
    prepareStatic (StateAuthoredBindingsTests.environment context)
      [.field "votes" (.legacy (.count "vote")),
       .condition "ready" (.read "votes" (.element (.count 1000001)))] = none := by rfl

end CBCL.StateAuthoredConditionTests
