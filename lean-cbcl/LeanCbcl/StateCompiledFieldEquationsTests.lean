import LeanCbcl.StateCompiledFieldEquations
import LeanCbcl.StateAuthoredBindingsTests

/-! Exact compiler structure and non-freezing recursive-reference witnesses. -/
namespace CBCL.StateCompiledFieldEquationsTests
open State StateLift StateObservation StateObservationPlan StateInstalledCompiler StateCompiledFieldEquations

/-- A derived field observes a source whose freeze is attached clause-wide. -/
def frozenSource : StateInstalledClause.Clause Nat := {
  fields := [("source",.source (.snapshot (fun _ => 2))),("derived",.derived (fun n => n+1) "source")]
  freezes := [("source",⟨"close",fun _ => True,false⟩)] }

/-- The compiled dependency retains the source's supersede freeze, rather than
binding the derived field to an undecorated or fault-policy source. -/
theorem derived_keeps_frozen_source : (match StateInstalledClause.compile frozenSource with
  | some plans => match plans.lookup "derived" with
      | some (.map _ (.freeze spec _)) => spec.verb == "close" && !spec.policy
      | _ => false
  | none => false) = true := by decide

/-- A concrete threshold-bearing non-freezing authored clause. -/
def counted : List StateAuthoredBindings.Entry := [
  .field "votes" (.legacy (.count "vote")),
  .threshold "enough" "votes" [.element (.count 3)]]

/-- The no-freeze recursive theorem has an actually admitted concrete clause. -/
theorem counted_prepares (context : StateKernelSEC.Context) (whole : List Act) :
    (StateAuthoredBindings.prepare (StateAuthoredBindingsTests.environment context) counted whole).isSome = true := rfl

/-- No-freeze metadata is constructed, rather than assumed for the witness. -/
theorem counted_freezes (context : StateKernelSEC.Context) (whole : List Act) :
    (StateAuthoredBindings.prepare (StateAuthoredBindingsTests.environment context) counted whole).map
      StateInstalledLowering.Clause.freezes = some [] := rfl

end CBCL.StateCompiledFieldEquationsTests
