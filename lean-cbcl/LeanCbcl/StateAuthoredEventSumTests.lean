import LeanCbcl.StateAuthoredEventSum
import LeanCbcl.StateAuthoredSourceProvenanceTests

/-! Sum installation and raw query fixtures. Typed nonnegative writer evidence
is computed separately from the installation's shape-policy metadata. -/
namespace CBCL.StateAuthoredEventSumTests
open State StateLift StateLVar StateObservation StateObservationPlan StateInstalledCompiler
open StateInstalledLegacy StateInstalledLowering StateAuthoredBindings StateOutputCompiler

/-- Recognized mandatory nonnegative shape metadata for the event writer. -/
def environment (context : StateKernelSEC.Context) : Environment :=
  { StateAuthoredSourceProvenanceTests.environment context with
    shapes := [⟨"mint","amount",true,true⟩]
    schema := ⟨["mint","close"],[(("mint","amount"),.nonnegative)]⟩ }

/-- The real authored event source, sum query and optional freeze. -/
def entries (bound : Int) (fault : Bool) : List Entry := [
  .field "credits" (.legacy (.events "mint" "amount")),
  .threshold "funded" "credits" [.element (.sum bound)],
  .freeze "credits" "close" fault]

/-- Actual preparation admits the bounded shaped sum. -/
theorem installation_succeeds (context : StateKernelSEC.Context) :
    (prepareStatic (environment context) (entries 5 true)).isSome = true := by rfl

/-- Missing shape metadata cannot admit a stable sum. -/
theorem unshaped_rejected (context : StateKernelSEC.Context) :
    prepareStatic (StateAuthoredSourceProvenanceTests.environment context) (entries 5 true) = none := by rfl

/-- The upper signed bound is excluded by the actual query policy. -/
theorem upper_bound_rejected (context : StateKernelSEC.Context) :
    prepareStatic (environment context) (entries (2^63) true) = none := by rfl

/-- Supersede freeze remains revisable and cannot supply a stable sum. -/
theorem supersede_rejected (context : StateKernelSEC.Context) :
    prepareStatic (environment context) (entries 5 false) = none := by rfl

/-- An explicit typed writer, independent of any protocol-admission assertion. -/
def writer : Act := ⟨1,"mint","@a",[],[("amount",.int 5)],[]⟩

/-- The fixture constructs its per-writer numeric premise. -/
theorem writer_nonnegative : ∀ act ∈ [writer], act.verb = "mint" → 0 ≤ amount "amount" act := by
  intro act member _
  have same : act = writer := by simpa using member
  subst act
  decide

/-- Actual source-owned code reaches from a pending displayed payload. -/
theorem pending_payload_reaches (context : StateKernelSEC.Context) : ∃ code,
    compileQuery [.element (.sum 5)]
      (primitive (environment context) [] (.mapped (StateEventMapKernel.plan "mint" "amount")) (.events "mint" "amount")) = some code ∧
      code.run [writer] (.data .pending) = .data (.reached (.element (.sum 5))) := by
  obtain ⟨code,compiled,run⟩ := StateNativeEventSum.compiled_sum (environment context) [] "mint" "amount" 5
    (by decide) (by rfl)
  refine ⟨code,compiled,?_⟩
  have unique : NodupAddr [writer] := by change ([1] : List Nat).Nodup; decide
  rw [run [writer] unique]
  have success : 5 ≤ sumField "amount" (StateDomainSupportLocality.selected [] ["mint"] [writer]) := by decide
  simp only [success,if_true]

end CBCL.StateAuthoredEventSumTests
