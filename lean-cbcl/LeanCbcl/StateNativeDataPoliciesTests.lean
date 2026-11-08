import LeanCbcl.StateNativeDataFreeze
import LeanCbcl.StateAuthoredSourceProvenanceTests
import LeanCbcl.StateDomainSupportLocalityTests

/-! Native kernel/query bridges use mixed initializer/roster domains and
reverse/duplicate delivery. Factory-level frozen output composition is explicit. -/
namespace CBCL.StateNativeDataPoliciesTests
open State StateLift StateLVar StateObservation StateObservationPlan StateInstalledCompiler
open StateInstalledLegacy StateDomainSupportLocalityTests StateDomainSupportLocality

/-- Actual count evaluation sees one distinct eligible act despite duplicate deliveries. -/
theorem duplicate_count (context : StateKernelSEC.Context) :
    StateInstalledDomains.evaluate context domains (.count (.verb "mark")) (rawHistory history) = .integer 1 := by
  rw [StateNativeDataPolicies.count_value]
  rfl

/-- The same mixed domain selection enables existence. -/
theorem duplicate_exists (context : StateKernelSEC.Context) :
    StateInstalledDomains.evaluate context domains (.existsRule (.verb "mark")) (rawHistory history) = .boolean true := by
  rw [StateNativeDataPolicies.exists_value]
  rfl

/-- The actual count query compiles and reaches from raw state even if the
completed source payload is pending. -/
theorem count_pending_payload (context : StateKernelSEC.Context) : ∃ code,
    StateOutputCompiler.compileQuery [.element (.count 1)]
      (StateAuthoredBindings.primitive (StateAuthoredSourceProvenanceTests.environment context) domains
        (.count (.verb "mark")) (.count "mark")) = some code ∧
      code.run history (.data .pending) = .data (.reached (.element (.count 1))) := by
  obtain ⟨code,compiled,run⟩ := StateNativeDataPolicies.compiled_count
    (StateAuthoredSourceProvenanceTests.environment context) domains "mark" 1 (by decide)
  refine ⟨code,compiled,?_⟩
  rw [run]
  rfl

/-- The existence query similarly uses selected raw state. -/
theorem exists_pending_payload (context : StateKernelSEC.Context) : ∃ code,
    StateOutputCompiler.compileQuery [.element (.scalar (.bool true))]
      (StateAuthoredBindings.primitive (StateAuthoredSourceProvenanceTests.environment context) domains
        (.existsRule (.verb "mark")) (.existsRule "mark")) = some code ∧
      code.run history (.data .pending) = .data (.reached (.element (.scalar (.bool true)))) := by
  obtain ⟨code,compiled,run⟩ := StateNativeDataPolicies.compiled_exists
    (StateAuthoredSourceProvenanceTests.environment context) domains "mark"
  refine ⟨code,compiled,?_⟩
  rw [run]
  rfl

/-- The actual source policy rejects a count bound outside native integer range. -/
theorem oversized_count_rejected (context : StateKernelSEC.Context) :
    StateOutputCompiler.compileQuery [.element (.count (2^63))]
      (StateAuthoredBindings.primitive (StateAuthoredSourceProvenanceTests.environment context) domains
        (.count (.verb "mark")) (.count "mark")) = none := by rfl

/-- Actual guarded native count source plan used by the output adapter. -/
noncomputable def countSource (context : StateKernelSEC.Context) : Plan Value := sourcePlan (StateInstalledTerm.source
  (StateInstalledDomains.term context domains (.count (.verb "mark"))
    (StateAuthoredBindings.resourceVerbs (StateAuthoredSourceProvenanceTests.environment context))))

/-- A supported growth trace constructs the actual factory-level frozen output
success-or-fault result, without a chosen-root or healthy-source premise. -/
theorem count_freeze_constructed (context : StateKernelSEC.Context) : ∃ code,
    StateOutputCompiler.compileQuery [.element (.count 1)]
      (StateAuthoredBindings.primitive (StateAuthoredSourceProvenanceTests.environment context) domains
        (.count (.verb "mark")) (.count "mark")) = some code ∧
      let output := (StateOutputCompiler.Output.threshold "enough" "count" code
        (StateNativeDataFreeze.decorate domains ["mark"] (StateScopePool.normalize history) (some "close") (countSource context))).observe history
          (StateNativeDataFreeze.metadata domains ["mark"] (StateScopePool.normalize history) "count" (some "close"))
      output = ("enough",.data (.reached (.element (.count 1)))) ∨ ∃ evidence, output = ("enough",.fault evidence) := by
  apply StateNativeDataFreeze.count_success_or_fault (StateAuthoredSourceProvenanceTests.environment context) domains "mark" 1
    (by decide) [root,opener,writer] history
    (by intro act member; simp only [List.mem_cons,List.not_mem_nil,or_false] at member; rcases member with rfl | rfl | rfl <;> simp [StateDomainSupportLocalityTests.history])
    (by decide) "count" "enough" (some "close")
  exact StateCausalRank.causalCheck_sound _ (by decide)

end CBCL.StateNativeDataPoliciesTests
