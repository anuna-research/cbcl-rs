import LeanCbcl.StateAuthoredDataPreservation
import LeanCbcl.StateAuthoredSourceProvenanceTests
import LeanCbcl.StateAuthoredFiniteStabilityTests
import LeanCbcl.StateFiniteOutputStabilityTests

/-! Actual authored mixed-domain count/existence programs, with forward
initializer references and late freezes. Both code walks are constructed. -/
namespace CBCL.StateAuthoredDataPreservationTests
open State StateLift StateLVar StateObservation StateObservationPlan StateInstalledCompiler
open StateInstalledLegacy StateInstalledLowering StateAuthoredBindings StateOutputCompiler

/-- Two native sources and thresholds share a verb but retain different policies. -/
def entries (fault : Bool) : List Entry := [
  .domain ⟨"mark","target","options"⟩,
  .field "reviewers" (.context ["thread","roles","reviewer"]),
  .domain ⟨"mark","target","reviewers"⟩,
  .field "votes" (.legacy (.count "mark")),
  .threshold "quorum" "votes" [.element (.count 1)],
  .field "observed" (.legacy (.existsRule "mark")),
  .threshold "started" "observed" [.element (.scalar (.bool true))],
  .freeze "votes" "close" fault,
  .freeze "observed" "close" fault,
  .field "options" (.legacy (.initial "open" "options"))]

/-- Full authored installation computes source-owned policy admission. -/
theorem installation_succeeds (context : StateKernelSEC.Context) :
    (prepareStatic (StateAuthoredSourceProvenanceTests.environment context) (entries true)).isSome = true := by rfl

/-- Revisable sources do not install these stable thresholds. -/
theorem supersede_rejected (context : StateKernelSEC.Context) :
    prepareStatic (StateAuthoredSourceProvenanceTests.environment context) (entries false) = none := by rfl

/-- Both actual complete programs are constructed; preservation starts from
named members of the earlier compiled vector, not assumed native predicates. -/
theorem constructed_programs_preserve_both (context : StateKernelSEC.Context) :
    ∃ prepared earlier later,
      prepareStatic (StateAuthoredSourceProvenanceTests.environment context) (entries true) = some prepared ∧
      compileAuthored (StateAuthoredSourceProvenanceTests.environment context) (entries true)
        StateFiniteOutputStabilityTests.beforeClose = some earlier ∧
      compileAuthored (StateAuthoredSourceProvenanceTests.environment context) (entries true)
        StateAuthoredFiniteStabilityTests.history = some later ∧
      FinSet.card (FinSet.mk (StateDomainSupportLocality.selected prepared.domains ["mark"] StateFiniteOutputStabilityTests.beforeClose)) = 1 ∧
      (("quorum",.data (.reached (.element (.count 1)))) ∈ earlier.observe →
        ("quorum",.data (.reached (.element (.count 1)))) ∈ later.observe ∨ ∃ evidence, ("quorum",.fault evidence) ∈ later.observe) ∧
      (("started",.data (.reached (.element (.scalar (.bool true))))) ∈ earlier.observe →
        ("started",.data (.reached (.element (.scalar (.bool true))))) ∈ later.observe ∨ ∃ evidence, ("started",.fault evidence) ∈ later.observe) := by
  let environment := StateAuthoredSourceProvenanceTests.environment context
  let A := StateFiniteOutputStabilityTests.beforeClose
  let B := StateAuthoredFiniteStabilityTests.history
  have uniqueA : NodupAddr A := by unfold NodupAddr A StateFiniteOutputStabilityTests.beforeClose; decide
  have uniqueB : NodupAddr B := by unfold NodupAddr B StateAuthoredFiniteStabilityTests.history; decide
  have consistentA : ∀ a ∈ A, ∀ b ∈ A, a.addr = b.addr → a = b := fun a ma b mb same => uniqueA.eq_of_addr ma mb same
  have consistentB : ∀ a ∈ B, ∀ b ∈ B, a.addr = b.addr → a = b := fun a ma b mb same => uniqueB.eq_of_addr ma mb same
  have rankedA : StateExecutableFreeze.Ranked A := StateCausalRank.causalCheck_sound _ (by decide)
  have rankedB : StateExecutableFreeze.Ranked B := StateCausalRank.causalCheck_sound _ (by decide)
  have growth : ∀ act ∈ A, act ∈ B := by
    intro act member
    have full : B = A ++ [StateDomainSupportLocalityTests.freezer] := rfl
    rw [full]
    exact List.mem_append_left _ member
  cases installed : prepareStatic environment (entries true) with
  | none => have accepted := installation_succeeds context; simp [environment,installed] at accepted
  | some prepared =>
    have countField : ("votes",StateAuthoredBindings.Rule.legacy (.count "mark")) ∈ rawFields (entries true) := by simp [rawFields,entries]
    have countThreshold : Entry.threshold "quorum" "votes" [.element (.count 1)] ∈ entries true := by simp [entries]
    have existsField : ("observed",StateAuthoredBindings.Rule.legacy (.existsRule "mark")) ∈ rawFields (entries true) := by simp [rawFields,entries]
    have existsThreshold : Entry.threshold "started" "observed" [.element (.scalar (.bool true))] ∈ entries true := by simp [entries]
    obtain ⟨earlier,compiledA,_⟩ := StateAuthoredDataOutputs.count_program_stability environment (entries true) prepared installed
      "votes" "quorum" "mark" 1 countField countThreshold A rankedA consistentA
    obtain ⟨later,compiledB,_⟩ := StateAuthoredDataOutputs.count_program_stability environment (entries true) prepared installed
      "votes" "quorum" "mark" 1 countField countThreshold B rankedB consistentB
    obtain ⟨_,_,domainResult,_,_,_⟩ := StateAuthoredSourceProvenance.static_trace environment (entries true) prepared installed
    have domainsBuilt : StateAuthoredBindings.domains environment (entries true) = some StateDomainSupportLocalityTests.domains := by rfl
    have domainsEq : prepared.domains = StateDomainSupportLocalityTests.domains := Option.some.inj (domainResult.symm.trans domainsBuilt)
    refine ⟨prepared,earlier,later,rfl,compiledA,compiledB,?_,?_,?_⟩
    · rw [domainsEq]
      rfl
    · exact fun reached => StateAuthoredDataPreservation.count_successive environment (entries true) prepared installed
        "votes" "quorum" "mark" 1 countField countThreshold A B growth rankedA rankedB consistentA consistentB earlier later compiledA compiledB reached
    · exact fun reached => StateAuthoredDataPreservation.exists_successive environment (entries true) prepared installed
        "observed" "started" "mark" existsField existsThreshold A B growth rankedA rankedB consistentA consistentB earlier later compiledA compiledB reached

end CBCL.StateAuthoredDataPreservationTests
