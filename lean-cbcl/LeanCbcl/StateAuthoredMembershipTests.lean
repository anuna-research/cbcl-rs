import LeanCbcl.StateAuthoredMembership
import LeanCbcl.StateAuthoredDataPreservationTests

/-! Set-union membership shares mixed domains with count/existence while
retaining its own scalar admission and source-owned raw query. -/
namespace CBCL.StateAuthoredMembershipTests
open State StateLift StateLVar StateObservation StateObservationPlan StateInstalledCompiler
open StateInstalledLegacy StateInstalledLowering StateAuthoredBindings StateOutputCompiler

/-- Extend an actual authored mixed-domain fixture with a set-union source. -/
def entries (value : Val) (fault : Bool) : List Entry := StateAuthoredDataPreservationTests.entries true ++ [
  .field "members" (.legacy (.setUnion "mark" "target")),
  .threshold "selected" "members" [.element (.member value)],
  .freeze "members" "close" fault]

/-- Actual installation admits a scalar member query. -/
theorem installation_succeeds (context : StateKernelSEC.Context) :
    (prepareStatic (StateAuthoredSourceProvenanceTests.environment context) (entries (.str "@a") true)).isSome = true := by rfl

/-- Structured members fail the actual source policy. -/
theorem structured_member_rejected (context : StateKernelSEC.Context) :
    prepareStatic (StateAuthoredSourceProvenanceTests.environment context) (entries (.list []) true) = none := by rfl

/-- Revisable supersede sources cannot supply this stable member threshold. -/
theorem supersede_rejected (context : StateKernelSEC.Context) :
    prepareStatic (StateAuthoredSourceProvenanceTests.environment context) (entries (.str "@a") false) = none := by rfl

/-- Actual kernel membership survives reverse/duplicate delivery. -/
theorem duplicate_native_member (context : StateKernelSEC.Context) :
    readTest (.element (.member (.str "@a"))) (.kernel (StateInstalledDomains.evaluate context StateDomainSupportLocalityTests.domains
      (.distinct (.verb "mark") "target") (rawHistory StateDomainSupportLocalityTests.history))) = true := by
  rw [StateNativeMembership.member_value]
  rfl

/-- Actual emitted membership reaches from raw selected state with a pending payload. -/
theorem pending_payload_reaches (context : StateKernelSEC.Context) : ∃ code,
    compileQuery [.element (.member (.str "@a"))]
      ((StateAuthoredDataProvenance.Head.setUnion "mark" "target").definition
        (StateAuthoredSourceProvenanceTests.environment context) StateDomainSupportLocalityTests.domains) = some code ∧
      code.run StateDomainSupportLocalityTests.history (.data .pending) = .data (.reached (.element (.member (.str "@a")))) := by
  obtain ⟨code,compiled,run⟩ := StateNativeMembership.compiled_member (StateAuthoredSourceProvenanceTests.environment context)
    StateDomainSupportLocalityTests.domains "mark" "target" (.str "@a") rfl
  refine ⟨code,compiled,?_⟩
  rw [run]
  rfl

/-- Both actual programs are constructed. The earlier native witness is
computed; preservation itself starts from an earlier named compiled result. -/
theorem constructed_programs_preserve_member (context : StateKernelSEC.Context) :
    ∃ prepared earlier later,
      prepareStatic (StateAuthoredSourceProvenanceTests.environment context) (entries (.str "@a") true) = some prepared ∧
      compileAuthored (StateAuthoredSourceProvenanceTests.environment context) (entries (.str "@a") true)
        StateFiniteOutputStabilityTests.beforeClose = some earlier ∧
      compileAuthored (StateAuthoredSourceProvenanceTests.environment context) (entries (.str "@a") true)
        StateAuthoredFiniteStabilityTests.history = some later ∧
      has "target" (StateDomainSupportLocality.selected prepared.domains ["mark"] StateFiniteOutputStabilityTests.beforeClose) (.str "@a") = true ∧
      (("selected",.data (.reached (.element (.member (.str "@a"))))) ∈ earlier.observe →
        ("selected",.data (.reached (.element (.member (.str "@a"))))) ∈ later.observe ∨ ∃ evidence, ("selected",.fault evidence) ∈ later.observe) := by
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
  cases installed : prepareStatic environment (entries (.str "@a") true) with
  | none => have accepted := installation_succeeds context; simp [environment,installed] at accepted
  | some prepared =>
    have field : ("members",StateAuthoredBindings.Rule.legacy (.setUnion "mark" "target")) ∈ rawFields (entries (.str "@a") true) := by
      simp [entries,StateAuthoredDataPreservationTests.entries,rawFields]
    have threshold : Entry.threshold "selected" "members" [.element (.member (.str "@a"))] ∈ entries (.str "@a") true := by simp [entries]
    obtain ⟨earlier,compiledA,_⟩ := StateAuthoredMembership.program_stability environment (entries (.str "@a") true) prepared installed
      "members" "selected" "mark" "target" (.str "@a") field threshold A rankedA consistentA
    obtain ⟨later,compiledB,_⟩ := StateAuthoredMembership.program_stability environment (entries (.str "@a") true) prepared installed
      "members" "selected" "mark" "target" (.str "@a") field threshold B rankedB consistentB
    obtain ⟨_,_,domainResult,_,_,_⟩ := StateAuthoredSourceProvenance.static_trace environment (entries (.str "@a") true) prepared installed
    have domainsBuilt : domains environment (entries (.str "@a") true) = some StateDomainSupportLocalityTests.domains := by rfl
    have domainsEq := Option.some.inj (domainResult.symm.trans domainsBuilt)
    refine ⟨prepared,earlier,later,rfl,compiledA,compiledB,?_,?_⟩
    · rw [domainsEq]
      rfl
    · exact fun reached => StateAuthoredMembership.successive_compiled environment (entries (.str "@a") true) prepared installed
        "members" "selected" "mark" "target" (.str "@a") field threshold A B growth rankedA rankedB consistentA consistentB
        earlier later compiledA compiledB reached

end CBCL.StateAuthoredMembershipTests
