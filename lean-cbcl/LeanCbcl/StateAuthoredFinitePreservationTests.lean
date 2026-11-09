import LeanCbcl.StateAuthoredFinitePreservation
import LeanCbcl.StateAuthoredFiniteStabilityTests
import LeanCbcl.StateFiniteOutputStabilityTests

/-! Recover native success from an actual reached output, and construct both
successive authored programs rather than assuming their compilation. -/
namespace CBCL.StateAuthoredFinitePreservationTests
open State StateLift StateLVar StateObservation StateObservationPlan StateInstalledCompiler
open StateInstalledLowering StateOutputCompiler StateAuthoredBindings

/-- The waiting-freezer output fixture actually reaches; inversion recovers
native success without supplying that native success as an inversion premise. -/
theorem waiting_output_inverts : StateFiniteRead.test StateFiniteFreezePolicyTests.field (.str "ready")
    (StateInstalledFinite.state StateFiniteFreezePolicyTests.field StateFiniteOutputStabilityTests.beforeClose) = true := by
  obtain ⟨code,compiled,reached⟩ := StateFiniteOutputStabilityTests.waiting_output_reached
  have codeEq : code = .raw [.element (.scalar (.str "ready"))] (StateFiniteRead.policy StateFiniteFreezePolicyTests.field).test
      (StateInstalledFinite.term StateFiniteFreezePolicyTests.field).state :=
    Option.some.inj (compiled.symm.trans (StateFiniteFreezePolicy.compiled_alternatives StateFiniteFreezePolicyTests.field
      [.str "ready"] StateFiniteFreezePolicyTests.policy_checked))
  have planEqual := StateAuthoredFiniteStability.source_setEq StateFiniteFreezePolicyTests.field
    (fun act => (StateScopePool.normalize_setEq StateFiniteOutputStabilityTests.beforeClose act).symm) (some "close")
  rw [codeEq,← planEqual] at reached
  exact (StateCompiledFiniteInversion.output_native_success StateFiniteFreezePolicyTests.field [.str "ready"] (.str "ready")
    StateFiniteOutputStabilityTests.beforeClose
    (StateFiniteOutputStability.freezes StateFiniteFreezePolicyTests.field
      (StateScopePool.normalize StateFiniteOutputStabilityTests.beforeClose) "phase" (some "close"))
    (some "close") "phase" "enough" reached).2

/-- Actual preparation constructs earlier and later complete authored programs;
preservation starts from a reached member of the earlier observation vector. -/
theorem constructed_successive_programs (context : StateKernelSEC.Context) :
    ∃ earlier later,
      compileAuthored (StateAuthoredSourceProvenanceTests.environment context)
        (StateAuthoredSourceProvenanceTests.entries true) StateFiniteOutputStabilityTests.beforeClose = some earlier ∧
      compileAuthored (StateAuthoredSourceProvenanceTests.environment context)
        (StateAuthoredSourceProvenanceTests.entries true) StateAuthoredFiniteStabilityTests.history = some later ∧
      (("enough",.data (.reached (.element (.scalar (.str "ready"))))) ∈ earlier.observe →
        ("enough",.data (.reached (.element (.scalar (.str "ready"))))) ∈ later.observe ∨
          ∃ evidence, ("enough",.fault evidence) ∈ later.observe) := by
  let environment := StateAuthoredSourceProvenanceTests.environment context
  let entries := StateAuthoredSourceProvenanceTests.entries true
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
  cases installed : prepareStatic environment entries with
  | none => have accepted := StateAuthoredSourceProvenanceTests.installation_succeeds context; simp [environment,entries,installed] at accepted
  | some prepared =>
    have field : ("phase",StateAuthoredBindings.Rule.finite "phase-lattice" StateAuthoredSourceProvenanceTests.finite) ∈ rawFields entries := by
      simp [entries,StateAuthoredSourceProvenanceTests.entries,rawFields]
    have threshold : Entry.threshold "enough" "phase" [.element (.scalar (.str "ready"))] ∈ entries := by
      simp [entries,StateAuthoredSourceProvenanceTests.entries]
    obtain ⟨_,earlier,compiledA,_,_,_⟩ := StateAuthoredFiniteStability.authored_program_stability environment entries prepared installed
      "phase" "phase-lattice" StateAuthoredSourceProvenanceTests.finite field "enough" [.str "ready"] threshold A rankedA consistentA
    obtain ⟨_,later,compiledB,_,_,_⟩ := StateAuthoredFiniteStability.authored_program_stability environment entries prepared installed
      "phase" "phase-lattice" StateAuthoredSourceProvenanceTests.finite field "enough" [.str "ready"] threshold B rankedB consistentB
    refine ⟨earlier,later,compiledA,compiledB,?_⟩
    intro reached
    exact StateAuthoredFinitePreservation.successive_compiled environment entries prepared installed "phase" "phase-lattice"
      StateAuthoredSourceProvenanceTests.finite field "enough" [.str "ready"] threshold A B growth rankedA rankedB
      consistentA consistentB earlier later compiledA compiledB (.str "ready") reached

end CBCL.StateAuthoredFinitePreservationTests
