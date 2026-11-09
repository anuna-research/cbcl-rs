import LeanCbcl.StateAuthoredFiniteStability
import LeanCbcl.StateAuthoredSourceProvenanceTests
import LeanCbcl.StateFiniteFreezePolicyTests

/-! Actual authored program construction plus a non-vacuous prefix-policy
execution whose raw query succeeds despite a deliberately unrelated payload. -/
namespace CBCL.StateAuthoredFiniteStabilityTests
open State StateLift StateLVar StateObservation StateObservationPlan StateInstalledCompiler
open StateInstalledLowering StateOutputCompiler StateAuthoredBindings

/-- A complete supported unique history for the actual authored fixture. -/
def history : List Act := [StateDomainSupportLocalityTests.root,StateDomainSupportLocalityTests.opener,
  StateDomainSupportLocalityTests.writer,StateDomainSupportLocalityTests.freezer]

/-- The actual authored compiler constructs a whole program and recovers the
source/policy needed for stability; it is not an assumed successful code walk. -/
theorem actual_authored_program (context : StateKernelSEC.Context) :
    ∃ prepared field program,
      prepareStatic (StateAuthoredSourceProvenanceTests.environment context)
        (StateAuthoredSourceProvenanceTests.entries true) = some prepared ∧
      compileAuthored (StateAuthoredSourceProvenanceTests.environment context)
        (StateAuthoredSourceProvenanceTests.entries true) history = some program ∧
      StateFiniteRead.check field [.str "ready"] = true ∧
      ∀ A : List Act, (∀ act ∈ A, act ∈ history) →
        StateFiniteRead.test field (.str "ready") (StateInstalledFinite.state field A) = true →
        ("enough",.data (.reached (.element (.scalar (.str "ready"))))) ∈ program.observe ∨
          ∃ evidence, ("enough",.fault evidence) ∈ program.observe := by
  let environment := StateAuthoredSourceProvenanceTests.environment context
  let entries := StateAuthoredSourceProvenanceTests.entries true
  cases installed : prepareStatic environment entries with
  | none => have accepted := StateAuthoredSourceProvenanceTests.installation_succeeds context; simp [environment,entries,installed] at accepted
  | some prepared =>
    have unique : NodupAddr history := by unfold NodupAddr history; decide
    have consistent : ∀ a ∈ history, ∀ b ∈ history, a.addr = b.addr → a = b := fun a ma b mb same => unique.eq_of_addr ma mb same
    obtain ⟨field,program,compiled,_,checked,stable⟩ := StateAuthoredFiniteStability.authored_program_stability
      environment entries prepared installed "phase" "phase-lattice" StateAuthoredSourceProvenanceTests.finite
      (by simp [entries,StateAuthoredSourceProvenanceTests.entries,rawFields]) "enough" [.str "ready"]
      (by simp [entries,StateAuthoredSourceProvenanceTests.entries]) history
      (StateCausalRank.causalCheck_sound _ (by decide)) consistent
    exact ⟨prepared,field,program,rfl,compiled,checked,fun A inside reached => stable A (.str "ready") inside (by simp) reached⟩

/-- The displayed payload is deliberately unrelated to the finite read. -/
def unrelatedPayload : Plan StateInstalledLegacy.Value := .snapshot (fun _ => .element (.scalar (.bool false)))

/-- The finite source and its threshold are separated by another declaration. -/
noncomputable def declarations : List (Declaration StateInstalledLegacy.Value) := [
  .field "phase" (StateFiniteRead.definition StateFiniteFreezePolicyTests.field),
  .field "other" (.native (.snapshot (fun _ => .element (.scalar (.bool true)))) none),
  .threshold "enough" "phase" [.element (.scalar (.str "ready"))]]

/-- Actual complete emitted code locates the threshold's source-owned raw policy
and returns ready despite its false displayed payload. -/
theorem prefix_query_actually_reaches : ∃ code,
    compileDeclarations [("phase",unrelatedPayload),("other",unrelatedPayload)] [] declarations = some code ∧
      ("enough",.data (.reached (.element (.scalar (.str "ready"))))) ∈
        code.map (Output.observe [StateDomainSupportLocalityTests.root,StateDomainSupportLocalityTests.opener,
          StateDomainSupportLocalityTests.writer] []) := by
  let plans : Plans StateInstalledLegacy.Value := [("phase",unrelatedPayload),("other",unrelatedPayload)]
  have existsCode : (compileDeclarations plans [] declarations).isSome = true := by rfl
  cases compiled : compileDeclarations plans [] declarations with
  | none => simp [compiled] at existsCode
  | some code =>
    obtain ⟨priorDefinitions,output,origins,member,emitted⟩ := StateAuthoredOutputProvenance.emitted_origin
      plans declarations declarations [] code (by intro name definition impossible; simp at impossible)
      (fun _ member => member) compiled (.threshold "enough" "phase" [.element (.scalar (.str "ready"))]) (by simp [declarations])
    obtain ⟨_,outputEq⟩ := StateAuthoredOutputProvenance.finite_emitted plans declarations (by decide)
      StateFiniteFreezePolicyTests.field "phase" "enough" [.str "ready"] (by simp [declarations])
      priorDefinitions origins unrelatedPayload rfl output emitted
    have inCode : output.observe [StateDomainSupportLocalityTests.root,StateDomainSupportLocalityTests.opener,StateDomainSupportLocalityTests.writer] [] ∈
        code.map (Output.observe [StateDomainSupportLocalityTests.root,StateDomainSupportLocalityTests.opener,StateDomainSupportLocalityTests.writer] []) :=
      List.mem_map.mpr ⟨output,member,rfl⟩
    let raw := StateScopePool.normalize [StateDomainSupportLocalityTests.root,StateDomainSupportLocalityTests.opener,StateDomainSupportLocalityTests.writer]
    have reached : StateFiniteRead.test StateFiniteFreezePolicyTests.field (.str "ready")
        (StateInstalledFinite.state StateFiniteFreezePolicyTests.field raw) = true := by
      rw [StateInstalledFinite.state_setEq _ (StateScopePool.normalize_setEq _)]
      exact StateFiniteFreezePolicyTests.prior_reached
    have run := StateFiniteOutputStability.run_reached StateFiniteFreezePolicyTests.field [.str "ready"] (.str "ready")
      StateFiniteFreezePolicyTests.policy_checked (by simp) raw reached (.snapshot (.element (.scalar (.bool false))))
    have result : output.observe [StateDomainSupportLocalityTests.root,StateDomainSupportLocalityTests.opener,StateDomainSupportLocalityTests.writer] [] =
        ("enough",.data (.reached (.element (.scalar (.str "ready"))))) := by
      simpa only [outputEq,Output.observe,sourceValue,unrelatedPayload,observe,path,errors,data,
        StateThresholdDispatch.referenceScope,List.lookup] using congrArg ("enough", ·) run
    exact ⟨code,rfl,result ▸ inCode⟩

end CBCL.StateAuthoredFiniteStabilityTests
