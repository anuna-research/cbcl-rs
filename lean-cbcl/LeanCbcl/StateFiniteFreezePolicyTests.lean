import LeanCbcl.StateFiniteFreezePolicy
import LeanCbcl.StateDomainSupportLocalityTests

/-! Concrete non-bottom finite reads with initializer and sealed-roster domains. -/
namespace CBCL.StateFiniteFreezePolicyTests
open State StateLift StateLVar StateObservation StateObservationPlan StateInstalledCompiler
open StateDomainSupportLocalityTests

/-- A checked three-element chain with a useful non-top reached state. -/
def table : StateFiniteTable.Resolved := {
  name := "phase"
  elements := ["empty","ready","conflict"]
  bottom := ⟨0,by decide⟩
  top := ⟨2,by decide⟩
  rows := (List.finRange 3).flatMap (fun left => (List.finRange 3).map
    (fun right => ((left,right),if left.val < right.val then right else left))) }

/-- Both domain sources govern an actual matching ready contribution. -/
def field : StateInstalledFinite.Field := {
  table := ⟨table,64,by decide⟩
  verb := "mark"
  rows := [⟨"target",.str "@a",⟨1,by decide⟩,by decide⟩]
  projection := none
  domains := domains }

/-- A real non-bottom success occurs before the close. -/
theorem prior_reached : StateFiniteRead.test field (.str "ready")
    (StateInstalledFinite.state field [root,opener,writer]) = true := by decide

/-- Successful installation is computed, rather than a supplied policy axiom. -/
theorem policy_checked : StateFiniteRead.check field [.str "ready"] = true := by decide

/-- Reverse/duplicate delivery constructs actual compiled output stability. -/
theorem compiled_mixed_domain_stability :
    ∃ code, StateOutputCompiler.compileQuery [.element (.scalar (.str "ready"))]
      (StateFiniteRead.definition field) = some code ∧
      let output := (StateOutputCompiler.Output.threshold "enough" "phase" code
        (StateFiniteFreezePolicy.frozenPlan field (StateScopePool.normalize history) "close")).observe history
        [("phase",StateFiniteFreezePolicy.freezeSpec field (StateScopePool.normalize history) "close")]
      output = ("enough",.data (.reached (.element (.scalar (.str "ready"))))) ∨
        ∃ evidence, output = ("enough",.fault evidence) := by
  apply StateFiniteFreezePolicy.output_success_or_fault field [.str "ready"] (.str "ready") policy_checked
    (by simp) [root,opener,writer] history
    (by intro act member; simp only [List.mem_cons,List.not_mem_nil,or_false] at member; rcases member with rfl | rfl | rfl <;> simp [history])
    prior_reached "close" "phase" "enough" freezer
  · apply StateCausalRank.causalCheck_sound
    decide
  · decide

/-- The complete mixed-domain source is healthy after normalization. -/
theorem normalized_source_clear : errors (fun act => act ∈ StateScopePool.normalize history)
    (path (StateFiniteFreezePolicy.frozenPlan field (StateScopePool.normalize history) "close"))
    (StateScopePool.normalize history) = none := by
  classical
  let whole := StateScopePool.normalize history
  have ranked : StateExecutableFreeze.Ranked whole := StateCausalRank.causalCheck_sound whole (by decide)
  have empty : (StateExecutableFreeze.conflicts whole "close" (fun _ => true) true).isEmpty = true := by decide
  have noConflict : ¬∃ a b, FreezeConflict (fun act => act ∈ whole) "close"
      (StateFiniteFreezePolicy.freezeSpec field whole "close").contributes true whole a b := by
    rintro ⟨a,b,bad⟩
    have general : FreezeConflict (fun act => act ∈ whole) "close" (fun _ => true = true) true whole a b := by
      cases bad with
      | concurrent left right different => exact .concurrent left right different
      | late first present _ absent policy => exact .late first present rfl absent policy
    have nonempty := (StateExecutableFreeze.has_conflict whole ranked "close" (fun _ => true) true).mpr ⟨a,b,general⟩
    simp [empty] at nonempty
  have rawClear : (StateInstalledFinite.errorSpec field).read whole = none := by decide
  change freezeFault (fun act => act ∈ whole) "close" _ true (unionError ((StateInstalledFinite.errorSpec field).read whole) none) whole = none
  simp only [rawClear,unionError]
  apply (StateNativeReader.freeze_clear (fun act => act ∈ whole)
    (StateFiniteFreezePolicy.freezeSpec field whole "close") none whole).mpr
  exact ⟨rfl,fun a b bad => noConflict ⟨a,b,bad⟩⟩

/-- The healthy fixture actually reaches, rather than merely satisfying a
success-or-fault disjunction by faulting. -/
theorem compiled_mixed_domain_reached :
    ∃ code, StateOutputCompiler.compileQuery [.element (.scalar (.str "ready"))]
      (StateFiniteRead.definition field) = some code ∧
      (StateOutputCompiler.Output.threshold "enough" "phase" code
        (StateFiniteFreezePolicy.frozenPlan field (StateScopePool.normalize history) "close")).observe history
        [("phase",StateFiniteFreezePolicy.freezeSpec field (StateScopePool.normalize history) "close")] =
          ("enough",.data (.reached (.element (.scalar (.str "ready"))))) := by
  obtain ⟨code,compiled,result⟩ := compiled_mixed_domain_stability
  refine ⟨code,compiled,?_⟩
  rcases result with reached | ⟨evidence,fault⟩
  · exact reached
  · have codeEq : code = .raw [.element (.scalar (.str "ready"))] (StateFiniteRead.policy field).test
        (StateInstalledFinite.term field).state := by
      simpa [StateOutputCompiler.compileQuery,StateFiniteRead.definition,StateFiniteRead.policy,
        StateFiniteRead.decode,policy_checked] using compiled.symm
    simp only [StateOutputCompiler.Output.observe,StateOutputCompiler.sourceValue,observe,
      normalized_source_clear,codeEq,StateOutputCompiler.Query.run,nativeRawThreshold] at fault
    split at fault <;> have impossible := congrArg Prod.snd fault <;> cases impossible

/-- A writer bypassing the opener makes the actual frozen source fault. -/
theorem bypass_source_faults : ∃ evidence,
    observe (fun act => act ∈ branch) (StateFiniteFreezePolicy.frozenPlan field branch "close") branch = .fault evidence := by
  classical
  have fault := StateDomainSupportLocalityTests.branch_faults
  have conflict : ∃ a b, FreezeConflict (fun act => act ∈ branch) "close"
      (StateAuthoredBindings.contributes domains branch (.verbs ["mark"])) true branch a b := by
    apply Classical.byContradiction
    intro absent
    simp [freezeFault,absent] at fault
  have terminal : (errors (fun act => act ∈ branch)
      (path (StateFiniteFreezePolicy.frozenPlan field branch "close")) branch).isSome = true := by
    simp only [StateFiniteFreezePolicy.frozenPlan,path,errors]
    simp [StateFiniteFreezePolicy.freezeSpec,field,freezeFault,conflict]
  cases result : errors (fun act => act ∈ branch)
      (path (StateFiniteFreezePolicy.frozenPlan field branch "close")) branch with
  | none => simp [result] at terminal
  | some evidence => exact ⟨evidence,by simp [observe,result]⟩

end CBCL.StateFiniteFreezePolicyTests
