import LeanCbcl.StateFiniteOutputStability
import LeanCbcl.StateFiniteFreezePolicyTests

/-! Public emitted-output fixtures for absent and concurrent freezer roots. -/
namespace CBCL.StateFiniteOutputStabilityTests
open State StateLift StateLVar StateObservation StateObservationPlan StateInstalledCompiler
open StateDomainSupportLocalityTests StateFiniteFreezePolicyTests StateFiniteOutputStability

/-- Complete supported history before a freezer arrives. -/
def beforeClose : List Act := [root,opener,writer]

/-- This fixture really exercises the absent-root dispatch branch. -/
theorem waiting_root_absent : StateScopePool.uniqueRoot (StateScopePool.normalize beforeClose) "close" = none := by decide

/-- Both the ordinary source and the waiting fault-freeze source are clear. -/
theorem before_clear (declaration : Option String) (permitted : declaration = none ∨ declaration = some "close") :
    errors (fun act => act ∈ StateScopePool.normalize beforeClose)
      (path (source field (StateScopePool.normalize beforeClose) declaration)) (StateScopePool.normalize beforeClose) = none := by
  have rawClear : (StateInstalledFinite.errorSpec field).read (StateScopePool.normalize beforeClose) = none := by decide
  rcases permitted with rfl | rfl
  · change unionError ((StateInstalledFinite.errorSpec field).read _) none = none
    simp [rawClear,unionError]
  · let whole := StateScopePool.normalize beforeClose
    have absent : ∀ act ∈ whole, act.verb ≠ "close" := by decide
    have noFirst : ∀ act, ¬Earliest (fun act => act ∈ whole) "close" whole act := by
      intro act first
      exact absent act first.1 first.2.1
    have noConflict : ¬∃ a b, FreezeConflict (fun act => act ∈ whole) "close"
        (StateFiniteFreezePolicy.freezeSpec field whole "close").contributes true whole a b := by
      rintro ⟨a,b,bad⟩
      cases bad with
      | concurrent first _ _ => exact noFirst a first
      | late first _ _ _ _ => exact noFirst a first
    change freezeFault (fun act => act ∈ whole) "close" _ true (unionError ((StateInstalledFinite.errorSpec field).read whole) none) whole = none
    rw [rawClear]
    simp only [unionError]
    apply (StateNativeReader.freeze_clear _ (StateFiniteFreezePolicy.freezeSpec field whole "close") none whole).mpr
    exact ⟨rfl,fun a b bad => noConflict ⟨a,b,bad⟩⟩

/-- An actual emitted output reaches with no freeze declaration. -/
theorem unfrozen_output_reached :
    ∃ code, StateOutputCompiler.compileQuery [.element (.scalar (.str "ready"))]
      (StateFiniteRead.definition field) = some code ∧
      (StateOutputCompiler.Output.threshold "enough" "phase" code
        (source field (StateScopePool.normalize beforeClose) none)).observe beforeClose [] =
          ("enough",.data (.reached (.element (.scalar (.str "ready"))))) := by
  exact output_reached field [.str "ready"] (.str "ready") policy_checked (by simp) beforeClose beforeClose
    (fun _ member => member) prior_reached none "phase" "enough"
    (StateCausalRank.causalCheck_sound _ (by decide)) (before_clear none (Or.inl rfl))

/-- The same reached output persists while an authored freeze awaits its verb. -/
theorem waiting_output_reached :
    ∃ code, StateOutputCompiler.compileQuery [.element (.scalar (.str "ready"))]
      (StateFiniteRead.definition field) = some code ∧
      (StateOutputCompiler.Output.threshold "enough" "phase" code
        (source field (StateScopePool.normalize beforeClose) (some "close"))).observe beforeClose
          (freezes field (StateScopePool.normalize beforeClose) "phase" (some "close")) =
            ("enough",.data (.reached (.element (.scalar (.str "ready"))))) := by
  exact output_reached field [.str "ready"] (.str "ready") policy_checked (by simp) beforeClose beforeClose
    (fun _ member => member) prior_reached (some "close") "phase" "enough"
    (StateCausalRank.causalCheck_sound _ (by decide)) (before_clear (some "close") (Or.inr rfl))

/-- Two close acts observe the same writer without observing each other. -/
def otherFreezer : Act := {freezer with addr := 4}

/-- Reverse/duplicate delivery of concurrent closes. -/
def concurrent : List Act := [otherFreezer,freezer,writer,opener,root,otherFreezer,freezer]

/-- Concurrent earliest roots use the same absent-unique-root dispatch branch. -/
theorem concurrent_root_absent : StateScopePool.uniqueRoot (StateScopePool.normalize concurrent) "close" = none := by decide

/-- The public compiled output faults for concurrent roots instead of treating
absence of a unique root as a healthy ordinary read. -/
theorem concurrent_output_faults :
    ∃ code, StateOutputCompiler.compileQuery [.element (.scalar (.str "ready"))]
      (StateFiniteRead.definition field) = some code ∧ ∃ evidence,
      (StateOutputCompiler.Output.threshold "enough" "phase" code
        (source field (StateScopePool.normalize concurrent) (some "close"))).observe concurrent
          (freezes field (StateScopePool.normalize concurrent) "phase" (some "close")) =
            ("enough",.fault evidence) := by
  classical
  let whole := StateScopePool.normalize concurrent
  have ranked : StateExecutableFreeze.Ranked whole := StateCausalRank.causalCheck_sound _ (by decide)
  have first : Earliest (fun act => act ∈ whole) "close" whole freezer :=
    (StateExecutableFreeze.earliest_iff whole ranked "close" freezer).mp (by decide)
  have second : Earliest (fun act => act ∈ whole) "close" whole otherFreezer :=
    (StateExecutableFreeze.earliest_iff whole ranked "close" otherFreezer).mp (by decide)
  have conflict : ∃ a b, FreezeConflict (fun act => act ∈ whole) "close"
      (StateFiniteFreezePolicy.freezeSpec field whole "close").contributes true whole a b :=
    ⟨freezer,otherFreezer,.concurrent first second (by decide)⟩
  have terminal : (errors (fun act => act ∈ whole) (path (source field whole (some "close"))) whole).isSome = true := by
    simp only [source,StateFiniteFreezePolicy.frozenPlan,path,errors]
    change (freezeFault (fun act => act ∈ whole) "close" _ true _ whole).isSome = true
    simp [freezeFault,conflict]
  refine ⟨.raw [.element (.scalar (.str "ready"))] (StateFiniteRead.policy field).test
    (StateInstalledFinite.term field).state,StateFiniteFreezePolicy.compiled_alternatives field [.str "ready"] policy_checked,?_⟩
  cases fault : errors (fun act => act ∈ whole) (path (source field whole (some "close"))) whole with
  | none => simp [fault] at terminal
  | some evidence =>
    refine ⟨evidence,?_⟩
    change errors (fun act => act ∈ StateScopePool.normalize concurrent)
      (path (source field (StateScopePool.normalize concurrent) (some "close"))) (StateScopePool.normalize concurrent) = some evidence at fault
    simp [StateOutputCompiler.Output.observe,StateOutputCompiler.sourceValue,observe,fault,
      StateOutputCompiler.Query.run,nativeRawThreshold]

/-- Unrelated fields/freezes coexist with the finite source in an installed dictionary. -/
noncomputable def installedClause : StateInstalledClause.Clause StateInstalledLegacy.Value := {
  fields := [("phase",.source (StateInstalledFinite.source field)),("copy",.derived id "phase")]
  freezes := [("phase",StateFiniteFreezePolicy.freezeSpec field (StateScopePool.normalize beforeClose) "close"),
    ("copy",⟨"unused",fun _ => False,true⟩)] }

/-- The installed field compiler constructs the actual final plan dictionary;
the output compiler then derives its guarded source lookup rather than assuming it. -/
theorem installed_dictionary_output : ∃ plans output,
    StateInstalledClause.compile installedClause = some plans ∧
    StateOutputCompiler.compileOne plans [("phase",StateFiniteRead.definition field)]
      (.threshold "enough" "phase" [.element (.scalar (.str "ready"))]) = some output ∧
      (output.observe beforeClose installedClause.freezes =
        ("enough",.data (.reached (.element (.scalar (.str "ready"))))) ∨
        ∃ evidence, output.observe beforeClose installedClause.freezes = ("enough",.fault evidence)) := by
  have installs : (StateInstalledClause.compile installedClause).isSome = true := by rfl
  cases compiled : StateInstalledClause.compile installedClause with
  | none => simp [compiled] at installs
  | some plans =>
    obtain ⟨output,emitted,result⟩ := installed_threshold_success_or_fault field [.str "ready"] (.str "ready")
      policy_checked (by simp) beforeClose beforeClose (fun _ member => member) prior_reached
      (some "close") "phase" "enough" (StateCausalRank.causalCheck_sound _ (by decide))
      installedClause plans compiled rfl rfl [("phase",StateFiniteRead.definition field)] rfl
    exact ⟨plans,output,rfl,emitted,result⟩

end CBCL.StateFiniteOutputStabilityTests
