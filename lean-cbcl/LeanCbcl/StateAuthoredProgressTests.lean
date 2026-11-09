import LeanCbcl.StateAuthoredProgress
import LeanCbcl.StateProgressFreezeTests
import LeanCbcl.StateAuthoredSumTrace

/-! Actual authored progress installation and a complete no-freeze trace.
Fixture decoding remains typed evidence, not native parsing/admission. -/
namespace CBCL.StateAuthoredProgressTests
open State StateLift StateLVar StateObservation StateObservationPlan StateInstalledCompiler
open StateInstalledLegacy StateInstalledLowering StateAuthoredBindings StateOutputCompiler
open StateAuthoredDataProvenance StateAuthoredDataOutputs StateProgressStore StateProgressStoreTests StateAuthoredProgress

/-- Concrete installed metadata for the repeated verb and optional freezer. -/
def environment (base : StateKernelSEC.Context) : Environment :=
  {StateAuthoredEventSumTests.environment {base with thread := 7,limit := fun _ => 3} with
    schema := ⟨["tick","close"],[]⟩}

/-- Existing progress source/query with an optional authored freeze. -/
def entries (bound : Nat) (declaration : Option Bool) : List Entry := [
  .field "stage" (.legacy (.progress "tick")),
  .threshold "done" "stage" [.element (.progress bound)]] ++
  declaration.toList.map (fun policy => .freeze "stage" "close" policy)

/-- Actual static preparation accepts the fault-frozen closure threshold. -/
theorem installation_succeeds (base : StateKernelSEC.Context) :
    (prepareStatic (installed (environment base) decode) (entries 2 (some true))).isSome = true := by rfl

/-- A revisable supersede freeze cannot install this stable threshold. -/
theorem supersede_rejected (base : StateKernelSEC.Context) :
    prepareStatic (installed (environment base) decode) (entries 2 (some false)) = none := by rfl

/-- Progress bound admission excludes the upper signed integer limit. -/
theorem upper_bound_rejected (base : StateKernelSEC.Context) :
    prepareStatic (installed (environment base) decode) (entries (2^63) none) = none := by rfl

/-- Exact no-freeze static result for the complete trace. -/
noncomputable def static (base : StateKernelSEC.Context) : Prepared :=
  ⟨[.field "stage" ((Head.progress "tick").definition (installed (environment base) decode) []),
    .threshold "done" "stage" [.element (.progress 2)]],[],[]⟩

/-- Preparation is computed before constructing output programs. -/
theorem nofreeze_preparation (base : StateKernelSEC.Context) :
    prepareStatic (installed (environment base) decode) (entries 2 none) = some (static base) := by rfl

/-- The earlier complete authored program really reaches the named query.
Neither earlier native success nor a reached-output member is a premise. -/
theorem earlier_reaches (base : StateKernelSEC.Context) : ∃ program,
    compileAuthored (installed (environment base) decode) (entries 2 none) before = some program ∧
      ("done",.data (.reached (.element (.progress 2)))) ∈ program.observe := by
  have ranked : StateExecutableFreeze.Ranked before := StateCausalRank.causalCheck_sound _ (by decide)
  obtain ⟨declaration,query,program,compiled,queryCompiled,member,history,metadata⟩ := authored_emitted (.progress "tick")
    (installed (environment base) decode) (entries 2 none) (static base) (nofreeze_preparation base) "stage" "done"
    (by simp [entries,rawFields,Head.rule]) [.element (.progress 2)] (by simp [entries]) before ranked before_consistent
  have actual := StateAuthoredSumTrace.compiled_metadata (installed (environment base) decode) (entries 2 none) (static base)
    (nofreeze_preparation base) before program compiled
  have noFreeze : program.program.freezes = [] := actual.2
  have noDeclaration : declaration = none := by
    rw [noFreeze] at metadata
    cases declaration with
    | none => rfl
    | some verb => simp at metadata
  subst declaration
  have same := (admitted_query (installed (environment base) decode) [] "tick" 2 query queryCompiled).2
  subst query
  refine ⟨program,compiled,?_⟩
  apply dispatch_member (.progress "tick") (installed (environment base) decode) [] before none "stage" "done" _ program member history metadata
  have normalized : StateScopePool.normalize before = before := by decide
  have reached : 2 ≤ protocolProgress (store decode (StateScopePool.normalize before)) (environment base).context.thread "tick"
      ((environment base).context.limit "tick") (StateScopePool.normalize before) := by
    change 2 ≤ protocolProgress (store decode (StateScopePool.normalize before)) 7 "tick" 3 (StateScopePool.normalize before)
    rw [normalized,before_progress]
    exact Nat.le_refl _
  have output := StateProgressFreeze.run_payload (environment base).context decode [] "tick" 2 (StateScopePool.normalize before)
    (StateScopePool.normalize before)
    (data (fun act => act ∈ StateScopePool.normalize before) ((Head.progress "tick").bare (installed (environment base) decode) []) (StateScopePool.normalize before))
    (congrArg Data.payload (StateProgressFreeze.bare_data (installed (environment base) decode) [] "tick" _ _)) reached
  exact congrArg ("done", ·) output

/-- Complete programs for reverse duplicate growth are constructed, and an
actual earlier reached member feeds the authored preservation theorem. -/
theorem successive_trace (base : StateKernelSEC.Context) : ∃ earlier later,
    compileAuthored (installed (environment base) decode) (entries 2 none) before = some earlier ∧
    compileAuthored (installed (environment base) decode) (entries 2 none) after = some later ∧
    ("done",.data (.reached (.element (.progress 2)))) ∈ earlier.observe ∧
    (("done",.data (.reached (.element (.progress 2)))) ∈ later.observe ∨ ∃ evidence, ("done",.fault evidence) ∈ later.observe) := by
  obtain ⟨earlier,compiledA,reached⟩ := earlier_reaches base
  have rankedA : StateExecutableFreeze.Ranked before := StateCausalRank.causalCheck_sound _ (by decide)
  have rankedB : StateExecutableFreeze.Ranked after := StateCausalRank.causalCheck_sound _ (by decide)
  have growth : ∀ act ∈ before, act ∈ after := by
    intro act member
    simp only [before,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> simp [after]
  obtain ⟨later,compiledB,_⟩ := program_stability (environment base) decode (entries 2 none) (static base) (nofreeze_preparation base)
    "stage" "done" "tick" 2 (by simp [entries,rawFields]) (by simp [entries]) after rankedB after_consistent StateProgressFreezeTests.coherent
  refine ⟨earlier,later,compiledA,compiledB,reached,?_⟩
  exact successive_compiled (environment base) decode (entries 2 none) (static base) (nofreeze_preparation base) "stage" "done" "tick" 2
    (by simp [entries,rawFields]) (by simp [entries]) before after growth rankedA rankedB before_consistent after_consistent
    StateProgressFreezeTests.coherent earlier later compiledA compiledB reached

/-- Fault-frozen complete programs are also constructed around the real source
footprint. This fixture specializes preservation conditional on earlier reached
membership; the separate no-freeze trace proves its antecedent concretely. -/
theorem frozen_programs_preserve (base : StateKernelSEC.Context) : ∃ prepared earlier later,
    prepareStatic (installed (environment base) decode) (entries 2 (some true)) = some prepared ∧
    compileAuthored (installed (environment base) decode) (entries 2 (some true)) before = some earlier ∧
    compileAuthored (installed (environment base) decode) (entries 2 (some true)) StateProgressFreezeTests.whole = some later ∧
    (("done",.data (.reached (.element (.progress 2)))) ∈ earlier.observe →
      ("done",.data (.reached (.element (.progress 2)))) ∈ later.observe ∨ ∃ evidence, ("done",.fault evidence) ∈ later.observe) := by
  have rankedA : StateExecutableFreeze.Ranked before := StateCausalRank.causalCheck_sound _ (by decide)
  have consistentB : ∀ a ∈ StateProgressFreezeTests.whole, ∀ b ∈ StateProgressFreezeTests.whole, a.addr = b.addr → a = b :=
    fun _ ha _ hb eq => StateProgressFreezeTests.unique.eq_of_addr ha hb eq
  have growth : ∀ act ∈ before, act ∈ StateProgressFreezeTests.whole := by
    intro act member
    simp only [before,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> simp [StateProgressFreezeTests.whole]
  cases accepted : prepareStatic (installed (environment base) decode) (entries 2 (some true)) with
  | none => have valid := installation_succeeds base; simp [accepted] at valid
  | some prepared =>
    obtain ⟨earlier,compiledA,_⟩ := program_stability (environment base) decode (entries 2 (some true)) prepared accepted
      "stage" "done" "tick" 2 (by simp [entries,rawFields]) (by simp [entries]) before rankedA before_consistent StateProgressFreezeTests.coherent
    obtain ⟨later,compiledB,_⟩ := program_stability (environment base) decode (entries 2 (some true)) prepared accepted
      "stage" "done" "tick" 2 (by simp [entries,rawFields]) (by simp [entries]) StateProgressFreezeTests.whole StateProgressFreezeTests.ranked consistentB StateProgressFreezeTests.coherent
    refine ⟨prepared,earlier,later,rfl,compiledA,compiledB,?_⟩
    exact fun reached => successive_compiled (environment base) decode (entries 2 (some true)) prepared accepted
      "stage" "done" "tick" 2 (by simp [entries,rawFields]) (by simp [entries]) before StateProgressFreezeTests.whole growth
      rankedA StateProgressFreezeTests.ranked before_consistent consistentB StateProgressFreezeTests.coherent earlier later compiledA compiledB reached

end CBCL.StateAuthoredProgressTests
