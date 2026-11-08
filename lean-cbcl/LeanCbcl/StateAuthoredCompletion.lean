import LeanCbcl.StateNativeReader

/-! Whole authored installation through cached scoped observation. Successful
preparation supplies compiler obligations; the functional reader agrees with
independently composed concrete source readers, including faulted results. -/
set_option autoImplicit false
namespace CBCL.StateAuthoredCompletion
open State StateLift StateLVar StateObservationPlan StateInstalledCompiler StateAuthoredBindings

/-- Every accepted concrete authored clause constructs plans and independent
readers whose complete observations agree with the cached scoped reader. -/
theorem prepared_readers_complete (world : Act → Prop) (environment : Environment) (entries : List Entry)
    (history : List Act) (clause : StateInstalledLowering.Clause StateInstalledLegacy.Value)
    (prepared : prepare environment entries history = some clause)
    (closed : CausallyClosed world history) (unique : NodupAddr history) :
    ∃ plans readers, compile environment entries history = some plans ∧
      interpret world environment entries history = some readers ∧
      plans.map (fun (name,plan) => (name,StateNativeReader.observe world plan history)) =
        readers.map (fun (name,reader) => (name,reader history)) := by
  obtain ⟨plans,compiled⟩ := prepared_compiler_complete environment entries history clause prepared
  have clauseCompiled : StateInstalledLowering.compile clause = some plans := by simpa [compile,prepared] using compiled
  obtain ⟨readers,interpreted,equal⟩ := StateInstalledLowering.native_installed_observations_refinement world clause plans clauseCompiled
  refine ⟨plans,readers,compiled,by simp [interpret,prepared,interpreted],?_⟩
  calc
    _ = plans.map (fun (name,plan) => (name,StateObservationPlan.observe world plan history)) := by
      apply List.map_congr_left
      rintro ⟨name,plan⟩ _
      simp only [StateNativeReader.native_reader_refinement world plan history closed unique]
    _ = _ := equal history closed

/-- Equal accepted sets preserve the entire concrete authored cached-reader
observation, including terminal evidence and frozen exclusion metadata. -/
theorem cached_observations_setEq (world : Act → Prop) (environment : Environment) (entries : List Entry)
    {A B : List Act} (uniqueA : NodupAddr A) (uniqueB : NodupAddr B) (same : SetEq A B)
    (closedA : CausallyClosed world A) (closedB : CausallyClosed world B)
    (plans : Plans StateInstalledLegacy.Value) (compiled : compile environment entries A = some plans) :
    compile environment entries B = some plans ∧
      plans.map (fun (name,plan) => (name,StateNativeReader.observe world plan A)) =
        plans.map (fun (name,plan) => (name,StateNativeReader.observe world plan B)) := by
  refine ⟨by rw [← compile_setEq environment entries same]; exact compiled,?_⟩
  apply List.map_congr_left
  rintro ⟨name,plan⟩ _
  simp only [StateNativeReader.native_reader_refinement world plan A closedA uniqueA,
    StateNativeReader.native_reader_refinement world plan B closedB uniqueB,
    observe_setEq world plan uniqueA uniqueB same]

end CBCL.StateAuthoredCompletion
