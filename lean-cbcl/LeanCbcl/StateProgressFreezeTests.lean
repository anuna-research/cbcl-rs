import LeanCbcl.StateProgressFreeze
import LeanCbcl.StateProgressStoreTests

/-! Typed progress-freeze fixtures retain a causal chain while omitting an
unrelated act. This is not a native admission or full authored-program trace. -/
namespace CBCL.StateProgressFreezeTests
open State StateLVar StateObservation StateObservationPlan StateInstalledLegacy
open StateProgressStore StateProgressStoreTests StateProgressFreeze

/-- The freezer observes both contributing repeat positions. -/
def closer : Act := ⟨60,"close","@a",[23],[],[]⟩
/-- Unrelated evidence is outside the freezer's causal cut. -/
def note : Act := ⟨90,"note","@a",[],[],[]⟩
/-- Full history contains one exact freezer and an unrelated act. -/
def whole : List Act := [first,second,closer,note]

/-- The fixture decoder preserves each source act's verb. -/
theorem coherent : ∀ act, (decode act).verb = act.verb := fun _ => rfl

/-- The full fixture has unique addresses. -/
theorem unique : NodupAddr whole := by change ([11,23,60,90] : List Nat).Nodup; decide

/-- Concrete causal ranking is checked independently of freeze health. -/
theorem ranked : StateExecutableFreeze.Ranked whole := StateCausalRank.causalCheck_sound _ (by decide)

/-- The raw progress footprint corresponds exactly to these two typed writers. -/
theorem footprint (act : Act) :
    (spec [] whole "tick" "close").contributes act ↔ (act.addr == 11 || act.addr == 23) = true := by
  simp [spec,StateAuthoredBindings.contributes,whole,first,second,closer,note,beq_iff_eq] <;> omega

/-- Actual semantic fault-freeze health follows from the executable conflict
checker, not from an assumed locality result or chosen healthy root. -/
theorem healthy : freezeFault (fun act => act ∈ whole) "close" (spec [] whole "tick" "close").contributes true none whole = none := by
  classical
  have empty : (StateExecutableFreeze.conflicts whole "close" (fun act => act.addr == 11 || act.addr == 23) true).isEmpty = true := by decide
  have absent : ¬∃ a b, FreezeConflict (fun act => act ∈ whole) "close" (spec [] whole "tick" "close").contributes true whole a b := by
    rintro ⟨a,b,bad⟩
    have equivalent : FreezeConflict (fun act => act ∈ whole) "close" (fun act => (act.addr == 11 || act.addr == 23) = true) true whole a b := by
      cases bad with
      | concurrent left right different => exact .concurrent left right different
      | late first present contributes outside policy => exact .late first present ((footprint b).mp contributes) outside policy
    have conflict := (StateExecutableFreeze.has_conflict whole ranked "close" (fun act => act.addr == 11 || act.addr == 23) true).mpr ⟨a,b,equivalent⟩
    simp [empty] at conflict
  simp [freezeFault,absent]

/-- The actual exact cut omits unrelated evidence while retaining the chain. -/
theorem exact_cut : causalCut (fun act => act ∈ whole) whole closer = [first,second,closer] := by
  rw [← StateExecutableFreeze.cut_refinement whole ranked closer (by simp [whole])]
  decide

/-- Computed earlier success feeds the actual compiled closure output under any
optional fault-freeze declaration and any global dispatch metadata. -/
theorem compiled_preserves (base : StateKernelSEC.Context) (declaration : Option String)
    (freezes : List (String × FreezeSpec)) :
    let environment := StateAuthoredEventSumTests.environment {base with thread := 7,limit := fun _ => 3}
    let installed := {environment with context := context environment.context decode}
    let bare := StateInstalledCompiler.sourcePlan (StateInstalledTerm.source (StateInstalledDomains.term installed.context []
      (.progress "tick") (StateAuthoredBindings.resourceVerbs installed)))
    ∃ code, StateOutputCompiler.compileQuery [.element (.progress 2)]
      (StateAuthoredBindings.primitive installed [] (.progress "tick") (.progress "tick")) = some code ∧
      let output := (StateOutputCompiler.Output.threshold "done" "stage" code
        (decorate [] (StateScopePool.normalize whole) "tick" declaration bare)).observe whole freezes
      output = ("done",.data (.reached (.element (.progress 2)))) ∨ ∃ evidence, output = ("done",.fault evidence) := by
  intro environment installed bare
  have growth : ∀ act ∈ before, act ∈ whole := by
    intro act member
    simp only [before,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> simp [whole]
  have reached : 2 ≤ protocolProgress (store decode before) environment.context.thread "tick" (environment.context.limit "tick") before := by
    change 2 ≤ protocolProgress (store decode before) 7 "tick" 3 before
    rw [before_progress]
    exact Nat.le_refl _
  exact success_or_fault environment decode [] "tick" 2 (by decide) coherent before whole growth
    (fun _ ha _ hb eq => unique.eq_of_addr ha hb eq) reached "stage" "done" declaration freezes

end CBCL.StateProgressFreezeTests
