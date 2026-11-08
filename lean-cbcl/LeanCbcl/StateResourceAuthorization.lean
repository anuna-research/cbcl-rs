import LeanCbcl.StateResourceMachine
import LeanCbcl.StateResourceRecordBounds

/-! Faulting native budget/record phase. Authorization happens before the
record transition. Budget failures are connected to concrete accepted witnesses;
missing-parent and record-failure branches remain distinct outcomes. -/
namespace CBCL.StateResourceAuthorization
open State CheckpointEvidence StateResource StateResourceSummary StateResourceCache StateResourceStructure
open StateResourceFrontier StateResourceDependency StateResourceOwnPrefix StateResourceLocalBudget StateResourceWitness
open StateResourceMachine

inductive Result where
  | done (machine : Machine) (ghost : Ghost)
  | blocked (node : ResourceFact) (machine : Machine) (ghost : Ghost)
  | budgetFault (node : ResourceFact) (machine : Machine) (ghost : Ghost)
  | recordFault (node : ResourceFact) (machine : Machine) (ghost : Ghost)

def checkedStep (c : ResourceConfig) (op node : ResourceFact) (known : Facts) (machine : Machine) (ghost : Ghost) : Result :=
  match StateResourceCones.gather op ghost.cones (links node), previousSummary op.id machine.summaries node with
  | some parents,some own =>
    if nativeBudgetCheck c op node own machine.summaries (mergedTips machine.summaries machine.tips parents) then
      match recordStep op node known machine ghost with
      | some (next,after) => .done next after
      | none => .recordFault node machine ghost
    else .budgetFault node machine ghost
  | _,_ => .blocked node machine ghost

theorem checkedStep_done_record (c : ResourceConfig) (op node : ResourceFact) (known : Facts)
    (machine next : Machine) (ghost after : Ghost)
    (success : checkedStep c op node known machine ghost = .done next after) :
    recordStep op node known machine ghost = some (next,after) := by
  cases lookups : StateResourceCones.gather op ghost.cones (links node) with
  | none => simp [checkedStep,lookups] at success
  | some parents =>
    cases previous : previousSummary op.id machine.summaries node with
    | none => simp [checkedStep,lookups,previous] at success
    | some own =>
      cases decision : nativeBudgetCheck c op node own machine.summaries (mergedTips machine.summaries machine.tips parents) with
      | false => simp [checkedStep,lookups,previous,decision] at success
      | true =>
        cases recorded : recordStep op node known machine ghost with
        | none => simp [checkedStep,lookups,previous,decision,recorded] at success
        | some pair =>
          obtain ⟨mid,annotations⟩ := pair
          have same : mid = next ∧ annotations = after := by simpa [checkedStep,lookups,previous,decision,recorded] using success
          obtain ⟨rfl,rfl⟩ := same
          rfl

theorem checkedStep_budget_fault (c : ResourceConfig) (op node : ResourceFact) (known : Facts)
    (machine : Machine) (ghost : Ghost)
    (failure : checkedStep c op node known machine ghost = .budgetFault node machine ghost) :
    ∃ parents own, StateResourceCones.gather op ghost.cones (links node) = some parents ∧
      previousSummary op.id machine.summaries node = some own ∧
      nativeBudgetCheck c op node own machine.summaries (mergedTips machine.summaries machine.tips parents) = false := by
  cases lookups : StateResourceCones.gather op ghost.cones (links node) with
  | none => simp [checkedStep,lookups] at failure
  | some parents =>
    cases previous : previousSummary op.id machine.summaries node with
    | none => simp [checkedStep,lookups,previous] at failure
    | some own =>
      cases decision : nativeBudgetCheck c op node own machine.summaries (mergedTips machine.summaries machine.tips parents) with
      | false => exact ⟨parents,own,rfl,rfl,decision⟩
      | true =>
        cases recorded : recordStep op node known machine ghost with
        | none => simp [checkedStep,lookups,previous,decision,recorded] at failure
        | some pair => obtain ⟨next,after⟩ := pair; simp [checkedStep,lookups,previous,decision,recorded] at failure

/-- A rejected native budget step, with the joint machine invariant maintained
by the whole record traversal, supplies an accepted finite certificate. -/
theorem checkedStep_budget_certificate (c : ResourceConfig) (op root node : ResourceFact) (known : Facts)
    (machine : Machine) (ghost : Ghost) (invariant : Invariant op known machine ghost)
    (fresh : machine.summaries node.id = none) (accepted : node ∈ known)
    (nonforking : Nonforking known) (unique : (known.map Fact.id).Nodup)
    (foreignChecked : previousOwnerCheck op.id known = true)
    (initial : validInitial c op root) (operations : ∀ entry ∈ known, validOperation c op root entry)
    (excludesOpener : ∀ entry ∈ known, entry.id ≠ op.id)
    (structural : StateResourceKahn.nativeKahn (StateResourceCycle.parents known) known = [])
    (sliceBound : known.length ≤ 2^63 - 1)
    (failure : checkedStep c op node known machine ghost = .budgetFault node machine ghost) :
    BudgetWitness c op node known := by
  obtain ⟨parents,own,lookups,previous,rejected⟩ := checkedStep_budget_fault c op node known machine ghost failure
  exact (native_budget_certificate_iff c op root node known own machine.summaries ghost.cones machine.tips ghost.prefixes parents
    invariant.parents invariant.summaries invariant.ownTips lookups previous nonforking accepted unique foreignChecked
    (fresh_excludes_parent_cones op node known machine ghost invariant fresh parents lookups) initial operations excludesOpener
    structural sliceBound).mp rejected


def SafeResult (c : ResourceConfig) (op : ResourceFact) (known : Facts) : Result → Prop
  | .done machine ghost => Invariant op known machine ghost
  | .blocked _ machine ghost => Invariant op known machine ghost
  | .recordFault _ _ _ => False
  | .budgetFault node machine ghost => Invariant op known machine ghost ∧ BudgetWitness c op node known

theorem checkedStep_safe (c : ResourceConfig) (op root node : ResourceFact) (known : Facts)
    (machine : Machine) (ghost : Ghost) (invariant : Invariant op known machine ghost)
    (fresh : machine.summaries node.id = none) (accepted : node ∈ known)
    (nonforking : Nonforking known) (unique : (known.map Fact.id).Nodup)
    (foreignChecked : previousOwnerCheck op.id known = true)
    (initial : validInitial c op root) (operations : ∀ entry ∈ known, validOperation c op root entry)
    (excludesOpener : ∀ entry ∈ known, entry.id ≠ op.id)
    (structural : StateResourceKahn.nativeKahn (StateResourceCycle.parents known) known = [])
    (sliceBound : known.length ≤ 2^63 - 1) : SafeResult c op known (checkedStep c op node known machine ghost) := by
  cases lookups : StateResourceCones.gather op ghost.cones (links node) with
  | none => simpa [checkedStep,lookups,SafeResult] using invariant
  | some parents =>
    cases previous : previousSummary op.id machine.summaries node with
    | none => simpa [checkedStep,lookups,previous,SafeResult] using invariant
    | some own =>
      cases decision : nativeBudgetCheck c op node own machine.summaries (mergedTips machine.summaries machine.tips parents) with
      | false =>
        have failed : checkedStep c op node known machine ghost = .budgetFault node machine ghost := by
          simp [checkedStep,lookups,previous,decision]
        rw [failed]
        exact ⟨invariant,checkedStep_budget_certificate c op root node known machine ghost invariant fresh accepted nonforking
          unique foreignChecked initial operations excludesOpener structural sliceBound failed⟩
      | true =>
        cases recorded : recordStep op node known machine ghost with
        | none =>
          obtain ⟨updated,recordedOwn⟩ := StateResourceRecordBounds.machine_record_complete c op root node known machine ghost parents own
            invariant fresh lookups previous accepted unique nonforking foreignChecked structural operations sliceBound
          simp [recordStep,lookups,previous,recordedOwn] at recorded
        | some pair =>
          obtain ⟨next,after⟩ := pair
          have valid := recordStep_invariant op node known machine next ghost after invariant fresh nonforking accepted unique foreignChecked structural recorded
          simpa [checkedStep,lookups,previous,decision,recorded,SafeResult] using valid

def execute (c : ResourceConfig) (op : ResourceFact) (known : Facts) : Facts → Machine → Ghost → Result
  | [],machine,ghost => .done machine ghost
  | node :: rest,machine,ghost => match checkedStep c op node known machine ghost with
    | .done next after => execute c op known rest next after
    | stopped => stopped

/-- The entire faulting budget/record schedule, not just a supplied successful
prefix, preserves the joint invariant and certifies every budget rejection.
Blocked histories remain separate; recognized record failure is proved unreachable. -/
theorem execute_safe (c : ResourceConfig) (op root : ResourceFact) (known schedule : Facts)
    (machine : Machine) (ghost : Ghost) (invariant : Invariant op known machine ghost)
    (absent : Absent schedule machine) (scheduleUnique : (schedule.map Fact.id).Nodup) (scheduled : schedule ⊆ known)
    (nonforking : Nonforking known) (unique : (known.map Fact.id).Nodup)
    (foreignChecked : previousOwnerCheck op.id known = true)
    (initial : validInitial c op root) (operations : ∀ entry ∈ known, validOperation c op root entry)
    (excludesOpener : ∀ entry ∈ known, entry.id ≠ op.id)
    (structural : StateResourceKahn.nativeKahn (StateResourceCycle.parents known) known = [])
    (sliceBound : known.length ≤ 2^63 - 1) : SafeResult c op known (execute c op known schedule machine ghost) := by
  induction schedule generalizing machine ghost with
  | nil => exact invariant
  | cons node rest ih =>
    have fresh := absent node (by simp)
    have accepted := scheduled (by simp : node ∈ node :: rest)
    have stepSafe := checkedStep_safe c op root node known machine ghost invariant fresh accepted nonforking unique foreignChecked
      initial operations excludesOpener structural sliceBound
    obtain ⟨notIn,uniqueRest⟩ := List.nodup_cons.mp scheduleUnique
    cases step : checkedStep c op node known machine ghost with
    | blocked bad mid annotations => simpa [execute,step] using stepSafe
    | budgetFault bad mid annotations => simpa [execute,step] using stepSafe
    | recordFault bad mid annotations => simpa [execute,step] using stepSafe
    | done mid annotations =>
      have recorded := checkedStep_done_record c op node known machine mid ghost annotations step
      have absentRest : Absent rest mid := by
        intro entry member
        have different : entry.id ≠ node.id := by
          intro equal
          exact notIn (List.mem_map.mpr ⟨entry,member,equal⟩)
        rw [recordStep_unchanged op node known machine mid ghost annotations recorded entry.id different]
        exact absent entry (by simp [member])
      have continued := ih mid annotations (by simpa [step,SafeResult] using stepSafe) absentRest uniqueRest
        (fun _ member => scheduled (by simp [member]))
      simpa [execute,step] using continued

/-- Empty-state whole faulting schedule: no caller supplies prefix, cone or
frontier invariants. Every budget-fault outcome carries a supported witness. -/
theorem native_budget_worklist_safe (c : ResourceConfig) (op root : ResourceFact) (known schedule : Facts)
    (scheduleUnique : (schedule.map Fact.id).Nodup) (scheduled : schedule ⊆ known)
    (nonforking : Nonforking known) (unique : (known.map Fact.id).Nodup)
    (foreignChecked : previousOwnerCheck op.id known = true)
    (initialValid : validInitial c op root) (operations : ∀ entry ∈ known, validOperation c op root entry)
    (excludesOpener : ∀ entry ∈ known, entry.id ≠ op.id)
    (structural : StateResourceKahn.nativeKahn (StateResourceCycle.parents known) known = [])
    (sliceBound : known.length ≤ 2^63 - 1) :
    SafeResult c op known (execute c op known schedule StateResourceMachine.initial initialGhost) :=
  execute_safe c op root known schedule StateResourceMachine.initial initialGhost (initial_invariant op known)
    (by intro _ _; rfl) scheduleUnique scheduled nonforking unique foreignChecked initialValid operations excludesOpener structural sliceBound


theorem checkedStep_budget_identity (c : ResourceConfig) (op node bad : ResourceFact) (known : Facts)
    (machine mid : Machine) (ghost annotations : Ghost)
    (failure : checkedStep c op node known machine ghost = .budgetFault bad mid annotations) :
    node = bad ∧ machine = mid ∧ ghost = annotations := by
  cases lookups : StateResourceCones.gather op ghost.cones (links node) with
  | none => simp [checkedStep,lookups] at failure
  | some parents =>
    cases previous : previousSummary op.id machine.summaries node with
    | none => simp [checkedStep,lookups,previous] at failure
    | some own =>
      cases decision : nativeBudgetCheck c op node own machine.summaries (mergedTips machine.summaries machine.tips parents) with
      | false => simpa [checkedStep,lookups,previous,decision] using failure
      | true =>
        cases recorded : recordStep op node known machine ghost with
        | none => simp [checkedStep,lookups,previous,decision,recorded] at failure
        | some pair => obtain ⟨next,after⟩ := pair; simp [checkedStep,lookups,previous,decision,recorded] at failure

end CBCL.StateResourceAuthorization
