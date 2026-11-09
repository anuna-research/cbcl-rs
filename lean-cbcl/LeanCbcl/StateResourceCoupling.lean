import LeanCbcl.StateResourceAuthorization
import LeanCbcl.StateResourceGraph

/-! Coupling native mutable readiness counters to the budget/summary machine.
A released first-pass identity exists iff it has an actual cached summary; the
structural missing-reference release phase is deliberately separate. -/
namespace CBCL.StateResourceCoupling
open State CheckpointEvidence StateResource StateResourceSummary StateResourceCache StateResourceStructure
open StateResourceMachine StateResourceFrontier StateResourceDependency StateResourceAuthorization StateResourceLocalBudget

/-- The resource worklist and erased native machine advance together. -/
def Coupled (worklist : StateResourceCounters.Worklist) (machine : Machine) : Prop :=
  ∀ address, (∃ node summary, machine.summaries address = some (node,summary)) ↔ address ∈ worklist.processed

theorem initial_coupled (op : ResourceFact) (known : Facts) :
    Coupled (StateResourceCounters.initWorklist (known.map Fact.id) (StateResourceGraph.parents op known)) initial := by
  intro address
  simp [StateResourceCounters.initWorklist,StateResourceMachine.initial,emptyCache]

theorem gather_available (op : ResourceFact) (cones : StateResourceCones.ConeCache) (references : List Nat)
    (available : ∀ address ∈ references, address = op.id ∨ ∃ node cone, cones address = some (node,cone)) :
    ∃ entries, StateResourceCones.gather op cones references = some entries := by
  induction references with
  | nil => exact ⟨[],rfl⟩
  | cons address rest ih =>
    obtain ⟨later,tail⟩ := ih (fun id member => available id (by simp [member]))
    by_cases root : address = op.id
    · exact ⟨later,by simp [StateResourceCones.gather,root,tail]⟩
    · rcases available address (by simp) with isRoot | ⟨node,cone,cached⟩
      · exact False.elim (root isRoot)
      · exact ⟨(node,cone) :: later,by simp [StateResourceCones.gather,root,cached,tail]⟩

/-- Native zero counters supply all actual parent-cache and previous-summary
lookups. No caller postulates that the chosen operation has a closed cone. -/
theorem ready_lookups (c : ResourceConfig) (op root node : ResourceFact) (known : Facts)
    (worklist : StateResourceCounters.Worklist) (machine : Machine) (ghost : Ghost)
    (counterInv : StateResourceCounters.Invariant (known.map Fact.id) (StateResourceGraph.parents op known) worklist)
    (machineInv : Invariant op known machine ghost) (coupled : Coupled worklist machine)
    (unique : (known.map Fact.id).Nodup) (accepted : node ∈ known) (valid : validOperation c op root node)
    (ready : worklist.ready node.id = true) :
    ∃ parents own, StateResourceCones.gather op ghost.cones (links node) = some parents ∧
      previousSummary op.id machine.summaries node = some own := by
  have knownId : node.id ∈ known.map Fact.id := List.mem_map.mpr ⟨node,accepted,rfl⟩
  have selected := (counterInv.readiness node.id knownId).mp ready
  have zero := (counterInv.counters node.id knownId).symm.trans selected.2
  have released := (StateResourceCounters.zero_count_ready _ worklist.processed).mp zero
  have allAvailable : ∀ address ∈ links node, address = op.id ∨
      ∃ entry summary, machine.summaries address = some (entry,summary) := by
    intro address edge
    by_cases root : address = op.id
    · exact Or.inl root
    · have dependency : address ∈ StateResourceGraph.parents op known node.id := by
        rw [StateResourceGraph.parents_known op known unique node accepted]
        exact List.mem_filter.mpr ⟨edge,by simpa using root⟩
      exact Or.inr ((coupled address).mpr (released address dependency))
  have coneAvailable : ∀ address ∈ links node, address = op.id ∨
      ∃ entry cone, ghost.cones address = some (entry,cone) := by
    intro address edge
    rcases allAvailable address edge with root | ⟨entry,summary,cached⟩
    · exact Or.inl root
    · obtain ⟨cone,found⟩ := machineInv.paired address entry summary cached
      exact Or.inr ⟨entry,cone,found⟩
  obtain ⟨parents,lookups⟩ := gather_available op ghost.cones (links node) coneAvailable
  have hasPrevious : node.data.prev.isSome := valid.2.2.2.2.2.2.2.2.2.1
  cases previous : node.data.prev with
  | none => simp [previous] at hasPrevious
  | some address =>
    have edge : address ∈ links node := by simp [links,previous]
    rcases allAvailable address edge with root | ⟨entry,summary,cached⟩
    · exact ⟨parents,empty,lookups,by simp [previousSummary,previous,root]⟩
    · by_cases root : address = op.id
      · exact ⟨parents,empty,lookups,by simp [previousSummary,previous,root]⟩
      · exact ⟨parents,summary,lookups,by simp [previousSummary,previous,root,cached]⟩

theorem ready_fresh (op node : ResourceFact) (known : Facts)
    (worklist : StateResourceCounters.Worklist) (machine : Machine)
    (counterInv : StateResourceCounters.Invariant (known.map Fact.id) (StateResourceGraph.parents op known) worklist)
    (coupled : Coupled worklist machine) (accepted : node ∈ known) (ready : worklist.ready node.id = true) :
    machine.summaries node.id = none := by
  have fresh := ((counterInv.readiness node.id (List.mem_map.mpr ⟨node,accepted,rfl⟩)).mp ready).1
  cases cached : machine.summaries node.id with
  | none => rfl
  | some pair =>
    obtain ⟨entry,summary⟩ := pair
    exact False.elim (fresh ((coupled node.id).mp ⟨entry,summary,cached⟩))


/-- The newly recorded summary is exactly the newly released counter identity;
all older identities retain the same cache presence. -/
theorem coupled_after_record (op node : ResourceFact) (known : Facts)
    (worklist : StateResourceCounters.Worklist) (machine next : Machine) (ghost after : Ghost)
    (coupled : Coupled worklist machine)
    (success : recordStep op node known machine ghost = some (next,after)) :
    Coupled (StateResourceCounters.pop worklist node.id) next := by
  cases lookups : StateResourceCones.gather op ghost.cones (links node) with
  | none => simp [recordStep,lookups] at success
  | some parents =>
    cases previous : previousSummary op.id machine.summaries node with
    | none => simp [recordStep,lookups,previous] at success
    | some own =>
      cases recorded : record own node with
      | none => simp [recordStep,lookups,previous,recorded] at success
      | some updated =>
        have shape : recordResult node known machine ghost parents updated = (next,after) := by
          simpa [recordStep,lookups,previous,recorded] using success
        intro address
        have cacheShape := congrArg (fun pair : Machine × Ghost => pair.1.summaries address) shape
        by_cases current : address = node.id
        · subst address
          constructor
          · intro _; simp [StateResourceCounters.pop]
          · intro _
            exact ⟨node,updated,by simpa [recordResult] using cacheShape.symm⟩
        · have same : next.summaries address = machine.summaries address := by
            simpa [recordResult,current] using cacheShape.symm
          simpa [same,StateResourceCounters.pop,current] using coupled address

/-- Ready queue selections cannot yield the blocked outcome: all references
have real paired caches, not merely counters manufactured by structural release. -/
theorem ready_not_blocked (c : ResourceConfig) (op root node : ResourceFact) (known : Facts)
    (worklist : StateResourceCounters.Worklist) (machine : Machine) (ghost : Ghost)
    (counterInv : StateResourceCounters.Invariant (known.map Fact.id) (StateResourceGraph.parents op known) worklist)
    (machineInv : Invariant op known machine ghost) (coupled : Coupled worklist machine)
    (unique : (known.map Fact.id).Nodup) (accepted : node ∈ known) (valid : validOperation c op root node)
    (ready : worklist.ready node.id = true) :
    ∀ bad mid annotations, checkedStep c op node known machine ghost ≠ .blocked bad mid annotations := by
  obtain ⟨parents,own,lookups,previous⟩ := ready_lookups c op root node known worklist machine ghost counterInv machineInv coupled unique accepted valid ready
  intro bad mid annotations
  cases decision : nativeBudgetCheck c op node own machine.summaries (mergedTips machine.summaries machine.tips parents) with
  | false => simp [checkedStep,lookups,previous,decision]
  | true =>
    cases recorded : recordStep op node known machine ghost with
    | none => simp [checkedStep,lookups,previous,decision,recorded]
    | some pair => obtain ⟨next,after⟩ := pair; simp [checkedStep,lookups,previous,decision,recorded]

end CBCL.StateResourceCoupling
