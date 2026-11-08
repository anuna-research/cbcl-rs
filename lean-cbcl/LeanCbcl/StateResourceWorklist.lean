import LeanCbcl.StateResourceCoupling

/-! Coupled executable native budget worklist. Its environment is recognized
by the actual executable phase checks; joint cache/readiness invariants are
constructed from empty state. No resource classifier is provided by a caller. -/
namespace CBCL.StateResourceWorklist
open State CheckpointEvidence StateResource StateResourceNative StateResourceSummary StateResourceCache
open StateResourceStructure StateResourceFrontier StateResourceDependency StateResourceLocalBudget StateResourceWitness
open StateResourceMachine StateResourceAuthorization StateResourceCoupling

/-- The checked resource configuration and dependency graph used by the worklist. -/
structure Environment where
  /-- The installed resource configuration. -/
  config : ResourceConfig
  /-- The accepted resource opener. -/
  opener : ResourceFact
  /-- The accepted thread root. -/
  root : ResourceFact
  /-- The recognized resource operation facts. -/
  known : Facts
  unique : (known.map Fact.id).Nodup
  initialization : initializationCheck config opener root = true
  operationsCheck : known.all (operationCheck config opener root) = true
  forks : forkCheck known = true
  foreign : previousOwnerCheck opener.id known = true
  excludesOpener : ∀ entry ∈ known, entry.id ≠ opener.id
  structural : StateResourceKahn.nativeKahn (StateResourceCycle.parents known) known = []
  sliceBound : known.length ≤ 2^63 - 1

namespace Environment

theorem operations (e : Environment) : ∀ entry ∈ e.known, validOperation e.config e.opener e.root entry :=
  fun entry member => (operationCheck_iff _ _ _ _).mp ((List.all_eq_true.mp e.operationsCheck) entry member)

theorem initialValid (e : Environment) : validInitial e.config e.opener e.root :=
  (initializationCheck_iff _ _ _).mp e.initialization

theorem nonforking (e : Environment) : Nonforking e.known :=
  (forkCheck_iff e.known (unique_ids_consistent e.known e.unique)).mp e.forks

theorem uniqueParents (e : Environment) : ∀ address ∈ e.known.map Fact.id,
    (StateResourceGraph.parents e.opener e.known address).Nodup :=
  StateResourceGraph.native_parent_lists_unique e.config e.opener e.root e.known e.unique e.operations

end Environment

/-- Every processed operation passed its exact-cone budget check. -/
def Authorized (e : Environment) (worklist : StateResourceCounters.Worklist) : Prop :=
  ∀ node ∈ e.known, node.id ∈ worklist.processed → ¬BudgetWitness e.config e.opener node e.known

/-- The coupled worklist, machine, and ghost invariants. -/
structure Joint (e : Environment) (worklist : StateResourceCounters.Worklist) (machine : Machine) (ghost : Ghost) : Prop where
  counters : StateResourceCounters.Invariant (e.known.map Fact.id) (StateResourceGraph.parents e.opener e.known) worklist
  cache : StateResourceMachine.Invariant e.opener e.known machine ghost
  coupled : Coupled worklist machine
  authorized : Authorized e worklist
  processedUnique : worklist.processed.Nodup
  processedKnown : worklist.processed ⊆ e.known.map Fact.id

/-- The initialized native resource budget worklist. -/
def initialWorklist (e : Environment) : StateResourceCounters.Worklist :=
  StateResourceCounters.initWorklist (e.known.map Fact.id) (StateResourceGraph.parents e.opener e.known)

theorem initial_joint (e : Environment) : Joint e (initialWorklist e) StateResourceMachine.initial initialGhost := by
  refine ⟨StateResourceCounters.initialize_invariant _ _,initial_invariant _ _,initial_coupled _ _,?_,?_,?_⟩
  · intro node _ member; contradiction
  · simp [initialWorklist,StateResourceCounters.initWorklist]
  · intro node member; contradiction

theorem done_authorized (e : Environment) (node : ResourceFact) (worklist : StateResourceCounters.Worklist)
    (machine next : Machine) (ghost after : Ghost) (invariant : Joint e worklist machine ghost)
    (accepted : node ∈ e.known) (ready : worklist.ready node.id = true)
    (success : checkedStep e.config e.opener node e.known machine ghost = .done next after) :
    ¬BudgetWitness e.config e.opener node e.known := by
  obtain ⟨parents,own,lookups,previous⟩ := ready_lookups e.config e.opener e.root node e.known worklist machine ghost
    invariant.counters invariant.cache invariant.coupled e.unique accepted (e.operations node accepted) ready
  have fresh := ready_fresh e.opener node e.known worklist machine invariant.counters invariant.coupled accepted ready
  have good : nativeBudgetCheck e.config e.opener node own machine.summaries (mergedTips machine.summaries machine.tips parents) = true := by
    cases decision : nativeBudgetCheck e.config e.opener node own machine.summaries (mergedTips machine.summaries machine.tips parents) with
    | false => simp [checkedStep,lookups,previous,decision] at success
    | true => rfl
  have correspondence := native_budget_certificate_iff e.config e.opener e.root node e.known own machine.summaries
    ghost.cones machine.tips ghost.prefixes parents invariant.cache.parents invariant.cache.summaries invariant.cache.ownTips
    lookups previous e.nonforking accepted e.unique e.foreign
    (fresh_excludes_parent_cones e.opener node e.known machine ghost invariant.cache fresh parents lookups)
    e.initialValid e.operations e.excludesOpener e.structural e.sliceBound
  intro witness
  have bad := correspondence.mpr witness
  rw [good] at bad
  contradiction

/-- A successfully authorized queue pop preserves cache, queue and authorization
invariants together. The newly processed operation is free of budget witnesses. -/
theorem done_joint (e : Environment) (node : ResourceFact) (worklist : StateResourceCounters.Worklist)
    (machine next : Machine) (ghost after : Ghost) (invariant : Joint e worklist machine ghost)
    (accepted : node ∈ e.known) (ready : worklist.ready node.id = true)
    (success : checkedStep e.config e.opener node e.known machine ghost = .done next after) :
    Joint e (StateResourceCounters.pop worklist node.id) next after := by
  have recorded := checkedStep_done_record e.config e.opener node e.known machine next ghost after success
  have fresh := ready_fresh e.opener node e.known worklist machine invariant.counters invariant.coupled accepted ready
  refine ⟨StateResourceCounters.pop_invariant _ _ worklist node.id invariant.counters e.unique e.uniqueParents
      (List.mem_map.mpr ⟨node,accepted,rfl⟩) ready,
    recordStep_invariant e.opener node e.known machine next ghost after invariant.cache fresh e.nonforking accepted e.unique e.foreign e.structural recorded,
    coupled_after_record e.opener node e.known worklist machine next ghost after invariant.coupled recorded,?_,?_,?_⟩
  · intro entry member released
    rcases List.mem_cons.mp released with same | old
    · have equal := unique_ids_consistent e.known e.unique entry member node accepted same
      subst entry
      exact done_authorized e node worklist machine next ghost after invariant accepted ready success
    · exact invariant.authorized entry member old
  · exact List.nodup_cons.mpr ⟨((invariant.counters.readiness node.id (List.mem_map.mpr ⟨node,accepted,rfl⟩)).mp ready).1,invariant.processedUnique⟩
  · intro address member
    rcases List.mem_cons.mp member with rfl | old
    · exact List.mem_map.mpr ⟨node,accepted,rfl⟩
    · exact invariant.processedKnown old


/-- A native worklist result, either a budget fault or a completed traversal. -/
inductive Outcome where
  | complete (worklist : StateResourceCounters.Worklist) (machine : Machine) (ghost : Ghost)
  | fault (node : ResourceFact) (worklist : StateResourceCounters.Worklist) (machine : Machine) (ghost : Ghost)
  | internalError

/-- Run at most the supplied number of worklist steps. -/
def runFuel (e : Environment) : Nat → StateResourceCounters.Worklist → Machine → Ghost → Outcome
  | 0,worklist,machine,ghost => .complete worklist machine ghost
  | fuel+1,worklist,machine,ghost =>
    match e.known.find? (fun node => worklist.ready node.id) with
    | none => .complete worklist machine ghost
    | some node => match checkedStep e.config e.opener node e.known machine ghost with
      | .done next after => runFuel e fuel (StateResourceCounters.pop worklist node.id) next after
      | .budgetFault bad mid annotations => .fault bad worklist mid annotations
      | .blocked _ _ _ | .recordFault _ _ _ => .internalError

/-- An execution outcome with its maintained worklist invariants. -/
def Verified (e : Environment) : Outcome → Prop
  | .complete worklist machine ghost => Joint e worklist machine ghost ∧
      StateResourceCounters.Saturated (e.known.map Fact.id) worklist
  | .fault node worklist machine ghost => Joint e worklist machine ghost ∧ BudgetWitness e.config e.opener node e.known
  | .internalError => False

/-- Full interleaved executable counter/authorization/cache traversal. A queue
selection cannot be blocked or suffer record overflow; every actual fault has
a concrete accepted budget witness, and normal completion is saturated. -/
theorem runFuel_verified (e : Environment) (fuel : Nat) (worklist : StateResourceCounters.Worklist)
    (machine : Machine) (ghost : Ghost) (invariant : Joint e worklist machine ghost)
    (enough : e.known.length ≤ fuel + worklist.processed.length) :
    Verified e (runFuel e fuel worklist machine ghost) := by
  induction fuel generalizing worklist machine ghost with
  | zero =>
    refine ⟨invariant,?_⟩
    intro address member
    obtain ⟨node,accepted,rfl⟩ := List.mem_map.mp member
    cases selected : worklist.ready node.id with
    | false => rfl
    | true =>
      have fresh := ((invariant.counters.readiness node.id (List.mem_map.mpr ⟨node,accepted,rfl⟩)).mp selected).1
      have extended : (node.id :: worklist.processed).Nodup := List.nodup_cons.mpr ⟨fresh,invariant.processedUnique⟩
      have subset : node.id :: worklist.processed ⊆ e.known.map Fact.id := by
        intro address member
        rcases List.mem_cons.mp member with rfl | old
        · exact List.mem_map.mpr ⟨node,accepted,rfl⟩
        · exact invariant.processedKnown old
      have length := (List.subperm_of_subset extended subset).length_le
      simp only [List.length_cons,List.length_map] at length
      omega
  | succ fuel ih =>
    simp only [runFuel]
    cases selected : e.known.find? (fun node => worklist.ready node.id) with
    | none =>
      refine ⟨invariant,?_⟩
      intro address member
      obtain ⟨node,accepted,rfl⟩ := List.mem_map.mp member
      cases ready : worklist.ready node.id with
      | false => rfl
      | true => exact False.elim (List.find?_eq_none.mp selected node accepted ready)
    | some node =>
      dsimp only
      have accepted := List.mem_of_find?_eq_some selected
      have ready := List.find?_some selected
      have fresh := ready_fresh e.opener node e.known worklist machine invariant.counters invariant.coupled accepted ready
      have safe := checkedStep_safe e.config e.opener e.root node e.known machine ghost invariant.cache fresh accepted
        e.nonforking e.unique e.foreign e.initialValid e.operations e.excludesOpener e.structural e.sliceBound
      cases step : checkedStep e.config e.opener node e.known machine ghost with
      | done next after =>
        apply ih (StateResourceCounters.pop worklist node.id) next after (done_joint e node worklist machine next ghost after invariant accepted ready step)
        change e.known.length ≤ fuel + (node.id :: worklist.processed).length
        simp only [List.length_cons]
        omega
      | budgetFault bad mid annotations =>
        obtain ⟨badEqual,machineEqual,ghostEqual⟩ := checkedStep_budget_identity e.config e.opener node bad e.known machine mid ghost annotations step
        subst bad; subst mid; subst annotations
        exact ⟨invariant,checkedStep_budget_certificate e.config e.opener e.root node e.known machine ghost invariant.cache fresh accepted
          e.nonforking e.unique e.foreign e.initialValid e.operations e.excludesOpener e.structural e.sliceBound step⟩
      | blocked bad mid annotations =>
        exact False.elim (ready_not_blocked e.config e.opener e.root node e.known worklist machine ghost invariant.counters
          invariant.cache invariant.coupled e.unique accepted (e.operations node accepted) ready bad mid annotations step)
      | recordFault bad mid annotations =>
        have impossible : False := by simpa [step,SafeResult] using safe
        exact False.elim impossible

/-- Execute the native budget worklist using its accepted-node fuel bound. -/
def run (e : Environment) : Outcome :=
  runFuel e e.known.length (initialWorklist e) StateResourceMachine.initial initialGhost

theorem native_worklist_verified (e : Environment) : Verified e (run e) :=
  runFuel_verified e e.known.length (initialWorklist e) StateResourceMachine.initial initialGhost (initial_joint e)
    (by simp [initialWorklist,StateResourceCounters.initWorklist])


theorem closed_cone_processed (e : Environment) (worklist : StateResourceCounters.Worklist)
    (machine : Machine) (ghost : Ghost) (invariant : Joint e worklist machine ghost)
    (saturated : StateResourceCounters.Saturated (e.known.map Fact.id) worklist)
    (node : ResourceFact) (cone : Facts) (exactCone : ExactCone e.opener node cone) (inside : Included cone e.known) :
    ∀ entry ∈ cone, entry.id ∈ worklist.processed := by
  have uniqueKnown : e.known.Nodup := List.Pairwise.of_map Fact.id (fun _ _ ne eq => ne (congrArg Fact.id eq)) e.unique
  have identities := unique_ids_consistent e.known e.unique
  obtain ⟨rank,lower⟩ := StateResourceKahn.nativeKahn_rank (StateResourceCycle.parents e.known) e.known uniqueKnown e.structural
  let processed := e.known.filter (fun entry => worklist.processed.contains entry.id)
  have closed : ∀ entry ∈ cone, ∀ parent ∈ StateResourceCycle.parents e.known entry, parent ∈ cone := by
    intro entry member parent edge
    have relation := (StateResourceCycle.parent_iff e.known entry parent).mp edge
    rcases exactCone.2.2.1 entry member parent.id relation.2 with opener | ⟨actual,ha,equal⟩
    · exact False.elim (e.excludesOpener parent relation.1 opener)
    · have same := identities parent relation.1 actual (inside actual ha) equal.symm
      simpa [same] using ha
  have complete : cone ⊆ processed := by
    apply StateResourceKahn.closed_component_processed (parents := StateResourceCycle.parents e.known)
      (nodes := cone) (component := cone) (processed := processed) (fun _ member => member) rank closed
    · intro child hc parent edge
      have parentInside := closed child hc parent edge
      exact lower child (inside child hc) parent (inside parent parentInside) edge
    · intro child hc prior
      have released : ∀ address ∈ StateResourceGraph.parents e.opener e.known child.id, address ∈ worklist.processed := by
        intro address member
        rw [StateResourceGraph.parents_known e.opener e.known e.unique child (inside child hc)] at member
        have selected := List.mem_filter.mp member
        rcases exactCone.2.2.1 child hc address selected.1 with root | ⟨parent,hp,equal⟩
        · have notRoot : address ≠ e.opener.id := by simpa using selected.2
          exact False.elim (notRoot root)
        · have edge : parent ∈ StateResourceCycle.parents e.known child :=
            (StateResourceCycle.parent_iff e.known child parent).mpr ⟨inside parent hp,by simpa [equal] using selected.1⟩
          have completed := List.mem_filter.mp (prior parent edge)
          have present : parent.id ∈ worklist.processed := by simpa using completed.2
          simpa [equal] using present
      have ready := StateResourceCounters.saturated_processes_ready (e.known.map Fact.id)
        (StateResourceGraph.parents e.opener e.known) worklist invariant.counters saturated child.id
        (List.mem_map.mpr ⟨child,inside child hc,rfl⟩) released
      exact List.mem_filter.mpr ⟨inside child hc,by simpa using ready⟩
  intro entry member
  have selected := List.mem_filter.mp (complete member)
  simpa using selected.2

/-- Test whether a resource read or traversal result is faulted. -/
def isFault : Outcome → Bool
  | .fault _ _ _ _ => true
  | _ => false

/-- Top-level budget worklist equivalence. A finite supported witness cannot
be hidden by an unrelated missing-reference component. The worklist computes
its queue, caches and cones; no saturation, rank or prefix oracle is a premise. -/
theorem native_budget_worklist_certificate_iff (e : Environment) :
    isFault (run e) = true ↔ ∃ node, BudgetWitness e.config e.opener node e.known := by
  have verified := native_worklist_verified e
  cases result : run e with
  | internalError => simp [result,Verified] at verified
  | fault node worklist machine ghost =>
    have current : Joint e worklist machine ghost ∧ BudgetWitness e.config e.opener node e.known := by
      simpa [result,Verified] using verified
    have witness := current.2
    constructor
    · intro _; exact ⟨node,witness⟩
    · intro _; rfl
  | complete worklist machine ghost =>
    have complete : Joint e worklist machine ghost ∧ StateResourceCounters.Saturated (e.known.map Fact.id) worklist := by
      simpa [result,Verified] using verified
    constructor
    · intro impossible; contradiction
    · rintro ⟨node,witness⟩
      have savedWitness := witness
      obtain ⟨cone,inside,exactCone,_⟩ := witness
      have accepted := inside node exactCone.1
      have processed := closed_cone_processed e worklist machine ghost complete.1 complete.2 node cone exactCone inside node exactCone.1
      exact False.elim (complete.1.authorized node accepted processed savedWitness)

end CBCL.StateResourceWorklist
