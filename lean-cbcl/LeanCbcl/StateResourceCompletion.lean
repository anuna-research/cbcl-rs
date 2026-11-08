import LeanCbcl.StateResourceValidated

/-! Native completion depends on exact dependency closure, not processing
order. This characterizes ready versus pending after a fault-free worklist and
is the successful-resource display bridge's scheduling component. -/
namespace CBCL.StateResourceCompletion
open State CheckpointEvidence StateResource StateResourceWorklist StateResourceMachine

/-- Every dependency of a recognized operation is the opener or another recognized operation. -/
def ClosedKnown (e : Environment) : Prop :=
  ∀ node ∈ e.known, ∀ address ∈ links node, address = e.opener.id ∨ ∃ parent ∈ e.known, parent.id = address

theorem closed_known_processed (e : Environment) (worklist : StateResourceCounters.Worklist)
    (machine : Machine) (ghost : Ghost) (invariant : Joint e worklist machine ghost)
    (saturated : StateResourceCounters.Saturated (e.known.map Fact.id) worklist)
    (closed : ClosedKnown e) : ∀ node ∈ e.known, node.id ∈ worklist.processed := by
  have uniqueKnown : e.known.Nodup := List.Pairwise.of_map Fact.id (fun _ _ ne eq => ne (congrArg Fact.id eq)) e.unique
  obtain ⟨rank,lower⟩ := StateResourceKahn.nativeKahn_rank (StateResourceCycle.parents e.known) e.known uniqueKnown e.structural
  let processed := e.known.filter (fun node => worklist.processed.contains node.id)
  have parentClosed : ∀ child ∈ e.known, ∀ parent ∈ StateResourceCycle.parents e.known child, parent ∈ e.known := by
    intro child hc parent edge
    exact ((StateResourceCycle.parent_iff e.known child parent).mp edge).1
  have complete : e.known ⊆ processed := by
    apply StateResourceKahn.closed_component_processed (parents := StateResourceCycle.parents e.known)
      (nodes := e.known) (component := e.known) (processed := processed) (fun _ member => member) rank parentClosed
    · intro child hc parent edge
      exact lower child hc parent (parentClosed child hc parent edge) edge
    · intro child hc prior
      have released : ∀ address ∈ StateResourceGraph.parents e.opener e.known child.id, address ∈ worklist.processed := by
        intro address member
        rw [StateResourceGraph.parents_known e.opener e.known e.unique child hc] at member
        have selected := List.mem_filter.mp member
        rcases closed child hc address selected.1 with root | ⟨parent,hp,equal⟩
        · have notRoot : address ≠ e.opener.id := by simpa using selected.2
          exact False.elim (notRoot root)
        · have edge : parent ∈ StateResourceCycle.parents e.known child :=
            (StateResourceCycle.parent_iff e.known child parent).mpr ⟨hp,by simpa [equal] using selected.1⟩
          have completed := List.mem_filter.mp (prior parent edge)
          have present : parent.id ∈ worklist.processed := by simpa using completed.2
          simpa [equal] using present
      have ready := StateResourceCounters.saturated_processes_ready (e.known.map Fact.id)
        (StateResourceGraph.parents e.opener e.known) worklist invariant.counters saturated child.id
        (List.mem_map.mpr ⟨child,hc,rfl⟩) released
      exact List.mem_filter.mpr ⟨hc,by simpa using ready⟩
  intro node member
  exact of_decide_eq_true (by simpa using (List.mem_filter.mp (complete member)).2)

theorem all_processed_closed (e : Environment) (worklist : StateResourceCounters.Worklist)
    (machine : Machine) (ghost : Ghost) (invariant : Joint e worklist machine ghost)
    (allProcessed : ∀ node ∈ e.known, node.id ∈ worklist.processed) : ClosedKnown e := by
  intro node member address edge
  by_cases root : address = e.opener.id
  · exact Or.inl root
  · have parent : address ∈ StateResourceGraph.parents e.opener e.known node.id := by
      rw [StateResourceGraph.parents_known e.opener e.known e.unique node member]
      exact List.mem_filter.mpr ⟨edge,by simpa using root⟩
    have released := invariant.counters.closed node.id (allProcessed node member) address parent
    obtain ⟨entry,accepted,identity⟩ := List.mem_map.mp (invariant.processedKnown released)
    exact Or.inr ⟨entry,accepted,identity⟩

theorem saturated_size_iff_closed (e : Environment) (worklist : StateResourceCounters.Worklist)
    (machine : Machine) (ghost : Ghost) (invariant : Joint e worklist machine ghost)
    (saturated : StateResourceCounters.Saturated (e.known.map Fact.id) worklist) :
    worklist.processed.length = e.known.length ↔ ClosedKnown e := by
  constructor
  · intro size
    exact all_processed_closed e worklist machine ghost invariant
      (StateResourceSolvency.all_processed_of_size e worklist machine ghost invariant size)
  · intro closed
    have allProcessed := closed_known_processed e worklist machine ghost invariant saturated closed
    have permutation : worklist.processed.Perm (e.known.map Fact.id) :=
      (List.perm_ext_iff_of_nodup invariant.processedUnique e.unique).mpr (fun address => ⟨fun member => invariant.processedKnown member,
        fun member => by obtain ⟨node,inside,rfl⟩ := List.mem_map.mp member; exact allProcessed node inside⟩)
    simpa using permutation.length_eq

/-- Test whether the native read has a completed resource snapshot. -/
def isReady : StateResourceValidated.Read → Bool
  | .ready _ => true
  | _ => false

/-- For a fault-free native worklist, readiness is exactly dependency closure.
Unrelated missing-reference components affect readiness without hiding faults. -/
theorem validated_ready_iff_closed (e : Environment) (configuration : StateResourceAggregate.NativeConfiguration e.config)
    (accountSlice : ((accounts e.opener.data.selected.initialAllocations).map Prod.fst).length ≤ 2^63 - 1)
    (noWitness : ¬∃ node, StateResourceWitness.BudgetWitness e.config e.opener node e.known) :
    isReady (StateResourceValidated.observe e) = true ↔ ClosedKnown e := by
  have verified := native_worklist_verified e
  cases result : run e with
  | internalError => simp [result,Verified] at verified
  | fault node worklist machine ghost =>
    have witness : Joint e worklist machine ghost ∧ StateResourceWitness.BudgetWitness e.config e.opener node e.known := by
      simpa [result,Verified] using verified
    exact False.elim (noWitness ⟨node,witness.2⟩)
  | complete worklist machine ghost =>
    have completed : Joint e worklist machine ghost ∧ StateResourceCounters.Saturated (e.known.map Fact.id) worklist := by
      simpa [result,Verified] using verified
    have closure := saturated_size_iff_closed e worklist machine ghost completed.1 completed.2
    by_cases size : worklist.processed.length = e.known.length
    · obtain ⟨snapshot,finished,_,_⟩ := StateResourceFinalize.native_aggregate_finishes e worklist machine ghost result size configuration accountSlice
      simp [StateResourceValidated.observe,result,size,finished,isReady,closure.mp size]
    · have notClosed : ¬ClosedKnown e := fun closed => size (closure.mpr closed)
      simp [StateResourceValidated.observe,result,size,isReady,notClosed]

/-- The finalizer retains the computed maps in either capacity mode. -/
theorem finishBalances_maps (config : ResourceConfig) (owners : List String) (rights : String → Int)
    (headroom : Option (String → Int)) (snapshot : StateResourceFinalize.AggregateSnapshot)
    (finished : StateResourceFinalize.finishBalances config owners rights headroom = some snapshot) :
    snapshot.rights = rights ∧ snapshot.headroom = headroom := by
  unfold StateResourceFinalize.finishBalances at finished
  split at finished
  · contradiction
  · cases total : checkedSum (owners.map rights) with
    | none => simp [total] at finished
    | some totalRights =>
      cases value : checkedAdd totalRights config.floor with
      | none => simp [total,value] at finished
      | some amount =>
        cases ceiling : config.ceiling with
        | none =>
          have equal : StateResourceFinalize.AggregateSnapshot.mk amount rights headroom = snapshot := by
            simpa [total,value,ceiling] using finished
          cases equal
          exact ⟨rfl,rfl⟩
        | some cap =>
          cases headroom with
          | none => simp [total,value,ceiling] at finished
          | some space =>
            cases spaceTotal : checkedSum (owners.map space) with
            | none => simp [total,value,ceiling,spaceTotal] at finished
            | some totalSpace =>
              simp [total,value,ceiling,spaceTotal] at finished
              cases finished.2
              exact ⟨rfl,rfl⟩

theorem validated_ready_finish (e : Environment) (snapshot : StateResourceFinalize.AggregateSnapshot)
    (ready : StateResourceValidated.observe e = .ready snapshot) :
    StateResourceFinalize.finish e.config e.opener e.known = some snapshot := by
  cases result : run e with
  | internalError => simp [StateResourceValidated.observe,result] at ready
  | fault _ _ _ _ => simp [StateResourceValidated.observe,result] at ready
  | complete worklist machine ghost =>
    by_cases size : worklist.processed.length = e.known.length
    · cases finished : StateResourceFinalize.finish e.config e.opener e.known with
      | none => simp [StateResourceValidated.observe,result,size,finished] at ready
      | some actual =>
        have equal : actual = snapshot := by simpa [StateResourceValidated.observe,result,size,finished] using ready
        simpa [equal] using finished
    · simp [StateResourceValidated.observe,result,size] at ready

/-- Successful native headroom is the same exact flat account fold as rights;
it is not an unspecified display callback. -/
theorem validated_ready_headroom (e : Environment) (snapshot : StateResourceFinalize.AggregateSnapshot)
    (ready : StateResourceValidated.observe e = .ready snapshot) :
    snapshot.headroom = if e.config.headroomKey.isSome then
      some (StateResourceAggregate.accountBalance (StateResourceSolvency.initialSide e true) true e.known) else none := by
  have finished := validated_ready_finish e snapshot ready
  have rights := StateResourceAggregate.native_rights_fold e.config e.opener e.root e.known e.initialValid e.operations e.sliceBound
  cases active : e.config.headroomKey.isSome with
  | false =>
    simp only [StateResourceFinalize.finish,rights,active,Bool.false_eq_true,if_false,Option.bind_some] at finished
    exact (finishBalances_maps _ _ _ _ _ finished).2
  | true =>
    have space := StateResourceAggregate.native_headroom_fold e.config e.opener e.root e.known e.initialValid active e.operations e.sliceBound
    simp only [StateResourceFinalize.finish,rights,active,if_true,space,Option.bind_some] at finished
    exact (finishBalances_maps _ _ _ _ _ finished).2

theorem accountBalance_perm (initial : String → Int) (headroom : Bool) {A B : Facts} (same : A.Perm B) :
    StateResourceAggregate.accountBalance initial headroom A = StateResourceAggregate.accountBalance initial headroom B := by
  funext owner
  unfold StateResourceAggregate.accountBalance
  rw [StateKernelAggregates.sum_perm (same.map (StateResourceAggregate.delta headroom owner))]

theorem closedKnown_equiv (left right : Environment)
    (opener : left.opener = right.opener) (same : ∀ node, node ∈ left.known ↔ node ∈ right.known) :
    ClosedKnown left ↔ ClosedKnown right := by
  constructor
  · intro closed node member address edge
    rcases closed node ((same node).mpr member) address edge with root | ⟨parent,accepted,equal⟩
    · exact Or.inl (root.trans (congrArg Fact.id opener))
    · exact Or.inr ⟨parent,(same parent).mp accepted,equal⟩
  · intro closed node member address edge
    rcases closed node ((same node).mp member) address edge with root | ⟨parent,accepted,equal⟩
    · exact Or.inl (root.trans (congrArg Fact.id opener.symm))
    · exact Or.inr ⟨parent,(same parent).mpr accepted,equal⟩

theorem budgetWitness_equiv (left right : Environment) (config : left.config = right.config)
    (opener : left.opener = right.opener) (same : ∀ node, node ∈ left.known ↔ node ∈ right.known) :
    (∃ node, StateResourceWitness.BudgetWitness left.config left.opener node left.known) ↔
      ∃ node, StateResourceWitness.BudgetWitness right.config right.opener node right.known := by
  simp only [StateResourceWitness.BudgetWitness]
  rw [config,opener]
  constructor
  · rintro ⟨node,cone,inside,exactCone,bad⟩
    exact ⟨node,cone,(fun entry member => (same entry).mp (inside entry member)),exactCone,bad⟩
  · rintro ⟨node,cone,inside,exactCone,bad⟩
    exact ⟨node,cone,(fun entry member => (same entry).mpr (inside entry member)),exactCone,bad⟩

theorem ready_snapshot_eq (left right : Environment) (config : left.config = right.config)
    (opener : left.opener = right.opener) (same : left.known.Perm right.known)
    (leftConfiguration : StateResourceAggregate.NativeConfiguration left.config)
    (rightConfiguration : StateResourceAggregate.NativeConfiguration right.config)
    (leftSlice : ((accounts left.opener.data.selected.initialAllocations).map Prod.fst).length ≤ 2^63 - 1)
    (rightSlice : ((accounts right.opener.data.selected.initialAllocations).map Prod.fst).length ≤ 2^63 - 1)
    (a b : StateResourceFinalize.AggregateSnapshot) (readyA : StateResourceValidated.observe left = .ready a)
    (readyB : StateResourceValidated.observe right = .ready b) : a = b := by
  obtain ⟨rightsA,valueA⟩ := StateResourceValidated.ready_aggregate_value left leftConfiguration leftSlice a readyA
  obtain ⟨rightsB,valueB⟩ := StateResourceValidated.ready_aggregate_value right rightConfiguration rightSlice b readyB
  have initial : StateResourceSolvency.initialSide left = StateResourceSolvency.initialSide right := by
    funext headroom owner
    simp [StateResourceSolvency.initialSide,opener]
  have rights : a.rights = b.rights := by
    rw [rightsA,rightsB,initial]
    exact accountBalance_perm _ false same
  have value : a.value = b.value := by rw [valueA,valueB,rights,opener,config]
  have headroom : a.headroom = b.headroom := by
    rw [validated_ready_headroom left a readyA,validated_ready_headroom right b readyB,config,initial,
      accountBalance_perm _ true same]
  cases a
  cases b
  simp_all

/-- Complete validated native read equivalence under permutation, including
pending versus ready and all successful account-map payloads. -/
theorem validated_observe_perm (left right : Environment) (config : left.config = right.config)
    (opener : left.opener = right.opener) (same : left.known.Perm right.known)
    (leftConfiguration : StateResourceAggregate.NativeConfiguration left.config)
    (rightConfiguration : StateResourceAggregate.NativeConfiguration right.config)
    (leftSlice : ((accounts left.opener.data.selected.initialAllocations).map Prod.fst).length ≤ 2^63 - 1)
    (rightSlice : ((accounts right.opener.data.selected.initialAllocations).map Prod.fst).length ≤ 2^63 - 1) :
    StateResourceValidated.observe left = StateResourceValidated.observe right := by
  have membership : ∀ node, node ∈ left.known ↔ node ∈ right.known := fun node => same.mem_iff
  have witnesses := budgetWitness_equiv left right config opener membership
  have faultClass : StateResourceValidated.isFault (StateResourceValidated.observe left) = true ↔
      StateResourceValidated.isFault (StateResourceValidated.observe right) = true := by
    rw [StateResourceValidated.native_validated_certificate_iff left leftConfiguration leftSlice,
      StateResourceValidated.native_validated_certificate_iff right rightConfiguration rightSlice]
    exact witnesses
  cases l : StateResourceValidated.observe left with
  | fault =>
    cases r : StateResourceValidated.observe right <;> simp [l,r,StateResourceValidated.isFault] at faultClass ⊢
  | pending =>
    have noLeft : ¬∃ node, StateResourceWitness.BudgetWitness left.config left.opener node left.known := by
      rw [← StateResourceValidated.native_validated_certificate_iff left leftConfiguration leftSlice,l]
      simp [StateResourceValidated.isFault]
    have noRight := fun witness => noLeft (witnesses.mpr witness)
    have readyClass : isReady (StateResourceValidated.observe left) = true ↔ isReady (StateResourceValidated.observe right) = true := by
      rw [validated_ready_iff_closed left leftConfiguration leftSlice noLeft,
        validated_ready_iff_closed right rightConfiguration rightSlice noRight]
      exact closedKnown_equiv left right opener membership
    cases r : StateResourceValidated.observe right <;> simp [l,r,isReady,StateResourceValidated.isFault] at faultClass readyClass ⊢
  | ready a =>
    have noLeft : ¬∃ node, StateResourceWitness.BudgetWitness left.config left.opener node left.known := by
      rw [← StateResourceValidated.native_validated_certificate_iff left leftConfiguration leftSlice,l]
      simp [StateResourceValidated.isFault]
    have noRight := fun witness => noLeft (witnesses.mpr witness)
    have readyClass : isReady (StateResourceValidated.observe left) = true ↔ isReady (StateResourceValidated.observe right) = true := by
      rw [validated_ready_iff_closed left leftConfiguration leftSlice noLeft,
        validated_ready_iff_closed right rightConfiguration rightSlice noRight]
      exact closedKnown_equiv left right opener membership
    cases r : StateResourceValidated.observe right <;> simp [l,r,isReady,StateResourceValidated.isFault] at faultClass readyClass ⊢
    exact ready_snapshot_eq left right config opener same leftConfiguration rightConfiguration leftSlice rightSlice _ _ l r

end CBCL.StateResourceCompletion
