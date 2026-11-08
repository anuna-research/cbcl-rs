import LeanCbcl.StateResourceAccounting

/-! Solvency from checked local authorization. The aggregate processed history
contains each ready operation's observed cone and the same current-owner prefix;
extra observations can therefore add only other-owner incoming funding. -/
namespace CBCL.StateResourceSolvency
open State CheckpointEvidence StateResource StateResourceNative StateResourceSummary StateResourceCache
open StateResourceStructure StateResourceFrontier StateResourcePartition StateResourceDependency StateResourceOwnPrefix
open StateResourceLocalBudget StateResourceWitness StateResourceMachine StateResourceAuthorization StateResourceCoupling
open StateResourceWorklist StateResourceAggregate StateResourceAccounting StateResourceBudget

def processedFacts (e : Environment) (worklist : StateResourceCounters.Worklist) : Facts :=
  e.known.filter (fun node => worklist.processed.contains node.id)

theorem cached_prefix (e : Environment) (worklist : StateResourceCounters.Worklist) (machine : Machine) (ghost : Ghost)
    (invariant : Joint e worklist machine ghost) (address : Nat) (node : ResourceFact) (summary : Summary)
    (cached : machine.summaries address = some (node,summary)) :
    ∃ chain, OwnerChain node.data.signer e.opener.id chain ∧ Included chain e.known ∧ node ∈ chain ∧
      ∀ entry ∈ chain, ∃ amount, machine.summaries entry.id = some (entry,amount) := by
  obtain ⟨cone,stored⟩ := invariant.cache.paired address node summary cached
  obtain ⟨otherSummary,D,otherCached,chainD,insideD,_,runD,prefixEq⟩ := cached_parent_prefix e.opener e.known machine.summaries
    ghost.cones machine.tips ghost.prefixes invariant.cache.parents invariant.cache.summaries invariant.cache.ownTips e.nonforking address node cone stored
  have summaryEqual : summary = otherSummary := by simpa [cached] using otherCached
  subst otherSummary
  obtain ⟨_,C,chainC,_,runC,insideC,lastNode⟩ := invariant.cache.summaries address node summary cached
  have chainsEqual := same_cached_prefix node.data.signer e.opener.id e.known C D summary
    (fun x hx y hy ox oy prev => e.nonforking x hx y hy (ox.trans oy.symm) prev)
    chainC chainD insideC insideD runC runD
  have member : node ∈ C := by
    obtain ⟨earlier,equal⟩ := List.getLast?_eq_some_iff.mp lastNode
    simp [equal]
  refine ⟨C,chainC,insideC,member,?_⟩
  intro entry inside
  have inCone : entry ∈ cone := ((invariant.cache.parents.2 address node cone stored).2 entry).mpr
    ⟨node.data.signer,by simpa [prefixEq,← chainsEqual] using inside⟩
  exact invariant.cache.processed address node cone stored entry inCone

theorem past_in_processed (e : Environment) (node : ResourceFact) (worklist : StateResourceCounters.Worklist)
    (machine : Machine) (ghost : Ghost) (invariant : Joint e worklist machine ghost)
    (parents : List (ResourceFact × Facts)) (accepted : node ∈ e.known)
    (fresh : machine.summaries node.id = none)
    (lookups : StateResourceCones.gather e.opener ghost.cones (links node) = some parents) :
    Included ((StateResourceCones.unionCone e.known node parents).filter (fun entry => entry.id != node.id)) (processedFacts e worklist) := by
  have unprocessed := fresh_excludes_parent_cones e.opener node e.known machine ghost invariant.cache fresh parents lookups
  have sound := (StateResourceCones.gather_lookup e.opener ghost.cones (links node) parents lookups).1
  have inside : ∀ parent ∈ parents, Included parent.2 e.known := by
    intro parent member
    obtain ⟨address,_,_,cached⟩ := sound parent member
    exact (invariant.cache.parents.1 address parent.1 parent.2 cached).2.2.1
  intro entry member
  obtain ⟨parent,hp,inParent⟩ := (unionCone_past e.known node entry parents inside unprocessed).mp member
  obtain ⟨address,_,_,cached⟩ := sound parent hp
  obtain ⟨summary,present⟩ := invariant.cache.processed address parent.1 parent.2 cached entry inParent
  exact List.mem_filter.mpr ⟨inside parent hp entry inParent,by simpa using (invariant.coupled entry.id).mp ⟨entry,summary,present⟩⟩

/-- The processed aggregate cannot contain an additional current-owner act
outside the ready act's past cone: such a prefix would already contain the
unprocessed current act or fork its immutable owner chain. -/
theorem processed_own_in_past (e : Environment) (node : ResourceFact) (worklist : StateResourceCounters.Worklist)
    (machine : Machine) (ghost : Ghost) (invariant : Joint e worklist machine ghost)
    (parents : List (ResourceFact × Facts)) (own : Summary) (accepted : node ∈ e.known)
    (fresh : machine.summaries node.id = none)
    (lookups : StateResourceCones.gather e.opener ghost.cones (links node) = some parents)
    (previous : previousSummary e.opener.id machine.summaries node = some own) :
    ∀ entry ∈ processedFacts e worklist, entry.data.signer = node.data.signer →
      entry ∈ (StateResourceCones.unionCone e.known node parents).filter (fun entry => entry.id != node.id) := by
  have unprocessed := fresh_excludes_parent_cones e.opener node e.known machine ghost invariant.cache fresh parents lookups
  obtain ⟨_,rep,covers⟩ := pre_record_frontier_exact e.opener node e.known machine.summaries ghost.cones machine.tips ghost.prefixes parents
    invariant.cache.parents lookups e.nonforking accepted e.unique unprocessed
  obtain ⟨C,prefixEq,currentChain,insideC,_⟩ := merged_previous_prefix e.opener node e.known machine.summaries ghost.cones machine.tips ghost.prefixes parents own
    invariant.cache.parents invariant.cache.summaries invariant.cache.ownTips lookups e.nonforking accepted e.unique e.foreign unprocessed e.structural previous
  intro entry member sameOwner
  have selected := List.mem_filter.mp member
  have released : entry.id ∈ worklist.processed := by simpa using selected.2
  obtain ⟨other,summary,cached⟩ := (invariant.coupled entry.id).mpr released
  have identity := (invariant.cache.summaries entry.id other summary cached).1
  obtain ⟨cone,stored⟩ := invariant.cache.paired entry.id other summary cached
  have otherKnown := (invariant.cache.parents.1 entry.id other cone stored).2.1
  have equal := unique_ids_consistent e.known e.unique other otherKnown entry selected.1 identity
  subst other
  obtain ⟨D,chainD,insideD,memberD,allCached⟩ := cached_prefix e worklist machine ghost invariant entry.id entry summary cached
  have notCurrent : node ∉ D := by
    intro inside
    obtain ⟨amount,present⟩ := allCached node inside
    rw [fresh] at present
    contradiction
  have before := dependency_own_prefix_before_current node.data.signer e.opener.id e.known C D node e.nonforking currentChain
    (by simpa [sameOwner] using chainD) (fun item inside => by
      rcases List.mem_append.mp inside with old | current
      · exact insideC item old
      · simpa using (List.mem_singleton.mp current ▸ accepted)) insideD notCurrent
  have inC := before.subset memberD
  exact (covers entry).mpr ⟨node.data.signer,by simpa [prefixEq] using inC⟩


theorem local_budget_le_processed (e : Environment) (node : ResourceFact) (worklist : StateResourceCounters.Worklist)
    (machine : Machine) (ghost : Ghost) (invariant : Joint e worklist machine ghost)
    (parents : List (ResourceFact × Facts)) (own : Summary) (accepted : node ∈ e.known)
    (fresh : machine.summaries node.id = none)
    (lookups : StateResourceCones.gather e.opener ghost.cones (links node) = some parents)
    (previous : previousSummary e.opener.id machine.summaries node = some own)
    (headroom : Bool) (value : Int)
    (budget : nativeLocalBudget e.opener node own machine.summaries (mergedTips machine.summaries machine.tips parents) headroom = some value) :
    value ≤ accountBalance (allocation (accounts (if headroom then e.opener.data.selected.headroomAllocations
      else e.opener.data.selected.initialAllocations))) headroom (processedFacts e worklist) node.data.signer := by
  let cone := StateResourceCones.unionCone e.known node parents
  let past := cone.filter (fun entry => entry.id != node.id)
  obtain ⟨exactCone,refinement⟩ := dependency_local_budgets_exact e.config e.opener e.root node e.known own machine.summaries ghost.cones
    machine.tips ghost.prefixes parents invariant.cache.parents invariant.cache.summaries invariant.cache.ownTips lookups previous
    e.nonforking accepted e.unique e.foreign
    (fresh_excludes_parent_cones e.opener node e.known machine ghost invariant.cache fresh parents lookups)
    e.initialValid e.operations e.structural e.sliceBound
  have insideCone : Included cone e.known := fun entry member =>
    ((StateResourceCones.unionCone_member e.known node entry parents).mp member).1
  have localSuccess : localBudget e.opener node cone headroom = some value := (refinement headroom).symm.trans budget
  have valueEq := localBudget_value e.config e.opener e.root node cone headroom value
    (fun entry member => e.operations entry (insideCone entry member)) localSuccess
  rw [valueEq]
  have uniqueKnown : e.known.Nodup := List.Pairwise.of_map Fact.id (fun _ _ ne eq => ne (congrArg Fact.id eq)) e.unique
  have uniqueCone : cone.Nodup := uniqueKnown.sublist List.filter_sublist
  apply account_balance_mono _ headroom node.data.signer past (processedFacts e worklist)
    (uniqueCone.sublist List.filter_sublist) (uniqueKnown.sublist List.filter_sublist)
    (past_in_processed e node worklist machine ghost invariant parents accepted fresh lookups)
  · intro entry member outside sameOwner
    exact outside (processed_own_in_past e node worklist machine ghost invariant parents own accepted fresh lookups previous entry member sameOwner)
  · intro entry member
    obtain ⟨_,_,_,_,_,_,amount,_⟩ := e.operations entry (List.mem_filter.mp member).1
    exact amount

def Spends (headroom : Bool) (node : ResourceFact) : Prop :=
  if headroom then node.data.kind = .increment ∨ node.data.kind = .transferHeadroom
    else node.data.kind = .decrement ∨ node.data.kind = .transfer

theorem decision_spending (bounded usesHeadroom side : Bool) (amount : Int) (rights space : Option Int)
    (good : budgetDecision bounded usesHeadroom amount rights space = true)
    (selected : side = usesHeadroom) (active : side = true → bounded = true) :
    ∃ budget, (if side then space else rights) = some budget ∧ amount ≤ budget := by
  cases bounded <;> cases usesHeadroom <;> cases side <;> cases rights <;> cases space <;>
    simp_all [budgetDecision]

theorem done_spending_covered (e : Environment) (node : ResourceFact) (worklist : StateResourceCounters.Worklist)
    (machine next : Machine) (ghost after : Ghost) (invariant : Joint e worklist machine ghost)
    (accepted : node ∈ e.known) (ready : worklist.ready node.id = true)
    (success : checkedStep e.config e.opener node e.known machine ghost = .done next after)
    (headroom : Bool) (spends : Spends headroom node) (active : headroom = true → e.config.headroomKey.isSome = true) :
    node.data.amount ≤ accountBalance (allocation (accounts (if headroom then e.opener.data.selected.headroomAllocations
      else e.opener.data.selected.initialAllocations))) headroom (processedFacts e worklist) node.data.signer := by
  obtain ⟨parents,own,lookups,previous⟩ := ready_lookups e.config e.opener e.root node e.known worklist machine ghost invariant.counters
    invariant.cache invariant.coupled e.unique accepted (e.operations node accepted) ready
  have fresh := ready_fresh e.opener node e.known worklist machine invariant.counters invariant.coupled accepted ready
  have good : nativeBudgetCheck e.config e.opener node own machine.summaries (mergedTips machine.summaries machine.tips parents) = true := by
    cases decision : nativeBudgetCheck e.config e.opener node own machine.summaries (mergedTips machine.summaries machine.tips parents) with
    | false => simp [checkedStep,lookups,previous,decision] at success
    | true => rfl
  have selected : headroom = decide (node.data.kind = .increment ∨ node.data.kind = .transferHeadroom) := by
    cases headroom <;> simp [Spends] at spends <;> rcases spends with kind | kind <;> simp [kind]
  obtain ⟨value,budget,sufficient⟩ := decision_spending e.config.headroomKey.isSome
    (decide (node.data.kind = .increment ∨ node.data.kind = .transferHeadroom)) headroom node.data.amount
    (nativeLocalBudget e.opener node own machine.summaries (mergedTips machine.summaries machine.tips parents) false)
    (nativeLocalBudget e.opener node own machine.summaries (mergedTips machine.summaries machine.tips parents) true) good selected active
  have actual : nativeLocalBudget e.opener node own machine.summaries (mergedTips machine.summaries machine.tips parents) headroom = some value := by
    cases headroom <;> simpa using budget
  exact Int.le_trans sufficient (local_budget_le_processed e node worklist machine ghost invariant parents own accepted fresh lookups previous headroom value actual)


theorem sender_spending_delta (e : Environment) (node : ResourceFact) (accepted : node ∈ e.known)
    (headroom : Bool) (spends : Spends headroom node) :
    delta headroom node.data.signer node = -node.data.amount := by
  have components := delta_components e.config e.opener e.root node headroom node.data.signer (e.operations node accepted)
  cases headroom <;> simp [Spends] at spends <;> rcases spends with kind | kind <;>
    simpa [creditPredicate,debitPredicate,outgoingPredicate,incomingPredicate,kind] using components

theorem sender_other_delta_nonnegative (headroom : Bool) (node : ResourceFact)
    (notSpending : ¬Spends headroom node) (recognized : natural64 node.data.amount) :
    0 ≤ delta headroom node.data.signer node := by
  cases headroom <;> cases kind : node.data.kind <;>
    simp [Spends,kind] at notSpending <;>
    simp [delta,rightsDelta,headroomDelta,kind] <;> exact recognized.1

theorem processed_after_permutation (e : Environment) (node : ResourceFact) (worklist : StateResourceCounters.Worklist)
    (accepted : node ∈ e.known) (fresh : node.id ∉ worklist.processed) :
    (processedFacts e (StateResourceCounters.pop worklist node.id)).Perm (processedFacts e worklist ++ [node]) := by
  have uniqueKnown : e.known.Nodup := List.Pairwise.of_map Fact.id (fun _ _ ne eq => ne (congrArg Fact.id eq)) e.unique
  have uniqueOld : (processedFacts e worklist).Nodup := uniqueKnown.sublist List.filter_sublist
  have absent : node ∉ processedFacts e worklist := by
    intro member
    have present : node.id ∈ worklist.processed := by simpa using (List.mem_filter.mp member).2
    exact fresh present
  have rightUnique : (processedFacts e worklist ++ [node]).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨uniqueOld,by simp,?_⟩
    intro first hf last hl same
    have lastEq : last = node := List.mem_singleton.mp hl
    apply absent
    simpa [same,lastEq] using hf
  apply (List.perm_ext_iff_of_nodup (uniqueKnown.sublist List.filter_sublist) rightUnique).mpr
  intro entry
  have selected : entry ∈ processedFacts e (StateResourceCounters.pop worklist node.id) ↔
      entry ∈ e.known ∧ (entry.id = node.id ∨ entry.id ∈ worklist.processed) := by
    simp [processedFacts,StateResourceCounters.pop]
  change entry ∈ processedFacts e (StateResourceCounters.pop worklist node.id) ↔ entry ∈ processedFacts e worklist ++ [node]
  rw [selected]
  constructor
  · rintro ⟨member,equal | old⟩
    · have same := unique_ids_consistent e.known e.unique entry member node accepted equal
      simp [same]
    · exact List.mem_append.mpr (Or.inl (List.mem_filter.mpr ⟨member,by simpa using old⟩))
  · intro member
    rcases List.mem_append.mp member with old | current
    · have selected := List.mem_filter.mp old
      exact ⟨selected.1,Or.inr (by simpa using selected.2)⟩
    · have same : entry = node := List.mem_singleton.mp current
      subst entry
      exact ⟨accepted,Or.inl rfl⟩

theorem processed_balance_after (e : Environment) (node : ResourceFact) (worklist : StateResourceCounters.Worklist)
    (accepted : node ∈ e.known) (fresh : node.id ∉ worklist.processed) (initial : String → Int)
    (headroom : Bool) (owner : String) :
    accountBalance initial headroom (processedFacts e (StateResourceCounters.pop worklist node.id)) owner =
      accountBalance initial headroom (processedFacts e worklist) owner + delta headroom owner node := by
  have permutation := processed_after_permutation e node worklist accepted fresh
  have sum := StateKernelAggregates.sum_perm (permutation.map (delta headroom owner))
  unfold accountBalance
  rw [sum]
  simp [List.map_append,List.sum_append,Int.add_assoc]

def initialSide (e : Environment) (headroom : Bool) : String → Int :=
  allocation (accounts (if headroom then e.opener.data.selected.headroomAllocations else e.opener.data.selected.initialAllocations))

def Economic (e : Environment) (worklist : StateResourceCounters.Worklist) : Prop :=
  ∀ headroom, (headroom = true → e.config.headroomKey.isSome = true) → ∀ owner,
    0 ≤ accountBalance (initialSide e headroom) headroom (processedFacts e worklist) owner

/-- Authorization preserves all aggregate account balances. Only the sender
can lose funds; the selected checked local budget covers that debit. -/
theorem done_economic (e : Environment) (node : ResourceFact) (worklist : StateResourceCounters.Worklist)
    (machine next : Machine) (ghost after : Ghost) (invariant : Joint e worklist machine ghost) (economic : Economic e worklist)
    (accepted : node ∈ e.known) (ready : worklist.ready node.id = true)
    (success : checkedStep e.config e.opener node e.known machine ghost = .done next after) :
    Economic e (StateResourceCounters.pop worklist node.id) := by
  intro headroom active owner
  have fresh := ((invariant.counters.readiness node.id (List.mem_map.mpr ⟨node,accepted,rfl⟩)).mp ready).1
  rw [processed_balance_after e node worklist accepted fresh]
  have before := economic headroom active owner
  have recognized : natural64 node.data.amount := by
    obtain ⟨_,_,_,_,_,_,amount,_⟩ := e.operations node accepted
    exact amount
  by_cases sameOwner : owner = node.data.signer
  · subst owner
    by_cases spends : Spends headroom node
    · have covered := done_spending_covered e node worklist machine next ghost after invariant accepted ready success headroom spends active
      rw [sender_spending_delta e node accepted headroom spends]
      exact Int.sub_nonneg_of_le covered
    · have change := sender_other_delta_nonnegative headroom node spends recognized
      omega
  · have other : node.data.signer ≠ owner := Ne.symm sameOwner
    have change := delta_other_nonnegative headroom owner node other recognized
    omega


theorem initial_side_natural (e : Environment) (headroom : Bool)
    (active : headroom = true → e.config.headroomKey.isSome = true) (owner : String) :
    natural64 (initialSide e headroom owner) := by
  cases headroom with
  | false =>
    obtain ⟨rows,value,_,_,recognized⟩ := e.initialValid.2.2.1
    simpa [initialSide,accounts,value] using allocation_natural64 rows (fun row member => (recognized row member).2) owner
  | true =>
    obtain ⟨rows,value,_,_,recognized⟩ := (e.initialValid.2.2.2.2.2.1 (active rfl)).1
    simpa [initialSide,accounts,value] using allocation_natural64 rows (fun row member => (recognized row member).2) owner

theorem initial_economic (e : Environment) : Economic e (initialWorklist e) := by
  have empty : processedFacts e (initialWorklist e) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro node _
    simp [initialWorklist,StateResourceCounters.initWorklist]
  intro headroom active owner
  have nonnegative := (initial_side_natural e headroom active owner).1
  simpa [empty,accountBalance] using nonnegative

def VerifiedEconomic (e : Environment) : StateResourceWorklist.Outcome → Prop
  | .complete worklist _ _ => Economic e worklist
  | .fault _ _ _ _ => True
  | .internalError => False

/-- Non-negative aggregate accounts are preserved across the actual faulting
worklist, with ready counters and native authorization interleaved. -/
theorem runFuel_economic (e : Environment) (fuel : Nat) (worklist : StateResourceCounters.Worklist)
    (machine : Machine) (ghost : Ghost) (invariant : Joint e worklist machine ghost) (economic : Economic e worklist) :
    VerifiedEconomic e (StateResourceWorklist.runFuel e fuel worklist machine ghost) := by
  induction fuel generalizing worklist machine ghost with
  | zero => exact economic
  | succ fuel ih =>
    simp only [StateResourceWorklist.runFuel]
    cases selected : e.known.find? (fun node => worklist.ready node.id) with
    | none => exact economic
    | some node =>
      dsimp only
      have accepted := List.mem_of_find?_eq_some selected
      have ready := List.find?_some selected
      cases step : checkedStep e.config e.opener node e.known machine ghost with
      | done next after =>
        exact ih (StateResourceCounters.pop worklist node.id) next after
          (done_joint e node worklist machine next ghost after invariant accepted ready step)
          (done_economic e node worklist machine next ghost after invariant economic accepted ready step)
      | budgetFault _ _ _ => trivial
      | blocked bad mid annotations =>
        exact False.elim (ready_not_blocked e.config e.opener e.root node e.known worklist machine ghost invariant.counters
          invariant.cache invariant.coupled e.unique accepted (e.operations node accepted) ready bad mid annotations step)
      | recordFault bad mid annotations =>
        have fresh := ready_fresh e.opener node e.known worklist machine invariant.counters invariant.coupled accepted ready
        have safe := checkedStep_safe e.config e.opener e.root node e.known machine ghost invariant.cache fresh accepted e.nonforking
          e.unique e.foreign e.initialValid e.operations e.excludesOpener e.structural e.sliceBound
        have impossible : False := by simpa [step,SafeResult] using safe
        exact False.elim impossible

theorem native_worklist_solvency (e : Environment) : VerifiedEconomic e (StateResourceWorklist.run e) :=
  runFuel_economic e e.known.length (initialWorklist e) StateResourceMachine.initial initialGhost (initial_joint e) (initial_economic e)

/-- Native final negative-account rejection is unreachable after complete
successful authorization. No non-negativity assumption is supplied by a host. -/
theorem completed_balances_nonnegative (e : Environment) (worklist : StateResourceCounters.Worklist) (machine : Machine) (ghost : Ghost)
    (completed : StateResourceWorklist.run e = .complete worklist machine ghost)
    (allProcessed : ∀ node ∈ e.known, node.id ∈ worklist.processed) :
    ∀ headroom, (headroom = true → e.config.headroomKey.isSome = true) → ∀ owner,
      0 ≤ accountBalance (initialSide e headroom) headroom e.known owner := by
  have economic : Economic e worklist := by simpa [completed,VerifiedEconomic] using native_worklist_solvency e
  have full : processedFacts e worklist = e.known := by
    apply List.filter_eq_self.mpr
    intro node member
    simpa using allProcessed node member
  intro headroom active owner
  simpa [full] using economic headroom active owner


theorem all_processed_of_size (e : Environment) (worklist : StateResourceCounters.Worklist) (machine : Machine) (ghost : Ghost)
    (invariant : Joint e worklist machine ghost) (size : worklist.processed.length = e.known.length) :
    ∀ node ∈ e.known, node.id ∈ worklist.processed := by
  intro node accepted
  by_cases present : node.id ∈ worklist.processed
  · exact present
  · have enlarged : (node.id :: worklist.processed).Nodup := List.nodup_cons.mpr ⟨present,invariant.processedUnique⟩
    have subset : node.id :: worklist.processed ⊆ e.known.map Fact.id := by
      intro address member
      rcases List.mem_cons.mp member with rfl | old
      · exact List.mem_map.mpr ⟨node,accepted,rfl⟩
      · exact invariant.processedKnown old
    have length := (List.subperm_of_subset enlarged subset).length_le
    simp only [List.length_cons,List.length_map] at length
    omega

theorem completed_size_balances_nonnegative (e : Environment) (worklist : StateResourceCounters.Worklist) (machine : Machine) (ghost : Ghost)
    (completed : StateResourceWorklist.run e = .complete worklist machine ghost) (size : worklist.processed.length = e.known.length) :
    ∀ headroom, (headroom = true → e.config.headroomKey.isSome = true) → ∀ owner,
      0 ≤ accountBalance (initialSide e headroom) headroom e.known owner := by
  have verified : Joint e worklist machine ghost ∧ StateResourceCounters.Saturated (e.known.map Fact.id) worklist := by
    simpa [completed,Verified] using native_worklist_verified e
  exact completed_balances_nonnegative e worklist machine ghost completed (all_processed_of_size e worklist machine ghost verified.1 size)

end CBCL.StateResourceSolvency
