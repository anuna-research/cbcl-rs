import LeanCbcl.StateResourceOwnPrefix
import LeanCbcl.StateResourceOutgoing

/-! Full local_budgets scalar path: native owner counters, outgoing map totals,
checked intermediate arithmetic and cached incoming maps versus cone arithmetic. -/
namespace CBCL.StateResourceLocalBudget
open State CheckpointEvidence StateResource StateResourceNative StateResourceSummary StateResourceCache
open StateResourceStructure StateResourceFrontier StateResourcePartition StateResourceBudget StateResourceOutgoing

/-- One rights/headroom side of native local_budgets, in native check order. -/
def nativeLocalBudget (op node : ResourceFact) (own : Summary) (cache : Cache) (tips : Tips)
    (headroom : Bool) : Option Int := do
  let owners := (accounts op.data.selected.initialAllocations).map Prod.fst
  let outgoing ← nativeOutgoing owners own headroom
  let initial := allocation (accounts (if headroom then op.data.selected.headroomAllocations
    else op.data.selected.initialAllocations)) node.data.signer
  let raised ← checkedAdd initial (if headroom then own.debited else own.credited)
  let lowered ← checkedSub raised (if headroom then own.credited else own.debited)
  let available ← checkedSub lowered outgoing
  nativeIncoming cache tips node.data.signer headroom owners available

theorem owner_prefix_partition (opener : Nat) (known past : Facts) (cache : Cache) (tips : Tips)
    (prefixes : Prefixes) (owner : String)
    (rep : Represents opener known cache tips prefixes) (covers : Covers prefixes past)
    (uniquePast : past.Nodup) (uniquePrefix : (prefixes owner).Nodup) :
    (past.filter (fun node => node.data.signer == owner)).Perm (prefixes owner) := by
  apply (List.perm_ext_iff_of_nodup (uniquePast.sublist List.filter_sublist) uniquePrefix).mpr
  intro node
  constructor
  · intro member
    have selected := List.mem_filter.mp member
    obtain ⟨chosen,inside⟩ := (covers node).mp selected.1
    have signer := chain_owner chosen opener (prefixes chosen)
      (represented_chain opener known cache tips prefixes rep chosen).1 node inside
    have same : chosen = owner := signer.symm.trans (by simpa using selected.2)
    simpa [same] using inside
  · intro member
    have signer := chain_owner owner opener (prefixes owner)
      (represented_chain opener known cache tips prefixes rep owner).1 node member
    exact List.mem_filter.mpr ⟨(covers node).mpr ⟨owner,member⟩,by simpa using signer⟩

theorem ownTotal_prefix (past C : Facts) (owner : String) (kind : ResourceKind)
    (partition : ((ordered past).filter (fun node => node.data.signer == owner)).Perm C)
    (positive : ∀ node ∈ C, 0 ≤ node.data.amount) :
    ownTotal past owner kind = checkedSum (amounts (fun node => node.data.kind == kind) C) := by
  have selected : ((ordered past).filter (fun node => node.data.signer == owner && node.data.kind == kind)) =
      (((ordered past).filter (fun node => node.data.signer == owner)).filter (fun node => node.data.kind == kind)) := by
    simp [List.filter_filter,Bool.and_comm]
  have perm := ((partition.filter (fun node => node.data.kind == kind)).map (fun node => node.data.amount))
  have rightPositive : ∀ value ∈ amounts (fun node => node.data.kind == kind) C, 0 ≤ value := by
    intro value member
    obtain ⟨node,hn,rfl⟩ := List.mem_map.mp member
    exact positive node (List.mem_filter.mp hn).1
  have leftPositive : ∀ value ∈ (((ordered past).filter (fun node => node.data.signer == owner && node.data.kind == kind)).map (fun node => node.data.amount)), 0 ≤ value := by
    intro value member
    rw [selected] at member
    exact rightPositive value (perm.mem_iff.mp member)
  unfold ownTotal
  rw [checkedSum_nonnegative _ leftPositive,checkedSum_nonnegative _ rightPositive]
  rw [selected,StateKernelAggregates.sum_perm perm]
  rfl

theorem own_credited_debited (known past C : Facts) (owner : String) (own : Summary)
    (partition : ((ordered past).filter (fun node => node.data.signer == owner)).Perm C)
    (uniqueC : C.Nodup) (inside : Included C known) (sliceBound : known.length ≤ 2^63 - 1)
    (recognized : ∀ node ∈ known, natural64 node.data.amount) (success : run C empty = some own) :
    ownTotal past owner .increment = some own.credited ∧ ownTotal past owner .decrement = some own.debited := by
  have positive : ∀ node ∈ C, 0 ≤ node.data.amount := fun node member => (recognized node (inside node member)).1
  have total (kind : ResourceKind) : checkedSum (amounts (fun node => node.data.kind == kind) C) =
      some (amounts (fun node => node.data.kind == kind) C).sum := by
    rw [checkedSum_nonnegative _ (by
      intro value member
      obtain ⟨node,hn,rfl⟩ := List.mem_map.mp member
      exact positive node (List.mem_filter.mp hn).1)]
    exact if_pos (selected_sum_bound known C _ uniqueC inside sliceBound recognized)
  have counters := native_counters_refinement C own success
  have credited : (amounts (fun node => node.data.kind == .increment) C).sum = own.credited := by
    rw [amounts_sum]
    simpa using counters.1.symm
  have debited : (amounts (fun node => node.data.kind == .decrement) C).sum = own.debited := by
    rw [amounts_sum]
    simpa using counters.2.1.symm
  rw [ownTotal_prefix past C owner .increment partition positive,
    ownTotal_prefix past C owner .decrement partition positive,total,total,credited,debited]
  exact ⟨rfl,rfl⟩


/-- Both rights and headroom sides of native local_budgets refine the exact
cone, including failures of any checked intermediate. -/
theorem native_local_budget_refinement (c : ResourceConfig) (op root node : ResourceFact)
    (known cone : Facts) (own : Summary) (cache : Cache) (tips : Tips) (prefixes : Prefixes)
    (initial : validInitial c op root) (operations : ∀ entry ∈ known, validOperation c op root entry)
    (unique : (known.map Fact.id).Nodup) (exactCone : ExactCone op node cone) (inside : Included cone known)
    (rep : Represents op.id known cache tips prefixes)
    (covers : Covers prefixes (cone.filter (fun entry => entry.id != node.id)))
    (ownRun : run (prefixes node.data.signer) empty = some own)
    (structural : StateResourceKahn.nativeKahn (StateResourceCycle.parents known) known = [])
    (sliceBound : known.length ≤ 2^63 - 1) (headroom : Bool) :
    nativeLocalBudget op node own cache tips headroom = localBudget op node cone headroom := by
  let past := cone.filter (fun entry => entry.id != node.id)
  let C := prefixes node.data.signer
  let owner := node.data.signer
  let owners := (accounts op.data.selected.initialAllocations).map Prod.fst
  have identities := StateResourceDependency.unique_ids_consistent known unique
  have uniqueKnown : known.Nodup := List.Pairwise.of_map Fact.id
    (fun _ _ ne eq => ne (congrArg Fact.id eq)) unique
  have uniqueCone : cone.Nodup := List.Pairwise.of_map Fact.id
    (fun _ _ ne eq => ne (congrArg Fact.id eq)) exactCone.2.1
  have uniquePast : past.Nodup := uniqueCone.sublist List.filter_sublist
  have pastInside : Included past known := fun entry member => inside entry (List.mem_filter.mp member).1
  have meaning := represented_chain op.id known cache tips prefixes rep owner
  have ids := native_prefix_ids_unique owner op.id known C uniqueKnown identities structural meaning.1 meaning.2
  have uniqueC : C.Nodup := List.Pairwise.of_map Fact.id (fun _ _ ne eq => ne (congrArg Fact.id eq)) ids
  have orderedPerm : (ordered past).Perm past := List.mergeSort_perm past _
  have partition : ((ordered past).filter (fun entry => entry.data.signer == owner)).Perm C :=
    (orderedPerm.filter _).trans (owner_prefix_partition op.id known past cache tips prefixes owner rep covers uniquePast uniqueC)
  have recognized : ∀ entry ∈ known, natural64 entry.data.amount := by
    intro entry member
    obtain ⟨_,_,_,_,_,_,amount,_⟩ := operations entry member
    exact amount
  have positive : ∀ entry ∈ C, 0 ≤ entry.data.amount :=
    fun entry member => (recognized entry (meaning.2 entry member)).1
  have totals := own_credited_debited known past C owner own partition uniqueC meaning.2 sliceBound recognized ownRun
  have outgoing : nativeOutgoing owners own headroom = ownTotal past owner
      (if headroom then ResourceKind.transferHeadroom else ResourceKind.transfer) :=
    (native_outgoing_refinement c op root C own initial
      (fun entry member => operations entry (meaning.2 entry member)) ownRun headroom).trans
      (ownTotal_prefix past C owner _ partition positive).symm
  have orderedCovers : Covers prefixes (ordered past) :=
    fun entry => (orderedPerm.mem_iff).trans (covers entry)
  obtain ⟨rows,value,_,rosterUnique,_⟩ := initial.2.2.1
  have uniqueOwners : owners.Nodup := by simpa [owners,accounts,value] using rosterUnique
  have ownerPresent : ∀ entry ∈ ordered past, entry.data.signer ∈ owners :=
    fun entry member => (operations entry (pastInside entry (orderedPerm.mem_iff.mp member))).2.2.2.1
  have incoming (available : Int) (bounded : i128 available) :
      nativeIncoming cache tips owner headroom owners available =
        ((ordered past).filter (incomingPredicate owner headroom)).foldlM
          (fun balance entry => checkedAdd balance entry.data.amount) available := by
    have agreement := native_incoming_cone_refinement op.id known (ordered past) cache tips prefixes owners owner headroom
      rep orderedCovers uniqueOwners (orderedPerm.symm.nodup uniquePast) uniqueKnown identities structural ownerPresent
      sliceBound recognized available bounded
    simpa [amounts,List.foldlM_map] using agreement
  unfold nativeLocalBudget localBudget
  change (do
    let out ← nativeOutgoing owners own headroom
    let raised ← checkedAdd (allocation (accounts (if headroom then op.data.selected.headroomAllocations else op.data.selected.initialAllocations)) owner)
      (if headroom then own.debited else own.credited)
    let lowered ← checkedSub raised (if headroom then own.credited else own.debited)
    let available ← checkedSub lowered out
    nativeIncoming cache tips owner headroom owners available) = _
  dsimp only
  rw [totals.1,totals.2,← outgoing]
  cases outRead : nativeOutgoing owners own headroom with
  | none => simp_all [owner,owners,past]
  | some out =>
    cases raisedRead : checkedAdd (allocation (accounts (if headroom then op.data.selected.headroomAllocations else op.data.selected.initialAllocations)) owner)
        (if headroom then own.debited else own.credited) with
    | none => simp_all [owner,owners,past]
    | some raised =>
      cases loweredRead : checkedSub raised (if headroom then own.credited else own.debited) with
      | none => simp_all [owner,owners,past]
      | some lowered =>
        cases availableRead : checkedSub lowered out with
        | none => simp_all [owner,owners,past]
        | some available =>
          have bound : i128 available := by
            obtain ⟨bounded,equal⟩ := (checkedSub_iff _ _ _).mp availableRead
            simpa [equal] using bounded
          have agreement := incoming available bound
          simp_all [owner,owners,past]
          rfl


/-- Native dependency lookups, previous lookup, frontier merge and both budget
sides refine the same reconstructed exact cone. The new operation's cone,
frontier partition and owner-prefix equality are all conclusions. -/
theorem dependency_local_budgets_exact (c : ResourceConfig) (op root node : ResourceFact)
    (known : Facts) (own : Summary) (cache : Cache) (cones : StateResourceCones.ConeCache)
    (tips : Nat → Tips) (prefixes : Nat → Prefixes) (parents : List (ResourceFact × Facts))
    (invariant : StateResourceDependency.ParentInvariant op known cache cones tips prefixes)
    (valid : StateResourceCache.Valid op.id known cache)
    (ownTips : StateResourceOwnPrefix.OwnTips cache cones tips)
    (lookups : StateResourceCones.gather op cones (links node) = some parents)
    (previous : previousSummary op.id cache node = some own)
    (nonforking : Nonforking known) (accepted : node ∈ known) (unique : (known.map Fact.id).Nodup)
    (foreignChecked : previousOwnerCheck op.id known = true)
    (unprocessed : ∀ parent ∈ parents, ∀ entry ∈ parent.2, entry.id ≠ node.id)
    (initial : validInitial c op root) (operations : ∀ entry ∈ known, validOperation c op root entry)
    (structural : StateResourceKahn.nativeKahn (StateResourceCycle.parents known) known = [])
    (sliceBound : known.length ≤ 2^63 - 1) :
    let cone := StateResourceCones.unionCone known node parents
    ExactCone op node cone ∧ ∀ headroom,
      nativeLocalBudget op node own cache (StateResourceDependency.mergedTips cache tips parents) headroom =
        localBudget op node cone headroom := by
  obtain ⟨exactCone,rep,covers⟩ := StateResourceDependency.pre_record_frontier_exact op node known cache cones tips prefixes
    parents invariant lookups nonforking accepted unique unprocessed
  obtain ⟨chain,equal,_,_,folded⟩ := StateResourceOwnPrefix.merged_previous_prefix op node known cache cones tips prefixes
    parents own invariant valid ownTips lookups nonforking accepted unique foreignChecked unprocessed structural previous
  have ownRun : run (StateResourceDependency.mergedPrefixes prefixes parents node.data.signer) empty = some own := by
    simpa [equal] using folded
  have inside : Included (StateResourceCones.unionCone known node parents) known :=
    fun entry member => ((StateResourceCones.unionCone_member known node entry parents).mp member).1
  exact ⟨exactCone,fun headroom => native_local_budget_refinement c op root node known _ own cache
    (StateResourceDependency.mergedTips cache tips parents) (StateResourceDependency.mergedPrefixes prefixes parents)
    initial operations unique exactCone inside rep covers ownRun structural sliceBound headroom⟩


/-- Native budget decisions preserve the distinction between absent unbounded
headroom and failed bounded-headroom arithmetic. -/
def budgetDecision (bounded usesHeadroom : Bool) (amount : Int) (rights space : Option Int) : Bool :=
  match rights with
  | none => false
  | some r =>
    if bounded then match space with
      | none => false
      | some h => decide (amount ≤ if usesHeadroom then h else r)
    else if usesHeadroom then true else decide (amount ≤ r)

theorem budgetDecision_false_iff (bounded usesHeadroom : Bool) (amount : Int) (rights space : Option Int) :
    budgetDecision bounded usesHeadroom amount rights space = false ↔
      rights = none ∨ (bounded = true ∧ space = none) ∨
        (if usesHeadroom then bounded = true else True) ∧
          ∃ budget, (if usesHeadroom then space else rights) = some budget ∧ budget < amount := by
  cases bounded <;> cases usesHeadroom <;> cases rights <;> cases space <;> simp [budgetDecision]
  all_goals omega

/-- Check the operation's available budget from native cached summaries. -/
def nativeBudgetCheck (c : ResourceConfig) (op node : ResourceFact) (own : Summary) (cache : Cache) (tips : Tips) : Bool :=
  budgetDecision c.headroomKey.isSome (decide (node.data.kind = .increment ∨ node.data.kind = .transferHeadroom))
    node.data.amount (nativeLocalBudget op node own cache tips false) (nativeLocalBudget op node own cache tips true)

/-- Full native local-budget rejection iff the concrete budget-certificate
predicate, after native dependency/frontier refinement. Summary overflow is
proved unreachable from representation bounds, rather than omitted. -/
theorem native_budget_rejection_iff (c : ResourceConfig) (op root node : ResourceFact)
    (known cone : Facts) (own : Summary) (cache : Cache) (tips : Tips)
    (uniqueCone : cone.Nodup) (inside : Included cone known) (sliceBound : known.length ≤ 2^63 - 1)
    (operations : ∀ entry ∈ known, validOperation c op root entry)
    (refinement : ∀ headroom, nativeLocalBudget op node own cache tips headroom = localBudget op node cone headroom) :
    nativeBudgetCheck c op node own cache tips = false ↔ budgetFault c op node cone := by
  have recognized : ∀ entry ∈ known, natural64 entry.data.amount := by
    intro entry member
    obtain ⟨_,_,_,_,_,_,amount,_⟩ := operations entry member
    exact amount
  have noSummary := summaryFault_unreachable known cone node uniqueCone inside sliceBound recognized
  unfold nativeBudgetCheck
  rw [refinement false,refinement true,budgetDecision_false_iff]
  by_cases uses : node.data.kind = .increment ∨ node.data.kind = .transferHeadroom
  · simp [budgetFault,noSummary,uses]
  · simp [budgetFault,noSummary,uses]

end CBCL.StateResourceLocalBudget
