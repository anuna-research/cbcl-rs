import LeanCbcl.StateResourcePartition

/-! Checked grouped budget arithmetic after dependency-frontier refinement.
Partition and chunk overflow bounds are derived here, rather than supplied as
arithmetic oracles by the final resource theorem. -/
namespace CBCL.StateResourceBudget
open State CheckpointEvidence StateResource StateResourceSummary StateResourceNative StateResourceCache
open StateResourceStructure StateResourceFrontier StateResourcePartition

/-- Extract the selected signed operation amounts. -/
def amounts (predicate : ResourceFact → Bool) (facts : Facts) : List Int :=
  (facts.filter predicate).map (fun node => node.data.amount)

/-- Partition incoming amounts by their contributing owner prefixes. -/
def chunks (owners : List String) (prefixes : Prefixes) (predicate : ResourceFact → Bool) : List (List Int) :=
  owners.map (fun owner => amounts predicate (prefixes owner))

theorem chunks_flatten (owners : List String) (prefixes : Prefixes) (predicate : ResourceFact → Bool) :
    (chunks owners prefixes predicate).flatten = amounts predicate (owners.flatMap prefixes) := by
  induction owners with
  | nil => rfl
  | cons owner rest ih =>
    simpa [chunks,amounts,List.flatMap_cons,List.filter_append,List.map_append] using congrArg (List.append (amounts predicate (prefixes owner))) ih

theorem selected_sum_bound (known selected : Facts) (predicate : ResourceFact → Bool)
    (unique : selected.Nodup) (inside : Included selected known)
    (sliceBound : known.length ≤ 2^63 - 1)
    (recognized : ∀ node ∈ known, natural64 node.data.amount) :
    i128 (amounts predicate selected).sum := by
  have length := (List.subperm_of_subset unique inside).length_le
  have filteredLength := List.length_filter_le predicate selected
  have amountLength : (amounts predicate selected).length ≤ known.length := by
    simp only [amounts,List.length_map]
    omega
  have bounds := sum_bounds (2^63 - 1) (amounts predicate selected) (by
    intro value member
    obtain ⟨node,hn,rfl⟩ := List.mem_map.mp member
    have bound := recognized node (inside node (List.mem_filter.mp hn).1)
    unfold natural64 at bound
    constructor <;> omega)
  apply aggregate_i128_bound (known.length : Int) 0 (by omega) (by omega) (by omega) (by omega)
    (amounts predicate selected).sum
  · have castLength : ((amounts predicate selected).length : Int) ≤ (known.length : Int) := by omega
    omega
  · have castLength : ((amounts predicate selected).length : Int) ≤ (known.length : Int) := by omega
    omega

/-- Native grouped incoming transfers equal flat exact-cone transfers,
including all checked i128 intermediates. The only size premise is the native
slice representation limit; chunk bounds and partition are conclusions. -/
theorem frontier_incoming_refinement (opener : Nat) (known cone : Facts) (cache : Cache) (tips : Tips)
    (prefixes : Prefixes) (owners : List String) (predicate : ResourceFact → Bool)
    (rep : Represents opener known cache tips prefixes) (covers : Covers prefixes cone)
    (uniqueOwners : owners.Nodup) (uniqueCone : cone.Nodup) (uniqueKnown : known.Nodup)
    (identities : IdentityConsistent known)
    (structural : StateResourceKahn.nativeKahn (StateResourceCycle.parents known) known = [])
    (ownerPresent : ∀ node ∈ cone, node.data.signer ∈ owners)
    (sliceBound : known.length ≤ 2^63 - 1) (recognized : ∀ node ∈ known, natural64 node.data.amount)
    (start : Int) (startBound : i128 start) :
    groupedIncoming (chunks owners prefixes predicate) start =
      (amounts predicate cone).foldlM checkedAdd start := by
  have partition := frontier_partition opener known cone cache tips prefixes owners rep covers
    uniqueOwners uniqueCone uniqueKnown identities structural ownerPresent
  have chains := represented_chain opener known cache tips prefixes rep
  apply groupedIncoming_refinement
  · rw [chunks_flatten]
    exact (partition.filter predicate).map (fun node => node.data.amount)
  · intro chunk member value inside
    obtain ⟨owner,_,rfl⟩ := List.mem_map.mp member
    obtain ⟨node,hn,rfl⟩ := List.mem_map.mp inside
    exact (recognized node ((chains owner).2 node (List.mem_filter.mp hn).1)).1
  · intro chunk member
    obtain ⟨owner,_,rfl⟩ := List.mem_map.mp member
    have ids := native_prefix_ids_unique owner opener known (prefixes owner) uniqueKnown identities structural
      (chains owner).1 (chains owner).2
    have nodup : (prefixes owner).Nodup := List.Pairwise.of_map Fact.id
      (fun _ _ ne eq => ne (congrArg Fact.id eq)) ids
    exact selected_sum_bound known (prefixes owner) predicate nodup (chains owner).2 sliceBound recognized
  · exact startBound


/-- Select incoming transfers to the requested account. -/
def incomingPredicate (recipient : String) (headroom : Bool) (node : ResourceFact) : Bool :=
  node.data.signer != recipient &&
    node.data.kind == (if headroom then ResourceKind.transferHeadroom else ResourceKind.transfer) &&
    node.data.selected.recipient == some recipient

/-- Actual map lookup used by local_budgets; the current owner's tip is skipped. -/
def readIncoming (cache : Cache) (tips : Tips) (recipient : String) (headroom : Bool) (owner : String) : Option Int := do
  if owner = recipient then some 0 else
    match tips owner with
    | none => some 0
    | some address =>
      let entry ← cache address
      some (if headroom then entry.2.sentHeadroom recipient else entry.2.sentRights recipient)

theorem amounts_sum (predicate : ResourceFact → Bool) (facts : Facts) :
    (amounts predicate facts).sum = (facts.map (fun node => if predicate node then node.data.amount else 0)).sum := by
  induction facts with
  | nil => rfl
  | cons node rest ih =>
    simp only [amounts] at ih
    cases selected : predicate node <;> simp [amounts,selected,ih]

theorem readIncoming_refinement (opener : Nat) (known : Facts) (cache : Cache) (tips : Tips)
    (prefixes : Prefixes) (rep : Represents opener known cache tips prefixes)
    (recipient owner : String) (headroom : Bool) :
    readIncoming cache tips recipient headroom owner =
      some (amounts (incomingPredicate recipient headroom) (prefixes owner)).sum := by
  have meaning := rep owner
  have chain := (represented_chain opener known cache tips prefixes rep owner).1
  by_cases own : owner = recipient
  · have zero : amounts (incomingPredicate recipient headroom) (prefixes owner) = [] := by
      have nil : (prefixes owner).filter (incomingPredicate recipient headroom) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro node member
        simp [incomingPredicate,chain_owner owner opener (prefixes owner) chain node member,own]
      simp [amounts,nil]
    rw [zero]
    simp [readIncoming,own]
  · cases selected : tips owner with
    | none =>
      have nil : prefixes owner = [] := by simpa [selected] using meaning
      simp [readIncoming,own,selected,nil,amounts]
    | some address =>
      simp only [selected] at meaning
      obtain ⟨node,summary,cached,_,_,_,_,folded⟩ := meaning
      have counters := (native_counters_refinement (prefixes owner) summary folded).2.2 recipient
      rw [amounts_sum]
      cases headroom with
      | false =>
        have same : (prefixes owner).map (fun node => if incomingPredicate recipient false node then node.data.amount else 0) =
            (prefixes owner).map (fun n => if n.data.kind = .transfer ∧ n.data.selected.recipient = some recipient then n.data.amount else 0) := by
          apply List.map_congr_left
          intro entry member
          simp [incomingPredicate,chain_owner owner opener (prefixes owner) chain entry member,own]
        simp [readIncoming,own,selected,cached,same,← counters.1]
      | true =>
        have same : (prefixes owner).map (fun node => if incomingPredicate recipient true node then node.data.amount else 0) =
            (prefixes owner).map (fun n => if n.data.kind = .transferHeadroom ∧ n.data.selected.recipient = some recipient then n.data.amount else 0) := by
          apply List.map_congr_left
          intro entry member
          simp [incomingPredicate,chain_owner owner opener (prefixes owner) chain entry member,own]
        simp [readIncoming,own,selected,cached,same,← counters.2]


/-- Compute incoming transfers using the native frontier summaries. -/
def nativeIncoming (cache : Cache) (tips : Tips) (recipient : String) (headroom : Bool)
    (owners : List String) (start : Int) : Option Int :=
  owners.foldlM (fun balance owner => do
    let amount ← readIncoming cache tips recipient headroom owner
    checkedAdd balance amount) start

theorem nativeIncoming_as_totals (opener : Nat) (known : Facts) (cache : Cache) (tips : Tips)
    (prefixes : Prefixes) (rep : Represents opener known cache tips prefixes)
    (recipient : String) (headroom : Bool) (owners : List String) (start : Int) :
    nativeIncoming cache tips recipient headroom owners start =
      ((chunks owners prefixes (incomingPredicate recipient headroom)).map List.sum).foldlM checkedAdd start := by
  induction owners generalizing start with
  | nil => rfl
  | cons owner rest ih =>
    simp only [nativeIncoming,List.foldlM_cons,chunks,List.map_cons]
    rw [readIncoming_refinement opener known cache tips prefixes rep recipient owner headroom]
    cases next : checkedAdd start (amounts (incomingPredicate recipient headroom) (prefixes owner)).sum with
    | none => simp [next]
    | some balance => simpa [next,nativeIncoming,chunks] using ih balance

/-- The actual cached sent-rights/sent-headroom lookups, not supplied transfer
sums, agree with checked exact-cone incoming arithmetic. -/
theorem native_incoming_cone_refinement (opener : Nat) (known cone : Facts) (cache : Cache) (tips : Tips)
    (prefixes : Prefixes) (owners : List String) (recipient : String) (headroom : Bool)
    (rep : Represents opener known cache tips prefixes) (covers : Covers prefixes cone)
    (uniqueOwners : owners.Nodup) (uniqueCone : cone.Nodup) (uniqueKnown : known.Nodup)
    (identities : IdentityConsistent known)
    (structural : StateResourceKahn.nativeKahn (StateResourceCycle.parents known) known = [])
    (ownerPresent : ∀ node ∈ cone, node.data.signer ∈ owners)
    (sliceBound : known.length ≤ 2^63 - 1) (recognized : ∀ node ∈ known, natural64 node.data.amount)
    (start : Int) (startBound : i128 start) :
    nativeIncoming cache tips recipient headroom owners start =
      (amounts (incomingPredicate recipient headroom) cone).foldlM checkedAdd start := by
  let predicate := incomingPredicate recipient headroom
  have chains := represented_chain opener known cache tips prefixes rep
  have positive : ∀ chunk ∈ chunks owners prefixes predicate, ∀ value ∈ chunk, 0 ≤ value := by
    intro chunk member value inside
    obtain ⟨owner,_,rfl⟩ := List.mem_map.mp member
    obtain ⟨node,hn,rfl⟩ := List.mem_map.mp inside
    exact (recognized node ((chains owner).2 node (List.mem_filter.mp hn).1)).1
  have bounded : ∀ chunk ∈ chunks owners prefixes predicate, i128 chunk.sum := by
    intro chunk member
    obtain ⟨owner,_,rfl⟩ := List.mem_map.mp member
    have ids := native_prefix_ids_unique owner opener known (prefixes owner) uniqueKnown identities structural
      (chains owner).1 (chains owner).2
    have nodup : (prefixes owner).Nodup := List.Pairwise.of_map Fact.id
      (fun _ _ ne eq => ne (congrArg Fact.id eq)) ids
    exact selected_sum_bound known (prefixes owner) predicate nodup (chains owner).2 sliceBound recognized
  rw [nativeIncoming_as_totals opener known cache tips prefixes rep recipient headroom owners start]
  change ((chunks owners prefixes predicate).map List.sum).foldlM checkedAdd start = _
  rw [← groupedIncoming_as_totals (chunks owners prefixes predicate) positive bounded start]
  exact frontier_incoming_refinement opener known cone cache tips prefixes owners predicate rep covers
    uniqueOwners uniqueCone uniqueKnown identities structural ownerPresent sliceBound recognized start startBound


theorem checked_selected_present (known C : Facts) (predicate : ResourceFact → Bool)
    (unique : C.Nodup) (inside : Included C known) (sliceBound : known.length ≤ 2^63 - 1)
    (recognized : ∀ node ∈ known, natural64 node.data.amount) :
    ∃ value, checkedSum (amounts predicate (ordered C)) = some value := by
  have permutation : (ordered C).Perm C := List.mergeSort_perm C _
  have orderedInside : Included (ordered C) known :=
    fun node member => inside node (permutation.mem_iff.mp member)
  have positive : ∀ value ∈ amounts predicate (ordered C), 0 ≤ value := by
    intro value member
    obtain ⟨node,hn,rfl⟩ := List.mem_map.mp member
    exact (recognized node (orderedInside node (List.mem_filter.mp hn).1)).1
  have bound := selected_sum_bound known (ordered C) predicate (permutation.symm.nodup unique)
    orderedInside sliceBound recognized
  refine ⟨(amounts predicate (ordered C)).sum,?_⟩
  rw [checkedSum_nonnegative _ positive]
  exact if_pos bound

/-- Under native slice/i64 recognition bounds, summary overflow cannot be an
additional resource fault. The bounds are derived for every selected total. -/
theorem summaryFault_unreachable (known C : Facts) (node : ResourceFact)
    (unique : C.Nodup) (inside : Included C known) (sliceBound : known.length ≤ 2^63 - 1)
    (recognized : ∀ entry ∈ known, natural64 entry.data.amount) : ¬summaryFault node C := by
  have length := (List.subperm_of_subset unique inside).length_le
  have count := List.length_filter_le (fun entry : ResourceFact => entry.data.signer == node.data.signer) C
  have selected := checked_selected_present known C
  have increment : ∃ value, ownTotal C node.data.signer .increment = some value := by
    exact selected (fun entry => entry.data.signer == node.data.signer && entry.data.kind == .increment)
      unique inside sliceBound recognized
  have decrement : ∃ value, ownTotal C node.data.signer .decrement = some value := by
    exact selected (fun entry => entry.data.signer == node.data.signer && entry.data.kind == .decrement)
      unique inside sliceBound recognized
  intro bad
  rcases bad with sequence | inc | dec | ⟨recipient,transfer⟩
  · omega
  · obtain ⟨value,equal⟩ := increment
    rw [equal] at inc; contradiction
  · obtain ⟨value,equal⟩ := decrement
    rw [equal] at dec; contradiction
  · obtain ⟨value,equal⟩ := selected (fun entry => entry.data.signer == node.data.signer &&
        entry.data.kind == node.data.kind && entry.data.selected.recipient == some recipient)
        unique inside sliceBound recognized
    change checkedSum (amounts _ (ordered C)) = none at transfer
    rw [equal] at transfer; contradiction


theorem budgetFault_perm (c : ResourceConfig) (op node : ResourceFact) {C D : Facts}
    (permutation : C.Perm D) (identities : ∀ x ∈ C, ∀ y ∈ D, x.id = y.id → x = y) :
    budgetFault c op node C ↔ budgetFault c op node D := by
  have canonical := ordered_of_perm permutation identities
  have count := (permutation.filter (fun entry => entry.data.signer == node.data.signer)).length_eq
  have budgets (headroom : Bool) := localBudget_perm op node permutation identities headroom
  simp only [budgetFault,summaryFault,ownTotal,canonical,count,budgets]

theorem budgetFault_cone_unique (c : ResourceConfig) (op node : ResourceFact) {C D : Facts}
    (left : ExactCone op node C) (right : ExactCone op node D)
    (excludeC : ∀ entry ∈ C, entry.id ≠ op.id) (excludeD : ∀ entry ∈ D, entry.id ≠ op.id)
    (identities : ∀ x ∈ C, ∀ y ∈ D, x.id = y.id → x = y) :
    budgetFault c op node C ↔ budgetFault c op node D := by
  have uniqueC : C.Nodup := List.Pairwise.of_map Fact.id
    (fun _ _ ne eq => ne (congrArg Fact.id eq)) left.2.1
  have uniqueD : D.Nodup := List.Pairwise.of_map Fact.id
    (fun _ _ ne eq => ne (congrArg Fact.id eq)) right.2.1
  have permutation := (List.perm_ext_iff_of_nodup uniqueC uniqueD).mpr
    (exact_cone_unique left right excludeC excludeD identities)
  exact budgetFault_perm c op node permutation identities

end CBCL.StateResourceBudget
