import LeanCbcl.StateResourceMachine

/-! Native Summary::record cannot introduce an unclassified overflow after
recognized operations on a finite native slice. Every updated field is bounded
by the corresponding selected sum of the actual owner prefix plus this act. -/
namespace CBCL.StateResourceRecordBounds
open State CheckpointEvidence StateResource StateResourceNative StateResourceSummary StateResourceBudget

theorem amounts_append_one (predicate : ResourceFact → Bool) (chain : Facts) (node : ResourceFact) :
    (amounts predicate (chain ++ [node])).sum =
      (amounts predicate chain).sum + if predicate node then node.data.amount else 0 := by
  rw [amounts_sum,amounts_sum]
  simp [List.map_append,List.sum_append]

theorem native_record_complete (c : ResourceConfig) (op root node : ResourceFact) (known chain : Facts) (own : Summary)
    (validNode : validOperation c op root node) (operations : ∀ entry ∈ known, validOperation c op root entry)
    (unique : (chain ++ [node]).Nodup) (inside : Included (chain ++ [node]) known)
    (sliceBound : known.length ≤ 2^63 - 1) (prefixRun : run chain empty = some own) :
    ∃ updated, record own node = some updated := by
  have length := (List.subperm_of_subset unique inside).length_le
  have seq := native_sequence_is_prefix_length chain own prefixRun
  have nextSequence : own.sequence + 1 < 2^64 := by simp only [List.length_append,List.length_singleton] at length; omega
  have recognized : ∀ entry ∈ known, natural64 entry.data.amount := by
    intro entry member
    obtain ⟨_,_,_,_,_,_,amount,_⟩ := operations entry member
    exact amount
  have bound (predicate : ResourceFact → Bool) := selected_sum_bound known (chain ++ [node]) predicate unique inside sliceBound recognized
  have component (predicate : ResourceFact → Bool) (value : Int)
      (counter : value = (amounts predicate chain).sum) (selected : predicate node = true) : i128 (value + node.data.amount) := by
    have bounded := bound predicate
    rw [amounts_append_one,selected,← counter] at bounded
    exact bounded
  have counters := native_counters_refinement chain own prefixRun
  have allowed := validNode.1
  unfold record
  rw [if_pos nextSequence]
  cases kind : node.data.kind <;> simp only [kind]
  all_goals try { simp [kindMatches,kind] at allowed }
  case increment =>
    have value : own.credited = (amounts (fun entry => entry.data.kind == .increment) chain).sum := by
      rw [amounts_sum]; simpa using counters.1
    have bounded := component (fun entry => entry.data.kind == .increment) own.credited value (by simp [kind])
    have checked : checkedAdd own.credited node.data.amount = some (own.credited + node.data.amount) :=
      (checkedAdd_iff _ _ _).mpr ⟨bounded,rfl⟩
    simp [checked]
  case decrement =>
    have value : own.debited = (amounts (fun entry => entry.data.kind == .decrement) chain).sum := by
      rw [amounts_sum]; simpa using counters.2.1
    have bounded := component (fun entry => entry.data.kind == .decrement) own.debited value (by simp [kind])
    have checked : checkedAdd own.debited node.data.amount = some (own.debited + node.data.amount) :=
      (checkedAdd_iff _ _ _).mpr ⟨bounded,rfl⟩
    simp [checked]
  case transfer =>
    obtain ⟨_,recipient,recipientValue,_,_⟩ := validNode.2.2.2.2.2.2.2.2.2.2.2.2.2.2 (Or.inl kind)
    rw [recipientValue]
    have value : own.sentRights recipient = (amounts (fun entry =>
        entry.data.kind == .transfer && entry.data.selected.recipient == some recipient) chain).sum := by
      rw [amounts_sum]; simpa using (counters.2.2 recipient).1
    have bounded := component (fun entry => entry.data.kind == .transfer && entry.data.selected.recipient == some recipient)
      (own.sentRights recipient) value (by simp [kind,recipientValue])
    have checked : checkedAdd (own.sentRights recipient) node.data.amount = some (own.sentRights recipient + node.data.amount) :=
      (checkedAdd_iff _ _ _).mpr ⟨bounded,rfl⟩
    simp [checked]
  case transferHeadroom =>
    obtain ⟨_,recipient,recipientValue,_,_⟩ := validNode.2.2.2.2.2.2.2.2.2.2.2.2.2.2 (Or.inr kind)
    rw [recipientValue]
    have value : own.sentHeadroom recipient = (amounts (fun entry =>
        entry.data.kind == .transferHeadroom && entry.data.selected.recipient == some recipient) chain).sum := by
      rw [amounts_sum]; simpa using (counters.2.2 recipient).2
    have bounded := component (fun entry => entry.data.kind == .transferHeadroom && entry.data.selected.recipient == some recipient)
      (own.sentHeadroom recipient) value (by simp [kind,recipientValue])
    have checked : checkedAdd (own.sentHeadroom recipient) node.data.amount = some (own.sentHeadroom recipient + node.data.amount) :=
      (checkedAdd_iff _ _ _).mpr ⟨bounded,rfl⟩
    simp [checked]


/-- The whole-machine invariant reconstructs the complete owner prefix and
native acyclicity proves its freshness. A ready recognized operation therefore
cannot take the native Summary::record failure branch. -/
theorem machine_record_complete (c : ResourceConfig) (op root node : ResourceFact) (known : Facts)
    (machine : StateResourceMachine.Machine) (ghost : StateResourceMachine.Ghost)
    (parents : List (ResourceFact × Facts)) (own : Summary)
    (invariant : StateResourceMachine.Invariant op known machine ghost)
    (fresh : machine.summaries node.id = none)
    (lookups : StateResourceCones.gather op ghost.cones (links node) = some parents)
    (previous : StateResourceCache.previousSummary op.id machine.summaries node = some own)
    (accepted : node ∈ known) (unique : (known.map Fact.id).Nodup)
    (nonforking : StateResourceStructure.Nonforking known)
    (foreignChecked : StateResourceStructure.previousOwnerCheck op.id known = true)
    (structural : StateResourceKahn.nativeKahn (StateResourceCycle.parents known) known = [])
    (operations : ∀ entry ∈ known, validOperation c op root entry) (sliceBound : known.length ≤ 2^63 - 1) :
    ∃ updated, record own node = some updated := by
  have unprocessed := StateResourceMachine.fresh_excludes_parent_cones op node known machine ghost invariant fresh parents lookups
  obtain ⟨chain,_,chainProof,inside,folded⟩ := StateResourceOwnPrefix.merged_previous_prefix op node known machine.summaries ghost.cones machine.tips ghost.prefixes
    parents own invariant.parents invariant.summaries invariant.ownTips lookups nonforking accepted unique foreignChecked unprocessed structural previous
  have wholeInside : Included (chain ++ [node]) known := by
    intro entry member
    rcases List.mem_append.mp member with old | current
    · exact inside entry old
    · simpa using (List.mem_singleton.mp current ▸ accepted)
  have uniqueKnown : known.Nodup := List.Pairwise.of_map Fact.id (fun _ _ ne eq => ne (congrArg Fact.id eq)) unique
  have identities := StateResourceDependency.unique_ids_consistent known unique
  have ids := StateResourcePartition.native_prefix_ids_unique node.data.signer op.id known (chain ++ [node]) uniqueKnown identities structural chainProof wholeInside
  have noRepeat : (chain ++ [node]).Nodup := List.Pairwise.of_map Fact.id (fun _ _ ne eq => ne (congrArg Fact.id eq)) ids
  exact native_record_complete c op root node known chain own (operations node accepted) operations noRepeat wholeInside sliceBound folded

end CBCL.StateResourceRecordBounds
