import LeanCbcl.StateResourceCones
import LeanCbcl.StateResourceFrontier
import LeanCbcl.StateResourceBudget

/-! Dependency-cache lookups coupled to the full native frontier merge loop.
Cone/prefix stores are ghost annotations. The computed tips contain only
identities and use the actual native summary cache for sequence arbitration. -/
namespace CBCL.StateResourceDependency
open State CheckpointEvidence StateResource StateResourceSummary StateResourceCache StateResourceStructure
open StateResourceFrontier

/-- The owner-tip map with no recognized prefixes. -/
def emptyTips : Tips := fun _ => none
/-- The owner-prefix map with empty prefixes. -/
def emptyPrefixes : Prefixes := fun _ => []

theorem empty_represents (opener : Nat) (known : Facts) (cache : Cache) :
    Represents opener known cache emptyTips emptyPrefixes := by intro owner; rfl

/-- Lookup annotations relate the same cached identity across summary, cone,
and frontier stores. There is no free display/error callback. -/
def ParentInvariant (op : ResourceFact) (known : Facts) (cache : Cache)
    (cones : StateResourceCones.ConeCache) (tips : Nat → Tips) (prefixes : Nat → Prefixes) : Prop :=
  StateResourceCones.Valid op known cones ∧
    ∀ address node cone, cones address = some (node,cone) →
      Represents op.id known cache (tips address) (prefixes address) ∧ Covers (prefixes address) cone

/-- Merge the cached parent frontier tips. -/
def mergedTips (cache : Cache) (tips : Nat → Tips) (parents : List (ResourceFact × Facts)) : Tips :=
  mergeAll cache emptyTips (parents.map (fun entry => tips entry.1.id))

/-- Merge the cached parent owner prefixes. -/
def mergedPrefixes (prefixes : Nat → Prefixes) (parents : List (ResourceFact × Facts)) : Prefixes :=
  mergeAllPrefixes emptyPrefixes (parents.map (fun entry => prefixes entry.1.id))

theorem parent_frontier_union (op node : ResourceFact) (known : Facts) (cache : Cache)
    (cones : StateResourceCones.ConeCache) (tips : Nat → Tips) (prefixes : Nat → Prefixes)
    (parents : List (ResourceFact × Facts)) (invariant : ParentInvariant op known cache cones tips prefixes)
    (lookups : StateResourceCones.gather op cones (links node) = some parents)
    (nonforking : Nonforking known) :
    Represents op.id known cache (mergedTips cache tips parents) (mergedPrefixes prefixes parents) ∧
    ∀ entry, (∃ owner, entry ∈ mergedPrefixes prefixes parents owner) ↔
      ∃ parent ∈ parents, entry ∈ parent.2 := by
  have sound := (StateResourceCones.gather_lookup op cones (links node) parents lookups).1
  have meaning : ∀ parent ∈ parents,
      Represents op.id known cache (tips parent.1.id) (prefixes parent.1.id) ∧ Covers (prefixes parent.1.id) parent.2 := by
    intro parent member
    obtain ⟨address,_,_,cached⟩ := sound parent member
    have identity := (invariant.1 address parent.1 parent.2 cached).1
    simpa [identity] using invariant.2 address parent.1 parent.2 cached
  let packets := parents.map (fun parent => (tips parent.1.id,prefixes parent.1.id))
  have reps : ∀ packet ∈ packets, Represents op.id known cache packet.1 packet.2 := by
    intro packet member
    obtain ⟨parent,hp,rfl⟩ := List.mem_map.mp member
    exact (meaning parent hp).1
  constructor
  · simpa [mergedTips,mergedPrefixes,packets,List.map_map] using
      mergeAll_represents op.id known cache emptyTips emptyPrefixes packets (empty_represents _ _ _) reps
  · intro entry
    have members (owner : String) := mergeAll_members op.id known cache emptyTips emptyPrefixes packets
      (empty_represents _ _ _) reps nonforking owner entry
    constructor
    · rintro ⟨owner,member⟩
      have selected : entry ∈ mergeAllPrefixes emptyPrefixes (packets.map Prod.snd) owner := by
        simpa [mergedPrefixes,packets,List.map_map] using member
      rcases (members owner).mp selected with impossible | ⟨packet,hp,inside⟩
      · simp [emptyPrefixes] at impossible
      · obtain ⟨parent,parentMember,rfl⟩ := List.mem_map.mp hp
        exact ⟨parent,parentMember,((meaning parent parentMember).2 entry).mpr ⟨owner,inside⟩⟩
    · rintro ⟨parent,hp,inside⟩
      obtain ⟨owner,member⟩ := ((meaning parent hp).2 entry).mp inside
      have selected := (members owner).mpr (Or.inr ⟨(tips parent.1.id,prefixes parent.1.id),
        List.mem_map.mpr ⟨parent,hp,rfl⟩,member⟩)
      exact ⟨owner,by simpa [mergedPrefixes,packets,List.map_map] using selected⟩

theorem unionCone_past (known : Facts) (node entry : ResourceFact) (parents : List (ResourceFact × Facts))
    (inside : ∀ parent ∈ parents, Included parent.2 known)
    (unprocessed : ∀ parent ∈ parents, ∀ entry ∈ parent.2, entry.id ≠ node.id) :
    entry ∈ (StateResourceCones.unionCone known node parents).filter (fun entry => entry.id != node.id) ↔
      ∃ parent ∈ parents, entry ∈ parent.2 := by
  constructor
  · intro member
    have selected := List.mem_filter.mp member
    rcases ((StateResourceCones.unionCone_member known node entry parents).mp selected.1).2 with same | parent
    · subst entry; simp at selected
    · exact parent
  · rintro ⟨parent,hp,member⟩
    exact List.mem_filter.mpr ⟨(StateResourceCones.unionCone_member known node entry parents).mpr
      ⟨inside parent hp entry member,Or.inr ⟨parent,hp,member⟩⟩,by simpa using unprocessed parent hp entry member⟩

/-- Full pre-record frontier: actual dependency lookups and the complete
native merge loop represent exactly the operation's past closed cone.
The unprocessed premise is the worklist's fresh-identity invariant. -/
theorem pre_record_frontier_exact (op node : ResourceFact) (known : Facts) (cache : Cache)
    (cones : StateResourceCones.ConeCache) (tips : Nat → Tips) (prefixes : Nat → Prefixes)
    (parents : List (ResourceFact × Facts)) (invariant : ParentInvariant op known cache cones tips prefixes)
    (lookups : StateResourceCones.gather op cones (links node) = some parents)
    (nonforking : Nonforking known) (accepted : node ∈ known) (unique : (known.map Fact.id).Nodup)
    (unprocessed : ∀ parent ∈ parents, ∀ entry ∈ parent.2, entry.id ≠ node.id) :
    let cone := StateResourceCones.unionCone known node parents
    ExactCone op node cone ∧
      Represents op.id known cache (mergedTips cache tips parents) (mergedPrefixes prefixes parents) ∧
      Covers (mergedPrefixes prefixes parents) (cone.filter (fun entry => entry.id != node.id)) := by
  have reconstructed : StateResourceCones.reconstruct op known cones node =
      some (StateResourceCones.unionCone known node parents) := by simp [StateResourceCones.reconstruct,lookups]
  have exactCone := StateResourceCones.reconstruct_exact op node known cones _ invariant.1 accepted unique reconstructed
  obtain ⟨rep,covered⟩ := parent_frontier_union op node known cache cones tips prefixes parents invariant lookups nonforking
  have sound := (StateResourceCones.gather_lookup op cones (links node) parents lookups).1
  have inside : ∀ parent ∈ parents, Included parent.2 known := by
    intro parent hp
    obtain ⟨address,_,_,cached⟩ := sound parent hp
    exact (invariant.1 address parent.1 parent.2 cached).2.2.1
  exact ⟨exactCone,rep,fun entry => (unionCone_past known node entry parents inside unprocessed).trans (covered entry).symm⟩


theorem unique_ids_consistent (known : Facts) (unique : (known.map Fact.id).Nodup) :
    IdentityConsistent known := by
  induction known with
  | nil => intro _ member; simp at member
  | cons first rest ih =>
    obtain ⟨notIn,tailUnique⟩ := List.nodup_cons.mp unique
    intro left hl right hr equal
    rcases List.mem_cons.mp hl with rfl | leftTail
    · rcases List.mem_cons.mp hr with rfl | rightTail
      · rfl
      · exact False.elim (notIn (List.mem_map.mpr ⟨right,rightTail,equal.symm⟩))
    · rcases List.mem_cons.mp hr with rfl | rightTail
      · exact False.elim (notIn (List.mem_map.mpr ⟨left,leftTail,equal⟩))
      · exact ih tailUnique left leftTail right rightTail equal

/-- Coupled dependency/frontier/incoming refinement. The cone and its owner
partition are reconstructed from the same parent-cache lookups used by the
native merge loop; neither ExactCone, Represents nor Covers is a premise for
the new operation. -/
theorem dependency_incoming_exact_cone (c : ResourceConfig) (op root node : ResourceFact)
    (known : Facts) (cache : Cache) (cones : StateResourceCones.ConeCache)
    (tips : Nat → Tips) (prefixes : Nat → Prefixes) (parents : List (ResourceFact × Facts))
    (invariant : ParentInvariant op known cache cones tips prefixes)
    (lookups : StateResourceCones.gather op cones (links node) = some parents)
    (nonforking : Nonforking known) (accepted : node ∈ known) (unique : (known.map Fact.id).Nodup)
    (unprocessed : ∀ parent ∈ parents, ∀ entry ∈ parent.2, entry.id ≠ node.id)
    (initial : validInitial c op root) (operations : ∀ entry ∈ known, validOperation c op root entry)
    (structural : StateResourceKahn.nativeKahn (StateResourceCycle.parents known) known = [])
    (sliceBound : known.length ≤ 2^63 - 1) (headroom : Bool) (start : Int) (startBound : i128 start) :
    let cone := StateResourceCones.unionCone known node parents
    ExactCone op node cone ∧
      StateResourceBudget.nativeIncoming cache (mergedTips cache tips parents) node.data.signer headroom
        ((accounts op.data.selected.initialAllocations).map Prod.fst) start =
      (StateResourceBudget.amounts (StateResourceBudget.incomingPredicate node.data.signer headroom)
        (cone.filter (fun entry => entry.id != node.id))).foldlM checkedAdd start := by
  obtain ⟨exactCone,rep,covers⟩ := pre_record_frontier_exact op node known cache cones tips prefixes parents
    invariant lookups nonforking accepted unique unprocessed
  let cone := StateResourceCones.unionCone known node parents
  have uniqueKnown : known.Nodup := List.Pairwise.of_map Fact.id
    (fun _ _ ne eq => ne (congrArg Fact.id eq)) unique
  have uniqueCone : cone.Nodup := List.Pairwise.of_map Fact.id
    (fun _ _ ne eq => ne (congrArg Fact.id eq)) exactCone.2.1
  have identities := unique_ids_consistent known unique
  have allocations := initial.2.2.1
  obtain ⟨rows,rowValue,_,ownerUnique,_⟩ := allocations
  have uniqueOwners : ((accounts op.data.selected.initialAllocations).map Prod.fst).Nodup := by
    simpa [accounts,rowValue] using ownerUnique
  have pastInside : Included (cone.filter (fun entry => entry.id != node.id)) known := by
    intro entry member
    exact ((StateResourceCones.unionCone_member known node entry parents).mp (List.mem_filter.mp member).1).1
  have ownerPresent : ∀ entry ∈ cone.filter (fun entry => entry.id != node.id),
      entry.data.signer ∈ (accounts op.data.selected.initialAllocations).map Prod.fst := by
    intro entry member
    exact (operations entry (pastInside entry member)).2.2.2.1
  have recognized : ∀ entry ∈ known, natural64 entry.data.amount := by
    intro entry member
    obtain ⟨_,_,_,_,_,_,amount,_⟩ := operations entry member
    exact amount
  exact ⟨exactCone,StateResourceBudget.native_incoming_cone_refinement op.id known _ cache
    (mergedTips cache tips parents) (mergedPrefixes prefixes parents) _ node.data.signer headroom rep covers
    uniqueOwners (uniqueCone.sublist List.filter_sublist) uniqueKnown identities structural ownerPresent
    sliceBound recognized start startBound⟩

end CBCL.StateResourceDependency
