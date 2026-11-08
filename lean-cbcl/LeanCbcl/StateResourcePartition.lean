import LeanCbcl.StateResourceFrontier
import LeanCbcl.StateResourceCycle

/-! The checked native structural traversal supplies the strict rank used to
rule out repeated prefix identities. Owner frontiers then partition the exact
cone, discharging the partition premise of grouped budget arithmetic. -/
namespace CBCL.StateResourcePartition
open State CheckpointEvidence StateResource StateResourceCache StateResourceStructure StateResourceFrontier

theorem chain_owner (owner : String) (opener : Nat) (chain : Facts)
    (meaning : OwnerChain owner opener chain) (node : ResourceFact) (member : node ∈ chain) :
    node.data.signer = owner := by
  induction chain generalizing opener with
  | nil => simp at member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with rfl | tail
    · exact meaning.1
    · exact ih first.id meaning.2.2 tail

def Ranked (known : Facts) (rank : ResourceFact → Nat) : Prop :=
  ∀ child ∈ known, ∀ parent ∈ known, parent.id ∈ links child → rank parent < rank child

theorem chain_rank_after (owner : String) (known chain : Facts) (previous : ResourceFact)
    (rank : ResourceFact → Nat) (ranked : Ranked known rank) (accepted : previous ∈ known)
    (meaning : OwnerChain owner previous.id chain) (inside : Included chain known) :
    ∀ node ∈ chain, rank previous < rank node := by
  induction chain generalizing previous with
  | nil => simp
  | cons first rest ih =>
    have firstKnown : first ∈ known := inside first (by simp)
    have edge : previous.id ∈ links first := by simp [links,meaning.2.1]
    have before := ranked first firstKnown previous accepted edge
    intro node member
    rcases List.mem_cons.mp member with rfl | tail
    · exact before
    · exact Nat.lt_trans before (ih first firstKnown meaning.2.2
        (fun entry he => inside entry (by simp [he])) node tail)

theorem chain_ids_unique (owner : String) (opener : Nat) (known chain : Facts)
    (rank : ResourceFact → Nat) (ranked : Ranked known rank) (identities : IdentityConsistent known)
    (meaning : OwnerChain owner opener chain) (inside : Included chain known) :
    (chain.map Fact.id).Nodup := by
  induction chain generalizing opener with
  | nil => simp
  | cons first rest ih =>
    have firstKnown : first ∈ known := inside first (by simp)
    have restInside : Included rest known := fun entry he => inside entry (by simp [he])
    simp only [List.map_cons,List.nodup_cons]
    constructor
    · intro member
      obtain ⟨other,ho,equal⟩ := List.mem_map.mp member
      have same := identities other (restInside other ho) first firstKnown equal
      have before := chain_rank_after owner known rest first rank ranked firstKnown meaning.2.2 restInside other ho
      rw [same] at before
      exact Nat.lt_irrefl _ before
    · exact ih first.id meaning.2.2 restInside

/-- Native successful cycle elimination, rather than a supplied acyclicity
oracle, proves that every cached owner prefix has unique accepted identities. -/
theorem native_prefix_ids_unique (owner : String) (opener : Nat) (known chain : Facts)
    (unique : known.Nodup) (identities : IdentityConsistent known)
    (structural : StateResourceKahn.nativeKahn (StateResourceCycle.parents known) known = [])
    (meaning : OwnerChain owner opener chain) (inside : Included chain known) :
    (chain.map Fact.id).Nodup := by
  obtain ⟨rank,lower⟩ := StateResourceKahn.nativeKahn_rank (StateResourceCycle.parents known) known unique structural
  apply chain_ids_unique owner opener known chain rank ?_ identities meaning inside
  intro child hc parent hp edge
  exact lower child hc parent hp ((StateResourceCycle.parent_iff known child parent).mpr ⟨hp,edge⟩)

theorem grouped_prefixes_nodup (owners : List String) (prefixes : Prefixes)
    (uniqueOwners : owners.Nodup) (uniquePrefixes : ∀ owner ∈ owners, (prefixes owner).Nodup)
    (owned : ∀ owner ∈ owners, ∀ node ∈ prefixes owner, node.data.signer = owner) :
    (owners.flatMap prefixes).Nodup := by
  induction owners with
  | nil => simp
  | cons owner rest ih =>
    obtain ⟨notIn,unique⟩ := List.nodup_cons.mp uniqueOwners
    simp only [List.flatMap_cons,List.nodup_append]
    refine ⟨uniquePrefixes owner (by simp),ih unique
      (fun o h => uniquePrefixes o (by simp [h])) (fun o h => owned o (by simp [h])),?_⟩
    intro left hl right hr equal
    obtain ⟨other,ho,member⟩ := List.mem_flatMap.mp hr
    have ownLeft := owned owner (by simp) left hl
    have ownRight := owned other (by simp [ho]) right member
    have same : other = owner := ownRight.symm.trans ((congrArg (fun n : ResourceFact => n.data.signer) equal.symm).trans ownLeft)
    exact notIn (same ▸ ho)

/-- The owner-frontier partition is a permutation of the represented cone.
Thus grouped transfers use each accepted operation exactly once. -/
theorem frontier_partition (opener : Nat) (known cone : Facts) (cache : Cache) (tips : Tips)
    (prefixes : Prefixes) (owners : List String) (rep : Represents opener known cache tips prefixes)
    (covers : Covers prefixes cone) (uniqueOwners : owners.Nodup) (uniqueCone : cone.Nodup)
    (uniqueKnown : known.Nodup) (identities : IdentityConsistent known)
    (structural : StateResourceKahn.nativeKahn (StateResourceCycle.parents known) known = [])
    (ownerPresent : ∀ node ∈ cone, node.data.signer ∈ owners) :
    (owners.flatMap prefixes).Perm cone := by
  have chains := represented_chain opener known cache tips prefixes rep
  have owned : ∀ owner ∈ owners, ∀ node ∈ prefixes owner, node.data.signer = owner :=
    fun owner _ node member => chain_owner owner opener (prefixes owner) (chains owner).1 node member
  have uniquePrefixes : ∀ owner ∈ owners, (prefixes owner).Nodup := by
    intro owner _
    have ids := native_prefix_ids_unique owner opener known (prefixes owner) uniqueKnown identities structural
      (chains owner).1 (chains owner).2
    exact List.Pairwise.of_map Fact.id (fun _ _ ne eq => ne (congrArg Fact.id eq)) ids
  apply (List.perm_ext_iff_of_nodup (grouped_prefixes_nodup owners prefixes uniqueOwners uniquePrefixes owned) uniqueCone).mpr
  intro node
  constructor
  · intro member
    obtain ⟨owner,_,inside⟩ := List.mem_flatMap.mp member
    exact (covers node).mpr ⟨owner,inside⟩
  · intro member
    obtain ⟨owner,inside⟩ := (covers node).mp member
    have same := chain_owner owner opener (prefixes owner) (chains owner).1 node inside
    exact List.mem_flatMap.mpr ⟨owner,by simpa [same] using ownerPresent node member,inside⟩

end CBCL.StateResourcePartition
