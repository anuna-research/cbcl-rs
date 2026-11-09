import LeanCbcl.StateResourceDependency

/-! Connection between the native previous-summary lookup and the current
owner's prefix in the merged dependency frontier. This rules out borrowing
unrelated/future own operations when interpreting local budget counters. -/
namespace CBCL.StateResourceOwnPrefix
open State CheckpointEvidence StateResource StateResourceSummary StateResourceCache StateResourceStructure
open StateResourceFrontier StateResourcePartition StateResourceDependency

/-- Native cache insertion always sets its own-owner tip to its own identity. -/
def OwnTips (cache : Cache) (cones : StateResourceCones.ConeCache) (tips : Nat → Tips) : Prop :=
  ∀ address node cone, cones address = some (node,cone) →
    ∃ summary, cache address = some (node,summary) ∧ tips address node.data.signer = some address

theorem cached_parent_prefix (op : ResourceFact) (known : Facts) (cache : Cache)
    (cones : StateResourceCones.ConeCache) (tips : Nat → Tips) (prefixes : Nat → Prefixes)
    (invariant : ParentInvariant op known cache cones tips prefixes)
    (valid : StateResourceCache.Valid op.id known cache) (ownTips : OwnTips cache cones tips)
    (nonforking : Nonforking known) (address : Nat) (node : ResourceFact) (cone : Facts)
    (found : cones address = some (node,cone)) :
    ∃ summary chain, cache address = some (node,summary) ∧
      OwnerChain node.data.signer op.id chain ∧ Included chain known ∧
      tipId op.id chain = address ∧ run chain empty = some summary ∧
      prefixes address node.data.signer = chain := by
  obtain ⟨summary,cached,own⟩ := ownTips address node cone found
  obtain ⟨identity,chain,chainProof,tip,folded,inside,_⟩ := valid address node summary cached
  have represented := (invariant.2 address node cone found).1 node.data.signer
  rw [own] at represented
  obtain ⟨other,otherSummary,otherCached,_,_,otherChain,otherInside,otherRun⟩ := represented
  have same : node = other ∧ summary = otherSummary := by simpa [cached] using otherCached
  obtain ⟨rfl,rfl⟩ := same
  have equal := same_cached_prefix node.data.signer op.id known chain
    (prefixes address node.data.signer) summary
    (fun x hx y hy ox oy prev => nonforking x hx y hy (ox.trans oy.symm) prev)
    chainProof otherChain inside otherInside folded otherRun
  exact ⟨summary,chain,cached,chainProof,inside,by simpa [identity] using tip,folded,equal.symm⟩

theorem prefix_eq_of_subset (C D : Facts) (unique : C.Nodup) (before : D.IsPrefix C) (inside : C ⊆ D) : D = C := by
  have length := (List.subperm_of_subset unique inside).length_le
  obtain ⟨suffix,equal⟩ := before
  have lens := congrArg List.length equal
  simp only [List.length_append] at lens
  have nil : suffix = [] := List.length_eq_zero_iff.mp (by omega)
  simpa [nil] using equal

/-- The frontier's current-owner prefix is the actual previous-summary
prefix. Nonforking, native cycle elimination and worklist freshness discharge
both possible ways a dependency could otherwise enlarge that owner prefix. -/
theorem merged_previous_prefix (op node : ResourceFact) (known : Facts) (cache : Cache)
    (cones : StateResourceCones.ConeCache) (tips : Nat → Tips) (prefixes : Nat → Prefixes)
    (parents : List (ResourceFact × Facts)) (own : Summary)
    (invariant : ParentInvariant op known cache cones tips prefixes)
    (valid : StateResourceCache.Valid op.id known cache) (ownTips : OwnTips cache cones tips)
    (lookups : StateResourceCones.gather op cones (links node) = some parents)
    (nonforking : Nonforking known) (accepted : node ∈ known) (unique : (known.map Fact.id).Nodup)
    (foreignChecked : previousOwnerCheck op.id known = true)
    (unprocessed : ∀ parent ∈ parents, ∀ entry ∈ parent.2, entry.id ≠ node.id)
    (structural : StateResourceKahn.nativeKahn (StateResourceCycle.parents known) known = [])
    (previous : previousSummary op.id cache node = some own) :
    ∃ chain, mergedPrefixes prefixes parents node.data.signer = chain ∧
      OwnerChain node.data.signer op.id (chain ++ [node]) ∧ Included chain known ∧
      run chain empty = some own := by
  obtain ⟨rep,covered⟩ := parent_frontier_union op node known cache cones tips prefixes parents invariant lookups nonforking
  let D := mergedPrefixes prefixes parents node.data.signer
  obtain ⟨depChain,depInside⟩ := represented_chain op.id known cache (mergedTips cache tips parents)
    (mergedPrefixes prefixes parents) rep node.data.signer
  have notCurrent : node ∉ D := by
    intro member
    obtain ⟨parent,hp,inside⟩ := (covered node).mp ⟨node.data.signer,member⟩
    exact unprocessed parent hp node inside rfl
  have identities := unique_ids_consistent known unique
  have uniqueKnown : known.Nodup := List.Pairwise.of_map Fact.id
    (fun _ _ ne eq => ne (congrArg Fact.id eq)) unique
  have finish (C : Facts) (chainProof : OwnerChain node.data.signer op.id C)
      (inside : Included C known) (prev : node.data.prev = some (tipId op.id C))
      (folded : run C empty = some own) (included : C ⊆ D) :
      ∃ chain, mergedPrefixes prefixes parents node.data.signer = chain ∧
        OwnerChain node.data.signer op.id (chain ++ [node]) ∧ Included chain known ∧ run chain empty = some own := by
    have currentChain := ownerChain_append node.data.signer op.id C node chainProof rfl prev
    have before := dependency_own_prefix_before_current node.data.signer op.id known C D node nonforking
      currentChain depChain (fun entry member => by
        rcases List.mem_append.mp member with old | fresh
        · exact inside entry old
        · simpa using (List.mem_singleton.mp fresh ▸ accepted)) depInside notCurrent
    have ids := native_prefix_ids_unique node.data.signer op.id known C uniqueKnown identities structural chainProof inside
    have nodup : C.Nodup := List.Pairwise.of_map Fact.id (fun _ _ ne eq => ne (congrArg Fact.id eq)) ids
    have equal : D = C := prefix_eq_of_subset C D nodup before included
    exact ⟨C,equal,currentChain,inside,folded⟩
  cases prev : node.data.prev with
  | none => simp [previousSummary,prev] at previous
  | some address =>
    by_cases root : address = op.id
    · have same : own = empty := by simpa [previousSummary,prev,root] using previous.symm
      apply finish [] trivial (by intro _ h; simp at h) (by simpa [tipId,root] using prev)
        (by simp [run,same])
      intro _ h; simp at h
    · have edge : address ∈ links node := by simp [links,prev]
      obtain isRoot | ⟨parent,hp,cached⟩ := (StateResourceCones.gather_lookup op cones (links node) parents lookups).2 address edge
      · exact False.elim (root isRoot)
      · have parentInfo := invariant.1 address parent.1 parent.2 cached
        obtain ⟨summary,C,summaryCached,chainProof,inside,tip,folded,prefixEq⟩ :=
          cached_parent_prefix op known cache cones tips prefixes invariant valid ownTips nonforking address parent.1 parent.2 cached
        have ownerSame : parent.1.data.signer = node.data.signer :=
          ((previousOwnerCheck_iff op.id known).mp foreignChecked) node accepted parent.1 parentInfo.2.1
            (by simpa [parentInfo.1] using prev) (by simpa [parentInfo.1] using root)
        have summarySame : summary = own := by simpa [previousSummary,prev,root,summaryCached] using previous
        subst summary
        apply finish C (by simpa [ownerSame] using chainProof) inside (by simpa [tip] using prev) folded
        intro entry member
        have parentMember : entry ∈ parent.2 := ((invariant.2 address parent.1 parent.2 cached).2 entry).mpr
          ⟨parent.1.data.signer,by simpa [prefixEq] using member⟩
        obtain ⟨owner,merged⟩ := (covered entry).mpr ⟨parent,hp,parentMember⟩
        have signer : entry.data.signer = node.data.signer :=
          (chain_owner parent.1.data.signer op.id C chainProof entry member).trans ownerSame
        have mergedChain := (represented_chain op.id known cache (mergedTips cache tips parents)
          (mergedPrefixes prefixes parents) rep owner).1
        have selectedOwner : owner = node.data.signer :=
          (chain_owner owner op.id _ mergedChain entry merged).symm.trans signer
        simpa [D,selectedOwner] using merged

end CBCL.StateResourceOwnPrefix
