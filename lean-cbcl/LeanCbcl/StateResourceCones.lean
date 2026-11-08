import LeanCbcl.StateResourceStructure

/-! Ghost cone reconstruction for the native dependency traversal. No cone is
provided by a caller: dependency-cache lookups supply previously reconstructed
cones, and the new cone is their union with the operation being evaluated. -/
namespace CBCL.StateResourceCones
open State CheckpointEvidence StateResource StateResourceCache StateResourceStructure

/-- An address-indexed cache of exact dependency cones. -/
abbrev ConeCache := Nat → Option (ResourceFact × Facts)

/-- A gathered parent entry agrees with the accepted dependency graph. -/
def ParentEntryValid (op : ResourceFact) (cache : ConeCache) : Prop :=
  ∀ address node cone, cache address = some (node,cone) → node.id = address ∧ ExactCone op node cone

/-- Resolve parent entries from the cache, treating the opener as an empty prefix. -/
def gather (op : ResourceFact) (cache : ConeCache) : List Nat →
    Option (List (ResourceFact × Facts))
  | [] => some []
  | address :: references =>
    if address = op.id then gather op cache references else do
      let entry ← cache address
      let entries ← gather op cache references
      some (entry :: entries)

/-- Build the exact cone from the current fact and its gathered parent cones. -/
def unionCone (known : Facts) (node : ResourceFact) (parents : List (ResourceFact × Facts)) : Facts :=
  known.filter fun entry => entry == node || parents.any (fun parent => parent.2.contains entry)

theorem unionCone_member (known : Facts) (node entry : ResourceFact)
    (parents : List (ResourceFact × Facts)) :
    entry ∈ unionCone known node parents ↔
      entry ∈ known ∧ (entry = node ∨ ∃ parent ∈ parents, entry ∈ parent.2) := by
  simp [unionCone,List.any_eq_true]

theorem reaches_enlarge {C D : Facts} (inside : Included C D) {a b : ResourceFact}
    (reach : Reaches C a b) : Reaches D a b := by
  induction reach with
  | refl => exact .refl
  | step member edge _ ih => exact .step (inside _ member) edge ih

theorem unionCone_exact (op node : ResourceFact) (known : Facts)
    (parents : List (ResourceFact × Facts)) (accepted : node ∈ known)
    (unique : (known.map Fact.id).Nodup)
    (included : ∀ parent ∈ parents, Included parent.2 known)
    (exactParents : ∀ parent ∈ parents, ExactCone op parent.1 parent.2)
    (referenced : ∀ parent ∈ parents, parent.1.id ∈ links node)
    (complete : ∀ address ∈ links node, address = op.id ∨ ∃ parent ∈ parents, parent.1.id = address) :
    ExactCone op node (unionCone known node parents) := by
  have member := unionCone_member known node
  have parentInside : ∀ parent ∈ parents, Included parent.2 (unionCone known node parents) := by
    intro parent hp entry he
    exact (member entry parents).mpr ⟨included parent hp entry he,Or.inr ⟨parent,hp,he⟩⟩
  refine ⟨(member node parents).mpr ⟨accepted,Or.inl rfl⟩,?_,?_,?_⟩
  · exact unique.sublist (List.Sublist.map Fact.id (List.filter_sublist))
  · intro entry he address edge
    rcases ((member entry parents).mp he).2 with rfl | ⟨parent,hp,he⟩
    · rcases complete address edge with root | ⟨parent,hp,equal⟩
      · exact Or.inl root
      · exact Or.inr ⟨parent.1,parentInside parent hp parent.1 (exactParents parent hp).1,equal⟩
    · rcases (exactParents parent hp).2.2.1 entry he address edge with root | ⟨ancestor,ha,equal⟩
      · exact Or.inl root
      · exact Or.inr ⟨ancestor,parentInside parent hp ancestor ha,equal⟩
  · intro entry he
    rcases ((member entry parents).mp he).2 with rfl | ⟨parent,hp,he⟩
    · exact .refl
    · exact .step (parentInside parent hp parent.1 (exactParents parent hp).1)
        (referenced parent hp) (reaches_enlarge (parentInside parent hp) ((exactParents parent hp).2.2.2 entry he))


theorem gather_lookup (op : ResourceFact) (cache : ConeCache) (references : List Nat)
    (entries : List (ResourceFact × Facts)) (success : gather op cache references = some entries) :
    (∀ entry ∈ entries, ∃ address ∈ references, address ≠ op.id ∧ cache address = some entry) ∧
    (∀ address ∈ references, address = op.id ∨ ∃ entry ∈ entries, cache address = some entry) := by
  induction references generalizing entries with
  | nil =>
    have equal : entries = [] := by simpa [gather] using success.symm
    subst entries
    simp
  | cons address rest ih =>
    by_cases root : address = op.id
    · have tail : gather op cache rest = some entries := by simpa [gather,root] using success
      obtain ⟨sound,complete⟩ := ih entries tail
      constructor
      · intro entry member
        obtain ⟨id,hr,notRoot,found⟩ := sound entry member
        exact ⟨id,by simp [hr],notRoot,found⟩
      · intro id member
        rcases List.mem_cons.mp member with rfl | hr
        · exact Or.inl root
        · exact complete id hr
    · cases cached : cache address with
      | none => simp [gather,root,cached] at success
      | some first =>
        cases tail : gather op cache rest with
        | none => simp [gather,root,cached,tail] at success
        | some later =>
          have equal : entries = first :: later := by simpa [gather,root,cached,tail] using success.symm
          subst entries
          obtain ⟨sound,complete⟩ := ih later tail
          constructor
          · intro entry member
            rcases List.mem_cons.mp member with rfl | member
            · exact ⟨address,by simp,root,cached⟩
            · obtain ⟨id,hr,notRoot,found⟩ := sound entry member
              exact ⟨id,by simp [hr],notRoot,found⟩
          · intro id member
            rcases List.mem_cons.mp member with rfl | member
            · exact Or.inr ⟨first,by simp,cached⟩
            · rcases complete id member with isRoot | ⟨entry,he,found⟩
              · exact Or.inl isRoot
              · exact Or.inr ⟨entry,by simp [he],found⟩

/-- Each cached cone agrees with exact accepted dependency ancestry. -/
def Valid (op : ResourceFact) (known : Facts) (cache : ConeCache) : Prop :=
  ∀ address node cone, cache address = some (node,cone) →
    node.id = address ∧ node ∈ known ∧ Included cone known ∧ ExactCone op node cone

/-- Reconstruct a dependency cone from the processed parent entries. -/
def reconstruct (op : ResourceFact) (known : Facts) (cache : ConeCache) (node : ResourceFact) : Option Facts := do
  let parents ← gather op cache (links node)
  some (unionCone known node parents)

/-- Exactness follows from successful dependency lookups and previously
established cache entries. No exact cone for the new operation is assumed. -/
theorem reconstruct_exact (op node : ResourceFact) (known : Facts) (cache : ConeCache) (cone : Facts)
    (valid : Valid op known cache) (accepted : node ∈ known) (unique : (known.map Fact.id).Nodup)
    (success : reconstruct op known cache node = some cone) : ExactCone op node cone := by
  cases found : gather op cache (links node) with
  | none => simp [reconstruct,found] at success
  | some parents =>
    have equal : cone = unionCone known node parents := by simpa [reconstruct,found] using success.symm
    subst cone
    obtain ⟨sound,complete⟩ := gather_lookup op cache (links node) parents found
    apply unionCone_exact op node known parents accepted unique
    · intro parent member
      obtain ⟨address,_,_,cached⟩ := sound parent member
      exact (valid address parent.1 parent.2 cached).2.2.1
    · intro parent member
      obtain ⟨address,_,_,cached⟩ := sound parent member
      exact (valid address parent.1 parent.2 cached).2.2.2
    · intro parent member
      obtain ⟨address,edge,_,cached⟩ := sound parent member
      simpa [(valid address parent.1 parent.2 cached).1] using edge
    · intro address edge
      rcases complete address edge with root | ⟨parent,member,cached⟩
      · exact Or.inl root
      · exact Or.inr ⟨parent,member,(valid address parent.1 parent.2 cached).1⟩


/-- Insert the reconstructed dependency cone into the cache. -/
def insert (op : ResourceFact) (known : Facts) (cache : ConeCache) (node : ResourceFact) : Option ConeCache := do
  let cone ← reconstruct op known cache node
  some (fun address => if address = node.id then some (node,cone) else cache address)

theorem insert_valid (op node : ResourceFact) (known : Facts) (cache next : ConeCache)
    (valid : Valid op known cache) (accepted : node ∈ known) (unique : (known.map Fact.id).Nodup)
    (success : insert op known cache node = some next) : Valid op known next := by
  cases reconstructed : reconstruct op known cache node with
  | none => simp [insert,reconstructed] at success
  | some cone =>
    have equal : next = (fun address => if address = node.id then some (node,cone) else cache address) := by
      simpa [insert,reconstructed] using success.symm
    rw [equal]
    intro address entry C found
    by_cases current : address = node.id
    · subst address
      have pair : node = entry ∧ cone = C := by simpa using found
      obtain ⟨rfl,rfl⟩ := pair
      refine ⟨rfl,accepted,?_,reconstruct_exact op node known cache cone valid accepted unique reconstructed⟩
      cases parents : gather op cache (links node) with
      | none => simp [reconstruct,parents] at reconstructed
      | some entries =>
        have same : cone = unionCone known node entries := by simpa [reconstruct,parents] using reconstructed.symm
        subst cone
        intro entry member
        exact ((unionCone_member known node entry entries).mp member).1
    · exact valid address entry C (by simpa [current] using found)

/-- Fold exact-cone reconstruction over an operation sequence. -/
def execute (op : ResourceFact) (known schedule : Facts) (cache : ConeCache) : Option ConeCache :=
  schedule.foldlM (insert op known) cache

theorem execute_valid (op : ResourceFact) (known schedule : Facts) (cache finalCache : ConeCache)
    (valid : Valid op known cache) (unique : (known.map Fact.id).Nodup) (scheduled : schedule ⊆ known)
    (success : execute op known schedule cache = some finalCache) : Valid op known finalCache := by
  induction schedule generalizing cache with
  | nil =>
    have same : cache = finalCache := by simpa [execute] using success
    simpa [← same] using valid
  | cons node rest ih =>
    cases step : insert op known cache node with
    | none => simp [execute,List.foldlM_cons,step] at success
    | some next =>
      apply ih next (insert_valid op node known cache next valid (scheduled (by simp)) unique step)
        (fun _ member => scheduled (by simp [member]))
      simpa [execute,List.foldlM_cons,step] using success

/-- End-to-end ghost reconstruction along a successful native dependency
schedule. The exact cone is obtained from dependency lookups, not a premise. -/
theorem executed_cone_exact (op : ResourceFact) (known schedule : Facts) (cache : ConeCache)
    (unique : (known.map Fact.id).Nodup) (scheduled : schedule ⊆ known)
    (success : execute op known schedule (fun _ => none) = some cache)
    (address : Nat) (node : ResourceFact) (cone : Facts) (found : cache address = some (node,cone)) :
    ExactCone op node cone := by
  have initial : Valid op known (fun _ => none) := by intro _ _ _ h; contradiction
  exact (execute_valid op known schedule _ cache initial unique scheduled success address node cone found).2.2.2

end CBCL.StateResourceCones
