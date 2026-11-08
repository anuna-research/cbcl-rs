import LeanCbcl.StateResourceMachine
import LeanCbcl.StateResourceCounters

/-! Native identity-indexed graph view, derived from the recognized operation
map. Opener references are released initially; absent external references remain
in parent lists and therefore block the first budget pass. -/
namespace CBCL.StateResourceGraph
open State CheckpointEvidence StateResource StateResourceStructure StateResourceDependency

/-- Look up an accepted fact by its address. -/
def lookup (known : Facts) (address : Nat) : Option ResourceFact := known.find? (fun node => node.id == address)

/-- The dependency identities used by this module's graph traversal. -/
def parents (op : ResourceFact) (known : Facts) (address : Nat) : List Nat :=
  ((lookup known address).map links).getD [] |>.filter (fun parent => parent != op.id)

theorem lookup_known (known : Facts) (unique : (known.map Fact.id).Nodup) (node : ResourceFact) (member : node ∈ known) :
    lookup known node.id = some node := by
  cases found : lookup known node.id with
  | none =>
    have absent := List.find?_eq_none.mp found node member
    have same : (node.id == node.id) = true := by simp
    exact False.elim (absent same)
  | some other =>
    have accepted := List.mem_of_find?_eq_some found
    have identity : other.id = node.id := by simpa using List.find?_some found
    have equal := unique_ids_consistent known unique other accepted node member identity
    simpa [equal] using found

theorem parents_known (op : ResourceFact) (known : Facts) (unique : (known.map Fact.id).Nodup)
    (node : ResourceFact) (member : node ∈ known) :
    parents op known node.id = (links node).filter (fun parent => parent != op.id) := by
  simp [parents,lookup_known known unique node member]

theorem unknown_has_no_outgoing (op : ResourceFact) (known : Facts) (address : Nat)
    (missing : address ∉ known.map Fact.id) : parents op known address = [] := by
  cases found : lookup known address with
  | none => simp [parents,found]
  | some node =>
    have member := List.mem_of_find?_eq_some found
    have equal : node.id = address := by simpa using List.find?_some found
    exact False.elim (missing (List.mem_map.mpr ⟨node,member,equal⟩))

theorem recognized_links_unique (c : ResourceConfig) (op root node : ResourceFact)
    (valid : validOperation c op root node) : (links node).Nodup := by
  obtain ⟨_,_,_,_,_,_,_,_,_,hasPrevious,_,depsUnique,notPrevious,_⟩ := valid
  cases previous : node.data.prev with
  | none => simp [previous] at hasPrevious
  | some address =>
    simp only [links,previous,Option.toList_some,List.singleton_append,List.nodup_cons]
    exact ⟨notPrevious address previous,depsUnique⟩

theorem native_parent_lists_unique (c : ResourceConfig) (op root : ResourceFact) (known : Facts)
    (unique : (known.map Fact.id).Nodup) (operations : ∀ node ∈ known, validOperation c op root node) :
    ∀ address ∈ known.map Fact.id, (parents op known address).Nodup := by
  intro address member
  obtain ⟨node,hn,rfl⟩ := List.mem_map.mp member
  rw [parents_known op known unique node hn]
  exact (recognized_links_unique c op root node (operations node hn)).sublist List.filter_sublist

end CBCL.StateResourceGraph
