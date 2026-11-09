import LeanCbcl.StateAddressCounting

/-! Operational scratch writes for the address radix sorter. Function-valued
cells model indexed updates; native Array/usize extraction remains a port. -/
set_option autoImplicit false
namespace CBCL.StateAddressScatter
open StateAddressCounting

/-- Native scatter state: next free slot in each bucket and scratch cells. -/
structure Buffer where
  /-- Next write position for each byte bucket. -/
  next : Nat → Nat
  /-- Scratch index array, with arbitrary initial contents. -/
  cells : Nat → Nat

/-- One native scratch write followed by its bucket-pointer increment. -/
def step (key : Nat → Nat) (state : Buffer) (index : Nat) : Buffer :=
  let bucket := key index
  let destination := state.next bucket
  let next := bump bucket state.next
  ⟨next,fun position => if position = destination then index else state.cells position⟩

/-- Execute the scatter loop in input order. -/
def run (key : Nat → Nat) (order : List Nat) (state : Buffer) : Buffer :=
  order.foldl (step key) state

/-- Counters initialized by the actual count and prefix loops. -/
def initial (key : Nat → Nat) (order : List Nat) (cells : Nat → Nat) : Buffer :=
  ⟨offsets (countLoop key order (fun _ => 0)),cells⟩

/-- Count-loop concatenation is native continuation from the prior counters. -/
theorem count_append (key : Nat → Nat) (A B : List Nat) (counts : Nat → Nat) :
    countLoop key B (countLoop key A counts) = countLoop key (A ++ B) counts := by
  simp [countLoop,List.foldl_append]

/-- Operational scatter pointers are exactly the increment-loop counters. -/
theorem next_refinement (key : Nat → Nat) (order : List Nat) (state : Buffer) :
    (run key order state).next = countLoop key order state.next := by
  induction order generalizing state with
  | nil => rfl
  | cons index rest ih =>
    simp only [run,List.foldl_cons]
    exact ih (step key state index)

/-- A split input executes the same steps as one complete scatter loop. -/
theorem run_append (key : Nat → Nat) (A B : List Nat) (state : Buffer) :
    run key (A ++ B) state = run key B (run key A state) := by
  simp [run,List.foldl_append]

/-- A cell never targeted by the remaining steps retains its current contents.
Destinations are the operational evolving counters, not an external map. -/
theorem run_preserves (key : Nat → Nat) (order : List Nat) (state : Buffer) (target : Nat)
    (avoids : ∀ processed index rest, order = processed ++ index::rest →
      countLoop key processed state.next (key index) ≠ target) :
    (run key order state).cells target = state.cells target := by
  induction order generalizing state with
  | nil => rfl
  | cons index rest ih =>
    have headAvoid : state.next (key index) ≠ target := avoids [] index rest rfl
    change (run key rest (step key state index)).cells target = state.cells target
    rw [ih (step key state index)]
    · simp [step,Ne.symm headAvoid]
    · intro processed other tail split
      have remaining := avoids (index::processed) other tail (by simp [split])
      exact remaining

/-- Every occurrence is retained at its computed bucket destination after all
later writes, regardless of the initial scratch contents. Collision freedom
comes from the counting arithmetic, not a caller-provided premise. -/
theorem occurrence_retained (key : Nat → Nat) (processed : List Nat) (index : Nat) (rest : List Nat)
    (cells : Nat → Nat) :
    let order := processed ++ index::rest
    (run key order (initial key order cells)).cells (cursor key order processed (key index)) = index := by
  dsimp
  let order := processed ++ index::rest
  let state := run key processed (initial key order cells)
  have next : state.next = countLoop key processed (initial key order cells).next := next_refinement key processed _
  have destination : state.next (key index) = cursor key order processed (key index) := by
    rw [next]
    rfl
  have avoids : ∀ middle other tail, rest = middle ++ other::tail →
      countLoop key middle (step key state index).next (key other) ≠ cursor key order processed (key index) := by
    intro middle other tail split
    have collision := scatter_no_collision key processed middle tail index other
    simp only [step]
    have merged : countLoop key middle (bump (key index) state.next) =
        countLoop key (processed ++ index::middle) (initial key order cells).next := by
      rw [next]
      change countLoop key (index::middle) (countLoop key processed (initial key order cells).next) = _
      exact count_append key processed (index::middle) _
    rw [merged]
    change cursor key order (processed ++ index::middle) (key other) ≠ _
    have sameOrder : order = processed ++ index::(middle ++ other::tail) := by simp [order,split]
    rw [sameOrder]
    exact Ne.symm collision
  change (run key (processed ++ index::rest) (initial key order cells)).cells _ = _
  rw [run_append]
  change (run key rest (step key state index)).cells _ = _
  rw [run_preserves key rest (step key state index) _ avoids]
  simp only [step]
  rw [destination]
  simp

/-- The destinations/values of successive scatter writes, computed from
prefix counters rather than supplied as a permutation certificate. -/
def writes (key : Nat → Nat) (order processed : List Nat) : List Nat → List (Nat × Nat)
  | [] => []
  | index::rest => (cursor key order processed (key index),index) ::
      writes key order (processed ++ [index]) rest

/-- There is exactly one write per remaining input occurrence. -/
theorem writes_length (key : Nat → Nat) (order processed remaining : List Nat) :
    (writes key order processed remaining).length = remaining.length := by
  induction remaining generalizing processed with
  | nil => rfl
  | cons index rest ih => simp [writes,ih]

/-- The write log retains every input occurrence in input order. -/
theorem writes_values (key : Nat → Nat) (order processed remaining : List Nat) :
    (writes key order processed remaining).map Prod.snd = remaining := by
  induction remaining generalizing processed with
  | nil => rfl
  | cons index rest ih => simp [writes,ih]

/-- Every logged write comes from a concrete occurrence decomposition. -/
theorem write_member (key : Nat → Nat) (order processed remaining : List Nat) (row : Nat × Nat)
    (member : row ∈ writes key order processed remaining) :
    ∃ middle index rest, remaining = middle ++ index::rest ∧
      row = (cursor key order (processed ++ middle) (key index),index) := by
  induction remaining generalizing processed with
  | nil => simp [writes] at member
  | cons index rest ih =>
    rcases List.mem_cons.mp member with head | tail
    · exact ⟨[],index,rest,rfl,by simpa using head⟩
    · obtain ⟨middle,other,last,split,same⟩ := ih (processed ++ [index]) tail
      refine ⟨index::middle,other,last,by simp [split],?_⟩
      simpa [List.append_assoc] using same

/-- Destinations of all remaining writes are distinct, derived from operational
cursor collision freedom and the actual unprocessed suffix. -/
theorem destinations_unique (key : Nat → Nat) (order processed remaining : List Nat)
    (split : order = processed ++ remaining) :
    ((writes key order processed remaining).map Prod.fst).Nodup := by
  induction remaining generalizing processed with
  | nil => simp [writes]
  | cons index rest ih =>
    simp only [writes,List.map_cons,List.nodup_cons]
    constructor
    · intro member
      obtain ⟨row,inside,same⟩ := List.mem_map.mp member
      obtain ⟨middle,other,last,tailSplit,rowEq⟩ := write_member key order (processed ++ [index]) rest row inside
      have collision := scatter_no_collision key processed middle last index other
      have full : order = processed ++ index::(middle ++ other::last) := by simp [split,tailSplit]
      rw [← full] at collision
      apply collision
      simpa [rowEq,List.append_assoc] using same.symm
    · exact ih (processed ++ [index]) (by simpa [List.append_assoc] using split)

/-- Every logged destination is inside the actual scratch allocation. -/
theorem destinations_bounded (key : Nat → Nat) (order processed remaining : List Nat)
    (split : order = processed ++ remaining) (destination : Nat)
    (member : destination ∈ (writes key order processed remaining).map Prod.fst) : destination < order.length := by
  obtain ⟨row,inside,same⟩ := List.mem_map.mp member
  obtain ⟨middle,index,last,tailSplit,rowEq⟩ := write_member key order processed remaining row inside
  have full : order = (processed ++ middle) ++ index::last := by simp [split,tailSplit,List.append_assoc]
  have bound := scatter_index_bound key (processed ++ middle) index last
  rw [← full] at bound
  have equal : destination = cursor key order (processed ++ middle) (key index) := by simpa [rowEq] using same.symm
  rw [equal]
  exact bound

/-- Distinct bounded destinations fill every scratch slot exactly once: the
permutation is derived from the loop, not accepted as an input premise. -/
theorem destination_permutation (key : Nat → Nat) (order : List Nat) :
    ((writes key order [] order).map Prod.fst).Perm (List.range order.length) := by
  apply List.Subperm.perm_of_length_le
  · apply List.subperm_of_subset (destinations_unique key order [] order rfl)
    intro destination member
    exact List.mem_range.mpr (destinations_bounded key order [] order rfl destination member)
  · simp [writes_length]

/-- Every value in the operational write log is present in final scratch. -/
theorem writes_retained (key : Nat → Nat) (order : List Nat) (cells : Nat → Nat)
    (row : Nat × Nat) (member : row ∈ writes key order [] order) :
    (run key order (initial key order cells)).cells row.1 = row.2 := by
  obtain ⟨processed,index,rest,split,rowEq⟩ := write_member key order [] order row member
  subst row
  simp only [List.nil_append]
  rw [split]
  exact occurrence_retained key processed index rest cells

/-- Read native scratch slots in increasing index order after one pass. -/
def pass (key : Nat → Nat) (order : List Nat) (cells : Nat → Nat) : List Nat :=
  (List.range order.length).map (run key order (initial key order cells)).cells

/-- Reading every final scratch slot yields exactly an input permutation,
including multiplicities and independently of initial scratch contents. -/
theorem scatter_permutation (key : Nat → Nat) (order : List Nat) (cells : Nat → Nat) :
    (pass key order cells).Perm order := by
  unfold pass
  have perm := (destination_permutation key order).symm.map (run key order (initial key order cells)).cells
  have values : ((writes key order [] order).map Prod.fst).map (run key order (initial key order cells)).cells = order := by
    rw [List.map_map]
    have same : (writes key order [] order).map (fun row => (run key order (initial key order cells)).cells row.1) =
        (writes key order [] order).map Prod.snd := by
      apply List.map_congr_left
      intro row member
      exact writes_retained key order cells row member
    simpa [writes_values] using same
  rwa [values] at perm

/-- Every final scratch cell has a concrete source occurrence and its exact
operational destination, obtained from the derived destination permutation. -/
theorem scratch_origin (key : Nat → Nat) (order : List Nat) (cells : Nat → Nat) (position : Nat)
    (inside : position < order.length) :
    ∃ processed index rest, order = processed ++ index::rest ∧
      cursor key order processed (key index) = position ∧
      (run key order (initial key order cells)).cells position = index := by
  have member := (destination_permutation key order).mem_iff.mpr (List.mem_range.mpr inside)
  obtain ⟨row,source,same⟩ := List.mem_map.mp member
  obtain ⟨processed,index,rest,split,rowEq⟩ := write_member key order [] order row source
  have destination : cursor key order processed (key index) = position := by simpa [rowEq] using same
  refine ⟨processed,index,rest,split,destination,?_⟩
  rw [← destination,split]
  exact occurrence_retained key processed index rest cells

/-- A complete scatter pass produces ascending bucket keys, without a supplied
ordering or permutation premise and regardless of initial scratch contents. -/
theorem scatter_bucket_order (key : Nat → Nat) (order : List Nat) (cells : Nat → Nat) :
    (pass key order cells).Pairwise (fun a b => key a ≤ key b) := by
  unfold pass
  apply List.pairwise_map.mpr
  apply List.Pairwise.imp_of_mem (p := List.pairwise_lt_range)
  intro a b left right less
  obtain ⟨ap,ai,ar,asplit,adest,aval⟩ := scratch_origin key order cells a (List.mem_range.mp left)
  obtain ⟨bp,bi,br,bsplit,bdest,bval⟩ := scratch_origin key order cells b (List.mem_range.mp right)
  rw [aval,bval]
  by_cases ordered : key ai ≤ key bi
  · exact ordered
  · have greater : key bi < key ai := by omega
    have backwards := distinct_key_order key order bp br ap bi ai bsplit greater
    rw [adest,bdest] at backwards
    omega

end CBCL.StateAddressScatter


