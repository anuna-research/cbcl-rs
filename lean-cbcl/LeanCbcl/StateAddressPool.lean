import LeanCbcl.StateAddressRange

/-! Destructive address extraction by a proved index permutation. Every lookup
is partial and checked; no fallback string stands in for a missing pool entry. -/
set_option autoImplicit false
namespace CBCL.StateAddressPool

/-- Native Option::take: read an existing address and clear its source slot. -/
def takeOne (pool : Array (Option String)) (index : Nat) : Option (String × Array (Option String)) := do
  let entry ← pool[index]?
  let value ← entry
  return (value,pool.setIfInBounds index none)

/-- Native final move loop, failing on an absent or already consumed source. -/
def takeMany (pool : Array (Option String)) : List Nat → Option (List String × Array (Option String))
  | [] => some ([],pool)
  | index::rest => do
    let (value,updated) ← takeOne pool index
    let (values,finished) ← takeMany updated rest
    return (value::values,finished)

/-- Checked source-array observations, retaining input index order. -/
def lookupMany (source : Array String) (order : List Nat) : Option (List String) :=
  order.mapM (fun index => source[index]?)

/-- Every successful take returns the original source and clears only that slot. -/
theorem takeOne_present (pool : Array (Option String)) (index : Nat) (value : String)
    (present : pool[index]? = some (some value)) :
    takeOne pool index = some (value,pool.setIfInBounds index none) := by simp [takeOne,present]

/-- Consuming distinct available indices succeeds, matches checked source
lookups, clears all selected slots and leaves every unselected slot unchanged. -/
theorem takeMany_refinement (source : Array String) (pool : Array (Option String)) (order : List Nat)
    (unique : order.Nodup) (bounded : ∀ index ∈ order, index < source.size)
    (available : ∀ index ∈ order, pool[index]? = (source[index]?).map some) :
    ∃ values finished, takeMany pool order = some (values,finished) ∧ lookupMany source order = some values ∧
      (∀ index, index ∉ order → finished[index]? = pool[index]?) ∧
      (∀ index ∈ order, finished[index]? = some none) := by
  induction order generalizing pool with
  | nil => exact ⟨[],pool,rfl,rfl,fun _ _ => rfl,by simp⟩
  | cons index rest ih =>
    have parts := List.nodup_cons.mp unique
    have inside := bounded index (by simp)
    have sourceValue : source[index]? = some source[index] := Array.getElem?_eq_getElem inside
    have present : pool[index]? = some (some source[index]) := by
      rw [available index (by simp),sourceValue]
      rfl
    have poolInside : index < pool.size := (Array.getElem?_eq_some_iff.mp present).choose
    let updated := pool.setIfInBounds index none
    have tailAvailable : ∀ other ∈ rest, updated[other]? = (source[other]?).map some := by
      intro other member
      have different : index ≠ other := by intro same; subst other; exact parts.1 member
      simpa [updated,different] using available other (by simp [member])
    obtain ⟨values,finished,computed,looked,frame,cleared⟩ := ih updated parts.2
      (fun other member => bounded other (by simp [member])) tailAvailable
    simp only [updated] at computed
    refine ⟨source[index]::values,finished,?_,?_,?_,?_⟩
    · simp [takeMany,takeOne_present pool index source[index] present,computed]
    · simp only [lookupMany] at looked
      simp [lookupMany,sourceValue,looked]
    · intro other outside
      have different : index ≠ other := by intro same; subst other; exact outside (by simp)
      have notTail : other ∉ rest := by intro member; exact outside (by simp [member])
      rw [frame other notTail]
      simp [updated,different]
    · intro other member
      rcases List.mem_cons.mp member with same | tail
      · subst other
        rw [frame index parts.1]
        simp [updated,Array.getElem?_setIfInBounds_self_of_lt poolInside]
      · exact cleared other tail

/-- A fresh pool provides every source slot exactly, including duplicate strings
stored at different indices. -/
theorem fresh_available (source : Array String) (index : Nat) :
    (source.map some)[index]? = (source[index]?).map some := by simp

/-- A derived source-index permutation can neither repeat nor omit a take. -/
theorem permutation_moves (source : Array String) (order : List Nat) (permutation : order.Perm (List.range source.size)) :
    ∃ values finished, takeMany (source.map some) order = some (values,finished) ∧
      lookupMany source order = some values ∧
      (∀ index < source.size, finished[index]? = some none) := by
  have unique := permutation.nodup_iff.mpr List.nodup_range
  have bounded : ∀ index ∈ order, index < source.size := by
    intro index member
    exact List.mem_range.mp (permutation.mem_iff.mp member)
  obtain ⟨values,finished,computed,looked,_,cleared⟩ := takeMany_refinement source (source.map some) order unique bounded
    (fun index _ => fresh_available source index)
  exact ⟨values,finished,computed,looked,fun index inside => cleared index (permutation.mem_iff.mpr (List.mem_range.mpr inside))⟩

/-- The actual word-array radix output supplies the index permutation; callers
do not provide a no-repeat or pool-consumption certificate. -/
theorem word_radix_moves (source : Array String) (digits : List (Nat → Nat)) :
    ∃ values finished, takeMany (source.map some) (StateAddressWords.wordSort digits (List.range source.size)) = some (values,finished) ∧
      lookupMany source (StateAddressWords.wordSort digits (List.range source.size)) = some values ∧
      (∀ index < source.size, finished[index]? = some none) := by
  apply permutation_moves
  rw [StateAddressWords.wordSort_refinement]
  exact StateAddressRadix.sort_permutation digits (List.range source.size)

/-- Enumerating a finite source pool reproduces its stored address sequence. -/
theorem source_enumeration (source : Array String) :
    (List.range source.size).map (fun index => source[index]!) = source.toList := by
  apply List.ext_getElem
  · simp
  · intro index left right
    have inside : index < source.size := by simpa using left
    simp [getElem!_pos source index inside]

/-- On a proved-valid index sequence, checked lookups agree with direct native
indexing; no missing-source default is observed. -/
theorem lookupMany_mapping (source : Array String) (order : List Nat)
    (bounded : ∀ index ∈ order, index < source.size) :
    lookupMany source order = some (order.map (fun index => source[index]!)) := by
  induction order with
  | nil => rfl
  | cons index rest ih =>
    have inside := bounded index (by simp)
    have tail := ih (fun other member => bounded other (by simp [member]))
    simp only [lookupMany] at tail
    simp [lookupMany,Array.getElem?_eq_getElem inside,getElem!_pos source index inside,tail]

/-- Every source index produced by any radix suffix still names a real pool
entry. The universally quantified digits cover every recursive LSD stage. -/
theorem word_pool_bound (source : Array String) (digits : List (Nat → Nat)) (index : Nat)
    (member : index ∈ StateAddressWords.wordSort digits (List.range source.size)) : index < source.size := by
  rw [StateAddressWords.wordSort_refinement] at member
  exact List.mem_range.mp ((StateAddressRadix.sort_permutation digits (List.range source.size)).mem_iff.mp member)

/-- Native-control source-index iteration preserves the finite pool domain at
all recursive LSD stages. -/
theorem control_pool_bound (source : Array String) (digits : List (Nat → Nat)) (index : Nat)
    (member : index ∈ StateAddressControl.controlSort digits (List.range source.size)) : index < source.size := by
  rw [StateAddressControl.controlSort_refinement] at member
  exact word_pool_bound source digits index member

/-- Native outer-range execution preserves the concrete source-pool domain. -/
theorem range_pool_bound (source : Array String) (width : Nat) (index : Nat)
    (member : index ∈ StateAddressRange.checkedRangeSort (fun index => source[index]!) width (List.range source.size)) :
    index < source.size := by
  rw [StateAddressRange.checkedRangeSort_refinement] at member
  exact control_pool_bound source _ index member

/-- Actual source-pool radix indices, starting from the native 0..len order. -/
def indices (source : Array String) : List Nat :=
  StateAddressRange.checkedRangeSort (fun index => source[index]!)
    (StateAddressDigits.maximumWidth source.toList) (List.range source.size)

/-- Complete native-style destructive address sorting. -/
def sortPool (source : Array String) : Option (List String) :=
  (takeMany (source.map some) (indices source)).map Prod.fst

/-- Source pool extraction closes the address representation port: the complete
word radix plus destructive moves returns exactly its mathematical address
sequence. It cannot fail, repeat a consumed slot or invent a missing address. -/
theorem sortPool_refinement (source : Array String) :
    sortPool source = some (StateAddressRadix.radix (fun index => source[index]!) (List.range source.size)) := by
  obtain ⟨values,finished,computed,looked,_⟩ := word_radix_moves source
    (StateAddressRadix.addressDigits (StateAddressDigits.maximumWidth source.toList) (fun index => source[index]!))
  rw [← StateAddressControl.controlSort_refinement,← StateAddressRange.checkedRangeSort_refinement] at computed looked
  change takeMany (source.map some) (indices source) = some (values,finished) at computed
  change lookupMany source (indices source) = some values at looked
  have valid : ∀ index ∈ indices source, index < source.size := fun index member => range_pool_bound source _ index member
  have expected := lookupMany_mapping source (indices source) valid
  have same : values = (indices source).map (fun index => source[index]!) := Option.some.inj (looked.symm.trans expected)
  unfold sortPool
  rw [computed]
  simp only [Option.map_some]
  rw [same]
  unfold indices StateAddressRadix.radix
  rw [StateAddressRange.checkedRangeSort_refinement,StateAddressControl.controlSort_refinement,StateAddressWords.wordSort_refinement,source_enumeration]

/-- Complete finite source-pool sorting and adjacent deduplication produces
exact canonical evidence, including repeated address strings at distinct slots. -/
theorem canonical_output (source : Array String) :
    (sortPool source).map StateAddressDigits.adjacent = some (StateFaultRendering.canonical source.toList) := by
  rw [sortPool_refinement]
  simp only [Option.map_some,StateAddressRadix.canonical_refinement,source_enumeration]

/-- Complete native-style evidence sorting, moves, adjacent dedup and JSON. -/
def faultBytes (reason : String) (source : Array String) : Option String :=
  (sortPool source).map (fun addresses => StateJsonValue.emit
    (.map [(.str "evidence",.list ((StateAddressDigits.adjacent addresses).map StateJsonValue.Value.str)),
      (.str "reason",.str reason),(.str "status",.str "fault")]) "")

/-- Concrete finite source-pool execution always succeeds with exact reference
fault bytes. No total address callback or pool-lookup certificate is supplied. -/
theorem faultBytes_refinement (reason : String) (source : Array String) :
    faultBytes reason source = some (StateJsonValue.render (StateFaultRendering.fault reason source.toList)) := by
  unfold faultBytes
  rw [sortPool_refinement]
  simp only [Option.map_some,StateAddressRadix.canonical_refinement,source_enumeration,StateJsonValue.empty_buffer]
  rfl

end CBCL.StateAddressPool


