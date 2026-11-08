import LeanCbcl.StateAddressControl

/-! Native reverse digit-range execution. The recursion is on the actual USize
cursor; its decoded value proves termination, with no caller-provided fuel.
Widths outside the native representable domain retain the generic semantics. -/
set_option autoImplicit false
namespace CBCL.StateAddressRange
open StateAddressControl

/-- A nonzero native reverse cursor has a positive decoded value. -/
theorem cursor_positive (cursor : USize) (nonzero : cursor ≠ 0) : 0 < cursor.toNat := by
  have different : cursor.toNat ≠ 0 := by
    intro zero
    apply nonzero
    exact USize.toNat_inj.mp (by simpa using zero)
  omega

/-- Decrementing a nonzero reverse cursor is exact and cannot underflow. -/
theorem previous_exact (cursor : USize) (nonzero : cursor ≠ 0) :
    (cursor-1).toNat + 1 = cursor.toNat := by
  have positive := cursor_positive cursor nonzero
  have atLeastOne : (1 : USize) ≤ cursor := by
    rw [USize.le_iff_toNat_le]
    simpa using positive
  rw [USize.toNat_sub_of_le cursor 1 atLeastOne]
  simp only [USize.toNat_one]
  omega

/-- Native reverse half-open range: stop at zero, otherwise yield cursor-1. -/
def reverseRange (cursor : USize) : List USize :=
  if stopped : cursor = 0 then [] else
    (cursor-1) :: reverseRange (cursor-1)
termination_by cursor.toNat
decreasing_by
  have smaller := previous_exact cursor stopped
  omega

/-- The actual reverse range yields exactly the descending mathematical indices
encoded as native words, including empty ranges and the largest native width. -/
theorem reverseRange_refinement (width : USize) :
    reverseRange width = (List.range width.toNat).reverse.map USize.ofNat := by
  induction count : width.toNat using Nat.strongRecOn generalizing width with
  | ind n ih =>
    by_cases stopped : width = 0
    · subst width
      have zero : n = 0 := by simpa using count.symm
      subst n
      rw [reverseRange,dif_pos rfl]
      rfl
    · have previous := previous_exact width stopped
      have smaller : (width-1).toNat < n := by omega
      have decoded : n = (width-1).toNat+1 := by omega
      rw [reverseRange,dif_neg stopped,ih _ smaller (width-1) rfl,decoded]
      simp [List.range_succ,List.reverse_append,USize.ofNat_toNat]

/-- Decoding the emitted word positions gives exactly the expected digit order. -/
theorem reverseRange_decoded (width : USize) :
    (reverseRange width).map USize.toNat = (List.range width.toNat).reverse := by
  rw [reverseRange_refinement,List.map_map]
  calc
    _ = ((List.range width.toNat).reverse).map (fun index => index) := by
      apply List.map_congr_left
      intro index member
      have inside := List.mem_range.mp (List.mem_reverse.mp member)
      exact USize.toNat_ofNat_of_lt' (Nat.lt_trans inside width.toNat_lt_size)
    _ = _ := List.map_id' _

/-- Every emitted digit is within both the source width and native word range. -/
theorem emitted_bound (width digit : USize) (member : digit ∈ reverseRange width) : digit.toNat < width.toNat := by
  have inside : digit.toNat ∈ (reverseRange width).map USize.toNat := List.mem_map.mpr ⟨digit,member,rfl⟩
  rw [reverseRange_decoded] at inside
  exact List.mem_range.mp (List.mem_reverse.mp inside)

/-- Complete native-width outer loop, executing each digit's proved word pass. -/
def rangeSort (address : Nat → String) (width : USize) (order : List Nat) : List Nat :=
  (reverseRange width).foldl (fun current position =>
    checkedNativePass (fun index => StateAddressDigits.digit (StateFaultRendering.bytes (address index)) position.toNat) current) order

/-- The existing control sorter is exactly the reversed-digit pass fold. -/
theorem controlSort_fold (digits : List (Nat → Nat)) (order : List Nat) :
    controlSort digits order = digits.reverse.foldl (fun current key => checkedNativePass key current) order := by
  induction digits with
  | nil => rfl
  | cons key rest ih => simp [controlSort,List.reverse_cons,List.foldl_append,ih]

/-- Direct native reverse-cursor execution refines the complete digit plan;
no supplied range/order/termination certificate is needed. -/
theorem rangeSort_refinement (address : Nat → String) (width : USize) (order : List Nat) :
    rangeSort address width order = controlSort (StateAddressRadix.addressDigits width.toNat address) order := by
  have decoded := reverseRange_decoded width
  unfold rangeSort
  calc
    _ = ((reverseRange width).map USize.toNat).foldl (fun current position =>
        checkedNativePass (fun index => StateAddressDigits.digit (StateFaultRendering.bytes (address index)) position) current) order := by
      simp only [List.foldl_map]
    _ = _ := by
      rw [decoded,controlSort_fold]
      simp only [StateAddressRadix.addressDigits,← List.map_reverse,List.foldl_map]

/-- Native-width execution with a semantics-preserving generic fallback for
unrepresentable mathematical widths; native allocated byte strings fit. -/
def checkedRangeSort (address : Nat → String) (width : Nat) (order : List Nat) : List Nat :=
  if width < USize.size then rangeSort address (USize.ofNat width) order
  else controlSort (StateAddressRadix.addressDigits width address) order

/-- Word-width recognition preserves the complete generic address sort. -/
theorem checkedRangeSort_refinement (address : Nat → String) (width : Nat) (order : List Nat) :
    checkedRangeSort address width order = controlSort (StateAddressRadix.addressDigits width address) order := by
  unfold checkedRangeSort
  split
  · rename_i fits
    rw [rangeSort_refinement,USize.toNat_ofNat_of_lt' fits]
  · rfl

end CBCL.StateAddressRange
