import LeanCbcl.StateFaultRendering

/-! Native radix-sort key representation. A missing byte is bucket zero;
actual bytes use buckets one through 256. This module proves padding and key
order correspondence, not the mutable counting/scatter pass implementation. -/
set_option autoImplicit false
namespace CBCL.StateAddressDigits
open Std

/-- The exact native byte lookup and missing-byte sentinel. -/
def digit (data : List UInt8) (position : Nat) : Nat :=
  ((data[position]?).map (fun byte => byte.toNat + 1)).getD 0

/-- Fixed-width most-significant-first key sequence consumed by radix passes. -/
def keys : Nat → List UInt8 → List Nat
  | 0, _ => []
  | width+1, [] => 0 :: keys width []
  | width+1, byte::rest => (byte.toNat+1) :: keys width rest

/-- Byte buckets fit the native 257-entry count/next arrays. -/
theorem digit_bound (data : List UInt8) (position : Nat) : digit data position < 257 := by
  unfold digit
  cases data[position]? with
  | none => decide
  | some byte =>
    have bound := byte.toNat_lt_size
    simp only [Option.map_some,Option.getD_some]
    change byte.toNat < 256 at bound
    omega

/-- No actual byte, including NUL, aliases the missing-byte bucket. -/
theorem digit_zero (data : List UInt8) (position : Nat) : digit data position = 0 ↔ data[position]? = none := by
  unfold digit
  cases data[position]? <;> simp

/-- Adding the sentinel offset preserves byte comparison exactly. -/
theorem byte_compare (a b : UInt8) : compare (a.toNat+1) (b.toNat+1) = compare a b := by
  simp [compare,compareOfLessAndEq,UInt8.lt_iff_toNat_lt,← UInt8.toNat_inj]

/-- Padding always produces exactly the requested number of digits. -/
theorem keys_length (width : Nat) (data : List UInt8) : (keys width data).length = width := by
  induction width generalizing data with
  | zero => rfl
  | succ width ih => cases data <;> simp [keys,ih]

/-- Each fixed-width digit is the operational native lookup at that position. -/
theorem keys_lookup (width : Nat) (data : List UInt8) (position : Nat) (inside : position < width) :
    (keys width data)[position]? = some (digit data position) := by
  induction width generalizing data position with
  | zero => omega
  | succ width ih =>
    cases position with
    | zero => cases data <;> simp [keys,digit]
    | succ position =>
      have bound : position < width := by omega
      cases data with
      | nil => simpa [keys,digit] using ih [] position bound
      | cons byte rest => simpa [keys,digit] using ih rest position bound

/-- At any sufficient width, sentinel padding preserves raw byte lexicographic
comparison, including empty keys, strict prefixes and actual zero bytes. -/
theorem keys_compare (width : Nat) (A B : List UInt8) (left : A.length ≤ width) (right : B.length ≤ width) :
    compare (keys width A) (keys width B) = compare A B := by
  induction width generalizing A B with
  | zero =>
    have a : A = [] := List.length_eq_zero_iff.mp (by omega)
    have b : B = [] := List.length_eq_zero_iff.mp (by omega)
    subst A; subst B
    rfl
  | succ width ih =>
    cases A with
    | nil =>
      cases B with
      | nil => simp [keys]
      | cons byte rest =>
        simp only [keys,List.compare_cons_cons,List.compare_nil_cons]
        have ordered : compare 0 (byte.toNat+1) = Ordering.lt := by simp [compare,compareOfLessAndEq]
        simp [ordered]
    | cons byte rest =>
      cases B with
      | nil =>
        simp only [keys,List.compare_cons_cons,List.compare_cons_nil]
        have ordered : compare (byte.toNat+1) 0 = Ordering.gt := by simp [compare,compareOfLessAndEq]
        simp [ordered]
      | cons other tail =>
        have l : rest.length ≤ width := by simpa using left
        have r : tail.length ≤ width := by simpa using right
        simp only [keys,List.compare_cons_cons,byte_compare,ih rest tail l r]

/-- Fixed-width byte keys identify exactly the original byte strings. -/
theorem keys_injective (width : Nat) (A B : List UInt8) (left : A.length ≤ width) (right : B.length ≤ width) :
    keys width A = keys width B ↔ A = B := by
  constructor
  · intro same
    apply compare_eq_iff_eq.mp
    rw [← keys_compare width A B left right,same]
    exact compare_self
  · intro same; subst B; rfl

/-- The maximum byte length chosen by the native sorter. -/
def maximumWidth (addresses : List String) : Nat :=
  (addresses.map (fun text => (StateFaultRendering.bytes text).length)).foldl max 0

/-- Every observed address fits the computed native radix width. -/
theorem width_covers (addresses : List String) (address : String) (member : address ∈ addresses) :
    (StateFaultRendering.bytes address).length ≤ maximumWidth addresses := by
  have helper : ∀ (lengths : List Nat) (initial : Nat) (n : Nat), n ∈ lengths → n ≤ lengths.foldl max initial := by
    intro lengths
    induction lengths with
    | nil => simp
    | cons head rest ih =>
      intro initial n inside
      rcases List.mem_cons.mp inside with same | remaining
      · subst n
        have grows : ∀ (xs : List Nat) (start : Nat), start ≤ xs.foldl max start := by
          intro xs
          induction xs with
          | nil => intro start; exact Nat.le_refl _
          | cons x xs h => intro start; exact Nat.le_trans (Nat.le_max_left _ _) (h _)
        exact Nat.le_trans (Nat.le_max_right _ _) (grows rest _)
      · exact ih _ n remaining
  exact helper _ 0 _ (List.mem_map.mpr ⟨address,member,rfl⟩)

/-- Actual computed-width digit comparison equals the canonical evidence
comparator for any two addresses supplied to the native sorter. -/
theorem native_key_order (addresses : List String) (a b : String) (left : a ∈ addresses) (right : b ∈ addresses) :
    (compare (keys (maximumWidth addresses) (StateFaultRendering.bytes a))
      (keys (maximumWidth addresses) (StateFaultRendering.bytes b))).isLE = StateFaultRendering.byteLE a b := by
  rw [keys_compare _ _ _ (width_covers addresses a left) (width_covers addresses b right)]
  rfl

/-- Duplicate removal retains an ordered subsequence rather than reordering it. -/
theorem dedup_sublist (addresses : List String) : List.Sublist (StateLift.FinSet.dedup addresses) addresses := by
  induction addresses with
  | nil => exact .refl _
  | cons address rest ih =>
    simp only [StateLift.FinSet.dedup]
    split
    · exact ih.cons address
    · exact ih.cons₂ address

/-- Native adjacent duplicate removal after sorting. -/
def adjacent : List String → List String
  | [] => []
  | [address] => [address]
  | a::b::rest => if a = b then adjacent (b::rest) else a :: adjacent (b::rest)

/-- On byte-ordered results, native adjacent duplicate removal equals exact
finite-set duplicate removal; separated equal addresses cannot survive. -/
theorem adjacent_refinement (addresses : List String)
    (ordered : addresses.Pairwise (fun a b => StateFaultRendering.byteLE a b = true)) :
    adjacent addresses = StateLift.FinSet.dedup addresses := by
  induction addresses with
  | nil => rfl
  | cons a rest ih =>
    cases rest with
    | nil => simp [adjacent,StateLift.FinSet.dedup]
    | cons b tail =>
      have tailOrder := ordered.tail
      by_cases same : a = b
      · subst a
        simp [adjacent,StateLift.FinSet.dedup,ih tailOrder]
      · have absent : a ∉ b::tail := by
          intro member
          rcases List.mem_cons.mp member with equal | inside
          · exact same equal
          · have ab := (List.pairwise_cons.mp ordered).1 b (by simp)
            have ba := (List.pairwise_cons.mp tailOrder).1 a inside
            exact same (StateFaultRendering.byte_antisymm a b ab ba)
        simp only [adjacent,if_neg same,StateLift.FinSet.dedup,if_neg absent]
        rw [ih tailOrder]
        rfl

/-- Once counting/scatter establishes permutation and padded-key ordering,
normalizing its result is exactly canonical fault evidence. The two operational
premises are explicit obligations, not assumed sorter correctness. -/
theorem sorted_result_refinement (addresses result : List String) (permutation : result.Perm addresses)
    (ordered : result.Pairwise (fun a b =>
      (compare (keys (maximumWidth addresses) (StateFaultRendering.bytes a))
        (keys (maximumWidth addresses) (StateFaultRendering.bytes b))).isLE = true)) :
    StateLift.FinSet.dedup result = StateFaultRendering.canonical addresses := by
  have byteOrdered : result.Pairwise (fun a b => StateFaultRendering.byteLE a b = true) := by
    apply List.Pairwise.imp_of_mem (p := ordered)
    intro a b left right relation
    rwa [native_key_order addresses a b ((permutation.mem_iff).mp left) ((permutation.mem_iff).mp right)] at relation
  apply List.Perm.eq_of_pairwise (fun a b _ _ => StateFaultRendering.byte_antisymm a b)
    (byteOrdered.sublist (dedup_sublist result)) (StateFaultRendering.canonical_order addresses)
  apply (List.perm_ext_iff_of_nodup (StateLift.FinSet.nodup_dedup result) (StateFaultRendering.canonical_unique addresses)).mpr
  intro address
  rw [StateLift.FinSet.mem_dedup,StateFaultRendering.canonical_member]
  exact permutation.mem_iff

/-- The actual adjacent-normalized radix output is canonical evidence once
its counting/scatter permutation and digit ordering obligations are proved. -/
theorem adjacent_result_refinement (addresses result : List String) (permutation : result.Perm addresses)
    (ordered : result.Pairwise (fun a b =>
      (compare (keys (maximumWidth addresses) (StateFaultRendering.bytes a))
        (keys (maximumWidth addresses) (StateFaultRendering.bytes b))).isLE = true)) :
    adjacent result = StateFaultRendering.canonical addresses := by
  have byteOrdered : result.Pairwise (fun a b => StateFaultRendering.byteLE a b = true) := by
    apply List.Pairwise.imp_of_mem (p := ordered)
    intro a b left right relation
    rwa [native_key_order addresses a b ((permutation.mem_iff).mp left) ((permutation.mem_iff).mp right)] at relation
  rw [adjacent_refinement result byteOrdered,sorted_result_refinement addresses result permutation ordered]

/-- Native digit-order/permutation obligations suffice for byte-identical public
fault rendering after normalization, with the reason fixed independently. -/
theorem sorted_fault_bytes (reason : String) (addresses result : List String) (permutation : result.Perm addresses)
    (ordered : result.Pairwise (fun a b =>
      (compare (keys (maximumWidth addresses) (StateFaultRendering.bytes a))
        (keys (maximumWidth addresses) (StateFaultRendering.bytes b))).isLE = true)) :
    StateJsonValue.emit (.map [(.str "evidence",.list ((adjacent result).map StateJsonValue.Value.str)),
      (.str "reason",.str reason),(.str "status",.str "fault")]) "" =
        StateJsonValue.render (StateFaultRendering.fault reason addresses) := by
  rw [adjacent_result_refinement addresses result permutation ordered,StateJsonValue.empty_buffer]
  rfl

end CBCL.StateAddressDigits
