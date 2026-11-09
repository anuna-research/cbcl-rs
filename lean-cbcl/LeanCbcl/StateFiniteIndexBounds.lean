import LeanCbcl.StateFiniteReadCache
import LeanCbcl.StateInstalledBounds

/-! Native row-major finite-table offsets. The installed carrier cap comes
from R7's positive/default-tightening bound gate, not an assumed architecture.
Both supported 32- and 64-bit index arithmetic preserve the exact Nat offset. -/
set_option autoImplicit false
namespace CBCL.StateFiniteIndexBounds
open State StateFiniteTable

/-- Successful finite validation retains a nonempty carrier of at most 64. -/
theorem carrier_bound (verified : Verified) : 0 < verified.table.elements.length ∧ verified.table.elements.length ≤ 64 := by
  have valid := (check_iff verified.limit verified.table).mp verified.checked
  exact ⟨by have := verified.table.bottom.isLt; omega,valid.1.2⟩

/-- A native row-major offset is inside the complete square join vector. -/
theorem flat_bound (table : Resolved) (left right : Fin table.elements.length) :
    left.val * table.elements.length + right.val < table.elements.length * table.elements.length := by
  have within : left.val * table.elements.length + right.val < (left.val+1) * table.elements.length := by
    rw [Nat.add_mul]
    have := right.isLt
    omega
  exact Nat.lt_of_lt_of_le within (Nat.mul_le_mul_right table.elements.length (Nat.succ_le_of_lt left.isLt))

/-- The complete installed native join vector has at most 4096 entries. -/
theorem square_bound (verified : Verified) : verified.table.elements.length * verified.table.elements.length ≤ 4096 :=
  Nat.mul_le_mul (carrier_bound verified).2 (carrier_bound verified).2

/-- Both native word sizes have ample space for every table offset. -/
theorem word_bounds (verified : Verified) (left right : Fin verified.table.elements.length) :
    left.val * verified.table.elements.length + right.val < 2^32 ∧
    left.val * verified.table.elements.length + right.val < 2^64 := by
  have small := Nat.lt_of_lt_of_le (flat_bound verified.table left right) (square_bound verified)
  exact ⟨Nat.lt_trans small (by decide),Nat.lt_trans small (by decide)⟩

/-- Actual 32-bit multiplication/addition implements the exact row-major offset. -/
theorem offset32 (verified : Verified) (left right : Fin verified.table.elements.length) :
    (UInt32.ofNat left.val * UInt32.ofNat verified.table.elements.length + UInt32.ofNat right.val).toNat =
      left.val * verified.table.elements.length + right.val := by
  rw [← UInt32.ofNat_mul,← UInt32.ofNat_add,UInt32.toNat_ofNat']
  exact Nat.mod_eq_of_lt (word_bounds verified left right).1

/-- Actual 64-bit multiplication/addition implements the same exact offset. -/
theorem offset64 (verified : Verified) (left right : Fin verified.table.elements.length) :
    (UInt64.ofNat left.val * UInt64.ofNat verified.table.elements.length + UInt64.ofNat right.val).toNat =
      left.val * verified.table.elements.length + right.val := by
  rw [← UInt64.ofNat_mul,← UInt64.ofNat_add,UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt (word_bounds verified left right).2

/-- Native compilation pushes each row in left-index then right-index order. -/
def denseRows (table : Resolved) : List (Fin table.elements.length) :=
  (indices table).flatMap (fun left => (indices table).map (merge table left))

/-- Native row-major construction yields exactly the square vector length. -/
theorem dense_length (table : Resolved) : (denseRows table).length = table.elements.length * table.elements.length := by
  have rows : ∀ lefts : List (Fin table.elements.length),
      (lefts.flatMap (fun left => (indices table).map (merge table left))).length = lefts.length * table.elements.length := by
    intro lefts
    induction lefts with
    | nil => simp
    | cons left rest ih =>
      rw [List.flatMap_cons,List.length_append,List.length_map,ih,List.length_cons,Nat.succ_mul]
      simp [indices,Nat.add_comm]
  simpa [denseRows,indices] using rows (indices table)

/-- An original in-range carrier index reads the matching enumerated element. -/
theorem range_lookup (n : Nat) (index : Fin n) : (List.finRange n)[index.val]? = some index := by
  simp [index.isLt]

/-- Each flattened table slot contains its original checked join result. -/
theorem dense_lookup (table : Resolved) (left right : Fin table.elements.length) :
    (denseRows table)[left.val * table.elements.length + right.val]? = some (merge table left right) := by
  have rows : ∀ (lefts : List (Fin table.elements.length)) (index : Nat) (source : Fin table.elements.length),
      lefts[index]? = some source →
      (lefts.flatMap (fun current => (indices table).map (merge table current)))[index * table.elements.length + right.val]? =
        some (merge table source right) := by
    intro lefts
    induction lefts with
    | nil => intro index source impossible; simp at impossible
    | cons current rest ih =>
      intro index source found
      cases index with
      | zero =>
        have same : current = source := Option.some.inj found
        subst source
        simp [List.getElem?_append,indices,right.isLt]
      | succ index =>
        have tail : rest[index]? = some source := found
        have offset : index.succ * table.elements.length + right.val - table.elements.length = index * table.elements.length + right.val := by
          rw [Nat.succ_mul]
          omega
        have beyond : ¬index.succ * table.elements.length + right.val < table.elements.length := by
          rw [Nat.succ_mul]
          omega
        simpa [List.getElem?_append,indices,beyond,offset] using ih index source tail
  exact rows (indices table) left.val left (range_lookup _ left)

/-- Flattened lookup using actual 32-bit offset arithmetic returns the same
checked join result as the semantic table, without out-of-range fallback. -/
theorem dense_lookup32 (verified : Verified) (left right : Fin verified.table.elements.length) :
    (denseRows verified.table)[(UInt32.ofNat left.val * UInt32.ofNat verified.table.elements.length + UInt32.ofNat right.val).toNat]? =
      some (merge verified.table left right) := by
  rw [offset32]
  exact dense_lookup verified.table left right

/-- The corresponding 64-bit native lookup has exactly the same join value. -/
theorem dense_lookup64 (verified : Verified) (left right : Fin verified.table.elements.length) :
    (denseRows verified.table)[(UInt64.ofNat left.val * UInt64.ofNat verified.table.elements.length + UInt64.ofNat right.val).toNat]? =
      some (merge verified.table left right) := by
  rw [offset64]
  exact dense_lookup verified.table left right

/-- The native pair-loop start i+1 fits a physical query slice. Physical length
is explicit because logical scalar lists are not bounded by the carrier size. -/
theorem next_index (length index bits : Nat) (physical : length < 2^bits) (inside : index < length) :
    index+1 ≤ length ∧ index+1 < 2^bits := by omega

/-- Native 32-bit loop increment does not wrap for an in-range physical query. -/
theorem next32 (length index : Nat) (physical : length < 2^32) (inside : index < length) :
    (UInt32.ofNat index + 1).toNat = index+1 := by
  change (UInt32.ofNat index + UInt32.ofNat 1).toNat = _
  rw [← UInt32.ofNat_add,UInt32.toNat_ofNat']
  exact Nat.mod_eq_of_lt (next_index length index 32 physical inside).2

/-- Native 64-bit loop increment has the same exact value. -/
theorem next64 (length index : Nat) (physical : length < 2^64) (inside : index < length) :
    (UInt64.ofNat index + 1).toNat = index+1 := by
  change (UInt64.ofNat index + UInt64.ofNat 1).toNat = _
  rw [← UInt64.ofNat_add,UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt (next_index length index 64 physical inside).2

end CBCL.StateFiniteIndexBounds
