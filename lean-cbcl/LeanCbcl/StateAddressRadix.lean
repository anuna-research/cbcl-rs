import LeanCbcl.StateAddressScatter

/-! Stable secondary ordering and complete least-significant-digit composition
of operational counting/scatter passes. Native array/word extraction is a port. -/
set_option autoImplicit false
namespace CBCL.StateAddressRadix
open StateAddressCounting StateAddressScatter Std

/-- In input occurrence order, equal buckets get increasing destinations and
retain any relation already holding between their values. -/
theorem writes_stable (key : Nat → Nat) (order processed remaining : List Nat) (R : Nat → Nat → Prop)
    (split : order = processed ++ remaining) (related : remaining.Pairwise R) :
    (writes key order processed remaining).Pairwise (fun a b => key a.2 = key b.2 → a.1 < b.1 ∧ R a.2 b.2) := by
  induction remaining generalizing processed with
  | nil => simp [writes]
  | cons index rest ih =>
    apply List.pairwise_cons.mpr
    constructor
    · intro row member same
      obtain ⟨middle,other,last,tailSplit,rowEq⟩ := write_member key order (processed ++ [index]) rest row member
      subst row
      simp only at same ⊢
      have valueMember : other ∈ rest := by simp [tailSplit]
      refine ⟨?_,(List.pairwise_cons.mp related).1 other valueMember⟩
      have stable := equal_key_stability key order processed middle index other same
      simpa [List.append_assoc] using stable
    · exact ih (processed ++ [index]) (by simpa [List.append_assoc] using split) related.tail

/-- Increasing destination order reflects an input equal-key relation because
reversing two source occurrences would reverse their strict destination order. -/
theorem stable_reflect (key : Nat → Nat) (R : Nat → Nat → Prop) (rows : List (Nat × Nat))
    (stable : rows.Pairwise (fun a b => key a.2 = key b.2 → a.1 < b.1 ∧ R a.2 b.2))
    (a b : Nat × Nat) (left : a ∈ rows) (right : b ∈ rows) (ordered : a.1 < b.1) (same : key a.2 = key b.2) : R a.2 b.2 := by
  induction rows with
  | nil => simp at left
  | cons head rest ih =>
    rcases List.mem_cons.mp left with leftHead | leftTail
    · subst a
      rcases List.mem_cons.mp right with rightHead | rightTail
      · subst b; omega
      · exact ((List.pairwise_cons.mp stable).1 b rightTail same).2
    · rcases List.mem_cons.mp right with rightHead | rightTail
      · subst b
        have backwards := ((List.pairwise_cons.mp stable).1 a leftTail same.symm).1
        omega
      · exact ih stable.tail leftTail rightTail

/-- Every readback slot is identified with a retained concrete write-log row. -/
theorem scratch_row (key : Nat → Nat) (order : List Nat) (cells : Nat → Nat) (position : Nat)
    (inside : position < order.length) :
    ∃ row ∈ writes key order [] order, row.1 = position ∧
      (run key order (initial key order cells)).cells position = row.2 := by
  have member := (destination_permutation key order).mem_iff.mpr (List.mem_range.mpr inside)
  obtain ⟨row,source,same⟩ := List.mem_map.mp member
  refine ⟨row,source,same,?_⟩
  rw [← same]
  exact writes_retained key order cells row source

/-- A scatter pass preserves any existing secondary relation inside equal-key
buckets; it does not assume that the output is stable. -/
theorem pass_stable (key : Nat → Nat) (order : List Nat) (cells : Nat → Nat) (R : Nat → Nat → Prop)
    (related : order.Pairwise R) :
    (pass key order cells).Pairwise (fun a b => key a = key b → R a b) := by
  unfold pass
  apply List.pairwise_map.mpr
  apply List.Pairwise.imp_of_mem (p := List.pairwise_lt_range)
  intro a b left right less same
  obtain ⟨ar,am,apos,aval⟩ := scratch_row key order cells a (List.mem_range.mp left)
  obtain ⟨br,bm,bpos,bval⟩ := scratch_row key order cells b (List.mem_range.mp right)
  rw [aval,bval] at same ⊢
  exact stable_reflect key R _ (writes_stable key order [] order R rfl related) ar br am bm
    (by simpa [apos,bpos] using less) same

/-- Scratch initialization is unobservable once every destination is filled. -/
theorem pass_initial_independent (key : Nat → Nat) (order : List Nat) (A B : Nat → Nat) : pass key order A = pass key order B := by
  unfold pass
  apply List.map_congr_left
  intro position inside
  obtain ⟨row,member,same,value⟩ := scratch_row key order A position (List.mem_range.mp inside)
  rw [value,← same]
  exact (writes_retained key order B row member).symm

/-- Lexicographic digit-sequence comparison of two source indices. -/
def digitLE (digits : List (Nat → Nat)) (a b : Nat) : Prop :=
  (compare (digits.map (fun digit => digit a)) (digits.map (fun digit => digit b))).isLE = true

/-- Operational LSD composition: sort lower-significance digits before the
current head digit, then execute its counting/scatter pass. -/
def sort (digits : List (Nat → Nat)) (order : List Nat) : List Nat :=
  match digits with
  | [] => order
  | key::rest => pass key (sort rest order) (fun _ => 0)

/-- The recursive specification executes exactly the native reversed-digit
fold, so the composition theorem concerns LSD pass order explicitly. -/
theorem sort_fold (digits : List (Nat → Nat)) (order : List Nat) :
    sort digits order = digits.reverse.foldl (fun current key => pass key current (fun _ => 0)) order := by
  induction digits with
  | nil => rfl
  | cons key rest ih => simp [sort,List.reverse_cons,List.foldl_append,ih]

/-- Every composed pass preserves the complete input multiset. -/
theorem sort_permutation (digits : List (Nat → Nat)) (order : List Nat) : (sort digits order).Perm order := by
  induction digits with
  | nil => exact .refl _
  | cons key rest ih => exact (scatter_permutation key _ _).trans ih

/-- Bucket order plus an equal-key secondary relation yields full lexicographic
order at the next digit. -/
theorem digit_cons (key : Nat → Nat) (rest : List (Nat → Nat)) (a b : Nat)
    (ordered : key a ≤ key b) (secondary : key a = key b → digitLE rest a b) : digitLE (key::rest) a b := by
  simp only [digitLE,List.map_cons,List.compare_cons_cons]
  by_cases same : key a = key b
  · have relation := secondary same
    simpa [same,compare_self] using relation
  · have less : key a < key b := by omega
    have comparison : compare (key a) (key b) = Ordering.lt := by simp [compare,compareOfLessAndEq,less]
    simp [comparison]

/-- Complete LSD sorting derives digit lexicographic order from execution,
without a supplied stable-pass or sortedness premise. -/
theorem sort_order (digits : List (Nat → Nat)) (order : List Nat) : (sort digits order).Pairwise (digitLE digits) := by
  induction digits with
  | nil =>
    induction order with
    | nil => exact .nil
    | cons a rest h => exact .cons (fun b _ => rfl) h
  | cons key rest ih =>
    have buckets := scatter_bucket_order key (sort rest order) (fun _ => 0)
    have secondary := pass_stable key (sort rest order) (fun _ => 0) (digitLE rest) ih
    apply (buckets.and secondary).imp
    intro a b relation
    exact digit_cons key rest a b relation.1 relation.2

/-- Native digit functions in most-significant-first comparison order. -/
def addressDigits (width : Nat) (address : Nat → String) : List (Nat → Nat) :=
  (List.range width).map (fun position index => StateAddressDigits.digit (StateFaultRendering.bytes (address index)) position)

/-- Evaluating the native digit functions yields exactly the previously proved
fixed-width, sentinel-padded byte representation. -/
theorem digit_sequence (width : Nat) (address : Nat → String) (index : Nat) :
    (addressDigits width address).map (fun digit => digit index) =
      StateAddressDigits.keys width (StateFaultRendering.bytes (address index)) := by
  apply List.ext_getElem
  · simp [addressDigits,StateAddressDigits.keys_length]
  · intro position left right
    have inside : position < width := by simpa [addressDigits] using left
    have lookup := StateAddressDigits.keys_lookup width (StateFaultRendering.bytes (address index)) position inside
    rw [List.getElem?_eq_getElem right] at lookup
    simpa [addressDigits] using (Option.some.inj lookup).symm

/-- Complete address sorting through indices; the total address representation
is an explicit native-pool port, with no fabricated fallback address. -/
def radix (address : Nat → String) (order : List Nat) : List String :=
  (sort (addressDigits (StateAddressDigits.maximumWidth (order.map address)) address) order).map address

/-- The complete indexed radix computation retains exactly the input addresses. -/
theorem radix_permutation (address : Nat → String) (order : List Nat) : (radix address order).Perm (order.map address) :=
  (sort_permutation _ order).map address

/-- Complete radix passes establish padded digit ordering without a caller
certificate about pass stability, sorting or permutation. -/
theorem radix_digit_order (address : Nat → String) (order : List Nat) :
    (radix address order).Pairwise (fun a b =>
      (compare (StateAddressDigits.keys (StateAddressDigits.maximumWidth (order.map address)) (StateFaultRendering.bytes a))
        (StateAddressDigits.keys (StateAddressDigits.maximumWidth (order.map address)) (StateFaultRendering.bytes b))).isLE = true) := by
  unfold radix
  apply List.pairwise_map.mpr
  apply (sort_order (addressDigits (StateAddressDigits.maximumWidth (order.map address)) address) order).imp
  intro a b relation
  simpa only [digitLE,digit_sequence] using relation

/-- Native-style adjacent deduplication of the complete operational radix result
is exactly canonical finite fault evidence. Array/word and native pool extraction remain ports, rather than assumed
permutation/order premises. -/
theorem canonical_refinement (address : Nat → String) (order : List Nat) :
    StateAddressDigits.adjacent (radix address order) = StateFaultRendering.canonical (order.map address) :=
  StateAddressDigits.adjacent_result_refinement _ _ (radix_permutation address order) (radix_digit_order address order)

/-- Complete operational counting/scatter/radix composition produces the exact
reference public fault bytes for every finite indexed address input. -/
theorem fault_bytes (reason : String) (address : Nat → String) (order : List Nat) :
    StateJsonValue.emit (.map [(.str "evidence",.list ((StateAddressDigits.adjacent (radix address order)).map StateJsonValue.Value.str)),
      (.str "reason",.str reason),(.str "status",.str "fault")]) "" =
      StateJsonValue.render (StateFaultRendering.fault reason (order.map address)) := by
  rw [canonical_refinement,StateJsonValue.empty_buffer]
  rfl

end CBCL.StateAddressRadix

