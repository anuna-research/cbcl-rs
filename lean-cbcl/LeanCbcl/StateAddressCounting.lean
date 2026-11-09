import LeanCbcl.StateAddressDigits

/-! Operational counting and prefix-offset arithmetic for native radix sorting.
Counters are natural numbers here; array/usize extraction and scratch-cell
permutation are separate obligations. No collision-freedom premise is supplied. -/
set_option autoImplicit false
namespace CBCL.StateAddressCounting

/-- Increment the one bucket selected by the current address index. -/
def bump (bucket : Nat) (counts : Nat → Nat) : Nat → Nat :=
  let updated := counts bucket + 1
  fun target => if target = bucket then updated else counts target

/-- The native count/scatter-cursor increment loop over an index order. -/
def countLoop (key : Nat → Nat) (order : List Nat) (initial : Nat → Nat) : Nat → Nat :=
  order.foldl (fun counts index => bump (key index) counts) initial

/-- Number of encountered indices belonging to one bucket. -/
def frequency (key : Nat → Nat) (order : List Nat) (bucket : Nat) : Nat :=
  order.countP (fun index => key index == bucket)

/-- Number of indices in buckets before the selected bucket. -/
def before (key : Nat → Nat) (order : List Nat) (bucket : Nat) : Nat :=
  order.countP (fun index => key index < bucket)

/-- Operational bucket increments refine exact occurrence counts. -/
theorem countLoop_refinement (key : Nat → Nat) (order : List Nat) (initial : Nat → Nat) (bucket : Nat) :
    countLoop key order initial bucket = initial bucket + frequency key order bucket := by
  induction order generalizing initial with
  | nil => simp [countLoop,frequency]
  | cons index rest ih =>
    simp only [countLoop,List.foldl_cons]
    rw [show rest.foldl (fun counts index => bump (key index) counts) (bump (key index) initial) bucket =
      (bump (key index) initial) bucket + frequency key rest bucket from ih _]
    by_cases same : key index = bucket
    · simp [bump,frequency,same,Nat.add_assoc,Nat.add_comm]
    · simp [bump,frequency,same,Ne.symm same]

/-- Native prefix recurrence next[k+1] = next[k] + counts[k]. -/
def offsets (counts : Nat → Nat) : Nat → Nat
  | 0 => 0
  | bucket+1 => offsets counts bucket + counts bucket

/-- Exact counts partition the next prefix step into earlier/equal buckets. -/
theorem before_succ (key : Nat → Nat) (order : List Nat) (bucket : Nat) :
    before key order (bucket+1) = before key order bucket + frequency key order bucket := by
  induction order with
  | nil => simp [before,frequency]
  | cons index rest ih =>
    by_cases low : key index < bucket
    · have lower : key index < bucket+1 := by omega
      have different : key index ≠ bucket := by omega
      simp [before,frequency,low,lower,different] at *
      omega
    · by_cases equal : key index = bucket
      · simp [before,frequency,equal] at *
        omega
      · have higher : ¬key index < bucket+1 := by omega
        simp [before,frequency,low,higher,equal] at *
        omega

/-- Prefix offsets are computed from the actual count loop, not an input oracle. -/
theorem offsets_refinement (key : Nat → Nat) (order : List Nat) (bucket : Nat) :
    offsets (countLoop key order (fun _ => 0)) bucket = before key order bucket := by
  induction bucket with
  | zero => simp [offsets,before]
  | succ bucket ih => rw [offsets,ih,countLoop_refinement,before_succ]; simp

/-- A scatter cursor after processing a prefix is its initial offset plus the
number of earlier equal-key indices, exactly as native next[k] increments. -/
def cursor (key : Nat → Nat) (order processed : List Nat) (bucket : Nat) : Nat :=
  countLoop key processed (offsets (countLoop key order (fun _ => 0))) bucket

/-- Exact arithmetic interpretation of the operational scatter cursor. -/
theorem cursor_refinement (key : Nat → Nat) (order processed : List Nat) (bucket : Nat) :
    cursor key order processed bucket = before key order bucket + frequency key processed bucket := by
  rw [cursor,countLoop_refinement,offsets_refinement]

/-- Bucket end positions never exceed the allocated scratch length. -/
theorem bucket_end_bound (key : Nat → Nat) (order : List Nat) (bucket : Nat) :
    before key order bucket + frequency key order bucket ≤ order.length := by
  rw [← before_succ]
  exact List.countP_le_length

/-- Scattering the next index always writes strictly inside its bucket. -/
theorem cursor_inside_bucket (key : Nat → Nat) (processed : List Nat) (index : Nat) (rest : List Nat) :
    cursor key (processed ++ index::rest) processed (key index) <
      before key (processed ++ index::rest) (key index) + frequency key (processed ++ index::rest) (key index) := by
  rw [cursor_refinement]
  simp only [frequency,List.countP_append,List.countP_cons,BEq.rfl,if_true]
  omega

/-- Every operational scatter destination is a valid scratch index. -/
theorem scatter_index_bound (key : Nat → Nat) (processed : List Nat) (index : Nat) (rest : List Nat) :
    cursor key (processed ++ index::rest) processed (key index) < (processed ++ index::rest).length :=
  Nat.lt_of_lt_of_le (cursor_inside_bucket key processed index rest) (bucket_end_bound key _ _)

/-- Later occurrences of the same bucket get strictly increasing destinations. -/
theorem equal_key_stability (key : Nat → Nat) (order processed middle : List Nat) (a b : Nat) (same : key a = key b) :
    cursor key order processed (key a) < cursor key order (processed ++ a::middle) (key b) := by
  simp only [cursor_refinement,frequency,List.countP_append,List.countP_cons]
  simp only [same,BEq.rfl,if_true]
  omega

/-- Counting a smaller bucket plus all its predecessors fits before any later
bucket, so two different bucket ranges cannot overlap. -/
theorem bucket_separation (key : Nat → Nat) (order : List Nat) (a b : Nat) (less : a < b) :
    before key order a + frequency key order a ≤ before key order b := by
  rw [← before_succ]
  apply List.countP_mono_left
  intro index _
  simp only [decide_eq_true_eq]
  omega

/-- The cursor for any processed prefix starts at or after its bucket offset. -/
theorem cursor_after_start (key : Nat → Nat) (order processed : List Nat) (bucket : Nat) :
    before key order bucket ≤ cursor key order processed bucket := by
  rw [cursor_refinement]
  omega

/-- Any two actual scatter steps with ordered distinct keys have ordered,
therefore different, destinations. The first occurrence decomposition is explicit;
the later bucket cursor may be at any processed prefix. -/
theorem distinct_key_order (key : Nat → Nat) (order leftPrefix leftRest rightPrefix : List Nat)
    (a b : Nat) (left : order = leftPrefix ++ a::leftRest) (less : key a < key b) :
    cursor key order leftPrefix (key a) < cursor key order rightPrefix (key b) := by
  have inside := cursor_inside_bucket key leftPrefix a leftRest
  rw [← left] at inside
  exact Nat.lt_of_lt_of_le inside (Nat.le_trans (bucket_separation key order _ _ less)
    (cursor_after_start key order rightPrefix (key b)))

/-- Distinct occurrence positions never target the same scratch cell, even
when they contain the same index or duplicate byte keys. -/
theorem scatter_no_collision (key : Nat → Nat) (processedFirst middle rest : List Nat) (a b : Nat) :
    let order := processedFirst ++ a::(middle ++ b::rest)
    cursor key order processedFirst (key a) ≠ cursor key order (processedFirst ++ a::middle) (key b) := by
  dsimp
  rcases Nat.lt_trichotomy (key a) (key b) with less | same | greater
  · exact Nat.ne_of_lt (distinct_key_order key _ processedFirst (middle ++ b::rest) _ a b rfl less)
  · exact Nat.ne_of_lt (equal_key_stability key _ processedFirst middle a b same)
  · apply Ne.symm
    apply Nat.ne_of_lt
    apply distinct_key_order key _ (processedFirst ++ a::middle) rest processedFirst b a
    · simp [List.append_assoc]
    · exact greater

/-- Every cursor update, including the last increment, stays within the total
length. This supplies the arithmetic bound needed for usize extraction. -/
theorem cursor_bound (key : Nat → Nat) (processed remaining : List Nat) (bucket : Nat) :
    cursor key (processed ++ remaining) processed bucket ≤ (processed ++ remaining).length := by
  rw [cursor_refinement]
  have frequencyBound : frequency key processed bucket ≤ frequency key (processed ++ remaining) bucket := by
    simp [frequency]
  exact Nat.le_trans (Nat.add_le_add_left frequencyBound _) (bucket_end_bound key _ bucket)

/-- Count-loop values from zero fit the allocated input length. -/
theorem counts_bound (key : Nat → Nat) (order : List Nat) (bucket : Nat) :
    countLoop key order (fun _ => 0) bucket ≤ order.length := by
  rw [countLoop_refinement]
  simpa [frequency] using (List.countP_le_length (p := fun index => key index == bucket) (l := order))

/-- Prefix offsets fit the same input length as scatter cursors. -/
theorem offsets_bound (key : Nat → Nat) (order : List Nat) (bucket : Nat) :
    offsets (countLoop key order (fun _ => 0)) bucket ≤ order.length := by
  rw [offsets_refinement]
  exact List.countP_le_length

/-- Under the native representable-length premise, counters, offsets and all
partial scatter cursors are simultaneously representable in that word width. -/
theorem word_bounds (bits : Nat) (key : Nat → Nat) (processed remaining : List Nat) (bucket : Nat)
    (fits : (processed ++ remaining).length < 2^bits) :
    countLoop key (processed ++ remaining) (fun _ => 0) bucket < 2^bits ∧
    offsets (countLoop key (processed ++ remaining) (fun _ => 0)) bucket < 2^bits ∧
    cursor key (processed ++ remaining) processed bucket < 2^bits :=
  ⟨Nat.lt_of_le_of_lt (counts_bound key _ bucket) fits,
    Nat.lt_of_le_of_lt (offsets_bound key _ bucket) fits,
    Nat.lt_of_le_of_lt (cursor_bound key processed remaining bucket) fits⟩

end CBCL.StateAddressCounting
