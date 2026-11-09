import LeanCbcl.StateAddressWords

/-! USize index iteration and in-place fixed-table prefix updates. Word-valued
source indices and bucket/control positions are decoded only at Array access.
The outer digit-range/literal Rust correspondence remains distinct. -/
set_option autoImplicit false
namespace CBCL.StateAddressControl
open StateAddressWords StateAddressTables

/-- Byte bucket as a native word, receiving a native source index. -/
def wordKey (key : Nat → Nat) (index : USize) : USize := USize.ofNat (key index.toNat)

/-- Native count loop over USize-valued source indices and bucket positions. -/
def countsIndex (key : USize → USize) (order : List USize) (table : Array USize) : Array USize :=
  order.foldl (fun current index => current.modify (key index).toNat (·+1)) table

/-- Native scatter step stores the original word index directly. -/
def stepIndex (key : USize → USize) (state : WordStorage) (index : USize) : WordStorage :=
  let bucket := (key index).toNat
  let destination := (readWord state.next bucket).toNat
  ⟨state.next.modify bucket (·+1),state.scratch.setIfInBounds destination index⟩

/-- Scatter loop over actual word source indices. -/
def runIndex (key : USize → USize) (order : List USize) (state : WordStorage) : WordStorage :=
  order.foldl (stepIndex key) state

/-- Bounded byte keys survive native-word bucket conversion exactly. -/
theorem key_exact (key : Nat → Nat) (index : USize) (bounded : key index.toNat < 257) :
    (wordKey key index).toNat = key index.toNat :=
  USize.toNat_ofNat_of_lt' (byte_bucket_fits _ bounded)

/-- Native count-index iteration equals the established decoded-index loop. -/
theorem countsIndex_refinement (key : Nat → Nat) (order : List USize) (table : Array USize)
    (bounded : ∀ index ∈ order, key index.toNat < 257) :
    countsIndex (wordKey key) order table = countsWord key (order.map USize.toNat) table := by
  induction order generalizing table with
  | nil => rfl
  | cons index rest ih =>
    simp only [countsIndex,List.foldl_cons,List.map_cons,countsWord]
    rw [key_exact key index (bounded index (by simp))]
    exact ih _ (fun other member => bounded other (by simp [member]))

/-- Native word-index writes match decoded source indices without truncation. -/
theorem stepIndex_refinement (key : Nat → Nat) (state : WordStorage) (index : USize)
    (bounded : key index.toNat < 257) :
    stepIndex (wordKey key) state index = stepWord key state index.toNat := by
  simp only [stepIndex,stepWord,key_exact key index bounded,USize.ofNat_toNat]

/-- Complete scatter index iteration retains exact word identity and order. -/
theorem runIndex_refinement (key : Nat → Nat) (order : List USize) (state : WordStorage)
    (bounded : ∀ index ∈ order, key index.toNat < 257) :
    runIndex (wordKey key) order state = runWord key (order.map USize.toNat) state := by
  induction order generalizing state with
  | nil => rfl
  | cons index rest ih =>
    simp only [runIndex,List.foldl_cons,List.map_cons,runWord]
    rw [stepIndex_refinement key state index (bounded index (by simp))]
    exact ih _ (fun other member => bounded other (by simp [member]))

/-- One native in-place prefix update next[k] = next[k-1] + counts[k-1]. -/
def prefixStep (counts next : Array USize) (position : USize) : Array USize :=
  let previous := (position-1).toNat
  next.setIfInBounds position.toNat (readWord next previous + readWord counts previous)

/-- Process the native prefix positions in ascending order. -/
def prefixLoop (counts : Array USize) : Nat → Array USize
  | 0 => Array.replicate 257 0
  | width+1 => prefixStep counts (prefixLoop counts width) (USize.ofNat (width+1))

/-- Every prefix-control word and its previous position decode exactly. -/
theorem prefix_position (width : Nat) (bounded : width < 256) :
    (USize.ofNat (width+1)).toNat = width+1 ∧ (USize.ofNat (width+1)-1).toNat = width := by
  have fits : width+1 < USize.size := byte_bucket_fits _ (by omega)
  have current := USize.toNat_ofNat_of_lt' fits
  refine ⟨current,?_⟩
  have positive : (1 : USize) ≤ USize.ofNat (width+1) := by
    rw [USize.le_iff_toNat_le,current]
    simp
  rw [USize.toNat_sub_of_le _ _ positive,current]
  simp

/-- In-place prefix updates retain the fixed native 257-slot allocation. -/
theorem prefixLoop_size (counts : Array USize) (width : Nat) : (prefixLoop counts width).size = 257 := by
  induction width with
  | zero => simp [prefixLoop]
  | succ width ih => simpa [prefixLoop,prefixStep] using ih

/-- Append-style word prefixes contain zero and one entry per update. -/
theorem prefixesWord_size (counts : Array USize) (width : Nat) : (prefixesWord counts width).size = width+1 := by
  induction width with
  | zero => rfl
  | succ width ih => simp [prefixesWord,ih]

/-- At each processed prefix position, the in-place table equals the previously
proved append-style word prefix computation. -/
theorem prefixLoop_observation (counts : Array USize) (width bucket : Nat)
    (bounded : width ≤ 256) (inside : bucket ≤ width) :
    readWord (prefixLoop counts width) bucket = readWord (prefixesWord counts width) bucket := by
  induction width generalizing bucket with
  | zero =>
    have same : bucket = 0 := by omega
    subst bucket
    simp [prefixLoop,prefixesWord,readWord]
  | succ width ih =>
    have small : width < 256 := by omega
    have current := (prefix_position width small).1
    have previous := (prefix_position width small).2
    by_cases last : bucket = width+1
    · subst bucket
      simp only [prefixLoop,prefixStep,current,previous]
      have destination : width+1 < (prefixLoop counts width).size := by rw [prefixLoop_size]; omega
      rw [show readWord ((prefixLoop counts width).setIfInBounds (width+1)
        (readWord (prefixLoop counts width) width + readWord counts width)) (width+1) =
        readWord (prefixLoop counts width) width + readWord counts width from by
          simp [readWord,Array.getElem?_setIfInBounds_self_of_lt destination]]
      rw [ih width (by omega) (by omega)]
      simp only [prefixesWord,readWord,Array.getElem?_push,prefixesWord_size]
      rfl
    · have earlier : bucket ≤ width := by omega
      simp only [prefixLoop,prefixStep,current,previous,readWord]
      rw [Array.getElem?_setIfInBounds_ne (Ne.symm last)]
      have distinct : bucket ≠ (prefixesWord counts width).size := by
        rw [prefixesWord_size]
        omega
      simpa only [prefixesWord,readWord,Array.getElem?_push,if_neg distinct] using ih bucket (by omega) earlier

/-- Recursive prefix execution equals ascending half-open index iteration. -/
theorem prefixLoop_fold (counts : Array USize) (width : Nat) :
    prefixLoop counts width = (List.range width).foldl
      (fun current index => prefixStep counts current (USize.ofNat (index+1))) (Array.replicate 257 0) := by
  induction width with
  | zero => rfl
  | succ width ih => simp [prefixLoop,List.range_succ,List.foldl_append,ih]

/-- The native fixed-table prefix loop, with USize control positions 1 ≤ k < 257. -/
def prefixNative (counts : Array USize) : Array USize :=
  ((List.range 256).map (fun index => USize.ofNat (index+1))).foldl (prefixStep counts) (Array.replicate 257 0)

/-- Every observed prefix word, including both allocation endpoints, matches
word-prefix semantics after the complete in-place loop. -/
theorem prefixNative_refinement (counts : Array USize) : prefixNative counts = prefixesWord counts 256 := by
  have loop : prefixNative counts = prefixLoop counts 256 := by
    simp only [prefixNative,List.foldl_map,← prefixLoop_fold]
  rw [loop]
  apply Array.ext
  · rw [prefixLoop_size,prefixesWord_size]
  · intro bucket left right
    have inside : bucket ≤ 256 := by rw [prefixLoop_size] at left; omega
    have same := prefixLoop_observation counts 256 bucket (by omega) inside
    simpa only [readWord,Array.getElem?_eq_getElem left,Array.getElem?_eq_getElem right,Option.getD_some] using same

/-- Encoding representable source indices and decoding them preserves the exact
input sequence, not merely its set. -/
theorem index_roundtrip (order : List Nat) (fits : ∀ index ∈ order, index < USize.size) :
    (order.map USize.ofNat).map USize.toNat = order := by
  rw [List.map_map]
  calc
    _ = order.map (fun index => index) := by
      apply List.map_congr_left
      intro index member
      exact USize.toNat_ofNat_of_lt' (fits index member)
    _ = _ := List.map_id' _

/-- The byte-key domain survives encoding source indices into native words. -/
theorem encoded_bounds (key : Nat → Nat) (order : List Nat)
    (bounded : ∀ index ∈ order, key index < 257) (fits : ∀ index ∈ order, index < USize.size) :
    ∀ index ∈ order.map USize.ofNat, key index.toNat < 257 := by
  intro index member
  obtain ⟨source,inside,rfl⟩ := List.mem_map.mp member
  rw [USize.toNat_ofNat_of_lt' (fits source inside)]
  exact bounded source inside

/-- Initial native counters/prefixes with actual USize source indices. -/
def initialNative (key : USize → USize) (order : List USize) (scratch : Array USize) : WordStorage :=
  ⟨prefixNative (countsIndex key order (Array.replicate 257 0)),scratch⟩

/-- Native index iteration and fixed-table prefix mutation initialize exactly
the previously proved word-array scatter state. -/
theorem initialNative_refinement (key : Nat → Nat) (order : List Nat) (scratch : Array USize)
    (bounded : ∀ index ∈ order, key index < 257) (fits : ∀ index ∈ order, index < USize.size) :
    initialNative (wordKey key) (order.map USize.ofNat) scratch = initialWord key order scratch := by
  unfold initialNative initialWord
  rw [prefixNative_refinement,countsIndex_refinement key _ _ (encoded_bounds key order bounded fits),index_roundtrip order fits]

/-- One pass with word-valued source-index and prefix-control iteration. -/
def passNative (key : Nat → Nat) (order : List Nat) (scratch : Array Nat) : List Nat :=
  let indices := order.map USize.ofNat
  (runIndex (wordKey key) indices (initialNative (wordKey key) indices (encode scratch))).scratch.toList.map USize.toNat

/-- Native source-index and prefix control introduce no observable difference
in the complete scatter pass, including duplicate source indices. -/
theorem passNative_refinement (key : Nat → Nat) (order : List Nat) (scratch : Array Nat)
    (bounded : ∀ index ∈ order, key index < 257) (fits : ∀ index ∈ order, index < USize.size) :
    passNative key order scratch = passWord key order scratch := by
  unfold passNative passWord
  dsimp only
  rw [initialNative_refinement key order _ bounded fits,
    runIndex_refinement key _ _ (encoded_bounds key order bounded fits),index_roundtrip order fits]

/-- Recognize the native domain before converting generic Nat inputs to words. -/
def checkedNativePass (key : Nat → Nat) (order : List Nat) : List Nat :=
  if byteKeys key order && decide (order.length < USize.size) && order.all (fun index => index < USize.size) then
    passNative key order (Array.replicate order.length 0)
  else StateAddressArrayScatter.checkedPass key order

/-- Domain recognition plus exact word control preserves the complete pass. -/
theorem checkedNativePass_refinement (key : Nat → Nat) (order : List Nat) :
    checkedNativePass key order = checkedWordPass key order := by
  unfold checkedNativePass checkedWordPass
  split
  · rename_i checked
    have parts : byteKeys key order = true ∧ order.length < USize.size ∧ (∀ index ∈ order, index < USize.size) := by
      simpa [Bool.and_eq_true,List.all_eq_true,and_assoc] using checked
    exact passNative_refinement key order _ (byteKeys_sound key order parts.1) parts.2.2
  · rfl

/-- Full radix composition using native source-index and prefix-word controls. -/
def controlSort (digits : List (Nat → Nat)) (order : List Nat) : List Nat :=
  match digits with
  | [] => order
  | key::rest => checkedNativePass key (controlSort rest order)

/-- Native index/prefix controls refine the already proved word-array radix. -/
theorem controlSort_refinement (digits : List (Nat → Nat)) (order : List Nat) :
    controlSort digits order = wordSort digits order := by
  induction digits with
  | nil => rfl
  | cons key rest ih => simp only [controlSort,checkedNativePass_refinement,ih,wordSort]

end CBCL.StateAddressControl

