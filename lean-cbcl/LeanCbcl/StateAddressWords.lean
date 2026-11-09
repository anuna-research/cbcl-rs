import LeanCbcl.StateAddressArrayScatter

/-! Native word representation for radix counter and prefix arrays. Encoding
commutes with actual USize increments/additions; decoding uses derived length
bounds, rather than an assumed no-overflow predicate for every operation. -/
set_option autoImplicit false
namespace CBCL.StateAddressWords
open StateAddressCounting StateAddressTables

/-- Encode each mathematical counter in the platform's native unsigned word. -/
def encode (table : Array Nat) : Array USize := table.map USize.ofNat

/-- Native word-array observation, including zero-initialized absent entries. -/
def readWord (table : Array USize) (bucket : Nat) : USize := table[bucket]?.getD 0

/-- Native indexed USize count increments. -/
def countsWord (key : Nat → Nat) (order : List Nat) (table : Array USize) : Array USize :=
  order.foldl (fun current index => current.modify (key index) (· + 1)) table

/-- Native indexed prefix addition, retaining every computed entry. -/
def prefixesWord (table : Array USize) : Nat → Array USize
  | 0 => #[0]
  | width+1 =>
    let previous := prefixesWord table width
    previous.push (readWord previous width + readWord table width)

/-- Observation of encoded arrays agrees even outside the allocation. -/
theorem read_encode (table : Array Nat) (bucket : Nat) :
    readWord (encode table) bucket = USize.ofNat (read table bucket) := by
  simp only [readWord,encode,Array.getElem?_map,StateAddressTables.read]
  cases table[bucket]? <;> rfl

/-- Word increments commute with Nat encoding without a hidden non-wrap premise;
this equality concerns modular encoding, with exact decoding established below. -/
theorem modify_encode (table : Array Nat) (bucket : Nat) :
    (encode table).modify bucket (·+1) = encode (table.modify bucket (·+1)) := by
  apply Array.ext
  · simp [encode]
  · intro position left right
    simp only [encode,Array.getElem_modify,Array.getElem_map]
    split <;> simp [USize.ofNat_add]

/-- The complete USize count loop encodes the Nat-array execution exactly. -/
theorem counts_encode (key : Nat → Nat) (order : List Nat) (table : Array Nat) :
    countsWord key order (encode table) = encode (counts key order table) := by
  induction order generalizing table with
  | nil => rfl
  | cons index rest ih =>
    change countsWord key rest ((encode table).modify (key index) (·+1)) = _
    rw [modify_encode,ih]
    rfl

/-- Every computed USize prefix entry encodes the corresponding Nat sum. -/
theorem prefixes_encode (table : Array Nat) (width : Nat) :
    prefixesWord (encode table) width = encode (prefixes table width) := by
  induction width with
  | zero => simp [prefixesWord,prefixes,encode,show USize.ofNat 0 = 0 from by decide]
  | succ width ih =>
    simp only [prefixesWord,prefixes,ih,read_encode]
    simp [encode,Array.map_push,USize.ofNat_add]

/-- A representable result makes native word addition exact, without wrapping. -/
theorem add_exact (a b limit : Nat) (within : a+b ≤ limit) (fits : limit < USize.size) :
    (USize.ofNat a + USize.ofNat b).toNat = a+b := by
  rw [← USize.ofNat_add]
  exact USize.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt within fits)

/-- Increment safety follows from the next value's operational length bound. -/
theorem increment_exact (value limit : Nat) (within : value+1 ≤ limit) (fits : limit < USize.size) :
    (USize.ofNat value + 1).toNat = value+1 :=
  add_exact value 1 limit within fits

/-- Finite zero count tables are the same native USize initial allocation. -/
theorem encode_zero (width : Nat) : encode (Array.replicate width 0) = Array.replicate width 0 := by
  simp [encode,show USize.ofNat 0 = 0 from by decide]

/-- Exact count decoding derives non-wrap from total input length. No per-cell
machine-width assumption is supplied by the caller. -/
theorem counts_exact (key : Nat → Nat) (order : List Nat) (bucket : Nat)
    (bounded : ∀ index ∈ order, key index < 257) (fits : order.length < USize.size) :
    (readWord (countsWord key order (Array.replicate 257 0)) bucket).toNat =
      countLoop key order (fun _ => 0) bucket := by
  rw [← encode_zero 257,counts_encode,read_encode]
  have represented := counts_refinement key order (Array.replicate 257 0) (by simpa using bounded)
  rw [read_zero] at represented
  have observation := congrFun represented bucket
  rw [observation]
  exact USize.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt (counts_bound key order bucket) fits)

/-- Native prefix values decode exactly at every initialized byte bucket;
count-loop and offset bounds derive the non-wrap result. -/
theorem prefixes_exact (key : Nat → Nat) (order : List Nat) (bucket : Nat)
    (bounded : ∀ index ∈ order, key index < 257) (inside : bucket < 257) (fits : order.length < USize.size) :
    (readWord (prefixesWord (countsWord key order (Array.replicate 257 0)) 256) bucket).toNat =
      offsets (countLoop key order (fun _ => 0)) bucket := by
  rw [← encode_zero 257,counts_encode,prefixes_encode,read_encode]
  have represented := counts_refinement key order (Array.replicate 257 0) (by simpa using bounded)
  rw [read_zero] at represented
  rw [prefixes_refinement _ 256 bucket (by omega),represented]
  exact USize.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt (offsets_bound key order bucket) fits)

/-- Every byte bucket is representable on both supported native word widths. -/
theorem byte_bucket_fits (bucket : Nat) (bounded : bucket < 257) : bucket < USize.size := by
  have native := USize.le_size
  have small : bucket < 2^32 := by omega
  exact Nat.lt_of_lt_of_le small native

/-- Native byte-to-usize conversion followed by the sentinel offset is exact,
including NUL and the maximum byte, on either supported word width. -/
theorem byte_digit_exact (byte : UInt8) :
    (USize.ofNat byte.toNat + 1).toNat = byte.toNat+1 := by
  have bound := byte.toNat_lt_size
  change byte.toNat < 256 at bound
  exact add_exact byte.toNat 1 256 (by omega) (byte_bucket_fits 256 (by decide))

/-- Native word arrays for next pointers and scratch indices. -/
structure WordStorage where
  /-- USize-valued bucket pointers. -/
  next : Array USize
  /-- USize-valued scratch indices. -/
  scratch : Array USize

/-- Encode the two finite Nat arrays without changing their allocation sizes. -/
def encodeStorage (state : StateAddressArrayScatter.Storage) : WordStorage :=
  ⟨encode state.next,encode state.scratch⟩

/-- Actual word destination lookup, indexed write and word increment. -/
def stepWord (key : Nat → Nat) (state : WordStorage) (index : Nat) : WordStorage :=
  let bucket := key index
  let destination := (readWord state.next bucket).toNat
  ⟨state.next.modify bucket (·+1),state.scratch.setIfInBounds destination (USize.ofNat index)⟩

/-- Execute the native-word scatter loop. -/
def runWord (key : Nat → Nat) (order : List Nat) (state : WordStorage) : WordStorage :=
  order.foldl (stepWord key) state

/-- Representable next pointers make word scatter commute with Nat-array
execution. Scratch values are encoded here; exact decoding follows bounds. -/
theorem step_encode (key : Nat → Nat) (state : StateAddressArrayScatter.Storage) (index : Nat)
    (fits : read state.next (key index) < USize.size) :
    stepWord key (encodeStorage state) index = encodeStorage (StateAddressArrayScatter.stepArray key state index) := by
  unfold stepWord encodeStorage StateAddressArrayScatter.stepArray
  dsimp only
  rw [read_encode,USize.toNat_ofNat_of_lt' fits,modify_encode]
  simp [encode,Array.map_setIfInBounds]

/-- Array scatter's next-pointer projection is the indexed count loop, started
from the computed prefix array. -/
theorem next_array_counts (key : Nat → Nat) (processed : List Nat) (state : StateAddressArrayScatter.Storage) :
    (StateAddressArrayScatter.runArray key processed state).next = counts key processed state.next := by
  induction processed generalizing state with
  | nil => rfl
  | cons index rest ih =>
    change (StateAddressArrayScatter.runArray key rest (StateAddressArrayScatter.stepArray key state index)).next = _
    rw [ih]
    rfl

/-- At every actual prefix, a finite next-array lookup is the exact operational
cursor. Its full input decomposition establishes the needed key domain. -/
theorem array_cursor (key : Nat → Nat) (order processed remaining : List Nat) (scratch : Array Nat) (bucket : Nat)
    (bounded : ∀ index ∈ order, key index < 257) (split : order = processed ++ remaining) (inside : bucket < 257) :
    read (StateAddressArrayScatter.runArray key processed (StateAddressArrayScatter.initialArray key order scratch)).next bucket =
      cursor key order processed bucket := by
  rw [next_array_counts]
  have prefixBounds : ∀ index ∈ processed, key index < (StateAddressArrayScatter.initialArray key order scratch).next.size := by
    intro index member
    simpa [StateAddressArrayScatter.initialArray,prefixes_size] using bounded index (by simp [split,member])
  rw [congrFun (counts_refinement key processed _ prefixBounds) bucket,countLoop_refinement,cursor_refinement]
  have initialized := congrArg (fun state : StateAddressScatter.Buffer => state.next bucket)
    (StateAddressArrayScatter.initial_refinement key order scratch bounded)
  have size : (StateAddressArrayScatter.initialArray key order scratch).next.size = 257 := by
    simp [StateAddressArrayScatter.initialArray,prefixes_size]
  simpa only [StateAddressArrayScatter.view,size,if_pos inside,StateAddressScatter.initial,offsets_refinement] using
    congrArg (fun value => value + frequency key processed bucket) initialized

/-- A source occurrence derives both scratch allocation safety and exact word
representability of its destination; no per-step overflow oracle is supplied. -/
theorem destination_exact (key : Nat → Nat) (processed : List Nat) (index : Nat) (rest : List Nat) (scratch : Array Nat)
    (bounded : ∀ source ∈ processed ++ index::rest, key source < 257)
    (fits : (processed ++ index::rest).length < USize.size) :
    let state := StateAddressArrayScatter.runArray key processed
      (StateAddressArrayScatter.initialArray key (processed ++ index::rest) scratch)
    read state.next (key index) < (processed ++ index::rest).length ∧
      read state.next (key index) < USize.size := by
  dsimp
  rw [array_cursor key _ processed (index::rest) scratch (key index) bounded rfl (bounded index (by simp))]
  have bound := scatter_index_bound key processed index rest
  exact ⟨bound,Nat.lt_trans bound fits⟩

/-- Word scatter commutes over the whole loop once its reachable Nat-array
states have representable destinations. Full-input bounds discharge this
internal simulation premise in run_exact below. -/
theorem run_encode (key : Nat → Nat) (remaining : List Nat) (state : StateAddressArrayScatter.Storage)
    (safe : ∀ processed index rest, remaining = processed ++ index::rest →
      read (StateAddressArrayScatter.runArray key processed state).next (key index) < USize.size) :
    runWord key remaining (encodeStorage state) = encodeStorage (StateAddressArrayScatter.runArray key remaining state) := by
  induction remaining generalizing state with
  | nil => rfl
  | cons index rest ih =>
    have head : read state.next (key index) < USize.size := safe [] index rest rfl
    change runWord key rest (stepWord key (encodeStorage state) index) = _
    rw [step_encode key state index head]
    rw [ih]
    · rfl
    · intro processed other tail split
      exact safe (index::processed) other tail (by simp [split])

/-- Complete native-word scatter equality derives every reachable destination's
representability from byte buckets and the input length alone. -/
theorem run_exact (key : Nat → Nat) (order : List Nat) (scratch : Array Nat)
    (bounded : ∀ index ∈ order, key index < 257) (fits : order.length < USize.size) :
    runWord key order (encodeStorage (StateAddressArrayScatter.initialArray key order scratch)) =
      encodeStorage (StateAddressArrayScatter.runArray key order (StateAddressArrayScatter.initialArray key order scratch)) := by
  apply run_encode
  intro processed index rest split
  have result := destination_exact key processed index rest scratch (by simpa [← split] using bounded) (by simpa [← split] using fits)
  simpa only [← split] using result.2

/-- Native USize count/prefix initialization, with word scratch storage. -/
def initialWord (key : Nat → Nat) (order : List Nat) (scratch : Array USize) : WordStorage :=
  ⟨prefixesWord (countsWord key order (Array.replicate 257 0)) 256,scratch⟩

/-- Native word initialization matches the encoded finite Nat initializer. -/
theorem initial_encode (key : Nat → Nat) (order : List Nat) (scratch : Array Nat) :
    initialWord key order (encode scratch) = encodeStorage (StateAddressArrayScatter.initialArray key order scratch) := by
  unfold initialWord encodeStorage StateAddressArrayScatter.initialArray
  rw [← encode_zero 257,counts_encode,prefixes_encode]

/-- Native word scratch readback converted to source indices. -/
def passWord (key : Nat → Nat) (order : List Nat) (scratch : Array Nat) : List Nat :=
  (runWord key order (initialWord key order (encode scratch))).scratch.toList.map USize.toNat

/-- Complete word scatter preserves exact source indices and multiplicities,
using input-index and allocation bounds rather than a decoding certificate. -/
theorem pass_exact (key : Nat → Nat) (order : List Nat) (scratch : Array Nat)
    (bounded : ∀ index ∈ order, key index < 257) (fits : order.length < USize.size)
    (indices : ∀ index ∈ order, index < USize.size) (allocated : scratch.size = order.length) :
    passWord key order scratch = StateAddressArrayScatter.passArray key order scratch := by
  unfold passWord
  rw [initial_encode,run_exact key order scratch bounded fits]
  change ((encode (StateAddressArrayScatter.runArray key order (StateAddressArrayScatter.initialArray key order scratch)).scratch).toList.map USize.toNat) = _
  simp only [encode,Array.toList_map,List.map_map]
  change ((StateAddressArrayScatter.passArray key order scratch).map (fun value => (USize.ofNat value).toNat)) = _
  have permutation := StateAddressArrayScatter.pass_permutation key order scratch bounded allocated
  calc
    _ = (StateAddressArrayScatter.passArray key order scratch).map (fun index => index) := by
      apply List.map_congr_left
      intro index member
      exact USize.toNat_ofNat_of_lt' (indices index (permutation.mem_iff.mp member))
    _ = _ := List.map_id' _

/-- Recognize precisely the finite byte-key, length and source-index bounds
needed by the native-word implementation. Generic inputs retain Nat semantics. -/
def checkedWordPass (key : Nat → Nat) (order : List Nat) : List Nat :=
  if byteKeys key order && decide (order.length < USize.size) && order.all (fun index => index < USize.size) then
    passWord key order (Array.replicate order.length 0)
  else StateAddressArrayScatter.checkedPass key order

/-- Word representation recognition and refinement preserve the complete pass. -/
theorem checkedWordPass_refinement (key : Nat → Nat) (order : List Nat) :
    checkedWordPass key order = StateAddressScatter.pass key order (fun _ => 0) := by
  unfold checkedWordPass
  split
  · rename_i checked
    have checkedParts : byteKeys key order = true ∧ order.length < USize.size ∧ (∀ index ∈ order, index < USize.size) := by
      simpa [Bool.and_eq_true,List.all_eq_true,and_assoc] using checked
    rw [pass_exact key order _ (byteKeys_sound key order checkedParts.1) checkedParts.2.1 checkedParts.2.2 (by simp),
      StateAddressArrayScatter.pass_refinement key order _ (byteKeys_sound key order checkedParts.1) (by simp),read_zero]
  · exact StateAddressArrayScatter.checkedPass_refinement key order

/-- Complete radix composition executing native-word arrays where representable. -/
def wordSort (digits : List (Nat → Nat)) (order : List Nat) : List Nat :=
  match digits with
  | [] => order
  | key::rest => checkedWordPass key (wordSort rest order)

/-- Every word-array pass composes to the established full radix semantics. -/
theorem wordSort_refinement (digits : List (Nat → Nat)) (order : List Nat) :
    wordSort digits order = StateAddressRadix.sort digits order := by
  induction digits with
  | nil => rfl
  | cons key rest ih => simp only [wordSort,checkedWordPass_refinement,ih,StateAddressRadix.sort]

end CBCL.StateAddressWords


