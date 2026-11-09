import LeanCbcl.StateAddressRadix

/-! Finite Nat-array execution of native radix count and prefix initialization.
The compiler substitution is justified by extensional equality; usize extraction
remains distinct. Out-of-domain generic keys retain the functional semantics. -/
set_option autoImplicit false
namespace CBCL.StateAddressTables
open StateAddressCounting StateAddressScatter

/-- Total observation of a finite zero-default counter table. -/
def read (table : Array Nat) (bucket : Nat) : Nat := table[bucket]?.getD 0

/-- The native indexed increment loop using an actual array. -/
def counts (key : Nat → Nat) (order : List Nat) (table : Array Nat) : Array Nat :=
  order.foldl (fun current index => current.modify (key index) (· + 1)) table

/-- Array bucket increments preserve allocated table length. -/
theorem counts_size (key : Nat → Nat) (order : List Nat) (table : Array Nat) :
    (counts key order table).size = table.size := by
  induction order generalizing table with
  | nil => rfl
  | cons index rest ih => simpa [counts] using ih (table.modify (key index) (·+1))

/-- A valid indexed array increment equals the functional bucket update. -/
theorem read_modify (table : Array Nat) (bucket : Nat) (inside : bucket < table.size) :
    read (table.modify bucket (·+1)) = bump bucket (read table) := by
  funext target
  by_cases same : bucket = target
  · subst target
    simp [read,Array.getElem?_modify,bump,Array.getElem?_eq_getElem inside]
  · simp [read,Array.getElem?_modify,bump,same,Ne.symm same]

/-- The complete indexed count array refines the operational increment fold. -/
theorem counts_refinement (key : Nat → Nat) (order : List Nat) (table : Array Nat)
    (bounded : ∀ index ∈ order, key index < table.size) :
    read (counts key order table) = countLoop key order (read table) := by
  induction order generalizing table with
  | nil => rfl
  | cons index rest ih =>
    have head := bounded index (by simp)
    have tail : ∀ other ∈ rest, key other < (table.modify (key index) (·+1)).size := by
      intro other member
      simpa using bounded other (by simp [member])
    change read (counts key rest (table.modify (key index) (·+1))) = _
    rw [ih _ tail,read_modify table (key index) head]
    rfl

/-- A zero-filled counter table observes the constant-zero function. -/
theorem read_zero (width : Nat) : read (Array.replicate width 0) = fun _ => 0 := by
  funext bucket
  simp only [read,Array.getElem?_replicate]
  split <;> rfl

/-- Compute successive native prefix offsets once, retaining earlier entries. -/
def prefixes (table : Array Nat) : Nat → Array Nat
  | 0 => #[0]
  | width+1 =>
    let previous := prefixes table width
    previous.push (read previous width + read table width)

/-- The prefix table includes zero and one entry per recurrence step. -/
theorem prefixes_size (table : Array Nat) (width : Nat) : (prefixes table width).size = width+1 := by
  induction width with
  | zero => rfl
  | succ width ih => simp [prefixes,ih]

/-- Every computed prefix entry equals the native offset recurrence. -/
theorem prefixes_refinement (table : Array Nat) (width bucket : Nat) (inside : bucket ≤ width) :
    read (prefixes table width) bucket = offsets (read table) bucket := by
  induction width generalizing bucket with
  | zero =>
    have same : bucket = 0 := by omega
    subst bucket
    rfl
  | succ width ih =>
    by_cases last : bucket = width+1
    · subst bucket
      simp only [prefixes,read,Array.getElem?_push,prefixes_size]
      change read (prefixes table width) width + read table width = offsets (read table) (width+1)
      rw [ih width (by omega),offsets]
    · have earlier : bucket ≤ width := by omega
      have different : bucket ≠ (prefixes table width).size := by rw [prefixes_size]; omega
      simpa [prefixes,read,Array.getElem?_push,different] using ih bucket earlier

/-- Recognize the byte bucket domain before finite table execution. -/
def byteKeys (key : Nat → Nat) (order : List Nat) : Bool := order.all (fun index => key index < 257)

/-- Successful bucket recognition covers every encountered source index. -/
theorem byteKeys_sound (key : Nat → Nat) (order : List Nat) (checked : byteKeys key order = true) :
    ∀ index ∈ order, key index < 257 := by
  simpa [byteKeys,List.all_eq_true] using checked

/-- Finite-array native initialization; generic non-byte keys keep the original
semantics. The fallback function outside the finite table is never used by byte
passes, but preserves full extensional equality for compiler substitution. -/
@[noinline] def initBuffer (key : Nat → Nat) (order : List Nat) (cells : Nat → Nat) : Buffer :=
  if byteKeys key order then
    let table := counts key order (Array.replicate 257 0)
    let next := prefixes table 256
    ⟨fun bucket => if bucket < 257 then read next bucket else offsets (countLoop key order (fun _ => 0)) bucket,cells⟩
  else initial key order cells

/-- Finite array initialization equals the functional semantics on every bucket,
including arbitrary generic key inputs and unobserved out-of-table buckets. -/
theorem initialize_refinement (key : Nat → Nat) (order : List Nat) (cells : Nat → Nat) :
    initBuffer key order cells = initial key order cells := by
  unfold initBuffer
  split
  · rename_i checked
    have bounded : ∀ index ∈ order, key index < (Array.replicate 257 0).size := by
      simpa using byteKeys_sound key order checked
    have represented := counts_refinement key order (Array.replicate 257 0) bounded
    rw [read_zero] at represented
    have same : (fun bucket => if bucket < 257 then read (prefixes (counts key order (Array.replicate 257 0)) 256) bucket
        else offsets (countLoop key order (fun _ => 0)) bucket) = offsets (countLoop key order (fun _ => 0)) := by
      funext bucket
      split
      · rename_i inside
        rw [prefixes_refinement _ 256 bucket (by omega),represented]
      · rfl
    dsimp only
    rw [same]
    rfl
  · rfl

/-- Execute one scatter pass with proved finite-array initialization. -/
def cachedPass (key : Nat → Nat) (order : List Nat) (cells : Nat → Nat) : List Nat :=
  (List.range order.length).map (run key order (initBuffer key order cells)).cells

/-- Finite-array initialization changes no scatter readback value. -/
theorem cachedPass_refinement (key : Nat → Nat) (order : List Nat) (cells : Nat → Nat) :
    cachedPass key order cells = pass key order cells := by
  unfold cachedPass
  rw [initialize_refinement]
  rfl

/-- Complete LSD execution using finite count and prefix tables. -/
def cachedSort (digits : List (Nat → Nat)) (order : List Nat) : List Nat :=
  match digits with
  | [] => order
  | key::rest => cachedPass key (cachedSort rest order) (fun _ => 0)

/-- Every finite-table LSD pass composes to the previously proved semantics. -/
theorem cachedSort_refinement (digits : List (Nat → Nat)) (order : List Nat) :
    cachedSort digits order = StateAddressRadix.sort digits order := by
  induction digits with
  | nil => rfl
  | cons key rest ih => simp only [cachedSort,cachedPass_refinement,ih,StateAddressRadix.sort]

/-- Compiled oracle execution substitutes finite arrays only after proving
complete function equality to the semantics used by every radix theorem. -/
@[csimp] theorem sort_compiled : @StateAddressRadix.sort = @cachedSort := by
  funext digits order
  exact (cachedSort_refinement digits order).symm

end CBCL.StateAddressTables
