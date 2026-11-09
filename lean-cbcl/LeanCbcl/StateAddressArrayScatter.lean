import LeanCbcl.StateAddressTables

/-! Finite-array scatter refinement. Valid bucket and destination accesses are
derived from the complete input's operational prefix invariant. Counter values
are Nat; native usize extraction remains a separate representation boundary. -/
set_option autoImplicit false
namespace CBCL.StateAddressArrayScatter
open StateAddressCounting StateAddressScatter StateAddressTables

/-- The two native arrays mutated by a radix scatter pass. -/
structure Storage where
  /-- Next free slot in each of the 257 byte buckets. -/
  next : Array Nat
  /-- Scratch indices, retaining the input allocation length. -/
  scratch : Array Nat

/-- A functional view uses a fixed fallback only for unobserved buckets outside
the finite table; valid byte-key accesses always use the array itself. -/
def view (fallback : Nat → Nat) (state : Storage) : Buffer :=
  ⟨fun bucket => if bucket < state.next.size then read state.next bucket else fallback bucket,
    read state.scratch⟩

/-- Native indexed scratch write followed by indexed bucket increment. -/
def stepArray (key : Nat → Nat) (state : Storage) (index : Nat) : Storage :=
  let bucket := key index
  let destination := read state.next bucket
  ⟨state.next.modify bucket (·+1),state.scratch.setIfInBounds destination index⟩

/-- Complete native array scatter loop in input order. -/
def runArray (key : Nat → Nat) (order : List Nat) (state : Storage) : Storage :=
  order.foldl (stepArray key) state

/-- Actual finite count and prefix arrays initialize scatter. -/
def initialArray (key : Nat → Nat) (order : List Nat) (scratch : Array Nat) : Storage :=
  ⟨prefixes (counts key order (Array.replicate 257 0)) 256,scratch⟩

/-- Array writes and increments preserve both allocation lengths. -/
theorem step_sizes (key : Nat → Nat) (state : Storage) (index : Nat) :
    (stepArray key state index).next.size = state.next.size ∧
      (stepArray key state index).scratch.size = state.scratch.size := by
  simp [stepArray]

/-- A valid scratch array write exactly matches a functional cell update. -/
theorem read_set (table : Array Nat) (destination value : Nat) (inside : destination < table.size) :
    read (table.setIfInBounds destination value) =
      fun position => if position = destination then value else read table position := by
  funext position
  by_cases same : position = destination
  · subst position
    simp [StateAddressTables.read,Array.getElem?_setIfInBounds_self_of_lt inside]
  · simp [StateAddressTables.read,Array.getElem?_setIfInBounds_ne (Ne.symm same),same]

/-- A valid bucket increment matches the functional next-pointer update,
including agreement on all unobserved outside-table buckets. -/
theorem next_modify (table : Array Nat) (fallback : Nat → Nat) (bucket : Nat) (inside : bucket < table.size) :
    (fun target => if target < (table.modify bucket (·+1)).size then read (table.modify bucket (·+1)) target else fallback target) =
      bump bucket (fun target => if target < table.size then read table target else fallback target) := by
  funext target
  by_cases observed : target < table.size
  · simp only [Array.size_modify,if_pos observed]
    have refined := congrFun (read_modify table bucket inside) target
    by_cases same : target = bucket
    · subst target
      simpa [bump,inside] using refined
    · simpa [bump,same,observed] using refined
  · have different : target ≠ bucket := by omega
    simp [bump,observed,different]

/-- Both actual indexed operations refine one semantic scatter step. -/
theorem step_refinement (key : Nat → Nat) (state : Storage) (fallback : Nat → Nat) (index : Nat)
    (bucket : key index < state.next.size)
    (destination : read state.next (key index) < state.scratch.size) :
    view fallback (stepArray key state index) = StateAddressScatter.step key (view fallback state) index := by
  have next := next_modify state.next fallback (key index) bucket
  have cells := read_set state.scratch (read state.next (key index)) index destination
  unfold view stepArray StateAddressScatter.step
  dsimp only
  rw [next,cells]
  simp only [if_pos bucket]

/-- The finite initializer represents every functional next pointer exactly. -/
theorem initial_refinement (key : Nat → Nat) (order : List Nat) (scratch : Array Nat)
    (bounded : ∀ index ∈ order, key index < 257) :
    view (offsets (countLoop key order (fun _ => 0))) (initialArray key order scratch) =
      initial key order (read scratch) := by
  have checked : byteKeys key order = true := by simpa [byteKeys,List.all_eq_true] using bounded
  have same := initialize_refinement key order (read scratch)
  simpa only [initBuffer,checked,if_true,initialArray,view,prefixes_size] using same

/-- Preserve the complete processed-prefix refinement across the remaining
array loop. Bucket/destination safety follows from the input and invariant. -/
theorem run_suffix_refinement (key : Nat → Nat) (order processed remaining : List Nat)
    (scratch : Array Nat) (state : Storage)
    (bounded : ∀ index ∈ order, key index < 257) (split : order = processed ++ remaining)
    (nextSize : state.next.size = 257) (scratchSize : state.scratch.size = order.length)
    (represented : view (offsets (countLoop key order (fun _ => 0))) state =
      run key processed (initial key order (read scratch))) :
    view (offsets (countLoop key order (fun _ => 0))) (runArray key remaining state) =
      run key order (initial key order (read scratch)) := by
  induction remaining generalizing processed state with
  | nil => simpa [runArray,split] using represented
  | cons index rest ih =>
    have member : index ∈ order := by simp [split]
    have bucket : key index < state.next.size := by rw [nextSize]; exact bounded index member
    have pointer : read state.next (key index) = cursor key order processed (key index) := by
      have pointer := congrArg (fun value : Buffer => value.next (key index)) represented
      simpa only [view,if_pos bucket,next_refinement,initial,cursor] using pointer
    have destination : read state.next (key index) < state.scratch.size := by
      rw [pointer,scratchSize,split]
      exact scatter_index_bound key processed index rest
    have step := step_refinement key state (offsets (countLoop key order (fun _ => 0))) index bucket destination
    have updated : view (offsets (countLoop key order (fun _ => 0))) (stepArray key state index) =
        run key (processed ++ [index]) (initial key order (read scratch)) := by
      rw [step,represented,run_append]
      rfl
    change view _ (runArray key rest (stepArray key state index)) = _
    exact ih (processed ++ [index]) (stepArray key state index) (by simpa [List.append_assoc] using split)
      (by rw [(step_sizes key state index).1,nextSize])
      (by rw [(step_sizes key state index).2,scratchSize]) updated

/-- Full native-array scatter execution refines functional execution from the
computed initializer. No safety, permutation or sorting certificate is supplied. -/
theorem run_refinement (key : Nat → Nat) (order : List Nat) (scratch : Array Nat)
    (bounded : ∀ index ∈ order, key index < 257) (allocated : scratch.size = order.length) :
    view (offsets (countLoop key order (fun _ => 0))) (runArray key order (initialArray key order scratch)) =
      run key order (initial key order (read scratch)) :=
  run_suffix_refinement key order [] order scratch (initialArray key order scratch) bounded rfl
    (by simp [initialArray,prefixes_size]) allocated (initial_refinement key order scratch bounded)

/-- Complete array scatter execution preserves both allocation lengths. -/
theorem run_sizes (key : Nat → Nat) (order : List Nat) (state : Storage) :
    (runArray key order state).next.size = state.next.size ∧
      (runArray key order state).scratch.size = state.scratch.size := by
  induction order generalizing state with
  | nil => exact ⟨rfl,rfl⟩
  | cons index rest ih =>
    have remaining := ih (stepArray key state index)
    exact ⟨remaining.1.trans (step_sizes key state index).1,remaining.2.trans (step_sizes key state index).2⟩

/-- Native array readback agrees with observations at increasing scratch indices. -/
theorem array_readback (table : Array Nat) : table.toList = (List.range table.size).map (read table) := by
  apply List.ext_getElem
  · simp
  · intro position left right
    have inside : position < table.size := by simpa using left
    simp [StateAddressTables.read,Array.getElem?_eq_getElem inside]

/-- One byte-key pass using actual next and scratch arrays throughout. -/
def passArray (key : Nat → Nat) (order : List Nat) (scratch : Array Nat) : List Nat :=
  (runArray key order (initialArray key order scratch)).scratch.toList

/-- Complete native-array pass readback equals operational functional scatter,
with all indexed-access safety derived by the run refinement. -/
theorem pass_refinement (key : Nat → Nat) (order : List Nat) (scratch : Array Nat)
    (bounded : ∀ index ∈ order, key index < 257) (allocated : scratch.size = order.length) :
    passArray key order scratch = pass key order (read scratch) := by
  unfold passArray
  rw [array_readback]
  have size := (run_sizes key order (initialArray key order scratch)).2
  change (runArray key order (initialArray key order scratch)).scratch.size = scratch.size at size
  rw [size,allocated]
  have represented := congrArg Buffer.cells (run_refinement key order scratch bounded allocated)
  change read (runArray key order (initialArray key order scratch)).scratch =
    (run key order (initial key order (read scratch))).cells at represented
  rw [represented]
  rfl

/-- Actual finite-array scatter retains every input index with multiplicities. -/
theorem pass_permutation (key : Nat → Nat) (order : List Nat) (scratch : Array Nat)
    (bounded : ∀ index ∈ order, key index < 257) (allocated : scratch.size = order.length) :
    (passArray key order scratch).Perm order := by
  rw [pass_refinement key order scratch bounded allocated]
  exact scatter_permutation key order _

/-- A byte pass executes native arrays; generic non-byte functions retain the
original semantics so the compiler substitution is valid on its full type. -/
def checkedPass (key : Nat → Nat) (order : List Nat) : List Nat :=
  if byteKeys key order then passArray key order (Array.replicate order.length 0)
  else pass key order (fun _ => 0)

/-- The guarded array implementation refines the pass on every possible input. -/
theorem checkedPass_refinement (key : Nat → Nat) (order : List Nat) :
    checkedPass key order = pass key order (fun _ => 0) := by
  unfold checkedPass
  split
  · rename_i checked
    rw [pass_refinement key order _ (byteKeys_sound key order checked) (by simp),read_zero]
  · rfl

/-- Complete LSD execution with finite count, prefix, next and scratch arrays. -/
def arraySort (digits : List (Nat → Nat)) (order : List Nat) : List Nat :=
  match digits with
  | [] => order
  | key::rest => checkedPass key (arraySort rest order)

/-- Every native-array pass composes to the already proved radix semantics. -/
theorem arraySort_refinement (digits : List (Nat → Nat)) (order : List Nat) :
    arraySort digits order = StateAddressRadix.sort digits order := by
  induction digits with
  | nil => rfl
  | cons key rest ih => simp only [arraySort,checkedPass_refinement,ih,StateAddressRadix.sort]

end CBCL.StateAddressArrayScatter
