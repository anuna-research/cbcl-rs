import LeanCbcl.StateFiniteIndexBounds

/-! Compose word-sized dense table access through the finite native cache and
once-decoded diagnostic loop. This is an executable typed implementation;
literal Rust extraction, allocation and diagnostic formatting remain separate. -/
set_option autoImplicit false
namespace CBCL.StateFiniteDenseCache
open State StateFiniteTable StateFiniteUpperCache StateFinitePairLoop StateFiniteReadCache

/-- Supported native index widths. -/
inductive Word where
  | bits32
  | bits64

/-- Actual unsigned machine offset into the compiled row-major table. -/
def offset (word : Word) (table : Resolved) (a b : Fin table.elements.length) : Nat :=
  match word with
  | .bits32 => (UInt32.ofNat a.val * UInt32.ofNat table.elements.length + UInt32.ofNat b.val).toNat
  | .bits64 => (UInt64.ofNat a.val * UInt64.ofNat table.elements.length + UInt64.ofNat b.val).toNat

/-- Dense native table access; successful validation excludes the fallback. -/
def denseMerge (word : Word) (verified : Verified) (a b : Fin verified.table.elements.length) : Fin verified.table.elements.length :=
  ((StateFiniteIndexBounds.denseRows verified.table)[offset word verified.table a b]?).getD verified.table.bottom

/-- Both machine-width backends return the exact checked join. -/
theorem merge_refinement (word : Word) (verified : Verified) (a b : Fin verified.table.elements.length) :
    denseMerge word verified a b = merge verified.table a b := by
  cases word <;> simp only [denseMerge,offset,StateFiniteIndexBounds.dense_lookup32,
    StateFiniteIndexBounds.dense_lookup64,Option.getD_some]

/-- Compute all non-top upper-set maxima using dense machine table access. -/
def denseMaxima (word : Word) (field : StateInstalledFinite.Field) : Vector (Option Int) field.table.table.elements.length :=
  Vector.ofFn (fun root => maximum (((indices field.table.table).filter (fun current =>
    current != field.table.table.top && denseMerge word field.table root current == current)).filterMap
      (fun current => (projected field)[current])))

/-- Dense lookup constructs exactly the previously verified cache vector. -/
theorem maxima_refinement (word : Word) (field : StateInstalledFinite.Field) :
    denseMaxima word field = maxima field := by
  simp only [denseMaxima,merge_refinement,maxima,upperMaximum,upperValues]

/-- Every compatibility branch now uses the machine-backed table/cache. -/
def denseCompatible (word : Word) (field : StateInstalledFinite.Field)
    (cache : Vector (Option Int) field.table.table.elements.length) : Query field.table → Query field.table → Bool
  | .named a, .named b => denseMerge word field.table a b != field.table.table.top
  | .named a, .numeric n | .numeric n, .named a =>
      cache[a].isSome && decide (n ≤ cache[a].getD 0)
  | .numeric a, .numeric b =>
      cache[field.table.table.bottom].isSome &&
        decide (max a b ≤ cache[field.table.table.bottom].getD 0)

/-- Named, mixed and numeric branches preserve exact compatibility. -/
theorem compatible_refinement (word : Word) (field : StateInstalledFinite.Field) (cache : Vector (Option Int) field.table.table.elements.length) (a b : Query field.table) :
    denseCompatible word field cache a b = storedCompatible field cache a b := by
  cases a <;> cases b <;> simp only [denseCompatible,storedCompatible,merge_refinement]

/-- Preserve raw scalar duplicate precedence over decoded compatibility. -/
def denseReason (word : Word) (field : StateInstalledFinite.Field)
    (cache : Vector (Option Int) field.table.table.elements.length) (a b : ReadRow field) : Option Reason :=
  if a.1 == b.1 then some .duplicate else if denseCompatible word field cache a.2 b.2 then some .compatible else none

/-- Machine cache substitution preserves the exact pair reason. -/
theorem reason_refinement (word : Word) (field : StateInstalledFinite.Field)
    (cache : Vector (Option Int) field.table.table.elements.length) (a b : ReadRow field) :
    denseReason word field cache a b = StateFiniteReadCache.reason field cache a b := by
  simp only [denseReason,StateFiniteReadCache.reason,compatible_refinement]

/-- Inner indexed native loop over once-decoded queries. -/
def denseRow (word : Word) (field : StateInstalledFinite.Field)
    (cache : Vector (Option Int) field.table.table.elements.length) (left : ReadRow field) :
    Nat → List (ReadRow field) → Option (Nat × Reason)
  | _,[] => none
  | index,right::rest => match denseReason word field cache left right with
    | some why => some (index,why)
    | none => denseRow word field cache left (index+1) rest

/-- Machine cache substitution preserves the first right-index diagnostic. -/
theorem row_refinement (word : Word) (field : StateInstalledFinite.Field)
    (cache : Vector (Option Int) field.table.table.elements.length) (left : ReadRow field)
    (reads : List (ReadRow field)) (index : Nat) :
    denseRow word field cache left index reads = StateFiniteReadCache.row field cache left index reads := by
  induction reads generalizing index with
  | nil => rfl
  | cons right rest ih =>
    simp only [denseRow,StateFiniteReadCache.row,reason_refinement]
    cases StateFiniteReadCache.reason field cache left right with
    | some why => rfl
    | none => exact ih (index+1)

/-- Outer indexed native loop retains original query indices. -/
def densePairs (word : Word) (field : StateInstalledFinite.Field)
    (cache : Vector (Option Int) field.table.table.elements.length) :
    Nat → List (ReadRow field) → Option (Nat × Nat × Reason)
  | _,[] => none
  | index,left::rest => match denseRow word field cache left (index+1) rest with
    | some (other,why) => some (index,other,why)
    | none => densePairs word field cache (index+1) rest

/-- Both machine backends preserve complete first-diagnostic ordering. -/
theorem pairs_refinement (word : Word) (field : StateInstalledFinite.Field)
    (cache : Vector (Option Int) field.table.table.elements.length) (reads : List (ReadRow field)) (index : Nat) :
    densePairs word field cache index reads = StateFiniteReadCache.pairs field cache index reads := by
  induction reads generalizing index with
  | nil => rfl
  | cons left rest ih =>
    simp only [densePairs,StateFiniteReadCache.pairs,row_refinement]
    cases StateFiniteReadCache.row field cache left (index+1) rest with
    | some result => cases result; rfl
    | none => exact ih (index+1)

/-- Complete machine-backed finite gate, including actual admission/decoding. -/
def check (word : Word) (field : StateInstalledFinite.Field) (queries : List Val) : Bool :=
  !queries.isEmpty && queries.all (StateFiniteRead.admitted field) &&
    match (compileReads field queries).map (densePairs word field (denseMaxima word field) 0) with
    | some none => true
    | _ => false

/-- Dense machine arithmetic, cache construction and pair scanning compose all
 the way to the exhaustive finite gate for every query list. -/
theorem check_refinement (word : Word) (field : StateInstalledFinite.Field) (queries : List Val) :
    check word field queries = StateFiniteRead.check field queries := by
  rw [← StateFiniteReadCache.check_refinement]
  simp only [check,StateFiniteReadCache.check,diagnostic]
  have same : densePairs word field (denseMaxima word field) 0 = StateFiniteReadCache.pairs field (maxima field) 0 := by
    rw [maxima_refinement]
    funext reads; exact pairs_refinement word field (maxima field) reads 0
  rw [same]
  rfl

/-- Source-owned scalar policy using the complete machine-backed gate. -/
def policyCheck (word : Word) (field : StateInstalledFinite.Field) (queries : List StateInstalledLegacy.Value) : Bool :=
  match queries.mapM StateFiniteRead.decode with
  | none => false
  | some values => check word field values

/-- The machine-backed validator preserves the actual installed scalar policy. -/
theorem policy_refinement (word : Word) (field : StateInstalledFinite.Field) (queries : List StateInstalledLegacy.Value) :
    policyCheck word field queries = (StateFiniteRead.policy field).check queries := by
  unfold policyCheck StateFiniteRead.policy
  cases decoded : queries.mapM StateFiniteRead.decode with
  | none => simp [decoded]
  | some values => simp [decoded,check_refinement]

/-- Both machine backends preserve actual source-owned query compilation,
including rejected scalar forms and retained raw-carrier strategy. -/
theorem compiled_query_refinement (word : Word) (field : StateInstalledFinite.Field) (queries : List StateInstalledLegacy.Value) :
    StateOutputCompiler.compileQuery queries
      (.factored (StateInstalledFinite.term field) (some {StateFiniteRead.policy field with check := policyCheck word field})) =
      StateOutputCompiler.compileQuery queries (StateFiniteRead.definition field) := by
  simp only [StateOutputCompiler.compileQuery,StateFiniteRead.definition,policy_refinement]

end CBCL.StateFiniteDenseCache
