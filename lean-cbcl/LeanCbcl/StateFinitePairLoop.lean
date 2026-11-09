import LeanCbcl.StateFiniteUpperCache

/-! Stored projected/maxima vectors and the unordered native finite-read loop.
The loop retains the first duplicate/compatible pair in row-major order. -/
set_option autoImplicit false
namespace CBCL.StateFinitePairLoop
open State StateLift StateFiniteTable StateFiniteUpperCache

/-- Stored native numeric projection vector in finite carrier order. -/
def projected (field : StateInstalledFinite.Field) : Vector (Option Int) field.table.table.elements.length :=
  Vector.ofFn (project field)

/-- Stored native maxima vector, computed once from the projected vector. -/
def maxima (field : StateInstalledFinite.Field) : Vector (Option Int) field.table.table.elements.length :=
  Vector.ofFn (fun root => upperMaximum field.table (fun current => (projected field)[current]) root)

/-- Projection vector indexing preserves the native scalar projection. -/
theorem projected_lookup (field : StateInstalledFinite.Field) (current : Fin field.table.table.elements.length) :
    (projected field)[current] = project field current := by simp [projected]

/-- Stored maxima indexing equals the proved functional upper-set maximum. -/
theorem maxima_lookup (field : StateInstalledFinite.Field) (root : Fin field.table.table.elements.length) :
    (maxima field)[root] = upperMaximum field.table (project field) root := by
  simp [maxima,projected]

/-- Native pair formulas read a supplied stored cache rather than rebuilding it. -/
def storedCompatible (field : StateInstalledFinite.Field)
    (cache : Vector (Option Int) field.table.table.elements.length) : Query field.table → Query field.table → Bool
  | .named a, .named b => merge field.table.table a b != field.table.table.top
  | .named a, .numeric threshold | .numeric threshold, .named a =>
      cache[a].isSome && decide (threshold ≤ cache[a].getD 0)
  | .numeric a, .numeric b =>
      cache[field.table.table.bottom].isSome && decide (max a b ≤ cache[field.table.table.bottom].getD 0)

/-- Each pair check over the precomputed vector equals its functional formula. -/
theorem stored_compatible_refinement (field : StateInstalledFinite.Field) (left right : Query field.table) :
    storedCompatible field (maxima field) left right = compatible field.table (project field) left right := by
  cases left <;> cases right <;> simp only [storedCompatible,compatible,maxima_lookup]

/-- Decode scalar queries once per pair at this typed boundary. -/
def storedScalarCompatible (field : StateInstalledFinite.Field)
    (cache : Vector (Option Int) field.table.table.elements.length) (left right : Val) : Bool :=
  match decode field left, decode field right with
  | some a, some b => storedCompatible field cache a b
  | _, _ => false

/-- Stored scalar compatibility equals the previously proved native formula. -/
theorem stored_scalar_refinement (field : StateInstalledFinite.Field) (left right : Val) :
    storedScalarCompatible field (maxima field) left right = cachedCompatible field left right := by
  unfold storedScalarCompatible cachedCompatible
  cases decode field left <;> cases decode field right <;> simp [stored_compatible_refinement]

/-- Native finite-pair diagnostic, with duplicate checks taking precedence. -/
inductive Reason where
  | duplicate
  | compatible
  deriving DecidableEq, Repr

/-- Exact per-pair diagnostic order in the native validator. -/
def reason (compatible : Val → Val → Bool) (left right : Val) : Option Reason :=
  if left == right then some .duplicate else if compatible left right then some .compatible else none

/-- Scan one row, keeping the index of its first rejected later element. -/
def row (compatible : Val → Val → Bool) (left : Val) : Nat → List Val → Option (Nat × Reason)
  | _, [] => none
  | index, right :: rest => match reason compatible left right with
      | some why => some (index,why)
      | none => row compatible left (index + 1) rest

/-- Scan rows in native i-then-j order, with each j strictly later than i. -/
def pairs (compatible : Val → Val → Bool) : Nat → List Val → Option (Nat × Nat × Reason)
  | _, [] => none
  | index, left :: rest => match row compatible left (index + 1) rest with
      | some (other,why) => some (index,other,why)
      | none => pairs compatible (index + 1) rest

/-- A single pair accepts precisely distinct incompatible scalar queries. -/
theorem reason_clear (compatible : Val → Val → Bool) (left right : Val) :
    reason compatible left right = none ↔ left ≠ right ∧ compatible left right = false := by
  by_cases same : left = right
  · simp [reason,same]
  · cases result : compatible left right <;> simp [reason,same,result]

/-- A row accepts exactly when each later query is distinct and incompatible. -/
theorem row_clear (compatible : Val → Val → Bool) (left : Val) (index : Nat) (queries : List Val) :
    row compatible left index queries = none ↔ ∀ right ∈ queries, left ≠ right ∧ compatible left right = false := by
  induction queries generalizing index with
  | nil => simp [row]
  | cons right rest ih =>
    cases checked : reason compatible left right with
    | none =>
      have accepted := (reason_clear compatible left right).mp checked
      simp [row,checked,ih,accepted]
    | some why =>
      have rejected : ¬(left ≠ right ∧ compatible left right = false) := by
        intro accepted; have := (reason_clear compatible left right).mpr accepted; simp [checked] at this
      simp [row,checked,rejected]

/-- Acceptance of the indexed native loop is exactly the ordered pairwise condition. -/
theorem pairs_clear (compatible : Val → Val → Bool) (index : Nat) (queries : List Val) :
    pairs compatible index queries = none ↔
      queries.Pairwise (fun left right => left ≠ right ∧ compatible left right = false) := by
  induction queries generalizing index with
  | nil => simp [pairs]
  | cons left rest ih =>
    cases checked : row compatible left (index + 1) rest with
    | none =>
      have accepted := (row_clear compatible left (index + 1) rest).mp checked
      simp only [pairs,checked,ih,List.pairwise_cons]
      exact ⟨fun tail => ⟨accepted,tail⟩,fun combined => combined.2⟩
    | some result =>
      have rejected : ¬∀ right ∈ rest, left ≠ right ∧ compatible left right = false := by
        intro accepted; have := (row_clear compatible left (index + 1) rest).mpr accepted; simp [checked] at this
      obtain ⟨other,why⟩ := result
      simp [pairs,checked,List.pairwise_cons,rejected]

/-- Symmetric compatibility lets unordered traversal characterize every distinct pair. -/
theorem pairwise_symmetric (compatible : Val → Val → Bool)
    (symmetric : ∀ left right, compatible left right = compatible right left) (queries : List Val) :
    queries.Pairwise (fun left right => left ≠ right ∧ compatible left right = false) ↔
      queries.Nodup ∧ ∀ left ∈ queries, ∀ right ∈ queries, left ≠ right → compatible left right = false := by
  constructor
  · intro pairwise
    refine ⟨List.nodup_iff_pairwise_ne.mpr (pairwise.imp (fun proof => proof.1)),?_⟩
    intro left leftMember right rightMember different
    obtain ⟨i,hi,leftAt⟩ := List.mem_iff_getElem.mp leftMember
    obtain ⟨j,hj,rightAt⟩ := List.mem_iff_getElem.mp rightMember
    have indexed := List.pairwise_iff_getElem.mp pairwise
    by_cases forward : i < j
    · simpa [leftAt,rightAt] using (indexed i j hi hj forward).2
    · have backward : j < i := by
        have unequal : i ≠ j := by intro same; subst j; exact different (leftAt.symm.trans rightAt)
        omega
      rw [symmetric]
      simpa [leftAt,rightAt] using (indexed j i hj hi backward).2
  · rintro ⟨unique,all⟩
    apply (List.nodup_iff_pairwise_ne.mp unique).imp_of_mem
    intro left right leftMember rightMember different
    exact ⟨different,all left leftMember right rightMember different⟩

/-- Common-upper-state compatibility is symmetric for every decoded query. -/
theorem compatible_symmetric (verified : Verified) (projection : Fin verified.table.elements.length → Option Int)
    (left right : Query verified) : compatible verified projection left right = compatible verified projection right left := by
  have equivalent : compatible verified projection left right = true ↔ compatible verified projection right left = true := by
    rw [compatible_iff,compatible_iff]
    constructor <;> rintro ⟨current,clear,left,right⟩ <;> exact ⟨current,clear,right,left⟩
  cases a : compatible verified projection left right <;> cases b : compatible verified projection right left <;> simp_all

/-- Scalar compatibility is symmetric even before admission checks. -/
theorem scalar_symmetric (field : StateInstalledFinite.Field) (left right : Val) :
    cachedCompatible field left right = cachedCompatible field right left := by
  unfold cachedCompatible
  cases decode field left <;> cases decode field right <;> simp [compatible_symmetric]

/-- The native stored-cache loop accepts exactly duplicate-free reference-compatible pairs. -/
theorem stored_pairs_refinement (field : StateInstalledFinite.Field) (queries : List Val) :
    pairs (storedScalarCompatible field (maxima field)) 0 queries = none ↔
      queries.Nodup ∧ cachedPairCheck field queries = true := by
  rw [show storedScalarCompatible field (maxima field) = cachedCompatible field from
    funext (fun left => funext (stored_scalar_refinement field left))]
  rw [pairs_clear,pairwise_symmetric _ (scalar_symmetric field)]
  simp only [cachedPairCheck,List.all_eq_true,Bool.or_eq_true,beq_iff_eq]
  constructor
  · rintro ⟨unique,checked⟩
    refine ⟨unique,?_⟩
    intro left leftMember right rightMember
    by_cases same : left = right
    · exact Or.inl same
    · exact Or.inr (by simp [checked left leftMember right rightMember same])
  · rintro ⟨unique,checked⟩
    refine ⟨unique,?_⟩
    intro left leftMember right rightMember different
    have rejected := (checked left leftMember right rightMember).resolve_left different
    cases value : cachedCompatible field left right <;> simp_all

/-- Complete native gate computes the stored cache once and scans only i < j pairs. -/
def check (field : StateInstalledFinite.Field) (queries : List Val) : Bool :=
  !queries.isEmpty && queries.all (StateFiniteRead.admitted field) &&
    (pairs (storedScalarCompatible field (maxima field)) 0 queries).isNone

/-- Stored-cache unordered native traversal equals the exhaustive reference gate. -/
theorem check_refinement (field : StateInstalledFinite.Field) (queries : List Val) :
    check field queries = StateFiniteRead.check field queries := by
  have equivalent : check field queries = true ↔ cachedCheck field queries = true := by
    simp only [check,cachedCheck,Bool.and_eq_true,Option.isNone_iff_eq_none,stored_pairs_refinement,decide_eq_true_eq]
    constructor
    · rintro ⟨⟨nonempty,admitted⟩,unique,pairs⟩; exact ⟨⟨⟨nonempty,unique⟩,admitted⟩,pairs⟩
    · rintro ⟨⟨⟨nonempty,unique⟩,admitted⟩,pairs⟩; exact ⟨⟨nonempty,admitted⟩,unique,pairs⟩
  rw [← cached_check_refinement]
  cases first : check field queries <;> cases second : cachedCheck field queries <;> simp_all

/-- One ordered candidate pair with original scalar values and absolute indices. -/
structure Candidate where
  /-- Original index of the left query. -/
  leftIndex : Nat
  /-- Original index of the strictly later right query. -/
  rightIndex : Nat
  /-- Authored left scalar. -/
  left : Val
  /-- Authored right scalar. -/
  right : Val

/-- Enumerate every i < j candidate in native row-major order, without early exit. -/
def candidates : Nat → List Val → List Candidate
  | _, [] => []
  | index, left :: rest =>
      ((rest.zipIdx (index + 1)).map (fun (right,other) => ⟨index,other,left,right⟩)) ++
        candidates (index + 1) rest

/-- Attach the exact native indices and reason to a rejected candidate. -/
def diagnose (compatible : Val → Val → Bool) (candidate : Candidate) : Option (Nat × Nat × Reason) :=
  (reason compatible candidate.left candidate.right).map (fun why => (candidate.leftIndex,candidate.rightIndex,why))

/-- A row scanner agrees with first-error search over its independently indexed row. -/
theorem row_reference (compatible : Val → Val → Bool) (left : Val) (index start : Nat) (queries : List Val) :
    (((queries.zipIdx start).map (fun (right,other) => (⟨index,other,left,right⟩ : Candidate))).findSome? (diagnose compatible)) =
      (row compatible left start queries).map (fun (other,why) => (index,other,why)) := by
  induction queries generalizing start with
  | nil => simp [row]
  | cons right rest ih =>
    cases checked : reason compatible left right <;>
      simp [List.zipIdx_cons,diagnose,checked,row,ih]

/-- Native early-exit loop returns the first rejected pair in the complete
row-major enumeration, preserving both original indices and diagnostic reason. -/
theorem pairs_reference (compatible : Val → Val → Bool) (index : Nat) (queries : List Val) :
    pairs compatible index queries = (candidates index queries).findSome? (diagnose compatible) := by
  induction queries generalizing index with
  | nil => simp [pairs,candidates]
  | cons left rest ih =>
    simp only [candidates,List.findSome?_append,row_reference]
    cases checked : row compatible left (index + 1) rest with
    | none => simp [pairs,checked,ih]
    | some result => obtain ⟨other,why⟩ := result; simp [pairs,checked]

/-- Every returned diagnostic is an actual rejected pair and every earlier
candidate in native iteration order was accepted. -/
theorem first_diagnostic (compatible : Val → Val → Bool) (index : Nat) (queries : List Val)
    (result : Nat × Nat × Reason) : pairs compatible index queries = some result ↔
      ∃ before candidate after, candidates index queries = before ++ candidate :: after ∧
        diagnose compatible candidate = some result ∧ ∀ earlier ∈ before, diagnose compatible earlier = none := by
  rw [pairs_reference,List.findSome?_eq_some_iff]

/-- Equality always reports duplicate before considering compatibility. -/
theorem duplicate_precedence (compatible : Val → Val → Bool) (query : Val) :
    reason compatible query query = some .duplicate := by simp [reason]

/-- Every enumerated candidate carries in-range original indices and values. -/
theorem candidate_indices (index : Nat) (queries : List Val) (candidate : Candidate)
    (member : candidate ∈ candidates index queries) :
    index ≤ candidate.leftIndex ∧ candidate.leftIndex < candidate.rightIndex ∧
      candidate.rightIndex < index + queries.length ∧
      queries[candidate.leftIndex - index]? = some candidate.left ∧
      queries[candidate.rightIndex - index]? = some candidate.right := by
  induction queries generalizing index with
  | nil => simp [candidates] at member
  | cons left rest ih =>
    simp only [candidates,List.mem_append,List.mem_map] at member
    rcases member with ⟨⟨right,other⟩,inRow,same⟩ | inTail
    · cases same
      have bounds := List.mem_zipIdx inRow
      refine ⟨by simp,by dsimp; omega,by dsimp; omega,by simp,?_⟩
      have offset : other - index = (other - (index + 1)) + 1 := by omega
      simp only [offset,List.getElem?_cons_succ]
      have inside : other - (index + 1) < rest.length := by omega
      simpa [inside] using congrArg some bounds.2.2.symm
    · have bounds := ih index.succ inTail
      refine ⟨by omega,bounds.2.1,by simp only [List.length_cons]; omega,?_⟩
      have leftOffset : candidate.leftIndex - index = (candidate.leftIndex - (index + 1)) + 1 := by omega
      have rightOffset : candidate.rightIndex - index = (candidate.rightIndex - (index + 1)) + 1 := by omega
      simpa only [leftOffset,rightOffset,List.getElem?_cons_succ] using bounds.2.2.2

/-- The reported indices select the actual authored queries and actual failure reason. -/
theorem diagnostic_sound (compatible : Val → Val → Bool) (queries : List Val)
    (i j : Nat) (why : Reason) (found : pairs compatible 0 queries = some (i,j,why)) :
    i < j ∧ j < queries.length ∧ ∃ left right,
      queries[i]? = some left ∧ queries[j]? = some right ∧ reason compatible left right = some why := by
  obtain ⟨before,candidate,after,enumeration,diagnosed,_⟩ := (first_diagnostic compatible 0 queries (i,j,why)).mp found
  have member : candidate ∈ candidates 0 queries := by rw [enumeration]; simp
  have bounds := candidate_indices 0 queries candidate member
  cases checked : reason compatible candidate.left candidate.right with
  | none => simp [diagnose,checked] at diagnosed
  | some cause =>
    simp only [diagnose,checked,Option.map_some,Option.some.injEq,Prod.mk.injEq] at diagnosed
    rcases diagnosed with ⟨rfl,rfl,rfl⟩
    exact ⟨bounds.2.1,by simpa using bounds.2.2.1,candidate.left,candidate.right,
      by simpa using bounds.2.2.2.1,by simpa using bounds.2.2.2.2,checked⟩

end CBCL.StateFinitePairLoop
