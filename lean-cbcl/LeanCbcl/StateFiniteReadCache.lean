import LeanCbcl.StateFinitePairLoop
import LeanCbcl.StateOutputCompiler

/-! Native R7 decodes admitted finite alternatives once before scanning pairs.
This executable cache stage retains original scalar identity for duplicate
precedence while storing typed query indices/numeric thresholds for compatibility. -/
set_option autoImplicit false
namespace CBCL.StateFiniteReadCache
open State StateFiniteTable StateFiniteUpperCache StateFinitePairLoop

/-- One original scalar and its cached native decoded query. -/
abbrev ReadRow (field : StateInstalledFinite.Field) := Val × Query field.table

/-- Construct aligned cached reads; an undecodable scalar rejects the stage. -/
def compileReads (field : StateInstalledFinite.Field) : List Val → Option (List (ReadRow field))
  | [] => some []
  | query :: rest => do
    let decoded ← decode field query
    let tail ← compileReads field rest
    return (query,decoded) :: tail

/-- Cache construction preserves original order/values and proves every stored
query is the actual scalar decoder result. No alignment oracle is supplied. -/
theorem reads_sound (field : StateInstalledFinite.Field) (queries : List Val) (reads : List (ReadRow field))
    (compiled : compileReads field queries = some reads) :
    reads.map Prod.fst = queries ∧ ∀ row ∈ reads, decode field row.1 = some row.2 := by
  induction queries generalizing reads with
  | nil =>
    have same : reads = [] := Option.some.inj compiled.symm
    subst reads
    exact ⟨rfl,by simp⟩
  | cons query rest ih =>
    cases decoded : decode field query with
    | none => simp [compileReads,decoded] at compiled
    | some value =>
      cases tail : compileReads field rest with
      | none => simp [compileReads,decoded,tail] at compiled
      | some rows =>
        have same : (query,value) :: rows = reads := by simpa [compileReads,decoded,tail] using compiled
        subst reads
        have valid := ih rows tail
        refine ⟨by simp [valid.1],?_⟩
        intro row member
        rcases List.mem_cons.mp member with rfl | inside
        · exact decoded
        · exact valid.2 row inside

/-- Parallel original-element and decoded-read arrays have equal lengths and
aligned in-range entries, as required by the native indexed pair loop. -/
theorem reads_index (field : StateInstalledFinite.Field) (queries : List Val) (reads : List (ReadRow field))
    (compiled : compileReads field queries = some reads) (index : Nat) (bound : index < queries.length) :
    ∃ item, queries[index]? = some item.1 ∧ reads[index]? = some item ∧ decode field item.1 = some item.2 := by
  have valid := reads_sound field queries reads compiled
  have lengths : reads.length = queries.length := by simpa using congrArg List.length valid.1
  have inRange : index < reads.length := by omega
  let item := reads[index]
  refine ⟨item,?_,by simp [item,inRange],?_⟩
  · rw [← valid.1]
    simp [item,inRange]
  · exact valid.2 item (List.getElem_mem inRange)

/-- Cached numeric projection indexing agrees with the actual rendered scalar
kind, including booleans and the default named display without a projection. -/
theorem projected_display (field : StateInstalledFinite.Field) (current : Fin field.table.table.elements.length) :
    (projected field)[current] = numericValue (StateInstalledFinite.display field current) := by
  rw [projected_lookup]
  cases projection : field.projection <;> simp [project,StateInstalledFinite.display,projection,numericValue]

/-- Every admitted scalar decodes, so the typed native pre-pass cannot reach its
unreachable/expect branches after the source-owned admission check. -/
theorem reads_complete (field : StateInstalledFinite.Field) (queries : List Val)
    (admitted : queries.all (StateFiniteRead.admitted field) = true) :
    ∃ reads, compileReads field queries = some reads := by
  induction queries with
  | nil => exact ⟨[],rfl⟩
  | cons query rest ih =>
    have parts : StateFiniteRead.admitted field query = true ∧ rest.all (StateFiniteRead.admitted field) = true := by simpa using admitted
    obtain ⟨decoded,found,_⟩ := decode_reaches field query parts.1
    obtain ⟨rows,tail⟩ := ih parts.2
    exact ⟨(query,decoded)::rows,by simp [compileReads,found,tail]⟩

/-- Native cached pair check retains duplicate precedence over compatibility. -/
def reason (field : StateInstalledFinite.Field) (cache : Vector (Option Int) field.table.table.elements.length)
    (left right : ReadRow field) : Option Reason :=
  if left.1 == right.1 then some .duplicate else
    if storedCompatible field cache left.2 right.2 then some .compatible else none

/-- Scan one cached row, preserving its original right index. -/
def row (field : StateInstalledFinite.Field) (cache : Vector (Option Int) field.table.table.elements.length)
    (left : ReadRow field) : Nat → List (ReadRow field) → Option (Nat × Reason)
  | _,[] => none
  | index,right::rest => match reason field cache left right with
    | some why => some (index,why)
    | none => row field cache left (index+1) rest

/-- Native indexed i<j scan over the once-decoded cached alternatives. -/
def pairs (field : StateInstalledFinite.Field) (cache : Vector (Option Int) field.table.table.elements.length) :
    Nat → List (ReadRow field) → Option (Nat × Nat × Reason)
  | _,[] => none
  | index,left::rest => match row field cache left (index+1) rest with
    | some (other,why) => some (index,other,why)
    | none => pairs field cache (index+1) rest

/-- A cached pair has exactly the reference scalar pair's diagnostic. -/
theorem reason_refinement (field : StateInstalledFinite.Field) (cache : Vector (Option Int) field.table.table.elements.length)
    (left right : ReadRow field) (leftDecoded : decode field left.1 = some left.2) (rightDecoded : decode field right.1 = some right.2) :
    reason field cache left right = StateFinitePairLoop.reason (storedScalarCompatible field cache) left.1 right.1 := by
  simp only [reason,StateFinitePairLoop.reason,storedScalarCompatible,leftDecoded,rightDecoded]

/-- Every cached row retains the reference scanner's first right-index/reason. -/
theorem row_refinement (field : StateInstalledFinite.Field) (cache : Vector (Option Int) field.table.table.elements.length)
    (left : ReadRow field) (leftDecoded : decode field left.1 = some left.2)
    (reads : List (ReadRow field)) (valid : ∀ item ∈ reads, decode field item.1 = some item.2) (index : Nat) :
    row field cache left index reads = StateFinitePairLoop.row (storedScalarCompatible field cache) left.1 index (reads.map Prod.fst) := by
  induction reads generalizing index with
  | nil => rfl
  | cons right rest ih =>
    have matching := reason_refinement field cache left right leftDecoded (valid right (by simp))
    simp only [row,List.map_cons,StateFinitePairLoop.row,matching]
    cases diagnosed : StateFinitePairLoop.reason (storedScalarCompatible field cache) left.1 right.1 with
    | some why => rfl
    | none => exact ih (fun item member => valid item (List.mem_cons_of_mem _ member)) (index+1)

/-- Cached decoded traversal preserves both indices and the first rejection. -/
theorem pairs_refinement (field : StateInstalledFinite.Field) (cache : Vector (Option Int) field.table.table.elements.length)
    (reads : List (ReadRow field)) (valid : ∀ item ∈ reads, decode field item.1 = some item.2) (index : Nat) :
    pairs field cache index reads = StateFinitePairLoop.pairs (storedScalarCompatible field cache) index (reads.map Prod.fst) := by
  induction reads generalizing index with
  | nil => rfl
  | cons left rest ih =>
    have matching := row_refinement field cache left (valid left (by simp)) rest
      (fun item member => valid item (List.mem_cons_of_mem _ member)) (index+1)
    simp only [pairs,List.map_cons,StateFinitePairLoop.pairs,matching]
    cases diagnosed : StateFinitePairLoop.row (storedScalarCompatible field cache) left.1 (index+1) (rest.map Prod.fst) with
    | some result => cases result; rfl
    | none => exact ih (fun item member => valid item (List.mem_cons_of_mem _ member)) (index+1)

/-- Run the cached native scanner after once-only query decoding. -/
def diagnostic (field : StateInstalledFinite.Field) (queries : List Val) : Option (Option (Nat × Nat × Reason)) :=
  (compileReads field queries).map (pairs field (maxima field) 0)

/-- Admitted reads produce the exact native pair diagnostic, not just the same
accept/reject bit. Original scalar identity survives mixed named/numeric caches. -/
theorem diagnostic_refinement (field : StateInstalledFinite.Field) (queries : List Val)
    (admitted : queries.all (StateFiniteRead.admitted field) = true) :
    diagnostic field queries = some (StateFinitePairLoop.pairs (storedScalarCompatible field (maxima field)) 0 queries) := by
  obtain ⟨reads,compiled⟩ := reads_complete field queries admitted
  have valid := reads_sound field queries reads compiled
  simp only [diagnostic,compiled,Option.map_some,pairs_refinement field (maxima field) reads valid.2,valid.1]

/-- Complete finite threshold gate with actual cached-read construction. -/
def check (field : StateInstalledFinite.Field) (queries : List Val) : Bool :=
  !queries.isEmpty && queries.all (StateFiniteRead.admitted field) &&
    match diagnostic field queries with | some none => true | _ => false

/-- The once-decoded cached gate is exactly the exhaustive verified checker. -/
theorem check_refinement (field : StateInstalledFinite.Field) (queries : List Val) :
    check field queries = StateFiniteRead.check field queries := by
  rw [← StateFinitePairLoop.check_refinement]
  cases admitted : queries.all (StateFiniteRead.admitted field) with
  | false => simp [check,StateFinitePairLoop.check,admitted]
  | true =>
    rw [check,diagnostic_refinement field queries admitted]
    cases found : StateFinitePairLoop.pairs (storedScalarCompatible field (maxima field)) 0 queries <;>
      simp [StateFinitePairLoop.check,admitted,found]

/-- A cached diagnostic identifies the actual original scalar values and a
real duplicate/compatible pair at the reported original indices. -/
theorem diagnostic_sound (field : StateInstalledFinite.Field) (queries : List Val)
    (admitted : queries.all (StateFiniteRead.admitted field) = true) (i j : Nat) (why : Reason)
    (found : diagnostic field queries = some (some (i,j,why))) :
    i < j ∧ j < queries.length ∧ ∃ left right, queries[i]? = some left ∧ queries[j]? = some right ∧
      StateFinitePairLoop.reason (storedScalarCompatible field (maxima field)) left right = some why := by
  rw [diagnostic_refinement field queries admitted] at found
  exact StateFinitePairLoop.diagnostic_sound _ queries i j why (Option.some.inj found)

/-- The source-owned policy's scalar wrapper, with once-decoded native caching. -/
def policyCheck (field : StateInstalledFinite.Field) (queries : List StateInstalledLegacy.Value) : Bool :=
  match queries.mapM StateFiniteRead.decode with | none => false | some values => check field values

/-- Cached gate construction refines the actual source-owned installed policy. -/
theorem policy_refinement (field : StateInstalledFinite.Field) (queries : List StateInstalledLegacy.Value) :
    policyCheck field queries = (StateFiniteRead.policy field).check queries := by
  unfold policyCheck StateFiniteRead.policy
  cases decoded : queries.mapM StateFiniteRead.decode with
  | none => simp [decoded]
  | some values => simp [decoded,check_refinement]

/-- Using the proved cached gate preserves exact actual query compilation,
including rejection and the retained raw-carrier strategy. -/
theorem compiled_query_refinement (field : StateInstalledFinite.Field) (queries : List StateInstalledLegacy.Value) :
    StateOutputCompiler.compileQuery queries
      (.factored (StateInstalledFinite.term field) (some {StateFiniteRead.policy field with check := policyCheck field})) =
      StateOutputCompiler.compileQuery queries (StateFiniteRead.definition field) := by
  simp only [StateOutputCompiler.compileQuery,StateFiniteRead.definition,policy_refinement]

end CBCL.StateFiniteReadCache
