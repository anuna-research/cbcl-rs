import LeanCbcl.StateInstalledFinite

/-! Closed finite read policies. Read elements are authored scalars; named
carrier elements and checked stable numeric/boolean projections share the
source's actual retained-state operation. Pair checks inspect non-top common
upper states, as the native cached-upper-set implementation does. -/
set_option autoImplicit false
namespace CBCL.StateFiniteRead
open State StateLift StateLVar StateObservation StateInstalledFinite

/-- Monotone reach predicate, extended to top only for order reasoning.
The native read below suppresses success at top before exposing this predicate. -/
def reaches (field : Field) (query : Val) (current : Fin field.table.table.elements.length) : Bool :=
  match query with
  | .str name => match StateFiniteTable.index field.table.table.elements name with
      | none => false
      | some element => StateFiniteTable.merge field.table.table element current == current
  | .int threshold => match field.projection with
      | none => false
      | some projection => projection.projection.stable && match StateFiniteProjection.value projection current with
          | .int value => decide (threshold ≤ value)
          | _ => false
  | .bool true => match field.projection with
      | none => false
      | some projection => projection.projection.stable && match StateFiniteProjection.value projection current with
          | .bool value => value
          | _ => false
  | _ => false

/-- Literal native finite read: conflict top never returns a successful match. -/
def test (field : Field) (query : Val) (current : Fin field.table.table.elements.length) : Bool :=
  current != field.table.table.top && reaches field query current

/-- The native fault guard rejects top before any candidate match. -/
theorem test_top (field : Field) (query : Val) : test field query field.table.table.top = false := by
  simp [test]

/-- Away from top, the native predicate equals its monotone reach interpretation. -/
theorem test_non_top (field : Field) (query : Val) (current : Fin field.table.table.elements.length)
    (clear : current ≠ field.table.table.top) : test field query current = reaches field query current := by
  simp [test,clear]

/-- Native finite-element admission, including projection type homogeneity. -/
def admitted (field : Field) (query : Val) : Bool :=
  StateFiniteProjection.scalarCheck query && match query with
  | .str name => match StateFiniteTable.index field.table.table.elements name with
      | none => false
      | some element => element != field.table.table.top
  | .int _ => match field.projection with
      | none => false
      | some projection => projection.projection.stable &&
          projection.projection.rows.all (fun row => match row.2 with | .int _ => true | _ => false)
  | .bool true => match field.projection with
      | none => false
      | some projection => projection.projection.stable &&
          projection.projection.rows.all (fun row => match row.2 with | .bool _ => true | _ => false)
  | _ => false

/-- Exhaustive pair check excludes a non-top common successful upper state. -/
def pairCheck (field : Field) (queries : List Val) : Bool :=
  queries.all (fun left => queries.all (fun right => left == right ||
    (StateFiniteTable.indices field.table.table).all (fun current =>
      current == field.table.table.top || !(reaches field left current && reaches field right current))))

/-- Complete finite-read installation gate; empty and duplicate lists reject. -/
def check (field : Field) (queries : List Val) : Bool :=
  !queries.isEmpty && decide queries.Nodup && queries.all (admitted field) && pairCheck field queries

/-- Actual native pair validation entails incompatibility at every non-top state. -/
theorem pairCheck_iff (field : Field) (queries : List Val) : pairCheck field queries = true ↔
    ∀ left ∈ queries, ∀ right ∈ queries, left ≠ right →
      ∀ current, current ≠ field.table.table.top → reaches field left current = true → reaches field right current = false := by
  simp only [pairCheck,List.all_eq_true,Bool.or_eq_true,Bool.not_eq_true,Bool.and_eq_false_iff,
    beq_iff_eq,StateFiniteTable.indices,List.mem_finRange,forall_const]
  constructor
  · intro checked left hl right hr different current notTop reached
    have pair := (checked left hl right hr).resolve_left different current
    have conflict := pair.resolve_left notTop
    cases result : reaches field right current <;> simp_all
  · intro incompatible left hl right hr
    by_cases same : left = right
    · exact Or.inl same
    · right
      intro current
      by_cases top : current = field.table.table.top
      · exact Or.inl top
      · right
        by_cases reached : reaches field left current = true
        · simp [incompatible left hl right hr same current top reached]
        · cases currentRead : reaches field left current <;> simp_all

private theorem and_left {a b : Bool} (checked : a && b = true) : a = true := by
  cases a <;> simp_all

/-- Closed finite successful predicates are upward closed on the checked join order. -/
theorem reaches_upward (field : Field) (query : Val) (a b : Fin field.table.table.elements.length)
    (below : StateFiniteTable.merge field.table.table a b = b) (reached : reaches field query a = true) :
    reaches field query b = true := by
  cases query with
  | str name =>
    cases resolved : StateFiniteTable.index field.table.table.elements name with
    | none => simp [reaches,resolved] at reached
    | some element =>
      have first : StateFiniteTable.merge field.table.table element a = a := by simpa [reaches,resolved] using reached
      letI := StateFiniteTable.algebra field.table
      have next : Below element b := below_trans (show Below element a from first) (show Below a b from below)
      simpa [reaches,resolved] using next
  | int threshold =>
    cases projection : field.projection with
    | none => simp [reaches,projection] at reached
    | some p =>
      have stable : p.projection.stable = true := and_left (by simpa [reaches,projection] using reached)
      have order := StateFiniteProjection.stable_value_order p stable a b below
      cases left : StateFiniteProjection.value p a <;> cases right : StateFiniteProjection.value p b <;>
        simp [reaches,projection,left,right,stable,StateFiniteProjection.ordered] at reached order ⊢ <;> omega
  | bool flag =>
    cases flag with
    | false => simp [reaches] at reached
    | true =>
      cases projection : field.projection with
      | none => simp [reaches,projection] at reached
      | some p =>
        have stable : p.projection.stable = true := and_left (by simpa [reaches,projection] using reached)
        have order := StateFiniteProjection.stable_value_order p stable a b below
        cases left : StateFiniteProjection.value p a <;> cases right : StateFiniteProjection.value p b <;>
          simp_all [reaches,StateFiniteProjection.ordered]
  | list _ => simp [reaches] at reached

/-- Distinct successful installed finite reads force their combined source to
conflict, including domain-selected contributions enabled by the union. -/
theorem distinct_reads_force_top (field : Field) (queries : List Val)
    (checked : check field queries = true) (A B : List Act) (left right : Val)
    (leftMember : left ∈ queries) (rightMember : right ∈ queries) (different : left ≠ right)
    (leftRead : reaches field left (state field A) = true) (rightRead : reaches field right (state field B) = true) :
    state field (A ++ B) = field.table.table.top := by
  have pairChecked : pairCheck field queries = true := by
    simp only [check,Bool.and_eq_true] at checked
    exact checked.2
  have leftGrowth := state_grows field (A := A) (B := A ++ B) (fun act member => List.mem_append_left _ member)
  have rightGrowth := state_grows field (A := B) (B := A ++ B) (fun act member => List.mem_append_right _ member)
  have leftReached := reaches_upward field left (state field A) (state field (A ++ B)) leftGrowth leftRead
  have rightReached := reaches_upward field right (state field B) (state field (A ++ B)) rightGrowth rightRead
  by_cases conflict : state field (A ++ B) = field.table.table.top
  · exact conflict
  · have rejected := (pairCheck_iff field queries).mp pairChecked left leftMember right rightMember different
      (state field (A ++ B)) conflict leftReached
    simp [rightReached] at rejected

/-- Decode only the finite scalar element form, never another head's query. -/
def decode : StateInstalledLegacy.Value → Option Val
  | .element (.scalar value) => some value
  | _ => none

/-- The policy reads the current raw carrier retained by the same source term. -/
noncomputable def policy (field : Field) : StateInstalledTerm.Policy StateInstalledLegacy.Value (FinSet Act) := {
  test := fun query carrier => match decode query with
    | none => false
    | some element => test field element (state field (StateInstalledLegacy.history carrier))
  check := fun queries => match queries.mapM decode with
    | none => false
    | some elements => check field elements }

/-- Bind the closed finite source and scalar policy into the installed lowerer. -/
noncomputable def definition (field : Field) : StateInstalledLowering.Definition StateInstalledLegacy.Value :=
  .factored (term field) (some (policy field))

/-- Raw finite thresholds read actual accepted history, not a frozen display. -/
theorem policy_actual_history (field : Field) (query : Val) (A : List Act) :
    (policy field).test (.element (.scalar query)) (rawHistory A) = test field query (state field A) := by
  simp only [policy,decode]
  rw [state_setEq field (StateInstalledLegacy.history_setEq A)]

/-- Finite fault evidence is the installed source guard used by all readers. -/
theorem definition_guard_coherence (field : Field) :
    (term field).guards = [.certified (errorSpec field)] := rfl

end CBCL.StateFiniteRead
