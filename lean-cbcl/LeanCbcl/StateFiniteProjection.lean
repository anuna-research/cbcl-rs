import LeanCbcl.StateFiniteTable

/-! Concrete finite projection and contribution validation. These factories
resolve authored names against the checked table, reject structured literals,
and derive monotone scalar reads from exhaustive installed comparisons. -/
set_option autoImplicit false
namespace CBCL.StateFiniteProjection
open State StateLift StateFiniteTable

/-- Scalar literals accepted by native finite contribution/projection rows. -/
def scalarCheck : Val → Bool
  | .str _ | .bool _ => true
  | .int n => decide (-(2^63) ≤ n ∧ n < 2^63)
  | _ => false

/-- Native stable projection order; mixed or string codomains reject. -/
def ordered : Val → Val → Bool
  | .int a, .int b => decide (a ≤ b)
  | .bool a, .bool b => !a || b
  | _, _ => false

/-- An authored projection before element-name resolution. -/
structure Declaration where
  /-- Whether this projection is declared order-preserving. -/
  stable : Bool
  /-- The authored rows retained in declaration order. -/
  rows : List (String × Val)

/-- Projection rows whose element names resolve in the installed carrier. -/
structure Resolved (table : StateFiniteTable.Resolved) where
  /-- Whether this projection is declared order-preserving. -/
  stable : Bool
  /-- The authored rows retained in declaration order. -/
  rows : List (Fin table.elements.length × Val)

/-- Resolve every authored row; an unknown element fails closed. -/
def resolve (table : StateFiniteTable.Resolved) (declaration : Declaration) : Option (Resolved table) := do
  let rows ← declaration.rows.mapM (fun (name,value) => do
    let element ← StateFiniteTable.index table.elements name
    some (element,value))
  some ⟨declaration.stable,rows⟩

/-- Exhaustive native scalar, uniqueness, totality, and stable-order checks. -/
def check (table : StateFiniteTable.Resolved) (projection : Resolved table) : Bool :=
  projection.rows.all (fun row => scalarCheck row.2) &&
  decide (projection.rows.map Prod.fst).Nodup &&
  (indices table).all (fun i => (projection.rows.lookup i).isSome) &&
  if projection.stable then
    (indices table).all (fun a => (indices table).all (fun b =>
      if StateFiniteTable.merge table a b == b then
        match projection.rows.lookup a, projection.rows.lookup b with
        | some x, some y => ordered x y
        | _, _ => false
      else true))
  else true

/-- The semantic obligations certified by the actual projection checker. -/
def Valid (table : StateFiniteTable.Resolved) (projection : Resolved table) : Prop :=
  (∀ row ∈ projection.rows, scalarCheck row.2 = true) ∧
  (projection.rows.map Prod.fst).Nodup ∧
  (∀ i, (projection.rows.lookup i).isSome = true) ∧
  (projection.stable = true → ∀ a b, StateFiniteTable.merge table a b = b →
    ∃ x y, projection.rows.lookup a = some x ∧ projection.rows.lookup b = some y ∧ ordered x y = true)

/-- No semantic monotonicity premise is supplied by the caller. -/
theorem check_iff (table : StateFiniteTable.Resolved) (projection : Resolved table) :
    check table projection = true ↔ Valid table projection := by
  simp only [check,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq,indices,List.mem_finRange,
    forall_const]
  simp only [Valid]
  constructor
  · rintro ⟨⟨⟨scalars,unique⟩,total⟩,stable⟩
    refine ⟨scalars,unique,total,?_⟩
    intro enabled a b below
    simp only [enabled,ite_true,all_indices] at stable
    have pair := stable a b
    simp only [below,BEq.rfl,ite_true] at pair
    cases left : projection.rows.lookup a with
    | none => simp [left] at pair
    | some x =>
      cases right : projection.rows.lookup b with
      | none => simp [right] at pair
      | some y => exact ⟨x,y,rfl,rfl,by simpa [left,right] using pair⟩
  · rintro ⟨scalars,unique,total,stable⟩
    refine ⟨⟨⟨scalars,unique⟩,total⟩,?_⟩
    split
    · rename_i enabled
      simp only [all_indices]
      intro a b
      by_cases below : StateFiniteTable.merge table a b = b
      · obtain ⟨x,y,left,right,safe⟩ := stable enabled a b below
        simp [below,left,right,safe]
      · simp [beq_eq_false_iff_ne.mpr below]
    · rfl

/-- A checked finite projection and its installed validation evidence. -/
structure Verified (table : StateFiniteTable.Resolved) where
  /-- The resolved finite projection and its checked validation evidence. -/
  projection : Resolved table
  checked : check table projection = true

/-- Compile authored projection rows using the executable validation gates. -/
def compile (table : StateFiniteTable.Resolved) (declaration : Declaration) : Option (Verified table) := do
  let projection ← resolve table declaration
  if checked : check table projection = true then some ⟨projection,checked⟩ else none

/-- The native projection fallback is unreachable after successful validation. -/
def value {table : StateFiniteTable.Resolved} (projection : Verified table) (element : Fin table.elements.length) : Val :=
  (projection.projection.rows.lookup element).getD (.str table.elements[element])

/-- Every rendered element is backed by an installed row, including top. -/
theorem value_row {table : StateFiniteTable.Resolved} (projection : Verified table) (element : Fin table.elements.length) :
    projection.projection.rows.lookup element = some (value projection element) := by
  have total := ((check_iff table projection.projection).mp projection.checked).2.2.1 element
  cases found : projection.projection.rows.lookup element with
  | none => simp [found] at total
  | some output => simp [value,found]

/-- Stable source displays preserve the table's actual join order. -/
theorem stable_value_order {table : StateFiniteTable.Resolved} (projection : Verified table)
    (stable : projection.projection.stable = true) (a b : Fin table.elements.length)
    (below : StateFiniteTable.merge table a b = b) : ordered (value projection a) (value projection b) = true := by
  obtain ⟨x,y,left,right,safe⟩ := ((check_iff table projection.projection).mp projection.checked).2.2.2 stable a b below
  simpa [value,left,right] using safe

/-- An authored finite contribution row. -/
structure Contribution where
  /-- The message keyword read by this declaration. -/
  key : String
  /-- The scalar literal compared with the message field. -/
  literal : Val
  /-- The resolved target element in the installed carrier. -/
  element : String

/-- A resolved scalar contribution row tied to its installed carrier. -/
structure Row (table : StateFiniteTable.Resolved) where
  /-- The message keyword read by this declaration. -/
  key : String
  /-- The scalar literal compared with the message field. -/
  literal : Val
  /-- The resolved target element in the installed carrier. -/
  element : Fin table.elements.length
  validLiteral : scalarCheck literal = true

/-- Verified scalar rows cannot match an opaque structured field value. This
lets bounded wire adapters retain symbol/string distinctions without treating
an unrecognized symbol as the equally spelled string literal. -/
theorem row_literal_not_list (table : StateFiniteTable.Resolved) (row : Row table) (values : List Scalar) :
    row.literal ≠ .list values := by
  intro equal
  have recognized := row.validLiteral
  simp [equal,scalarCheck] at recognized

/-- An opaque finite-profile input cannot trigger any valid scalar row. -/
theorem row_ignores_opaque (table : StateFiniteTable.Resolved) (row : Row table) (act : Act) (values : List Scalar)
    (fieldValue : act.get row.key = some (.list values)) : (act.get row.key == some row.literal) = false := by
  rw [fieldValue]
  apply beq_eq_false_iff_ne.mpr
  intro equal
  exact row_literal_not_list table row values (Option.some.inj equal).symm

/-- Reject structured/non-native literals and unknown contribution targets. -/
def resolveRow (table : StateFiniteTable.Resolved) (row : Contribution) : Option (Row table) := do
  if recognized : scalarCheck row.literal = true then
    let element ← StateFiniteTable.index table.elements row.element
    some ⟨row.key,row.literal,element,recognized⟩
  else none

/-- Every matching row contributes, in authored order; there is no first-match branch. -/
def contribution (table : StateFiniteTable.Resolved) (rows : List (Row table)) (act : Act) : Fin table.elements.length :=
  (rows.filter (fun row => act.get row.key == some row.literal)).foldl
    (fun accumulated row => StateFiniteTable.merge table accumulated row.element) table.bottom

/-- The all-matches native fold is exactly a lift into the checked finite algebra. -/
theorem contribution_lift (verified : StateFiniteTable.Verified) (rows : List (Row verified.table)) (A B : List Act) :
    letI := StateFiniteTable.algebra verified
    lift (contribution verified.table rows) (A ++ B) =
      lift (contribution verified.table rows) A ⊔ lift (contribution verified.table rows) B := by
  letI := StateFiniteTable.algebra verified
  exact lift_append (contribution verified.table rows) A B

/-- Numeric stable projection reads are upward closed on the actual table order. -/
theorem numeric_read_upward {table : StateFiniteTable.Resolved} (projection : Verified table)
    (stable : projection.projection.stable = true) (a b : Fin table.elements.length)
    (below : StateFiniteTable.merge table a b = b) (x y threshold : Int)
    (left : value projection a = .int x) (right : value projection b = .int y)
    (reached : threshold ≤ x) : threshold ≤ y := by
  have ordered := stable_value_order projection stable a b below
  simp [left,right,StateFiniteProjection.ordered] at ordered
  omega

/-- Successful compilation entails name resolution and every semantic check. -/
theorem compile_sound (table : StateFiniteTable.Resolved) (declaration : Declaration) (verified : Verified table)
    (compiled : compile table declaration = some verified) :
    resolve table declaration = some verified.projection ∧ Valid table verified.projection := by
  cases resolved : resolve table declaration with
  | none => simp [compile,resolved] at compiled
  | some projection =>
    unfold compile at compiled
    simp only [resolved,Bind.bind,Option.bind] at compiled
    split at compiled
    · cases Option.some.inj compiled
      exact ⟨rfl,(check_iff table projection).mp (by assumption)⟩
    · contradiction

/-- A resolved projection passing the native checks always compiles. -/
theorem compile_complete (table : StateFiniteTable.Resolved) (declaration : Declaration) (projection : Resolved table)
    (resolved : resolve table declaration = some projection) (valid : Valid table projection) :
    ∃ verified, compile table declaration = some verified := by
  exact ⟨⟨projection,(check_iff table projection).mpr valid⟩,
    by simp [compile,resolved,(check_iff table projection).mpr valid]⟩

/-- Boolean stable projection reads are upward closed on the actual table order. -/
theorem boolean_read_upward {table : StateFiniteTable.Resolved} (projection : Verified table)
    (stable : projection.projection.stable = true) (a b : Fin table.elements.length)
    (below : StateFiniteTable.merge table a b = b)
    (left : value projection a = .bool true) (right : ∃ output, value projection b = .bool output) :
    value projection b = .bool true := by
  obtain ⟨output,right⟩ := right
  have ordered := stable_value_order projection stable a b below
  cases output <;> simp [left,right,StateFiniteProjection.ordered] at ordered ⊢

end CBCL.StateFiniteProjection
