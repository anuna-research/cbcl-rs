import LeanCbcl.StateFaultRendering
import LeanCbcl.StateKeywordExtraction

/-! SPEC-042: canonicalisation of keyword/value pairs with positional slots.
Values are opaque. The executable model follows collect/sort/replace, including
the original positions of field slots. Recognition and byte encoding are separate
boundaries. No hash-injectivity axiom is required for these properties. -/
set_option autoImplicit false
namespace CBCL.BoundaryCanonical

/-- A recognized parameter is positional data or one complete keyword/value pair. -/
inductive Piece (α : Type) where
  | positional (value : α)
  | field (key : String) (value : α)
  deriving DecidableEq, Repr

/-- Keyword/value pairs collected without descending into their values. -/
def fields {α : Type} : List (Piece α) → List (String × α)
  | [] => []
  | .positional _ :: rest => fields rest
  | .field key value :: rest => (key,value) :: fields rest

/-- The exact positional layout, including opaque positional values. -/
def layout {α : Type} : List (Piece α) → List (Option α)
  | [] => []
  | .positional value :: rest => some value :: layout rest
  | .field _ _ :: rest => none :: layout rest

/-- Replace only pair slots. Exhausted replacement input preserves the original
slot; canonicalisation supplies exactly the required number of rows. -/
def replace {α : Type} : List (Piece α) → List (String × α) → List (Piece α)
  | [], _ => []
  | .positional value :: rest, rows => .positional value :: replace rest rows
  | .field key value :: rest, [] => .field key value :: replace rest []
  | .field _ _ :: rest, (key,value) :: rows => .field key value :: replace rest rows

/-- Native keyword comparison is lexicographic on UTF-8 bytes. -/
def rowLE {α : Type} (a b : String × α) : Bool := StateFaultRendering.byteLE a.1 b.1

/-- Canonical order of whole rows; duplicate rows are never collapsed. -/
def ordered {α : Type} (rows : List (String × α)) : List (String × α) := rows.mergeSort rowLE

/-- The collection/sort/replacement algorithm. -/
def canonical {α : Type} (pieces : List (Piece α)) : List (Piece α) := replace pieces (ordered (fields pieces))

/-- Sorting preserves complete rows, including duplicate multiplicity. -/
theorem ordered_perm {α : Type} (rows : List (String × α)) : (ordered rows).Perm rows := List.mergeSort_perm _ _

/-- Sorting produces the prescribed UTF-8 order. -/
theorem ordered_sorted {α : Type} (rows : List (String × α)) : (ordered rows).Pairwise (fun a b => rowLE a b = true) :=
  List.pairwise_mergeSort (fun a b c => StateFaultRendering.byte_trans a.1 b.1 c.1)
    (fun a b => StateFaultRendering.byte_total a.1 b.1) rows

/-- Sorting a sorted result is a fixed point, including duplicate keys. -/
theorem ordered_idempotent {α : Type} (rows : List (String × α)) : ordered (ordered rows) = ordered rows :=
  List.mergeSort_of_pairwise (ordered_sorted rows)

/-- Replacement preserves every positional slot and its complete opaque value. -/
theorem layout_replace {α : Type} (pieces : List (Piece α)) (rows : List (String × α)) : layout (replace pieces rows) = layout pieces := by
  induction pieces generalizing rows with
  | nil => rfl
  | cons piece rest ih =>
    cases piece with
    | positional value => simp [replace,layout,ih]
    | field key value => cases rows <;> simp [replace,layout,ih]

/-- Exact-length replacement installs exactly the supplied rows. -/
theorem fields_replace {α : Type} (pieces : List (Piece α)) (rows : List (String × α))
    (size : rows.length = (fields pieces).length) : fields (replace pieces rows) = rows := by
  induction pieces generalizing rows with
  | nil => cases rows <;> simp_all [fields,replace]
  | cons piece rest ih =>
    cases piece with
    | positional value => exact ih rows (by simpa [fields] using size)
    | field key value =>
      cases rows with
      | nil => simp [fields] at size
      | cons row rows =>
        obtain ⟨key',value'⟩ := row
        simp only [replace,fields]
        rw [ih rows (by simpa [fields] using size)]

/-- Layout and rows jointly determine the complete recognized parameter list. -/
theorem determined {α : Type} (a b : List (Piece α)) (slots : layout a = layout b) (rows : fields a = fields b) : a = b := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons piece rest => cases piece <;> simp [layout] at slots
  | cons piece rest ih =>
    cases b with
    | nil => cases piece <;> simp [layout] at slots
    | cons other tail =>
      cases piece with
      | positional value =>
        cases other with
        | field key value' => simp [layout] at slots
        | positional value' =>
          have parts : value = value' ∧ layout rest = layout tail := by simpa [layout] using slots
          have tailEq := ih tail parts.2 rows
          simp [parts.1,tailEq]
      | field key value =>
        cases other with
        | positional value' => simp [layout] at slots
        | field key' value' =>
          have parts : (key = key' ∧ value = value') ∧ fields rest = fields tail := by simpa [fields] using rows
          have tailEq := ih tail (by simpa [layout] using slots) parts.2
          simp [parts.1.1,parts.1.2,tailEq]

/-- Canonicalisation preserves the complete positional layout. -/
theorem canonical_layout {α : Type} (pieces : List (Piece α)) : layout (canonical pieces) = layout pieces := layout_replace _ _

/-- The exact output rows are the ordered input rows. -/
theorem canonical_fields {α : Type} (pieces : List (Piece α)) : fields (canonical pieces) = ordered (fields pieces) :=
  fields_replace _ _ (ordered_perm _).length_eq

/-- No keyword/value pair is invented, lost, split, or changed. -/
theorem canonical_preserves {α : Type} (pieces : List (Piece α)) : (fields (canonical pieces)).Perm (fields pieces) := by
  rw [canonical_fields]
  exact ordered_perm _

/-- Complete canonicalisation is idempotent, not only its sorting substep. -/
theorem canonical_idempotent {α : Type} (pieces : List (Piece α)) : canonical (canonical pieces) = canonical pieces := by
  apply determined
  · exact canonical_layout _
  · simp only [canonical_fields,ordered_idempotent]

/-- Unique keyword names identify the complete row, not just its sorting key. -/
theorem unique_row {α : Type} (rows : List (String × α)) (unique : (rows.map Prod.fst).Nodup)
    (a b : String × α) (ha : a ∈ rows) (hb : b ∈ rows) (key : a.1 = b.1) : a = b := by
  have left := StateKeywordExtraction.lookup_member rows unique a.1 a.2 ha
  have right := StateKeywordExtraction.lookup_member rows unique b.1 b.2 hb
  rw [← key] at right
  have values := Option.some.inj (left.symm.trans right)
  exact Prod.ext key values

/-- Every permutation of a unique mapping has the same canonical row sequence. -/
theorem ordered_permutation {α : Type} (a b : List (String × α)) (same : a.Perm b)
    (unique : (a.map Prod.fst).Nodup) : ordered a = ordered b := by
  apply List.Perm.eq_of_pairwise (le := fun a b => rowLE a b = true)
    ?_ (ordered_sorted a) (ordered_sorted b) ((ordered_perm a).trans (same.trans (ordered_perm b).symm))
  intro x y hx hy xy yx
  apply unique_row a unique x y
  · exact (ordered_perm a).subset hx
  · exact same.symm.subset ((ordered_perm b).subset hy)
  · exact StateFaultRendering.byte_antisymm x.1 y.1 xy yx

/-- Unique field mappings and identical positional layouts have one normal form. -/
theorem canonical_permutation {α : Type} (a b : List (Piece α))
    (slots : layout a = layout b) (same : (fields a).Perm (fields b))
    (unique : ((fields a).map Prod.fst).Nodup) : canonical a = canonical b := by
  apply determined
  · simpa only [canonical_layout] using slots
  · simpa only [canonical_fields] using ordered_permutation _ _ same unique

/-- Normal forms coincide exactly for equal positional layouts and equal complete
row mappings. Distinct values or positional layouts cannot be collapsed. -/
theorem canonical_eq_iff {α : Type} (a b : List (Piece α))
    (unique : ((fields a).map Prod.fst).Nodup) :
    canonical a = canonical b ↔ layout a = layout b ∧ (fields a).Perm (fields b) := by
  constructor
  · intro same
    constructor
    · simpa only [canonical_layout] using congrArg layout same
    · have rows := congrArg fields same
      exact (canonical_preserves a).symm.trans (rows ▸ canonical_preserves b)
  · rintro ⟨slots,rows⟩
    exact canonical_permutation a b slots rows unique

/-- The actual scanner: consume a keyword and its following opaque value as a
pair; every other token occupies a positional slot, including a dangling key. -/
def scan {α : Type} (keyword : α → Option String) : List α → List (Piece α)
  | [] => []
  | item :: rest =>
    match keyword item with
    | none => .positional item :: scan keyword rest
    | some key => match rest with
      | [] => [.positional item]
      | value :: tail => .field key value :: scan keyword tail

/-- Flatten complete pairs and positional slots to the original token grammar. -/
def flatten {α : Type} (keyToken : String → α) : List (Piece α) → List α
  | [] => []
  | .positional value :: rest => value :: flatten keyToken rest
  | .field key value :: rest => keyToken key :: value :: flatten keyToken rest

/-- Accepted positional slots cannot masquerade as keyword tokens. -/
def Clean {α : Type} (keyword : α → Option String) (pieces : List (Piece α)) : Prop :=
  ∀ value, some value ∈ layout pieces → keyword value = none

/-- Scanning a recognized flattened representation reconstructs every slot and
pair exactly. Keyword-looking values remain values, not additional keys. -/
theorem scan_flatten {α : Type} (keyword : α → Option String) (keyToken : String → α)
    (keys : ∀ key, keyword (keyToken key) = some key)
    (pieces : List (Piece α)) (clean : Clean keyword pieces) : scan keyword (flatten keyToken pieces) = pieces := by
  induction pieces with
  | nil => rfl
  | cons piece rest ih =>
    have tailClean : Clean keyword rest := by
      intro value member
      apply clean value
      cases piece <;> simp_all [layout]
    cases piece with
    | positional value =>
      have plain : keyword value = none := clean value (by simp [layout])
      simp [flatten,scan,plain,ih tailClean]
    | field key value => simp [flatten,scan,keys,ih tailClean]

/-- Normalisation cannot introduce keyword tokens into positional slots. -/
theorem canonical_clean {α : Type} (keyword : α → Option String) (pieces : List (Piece α))
    (clean : Clean keyword pieces) : Clean keyword (canonical pieces) := by
  simpa only [Clean,canonical_layout] using clean

/-- The complete executable token algorithm directly checked against Rust. -/
def canonicalTokens {α : Type} (keyword : α → Option String) (keyToken : String → α) (params : List α) : List α :=
  flatten keyToken (canonical (scan keyword params))

/-- Reapplying the whole scanner/sorter/rebuilder changes no accepted tokens. -/
theorem tokens_idempotent {α : Type} (keyword : α → Option String) (keyToken : String → α)
    (keys : ∀ key, keyword (keyToken key) = some key)
    (pieces : List (Piece α)) (clean : Clean keyword pieces) :
    canonicalTokens keyword keyToken (canonicalTokens keyword keyToken (flatten keyToken pieces)) =
      canonicalTokens keyword keyToken (flatten keyToken pieces) := by
  simp only [canonicalTokens,scan_flatten keyword keyToken keys pieces clean]
  rw [scan_flatten keyword keyToken keys _ (canonical_clean keyword pieces clean),canonical_idempotent]

/-- Equivalent accepted authored token mappings produce identical final tokens. -/
theorem tokens_permutation {α : Type} (keyword : α → Option String) (keyToken : String → α)
    (keys : ∀ key, keyword (keyToken key) = some key)
    (a b : List (Piece α)) (cleanA : Clean keyword a) (cleanB : Clean keyword b)
    (slots : layout a = layout b) (same : (fields a).Perm (fields b))
    (unique : ((fields a).map Prod.fst).Nodup) :
    canonicalTokens keyword keyToken (flatten keyToken a) = canonicalTokens keyword keyToken (flatten keyToken b) := by
  simp only [canonicalTokens,scan_flatten keyword keyToken keys a cleanA,scan_flatten keyword keyToken keys b cleanB]
  rw [canonical_permutation a b slots same unique]

/-- Exact semantic characterization at the executable flat-token boundary. -/
theorem tokens_eq_iff {α : Type} (keyword : α → Option String) (keyToken : String → α)
    (keys : ∀ key, keyword (keyToken key) = some key)
    (a b : List (Piece α)) (cleanA : Clean keyword a) (cleanB : Clean keyword b)
    (unique : ((fields a).map Prod.fst).Nodup) :
    canonicalTokens keyword keyToken (flatten keyToken a) = canonicalTokens keyword keyToken (flatten keyToken b) ↔
      layout a = layout b ∧ (fields a).Perm (fields b) := by
  constructor
  · intro same
    have scanned := congrArg (scan keyword) same
    simp only [canonicalTokens,scan_flatten keyword keyToken keys a cleanA,
      scan_flatten keyword keyToken keys b cleanB] at scanned
    rw [scan_flatten keyword keyToken keys _ (canonical_clean keyword a cleanA),
      scan_flatten keyword keyToken keys _ (canonical_clean keyword b cleanB)] at scanned
    exact (canonical_eq_iff a b unique).mp scanned
  · rintro ⟨slots,rows⟩
    exact tokens_permutation keyword keyToken keys a b cleanA cleanB slots rows unique

end CBCL.BoundaryCanonical
