import LeanCbcl.StateInstalledLattice

/-! Finite join tables are data. Name resolution, total/single-valued rows,
size bounds and exhaustive laws are executable checks. The lattice instance is
constructed from successful checks, never supplied as a user merge function. -/
set_option autoImplicit false
namespace CBCL.StateFiniteTable
open State StateLift

/-- An authored finite lattice with named elements and named join rows. -/
structure Definition where
  /-- The installed name. -/
  name : String
  /-- The ordered names of the finite carrier elements. -/
  elements : List String
  /-- The finite carrier identity element. -/
  bottom : String
  /-- The finite carrier absorbing conflict element. -/
  top : String
  /-- The authored rows retained in declaration order. -/
  rows : List (String × String × String)

/-- Finite table names resolved to bounded element indices. -/
structure Resolved where
  /-- The installed name. -/
  name : String
  /-- The ordered names of the finite carrier elements. -/
  elements : List String
  /-- The finite carrier identity element. -/
  bottom : Fin elements.length
  /-- The finite carrier absorbing conflict element. -/
  top : Fin elements.length
  /-- The authored rows retained in declaration order. -/
  rows : List ((Fin elements.length × Fin elements.length) × Fin elements.length)

/-- Resolve an element name to its position in the declared finite carrier. -/
def index (elements : List String) (name : String) : Option (Fin elements.length) :=
  (List.finRange elements.length).find? (fun i => elements[i] == name)

/-- Resolve bottom, top, and every join-row element; unknown names reject. -/
def resolve (definition : Definition) : Option Resolved := do
  let bottom ← index definition.elements definition.bottom
  let top ← index definition.elements definition.top
  let rows ← definition.rows.mapM (fun (a,b,c) => do
    let left ← index definition.elements a
    let right ← index definition.elements b
    let value ← index definition.elements c
    some ((left,right),value))
  some ⟨definition.name,definition.elements,bottom,top,rows⟩

/-- Enumerate every element of the resolved finite carrier. -/
def indices (table : Resolved) := List.finRange table.elements.length

/-- Look up the declared join result for an ordered pair of element indices. -/
def lookup (table : Resolved) (left right : Fin table.elements.length) : Option (Fin table.elements.length) :=
  table.rows.lookup (left,right)

/-- Read the join table, with a bottom fallback excluded by successful totality checks. -/
def merge (table : Resolved) (left right : Fin table.elements.length) : Fin table.elements.length :=
  (lookup table left right).getD table.bottom

theorem all_indices {n : Nat} (predicate : Fin n → Bool) :
    (List.finRange n).all predicate = true ↔ ∀ i, predicate i = true := by
  constructor
  · intro all i; exact (List.all_eq_true.mp all) i (List.mem_finRange i)
  · intro all; exact List.all_eq_true.mpr (fun i _ => all i)

/-- Check that every ordered pair has a declared join result. -/
def completeCheck (table : Resolved) : Bool :=
  (indices table).all (fun left => (indices table).all (fun right => (lookup table left right).isSome))

/-- Exhaustively check idempotence, bottom, top, commutativity, and associativity. -/
def lawCheck (table : Resolved) : Bool :=
  (indices table).all (fun a => merge table a a == a && merge table table.bottom a == a &&
    merge table a table.top == table.top && (indices table).all (fun b =>
      merge table a b == merge table b a && (indices table).all (fun c =>
        merge table (merge table a b) c == merge table a (merge table b c))))

/-- The semilattice laws required of the concrete finite table merge. -/
def Laws (table : Resolved) : Prop := ∀ a,
  merge table a a = a ∧ merge table table.bottom a = a ∧ merge table a table.top = table.top ∧
    ∀ b, merge table a b = merge table b a ∧ ∀ c, merge table (merge table a b) c = merge table a (merge table b c)

theorem lawCheck_iff (table : Resolved) : lawCheck table = true ↔ Laws table := by
  simp [lawCheck,Laws,indices,all_indices,and_assoc]

/-- Check installed size bounds, names, single-valued total rows, and every lattice law. -/
def check (limit : Nat) (table : Resolved) : Bool :=
  decide (table.elements.length ≤ limit ∧ table.elements.length ≤ 64) && decide table.elements.Nodup &&
    (table.bottom != table.top) && decide (table.rows.map Prod.fst).Nodup && completeCheck table && lawCheck table

/-- The semantic obligations established by successful native finite-table validation. -/
def Valid (limit : Nat) (table : Resolved) : Prop :=
  (table.elements.length ≤ limit ∧ table.elements.length ≤ 64) ∧ table.elements.Nodup ∧ table.bottom ≠ table.top ∧
    (table.rows.map Prod.fst).Nodup ∧ (∀ a b, (lookup table a b).isSome = true) ∧ Laws table

theorem check_iff (limit : Nat) (table : Resolved) : check limit table = true ↔ Valid limit table := by
  simp [check,Valid,completeCheck,indices,all_indices,lawCheck_iff,and_assoc]

/-- A resolved table with successful installed validation evidence. -/
structure Verified where
  /-- The installed finite table with checked semilattice laws. -/
  table : Resolved
  /-- The installed maximum number of carrier elements. -/
  limit : Nat
  checked : check limit table = true

/-- Resolve an authored finite table and construct a carrier only after all checks pass. -/
def compile (limit : Nat) (definition : Definition) : Option Verified := do
  let table ← resolve definition
  if checked : check limit table = true then some ⟨table,limit,checked⟩ else none

/-- Every semilattice law comes from its exhaustive native table check. -/
def algebra (verified : Verified) : BoundedJoinSemilattice (Fin verified.table.elements.length) := by
  have laws := ((check_iff verified.limit verified.table).mp verified.checked).2.2.2.2.2
  exact {
    join := merge verified.table
    join_assoc := fun a b c => (laws a).2.2.2 b |>.2 c
    join_comm := fun a b => (laws a).2.2.2 b |>.1
    join_idem := fun a => (laws a).1
    bot := verified.table.bottom
    bot_join := fun a => (laws a).2.1
    top := verified.table.top
    join_top := fun a => (laws a).2.2.1 }

/-- Success entails bounds, distinct names, total single-valued rows and laws. -/
theorem compile_sound (limit : Nat) (definition : Definition) (verified : Verified)
    (compiled : compile limit definition = some verified) :
    resolve definition = some verified.table ∧ Valid limit verified.table := by
  cases resolved : resolve definition with
  | none => simp [compile,resolved] at compiled
  | some table =>
    unfold compile at compiled
    simp only [resolved,Bind.bind,Option.bind] at compiled
    split at compiled
    · cases Option.some.inj compiled
      exact ⟨rfl,(check_iff limit table).mp (by assumption)⟩
    · contradiction

/-- No table that passes the actual data checks is rejected. -/
theorem compile_complete (limit : Nat) (definition : Definition) (table : Resolved)
    (resolved : resolve definition = some table) (valid : Valid limit table) :
    ∃ verified, compile limit definition = some verified := by
  let verified : Verified := ⟨table,limit,(check_iff limit table).mpr valid⟩
  exact ⟨verified,by simp [compile,resolved,verified,(check_iff limit table).mpr valid]⟩

theorem empty_elements_rejected (limit : Nat) (name bottom top : String) (rows : List (String × String × String)) :
    compile limit ⟨name,[],bottom,top,rows⟩ = none := rfl

end CBCL.StateFiniteTable
