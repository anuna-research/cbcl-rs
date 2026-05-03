import LeanCbcl.Message

/-!
# CBCL Message Store Lattice (REQ-511 / CON-511)

Models SPEC-003's grow-only message store as a `Set Message`, following
SPEC-005 Open Question §3 — the algebraic story is cleaner than the
indexed `HashMap ContentHash Message` view, which is deferred to a
separate `LookupSpec` module.

## Assumptions

Per SPEC-005 Open Question §2, the canonical content hash is modelled
as an opaque `ContentHash` together with an injective
`contentHash : Message → ContentHash`. Injectivity is a *cryptographic*
assumption (collision resistance of canonical-form SHA-256), not a
theorem; it is stated as `axiom contentHash_injective`. Together with
the existence axioms for `ContentHash` and `contentHash` themselves,
these are the only non-standard axioms introduced by this module — the
`axiom_audit` task (NFR-511 / TEST-551) is configured to expect them.

## Mathlib

The dedicated `task-mathlib-setup` (SPEC-005 IMPL-005) will add Mathlib
as a dependency. Until then, this module supplies inline minimal
definitions of `Set α := α → Prop` and a `JoinSemiLattice` typeclass
that mirror the Mathlib API. They will be replaced by the Mathlib
versions in a follow-up patch; the public theorems exposed here will
not change.

## Theorems

* `JoinSemiLattice MessageStore` instance with set union as join.
* `union_assoc`, `union_comm`, `union_idem`, `empty_union`, `union_empty`.
* `append_eq_union_singleton`: `append M S = {M} ∪ S`.
* `lookup_monotone`: `S₁ ⊆ S₂ → lookup h S₁ = some M → lookup h S₂ = some M`.

## Mirrors

- SPEC-003 §"CON-300: Store Lattice" and §"Deduplication (G-Set Idempotence)".
- Rust `crates/cbcl-core/src/store/` (forthcoming; the Rust mirror lives
  in the unmechanised path of the SPEC-002/003 verifier and will be
  pinned by SHA in `task-verify-skeleton`).
-/

namespace CBCL
namespace Lattice

/-! ## Local `Set` shim — mirrors `Mathlib.Data.Set.Basic`. -/

/-- A subset of `α`, encoded as its characteristic predicate.
    Mirrors `Mathlib.Init.Set.Set`. -/
def Set (α : Type u) : Type u := α → Prop

namespace Set

instance : Membership α (Set α) := ⟨fun s a => s a⟩

protected def empty : Set α := fun _ => False
protected def singleton (a : α) : Set α := fun b => b = a
protected def union (s t : Set α) : Set α := fun a => s a ∨ t a
protected def Subset (s t : Set α) : Prop := ∀ ⦃a⦄, a ∈ s → a ∈ t

instance : EmptyCollection (Set α) := ⟨Set.empty⟩
instance : Singleton α (Set α) := ⟨Set.singleton⟩
instance : Union (Set α) := ⟨Set.union⟩
instance : HasSubset (Set α) := ⟨Set.Subset⟩

@[simp] theorem mem_def {s : Set α} {a : α} : a ∈ s ↔ s a := Iff.rfl
@[simp] theorem mem_empty {a : α} : a ∈ (∅ : Set α) ↔ False := Iff.rfl
@[simp] theorem mem_singleton {a b : α} : a ∈ ({b} : Set α) ↔ a = b := Iff.rfl
@[simp] theorem mem_union {s t : Set α} {a : α} : a ∈ s ∪ t ↔ a ∈ s ∨ a ∈ t := Iff.rfl

theorem subset_def {s t : Set α} : s ⊆ t ↔ ∀ ⦃a⦄, a ∈ s → a ∈ t := Iff.rfl

@[ext] theorem ext {s t : Set α} (h : ∀ a, a ∈ s ↔ a ∈ t) : s = t := by
  funext a
  exact propext (h a)

end Set

/-! ## Local `JoinSemiLattice` typeclass — mirrors `Mathlib.Order.Lattice`.

    A type with a binary `⊔` that is associative, commutative and idempotent.
    REQ-511 only requires the algebraic axioms; the order-theoretic
    formulation `a ≤ b ↔ a ⊔ b = b` is left implicit. -/
class JoinSemiLattice (α : Type u) where
  join       : α → α → α
  join_assoc : ∀ a b c : α, join (join a b) c = join a (join b c)
  join_comm  : ∀ a b : α, join a b = join b a
  join_idem  : ∀ a : α, join a a = a

infixl:65 " ⊔ " => JoinSemiLattice.join

end Lattice

/-! ## ContentHash — opaque, with injective `contentHash` (Open Question §2). -/

/-- Opaque canonical-form content hash. Real CBCL: SHA-256 of the
    canonical S-expression encoding. -/
axiom ContentHash : Type

/-- Existence: `ContentHash` is nonempty. Bookkeeping axiom — Lean
    needs this to allow `Option ContentHash`-returning functions and
    classical reasoning about `lookup`. -/
axiom ContentHash.instNonempty : Nonempty ContentHash
attribute [instance] ContentHash.instNonempty

/-- The canonical content hash of a message. Mirrors
    `cbcl_core::hash::content_hash` in the Rust implementation. -/
axiom contentHash : Message → ContentHash

/-- **Cryptographic assumption** (SPEC-005 Open Question §2):
    canonical hashing is injective. In reality this is the collision
    resistance of SHA-256 applied to canonical-form bytes. -/
axiom contentHash_injective :
    ∀ m₁ m₂ : Message, contentHash m₁ = contentHash m₂ → m₁ = m₂

/-! ## MessageStore — the SPEC-003 G-Set, modelled as `Set Message`. -/

open Lattice

/-- The CBCL message store as a grow-only set (G-Set CRDT). -/
def MessageStore : Type := Set Message

namespace MessageStore

instance : Membership Message MessageStore := inferInstanceAs (Membership Message (Set Message))
instance : EmptyCollection MessageStore := inferInstanceAs (EmptyCollection (Set Message))
instance : Singleton Message MessageStore := inferInstanceAs (Singleton Message (Set Message))
instance : Union MessageStore := inferInstanceAs (Union (Set Message))
instance : HasSubset MessageStore := inferInstanceAs (HasSubset (Set Message))

/-- Empty store — the lattice bottom element. -/
def empty : MessageStore := (∅ : Set Message)

/-- Singleton store containing exactly `M`. -/
def singleton (M : Message) : MessageStore := ({M} : Set Message)

/-- Set-theoretic union — the G-Set merge / lattice join. -/
def union (S T : MessageStore) : MessageStore := (S ∪ T : Set Message)

/-- Append: dedup-by-construction since membership in a `Set` is idempotent.
    Mirrors `MessageStore::append` returning `false` on duplicates in Rust:
    here, `append M S = S` whenever `M ∈ S`. -/
def append (M : Message) (S : MessageStore) : MessageStore :=
  union (singleton M) S

/-- Lookup-by-content-hash. Classical: returns the unique witness from
    `S` whose hash matches `h`, or `none` if no such witness exists.

    *Non-computable.* The Rust implementation maintains a
    `HashMap ContentHash Message` index for amortised-O(1) lookup; that
    index is the subject of the deferred `LookupSpec` module
    (Open Question §3). For the lattice/monotonicity proof in this
    file, the classical formulation is sufficient — uniqueness of the
    returned witness follows from `contentHash_injective`. -/
noncomputable def lookup (h : ContentHash) (S : MessageStore) : Option Message :=
  open Classical in
  if hex : ∃ m : Message, m ∈ S ∧ contentHash m = h then
    some hex.choose
  else
    none

/-! ### Algebraic properties of `union` (SPEC-003 G-Set axioms). -/

theorem union_assoc (A B C : MessageStore) :
    union (union A B) C = union A (union B C) := by
  show ((A ∪ B : Set Message) ∪ C : Set Message) = (A ∪ (B ∪ C : Set Message) : Set Message)
  apply Set.ext
  intro m
  simp only [Set.mem_union]
  exact or_assoc

theorem union_comm (A B : MessageStore) : union A B = union B A := by
  show (A ∪ B : Set Message) = (B ∪ A : Set Message)
  apply Set.ext
  intro m
  simp only [Set.mem_union]
  exact Or.comm

theorem union_idem (A : MessageStore) : union A A = A := by
  show (A ∪ A : Set Message) = A
  apply Set.ext
  intro m
  simp only [Set.mem_union]
  exact or_self_iff

theorem empty_union (A : MessageStore) : union empty A = A := by
  show (∅ ∪ A : Set Message) = A
  apply Set.ext
  intro m
  simp only [Set.mem_union, Set.mem_empty, false_or]

theorem union_empty (A : MessageStore) : union A empty = A := by
  show (A ∪ ∅ : Set Message) = A
  apply Set.ext
  intro m
  simp only [Set.mem_union, Set.mem_empty, or_false]

/-! ### `append` is `union` with a singleton. -/

theorem append_eq_union_singleton (M : Message) (S : MessageStore) :
    append M S = union (singleton M) S := rfl

/-! ### `JoinSemiLattice` instance with union as join. -/

instance : JoinSemiLattice MessageStore where
  join       := union
  join_assoc := union_assoc
  join_comm  := union_comm
  join_idem  := union_idem

/-! ### Lookup characterisation and monotonicity. -/

/-- A successful lookup returns a witness in the store with matching hash,
    and conversely any such witness *is* the unique returned value
    (uniqueness follows from `contentHash_injective`). -/
theorem lookup_eq_some_iff {h : ContentHash} {S : MessageStore} {M : Message} :
    lookup h S = some M ↔ M ∈ S ∧ contentHash M = h := by
  unfold lookup
  constructor
  · intro hLook
    by_cases hex : ∃ m : Message, m ∈ S ∧ contentHash m = h
    · rw [dif_pos hex] at hLook
      have hSpec := hex.choose_spec
      have hChoose : hex.choose = M := by
        injection hLook
      exact ⟨hChoose ▸ hSpec.1, hChoose ▸ hSpec.2⟩
    · rw [dif_neg hex] at hLook
      cases hLook
  · intro ⟨hMem, hHash⟩
    have hex : ∃ m : Message, m ∈ S ∧ contentHash m = h := ⟨M, hMem, hHash⟩
    rw [dif_pos hex]
    have hSpec := hex.choose_spec
    have hEq : hex.choose = M :=
      contentHash_injective _ _ (hSpec.2.trans hHash.symm)
    rw [hEq]

/-- **Lookup monotonicity** (SPEC-003 store-growth invariant).
    If `lookup h S₁ = some M` and `S₁ ⊆ S₂`, then `lookup h S₂ = some M`. -/
theorem lookup_monotone {S₁ S₂ : MessageStore} (hSub : S₁ ⊆ S₂)
    (h : ContentHash) (M : Message) :
    lookup h S₁ = some M → lookup h S₂ = some M := by
  intro hLook
  have ⟨hMem, hHash⟩ := lookup_eq_some_iff.mp hLook
  exact lookup_eq_some_iff.mpr ⟨hSub hMem, hHash⟩

end MessageStore

end CBCL
