import LeanCbcl.BoundaryCanonical

/-! SPEC-042: recursive sibling normalization, parameterized by the complete
native ordering key. Node labels are opaque metadata and never rewritten.
The internal depth parameter has proofs for every finite budget; the complete
algorithm computes the exact authored height and proves it covers all children.
Key encoding remains an explicit
Rust/Lean conformance boundary, not an assumed encoding-injectivity theorem. -/
set_option autoImplicit false
namespace CBCL.BoundaryShapeCanonical
open Std

/-- A shape declaration or rule with opaque metadata and recursive siblings. -/
inductive Tree (α : Type) where
  | node (label : α) (children : List (Tree α))
  deriving Repr

mutual
/-- Complete node height, computed from all recursive children. -/
def height {α : Type} : Tree α → Nat
  | .node _ children => 1 + forestHeight children
/-- Maximum height of a sibling forest. -/
def forestHeight {α : Type} : List (Tree α) → Nat
  | [] => 0
  | child :: rest => max (height child) (forestHeight rest)
end

/-- Every child fits within its parent's computed recursive budget. -/
theorem height_member {α : Type} (children : List (Tree α)) (child : Tree α)
    (member : child ∈ children) : height child ≤ forestHeight children := by
  induction children with
  | nil => simp at member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with same | inside
    · subst child
      exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih inside) (Nat.le_max_right _ _)

/-- A forest fits a height bound exactly when every member does. -/
theorem forestHeight_le {α : Type} (children : List (Tree α)) (bound : Nat) :
    forestHeight children ≤ bound ↔ ∀ child ∈ children, height child ≤ bound := by
  induction children with
  | nil => simp [forestHeight]
  | cons child rest ih => simp [forestHeight,Nat.max_le,ih]

/-- Reordering siblings does not change their maximum height. -/
theorem forestHeight_perm {α : Type} (a b : List (Tree α)) (same : a.Perm b) : forestHeight a = forestHeight b := by
  apply Nat.le_antisymm
  · exact (forestHeight_le a _).mpr (fun child member => height_member b child (same.subset member))
  · exact (forestHeight_le b _).mpr (fun child member => height_member a child (same.symm.subset member))

/-- Siblings are ordered using the key computed after child normalization. -/
def order {α : Type} (key : Tree α → List (List UInt8)) (trees : List (Tree α)) : List (Tree α) :=
  trees.mergeSort (fun a b => (compare (key a) (key b)).isLE)

/-- Sorting changes only sibling order, retaining complete subtrees. -/
theorem order_perm {α : Type} (key : Tree α → List (List UInt8)) (trees : List (Tree α)) : (order key trees).Perm trees :=
  List.mergeSort_perm _ _

/-- The ordering substep has a fixed point for any deterministic key encoder. -/
theorem order_idempotent {α : Type} (key : Tree α → List (List UInt8)) (trees : List (Tree α)) : order key (order key trees) = order key trees := by
  apply List.mergeSort_of_pairwise
  apply List.pairwise_mergeSort (le := fun a b : Tree α => (compare (key a) (key b)).isLE) ?_ ?_ trees
  · intro a b c ab bc
    exact TransOrd.isLE_trans ab bc
  · intro a b
    change ((compare (key a) (key b)).isLE || (compare (key b) (key a)).isLE) = true
    have swapped : compare (key b) (key a) = (compare (key a) (key b)).swap := OrientedOrd.eq_swap
    rw [swapped]
    cases compare (key a) (key b) <;> rfl

/-- Normalize descendants before computing sibling ordering keys. -/
def normalize {α : Type} (key : Tree α → List (List UInt8)) : Nat → Tree α → Tree α
  | 0, tree => tree
  | depth+1, .node label children => .node label (order key (children.map (normalize key depth)))

/-- Complete normality requires ordered siblings and normality of every child. -/
inductive Normal {α : Type} (key : Tree α → List (List UInt8)) : Tree α → Prop where
  | node (label : α) (children : List (Tree α))
      (ordered : children.Pairwise (fun a b => (compare (key a) (key b)).isLE = true))
      (descendants : ∀ child ∈ children, Normal key child) : Normal key (.node label children)

/-- A budget covering the computed height normalizes every recursive sibling
list. The executable oracle uses exactly this computed height, never a cutoff. -/
theorem normalize_complete {α : Type} (key : Tree α → List (List UInt8)) (depth : Nat)
    (tree : Tree α) (covered : height tree ≤ depth) : Normal key (normalize key depth tree) := by
  induction depth generalizing tree with
  | zero => cases tree; simp [height] at covered
  | succ depth ih =>
    cases tree with
    | node label children =>
      apply Normal.node
      · apply List.pairwise_mergeSort (le := fun a b : Tree α => (compare (key a) (key b)).isLE) ?_ ?_ _
        · intro a b c ab bc
          exact TransOrd.isLE_trans ab bc
        · intro a b
          change ((compare (key a) (key b)).isLE || (compare (key b) (key a)).isLE) = true
          have swapped : compare (key b) (key a) = (compare (key a) (key b)).swap := OrientedOrd.eq_swap
          rw [swapped]
          cases compare (key a) (key b) <;> rfl
      · intro child member
        have mapped := (order_perm key _).subset member
        obtain ⟨original,inside,same⟩ := List.mem_map.mp mapped
        subst child
        apply ih original
        have bound := height_member children original inside
        simp only [height] at covered
        omega

/-- Reapplying the complete recursive transformation changes no nodes. -/
theorem normalize_idempotent {α : Type} (key : Tree α → List (List UInt8)) (depth : Nat) (tree : Tree α) :
    normalize key depth (normalize key depth tree) = normalize key depth tree := by
  induction depth generalizing tree with
  | zero => rfl
  | succ depth ih =>
    cases tree with
    | node label children =>
      have stable : (order key (children.map (normalize key depth))).map (normalize key depth) =
          order key (children.map (normalize key depth)) := by
        calc
          _ = (order key (children.map (normalize key depth))).map id := by
            apply List.map_congr_left
            intro child member
            have mapped := (order_perm key _).subset member
            obtain ⟨original,_,same⟩ := List.mem_map.mp mapped
            subst child
            exact ih original
          _ = _ := List.map_id _
      simp only [normalize,stable,order_idempotent]

/-- Recursive ordering preserves the computed tree height exactly. -/
theorem normalize_height {α : Type} (key : Tree α → List (List UInt8)) (depth : Nat) (tree : Tree α) :
    height (normalize key depth tree) = height tree := by
  induction depth generalizing tree with
  | zero => rfl
  | succ depth ih =>
    cases tree with
    | node label children =>
      have mapped : forestHeight (children.map (normalize key depth)) = forestHeight children := by
        induction children with
        | nil => rfl
        | cons child rest tail => simp [forestHeight,ih child,tail]
      simp only [normalize,height,forestHeight_perm _ _ (order_perm key _),mapped]

/-- The full recursive algorithm derives its budget from the authored tree. -/
def complete {α : Type} (key : Tree α → List (List UInt8)) (tree : Tree α) : Tree α := normalize key (height tree) tree

/-- The actual computed-height algorithm orders every sibling list. -/
theorem complete_ordered {α : Type} (key : Tree α → List (List UInt8)) (tree : Tree α) : Normal key (complete key tree) :=
  normalize_complete key _ tree (Nat.le_refl _)

/-- Recomputing the budget on the output still gives an exact fixed point. -/
theorem complete_idempotent {α : Type} (key : Tree α → List (List UInt8)) (tree : Tree α) : complete key (complete key tree) = complete key tree := by
  simp only [complete,normalize_height,normalize_idempotent]

/-- Structural equivalence permits only recursive sibling permutations. The
label and the association of each subtree with its parent remain intact. -/
inductive Equivalent {α : Type} : Tree α → Tree α → Prop where
  | refl (tree : Tree α) : Equivalent tree tree
  | node (label : α) (before intermediate after : List (Tree α))
      (children : List.Forall₂ Equivalent before intermediate)
      (siblings : intermediate.Perm after) : Equivalent (.node label before) (.node label after)

/-- Identity is structurally equivalent to itself. -/
theorem equivalent_refl {α : Type} (tree : Tree α) : Equivalent tree tree := by
  exact Equivalent.refl tree

/-- Lift pointwise structural equivalence over a list without dropping a child. -/
theorem children_map {α : Type} (f : Tree α → Tree α) (children : List (Tree α))
    (same : ∀ child ∈ children, Equivalent child (f child)) : List.Forall₂ Equivalent children (children.map f) := by
  induction children with
  | nil => exact .nil
  | cons child rest ih =>
    exact .cons (same child (by simp)) (ih (by intro x hx; exact same x (by simp [hx])))

/-- Recursive normalisation preserves every label, value and parent/subtree
association; its sole structural effect is reordering siblings. -/
theorem normalize_preserves {α : Type} (key : Tree α → List (List UInt8)) (depth : Nat) (tree : Tree α) :
    Equivalent tree (normalize key depth tree) := by
  induction depth generalizing tree with
  | zero => exact equivalent_refl tree
  | succ depth ih =>
    cases tree with
    | node label children =>
      apply Equivalent.node label children (children.map (normalize key depth))
        (order key (children.map (normalize key depth))) ?_ (order_perm key _).symm
      exact children_map _ children (by intro child member; exact ih child)

/-- The complete algorithm changes only recursive sibling order. -/
theorem complete_preserves {α : Type} (key : Tree α → List (List UInt8)) (tree : Tree α) : Equivalent tree (complete key tree) :=
  normalize_preserves key _ tree

end CBCL.BoundaryShapeCanonical
