import LeanCbcl.StateLVar

/-! Compress any causal rank into a finite-history bound without changing
semantic addresses or reordering history. Duplicate deliveries remain harmless. -/
namespace CBCL.StateFiniteCausalRank

/-- Number of delivered vertices strictly below a rank value. -/
def below {α : Type} (history : List α) (rank : α → Nat) (value : Nat) : Nat :=
  (history.filter (fun act => decide (rank act < value))).length

/-- Increasing a rank cutoff cannot decrease the finite lower set. -/
theorem below_mono {α : Type} (history : List α) (rank : α → Nat) (left right : Nat)
    (ordered : left ≤ right) : below history rank left ≤ below history rank right := by
  induction history with
  | nil => simp [below]
  | cons act rest ih =>
    by_cases low : rank act < left <;> by_cases high : rank act < right <;>
      simp [below,low,high] at ih ⊢ <;> omega

/-- A present intervening vertex makes the rank cutoff increase strictly. -/
theorem below_strict {α : Type} (history : List α) (rank : α → Nat) (parent : α)
    (member : parent ∈ history) (right : Nat) (ordered : rank parent < right) :
    below history rank (rank parent) < below history rank right := by
  induction history with
  | nil => simp at member
  | cons act rest ih =>
    rcases List.mem_cons.mp member with same | inside
    · subst act
      have monotone := below_mono rest rank (rank parent) right (by omega)
      simp [below,ordered] at monotone ⊢
      omega
    · have smaller := ih inside
      by_cases low : rank act < rank parent <;> by_cases high : rank act < right <;>
        simp [below,low,high] at smaller ⊢ <;> omega

/-- Compression excludes the vertex itself and is below history length. -/
theorem below_bound {α : Type} (history : List α) (rank : α → Nat) (act : α) (member : act ∈ history) :
    below history rank (rank act) < history.length := by
  have bound := List.length_filter_le (fun other => decide (rank other < rank act)) history
  have different : below history rank (rank act) ≠ history.length := by
    intro equal
    have all := List.length_filter_eq_length_iff.mp equal
    have self := all act member
    simp at self
  unfold below at different ⊢
  omega

end CBCL.StateFiniteCausalRank
