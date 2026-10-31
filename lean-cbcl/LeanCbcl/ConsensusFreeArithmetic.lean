import LeanCbcl.SealedCheckpoint

namespace CBCL.ConsensusFree
open CBCL.ValidatorBudget CBCL.SealedCheckpoint

/-- Function update at one key, leaving all other entries unchanged. -/
def setAt [DecidableEq α] (fn : α → β) (key : α) (value : β) : α → β :=
  fun x => if x = key then value else fn x

@[simp] theorem setAt_same [DecidableEq α] (fn : α → β) (key : α) (v : β) :
    setAt fn key v key = v := by simp [setAt]
@[simp] theorem setAt_other [DecidableEq α] (fn : α → β) (key x : α) (v : β)
    (different : x ≠ key) : setAt fn key v x = fn x := by simp [setAt, different]

/-- Sum an integer-valued function over a finite list. -/
def isum (xs : List α) (fn : α → Int) : Int :=
  match xs with
  | [] => 0
  | x :: rest => fn x + isum rest fn

theorem isum_congr (xs : List α) (fn gn : α → Int)
    (same : ∀ x ∈ xs, fn x = gn x) : isum xs fn = isum xs gn := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [isum]
      rw [same x (by simp), ih (fun y hy => same y (by simp [hy]))]
theorem isum_nonneg (xs : List α) (fn : α → Int)
    (positive : ∀ x ∈ xs, 0 ≤ fn x) : 0 ≤ isum xs fn := by
  induction xs with
  | nil => simp [isum]
  | cons x xs ih =>
      have hx := positive x (by simp)
      have ht := ih (fun y hy => positive y (by simp [hy]))
      simp only [isum]; omega
theorem isum_member (xs : List α) (fn : α → Int)
    (positive : ∀ x ∈ xs, 0 ≤ fn x) (hx : x ∈ xs) : fn x ≤ isum xs fn := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
      have ht := isum_nonneg ys fn (fun z hz => positive z (by simp [hz]))
      have hh := positive y (by simp)
      simp only [isum]
      rcases List.mem_cons.mp hx with same | tailMem
      · subst y; omega
      · have hb := ih (fun z hz => positive z (by simp [hz])) tailMem
        omega
theorem isum_update [DecidableEq α] (xs : List α) (fn : α → Int) (x : α) (value : Int)
    (unique : xs.Nodup) (member : x ∈ xs) :
    isum xs (setAt fn x value) = isum xs fn - fn x + value := by
  induction xs with
  | nil => simp at member
  | cons y ys ih =>
      obtain ⟨absent, tailUnique⟩ := List.nodup_cons.mp unique
      rcases List.mem_cons.mp member with same | tailMem
      · subst y
        have tailSame : isum ys (setAt fn x value) = isum ys fn :=
          isum_congr ys _ _ (fun z hz => by
            have diff : z ≠ x := by intro eq; exact absent (eq ▸ hz)
            simp [setAt, diff])
        simp only [isum, setAt_same, tailSame]; omega
      · have diff : y ≠ x := by intro eq; exact absent (eq ▸ tailMem)
        have ht := ih tailUnique tailMem
        simp only [isum, setAt_other fn x y value diff, ht]; omega


theorem finRange_unique (n : Nat) : (List.finRange n).Nodup := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.finRange_succ, List.nodup_cons]
      constructor
      · simp only [List.mem_map]
        intro ⟨x, hx, eq⟩
        have : (x.succ : Fin (n+1)).val = 0 := congrArg Fin.val eq
        simp at this
      · unfold List.Nodup at *
        rw [List.pairwise_map]
        exact ih.imp (fun different eq => different (Fin.ext (by
          have values := congrArg Fin.val eq
          simpa using values)))


theorem isum_add (xs : List α) (fn gn : α → Int) :
    isum xs (fun x => fn x + gn x) = isum xs fn + isum xs gn := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [isum, ih]; omega

theorem isum_sub (xs : List α) (fn gn : α → Int) :
    isum xs (fun x => fn x - gn x) = isum xs fn - isum xs gn := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [isum, ih]; omega

theorem isum_append (xs ys : List α) (fn : α → Int) :
    isum (xs ++ ys) fn = isum xs fn + isum ys fn := by
  induction xs with
  | nil => simp [isum]
  | cons x xs ih => simp only [List.cons_append, isum, ih]; omega


end CBCL.ConsensusFree
