import LeanCbcl.Repeat
import LeanCbcl.State

/-!
# Protocol progress: causal-position selection and maximum reduction

The concrete single-verb selection reuses Repeat.resolve, not an asserted
sender number. The maximum reduction is proved for arbitrary finite position
lists. Joint store/hash growth is monotone using Repeat.resolve_stable. These
are Lean model proofs; live comparisons exercise the Rust transcription.
-/
namespace CBCL.StateProgress
open CBCL.Repeat

/-- Maximum reduction with the empty-table identity zero. -/
def maximum : List Nat → Nat
  | [] => 0
  | x :: xs => max x (maximum xs)

/-- Characterisation independent of order and multiplicity. -/
theorem maximum_le (xs : List Nat) (n : Nat) :
    maximum xs ≤ n ↔ ∀ x ∈ xs, x ≤ n := by
  induction xs with
  | nil => simp [maximum]
  | cons x xs ih => simp [maximum, Nat.max_le, ih]

/-- Every selected value contributes a lower bound on the reduction. -/
theorem le_maximum {xs : List Nat} {x : Nat} (member : x ∈ xs) : x ≤ maximum xs :=
  (maximum_le xs (maximum xs)).mp (Nat.le_refl _) x member

/-- Maximum depends only on membership, not order or duplicate entries. -/
theorem maximum_setEq {xs ys : List Nat} (same : ∀ x, x ∈ xs ↔ x ∈ ys) :
    maximum xs = maximum ys := by
  apply Nat.le_antisymm
  · exact (maximum_le xs _).mpr (fun x hx => le_maximum ((same x).mp hx))
  · exact (maximum_le ys _).mpr (fun x hx => le_maximum ((same x).mpr hx))

/-- Resolve a causal position; unresolved/invalid evidence contributes zero.
The installed bound supplies enough fuel for every valid chain. -/
def position (s : Store) (t : Nat) (v : String) (k h : Nat) : Nat :=
  match resolve (k + 1) s t v k h with
  | .position n => n
  | _ => 0

/-- Protocol-position selection followed by the maximum kernel reduction. -/
def progress (s : Store) (t : Nat) (v : String) (k : Nat) (hashes : List Nat) : Nat :=
  maximum (hashes.map (position s t v k))

/-- An empty accepted store starts at zero. -/
@[simp] theorem progress_empty (s : Store) (t : Nat) (v : String) (k : Nat) :
    progress s t v k [] = 0 := rfl

/-- Every selected value is within the installed bound. -/
theorem position_bound (s : Store) (t : Nat) (v : String) (k h : Nat) :
    position s t v k h ≤ k := by
  unfold position
  cases result : resolve (k + 1) s t v k h with
  | unknown => exact Nat.zero_le _
  | invalid => exact Nat.zero_le _
  | position n => exact (at_bounds (resolve_sound _ result)).2

/-- The state cannot exceed the repeat bound, regardless of branch count. -/
theorem progress_bound (s : Store) (t : Nat) (v : String) (k : Nat) (hashes : List Nat) :
    progress s t v k hashes ≤ k := by
  apply (maximum_le _ _).mpr
  intro n member
  obtain ⟨h, _, rfl⟩ := List.mem_map.mp member
  exact position_bound s t v k h

/-- Hash-set equality implies identical state, even with different list orders. -/
theorem progress_setEq (s : Store) (t : Nat) (v : String) (k : Nat)
    {xs ys : List Nat} (same : ∀ h, h ∈ xs ↔ h ∈ ys) :
    progress s t v k xs = progress s t v k ys := by
  apply maximum_setEq
  intro n
  simp only [List.mem_map]
  constructor
  · rintro ⟨h, member, equality⟩
    exact ⟨h, (same h).mp member, equality⟩
  · rintro ⟨h, member, equality⟩
    exact ⟨h, (same h).mpr member, equality⟩

/-- Arrival order cannot affect the state. -/
theorem progress_perm (s : Store) (t : Nat) (v : String) (k : Nat)
    {xs ys : List Nat} (permutation : xs.Perm ys) :
    progress s t v k xs = progress s t v k ys :=
  progress_setEq s t v k (fun _ => permutation.mem_iff)

/-- Re-delivering all messages does not increase progress. -/
theorem progress_duplicate (s : Store) (t : Nat) (v : String) (k : Nat) (xs : List Nat) :
    progress s t v k (xs ++ xs) = progress s t v k xs := by
  apply progress_setEq
  intro h
  simp

/-- Distinct competing messages at one position do not inflate progress. -/
theorem progress_competing (s : Store) (t : Nat) (v : String) (k a b : Nat)
    (xs : List Nat) (same : position s t v k a = position s t v k b) :
    progress s t v k (a :: b :: xs) = progress s t v k (b :: xs) := by
  change max (position s t v k a) (max (position s t v k b) (progress s t v k xs)) =
    max (position s t v k b) (progress s t v k xs)
  rw [same]
  omega

/-- Resolving additional immutable evidence can only advance a position view. -/
theorem position_monotone {s u : Store} (growth : Extends s u)
    (t : Nat) (v : String) (k h : Nat) :
    position s t v k h ≤ position u t v k h := by
  unfold position
  cases result : resolve (k + 1) s t v k h with
  | unknown => exact Nat.zero_le _
  | invalid => exact Nat.zero_le _
  | position n =>
    rw [resolve_stable growth (by omega) result]
    exact Nat.le_refl _

/-- Joint immutable store growth and accepted-hash growth cannot decrease state. -/
theorem progress_monotone {s u : Store} (growth : Extends s u)
    (t : Nat) (v : String) (k : Nat) {xs ys : List Nat}
    (subset : ∀ h ∈ xs, h ∈ ys) :
    progress s t v k xs ≤ progress u t v k ys := by
  apply (maximum_le _ _).mpr
  intro n member
  obtain ⟨h, hx, rfl⟩ := List.mem_map.mp member
  exact Nat.le_trans (position_monotone growth t v k h)
    (le_maximum (List.mem_map.mpr ⟨h, subset h hx, rfl⟩))

/-- Once progress reaches the bound it stays there as evidence grows. -/
theorem progress_at_bound_stable {s u : Store} (growth : Extends s u)
    (t : Nat) (v : String) (k : Nat) {xs ys : List Nat}
    (subset : ∀ h ∈ xs, h ∈ ys) (complete : progress s t v k xs = k) :
    progress u t v k ys = k := by
  apply Nat.le_antisymm (progress_bound _ _ _ _ _)
  have monotone := progress_monotone growth t v k subset
  omega

/-- Under one evidence interpretation, combining selections reduces by max. -/
theorem progress_append (s : Store) (t : Nat) (v : String) (k : Nat) (xs ys : List Nat) :
    progress s t v k (xs ++ ys) = max (progress s t v k xs) (progress s t v k ys) := by
  induction xs with
  | nil => simp [progress, maximum]
  | cons x xs ih =>
    change max (position s t v k x) (progress s t v k (xs ++ ys)) =
      max (max (position s t v k x) (progress s t v k xs)) (progress s t v k ys)
    rw [ih, Nat.max_assoc]

/-- The counterexample to message counting: three accepted acts, progress two. -/
example : let s : Store := fun h =>
    if h = 0 then some ⟨0, "tick", .begin⟩
    else if h = 1 ∨ h = 2 then some ⟨0, "tick", .previous 0⟩ else none
    progress s 0 "tick" 100 [0, 1, 2] = 2 := by decide

end CBCL.StateProgress

namespace CBCL.State

/-- State-rule sugar over the accepted act addresses and immutable causal evidence.
Position evidence is independent of application fields and other state rules. -/
def protocolProgress (store : Repeat.Store) (thread : Nat) (verb : String)
    (bound : Nat) (accepted : List Act) : Nat :=
  StateProgress.progress store thread verb bound (accepted.map Act.addr)

/-- The new state rule is a set function of the accepted acts. -/
theorem protocolProgress_setEq (store : Repeat.Store) (thread : Nat) (verb : String)
    (bound : Nat) {A B : List Act} (same : SetEq A B) :
    protocolProgress store thread verb bound A = protocolProgress store thread verb bound B := by
  apply StateProgress.progress_setEq
  intro address
  simp only [List.mem_map]
  constructor
  · rintro ⟨a, member, equality⟩
    exact ⟨a, (same a).mp member, equality⟩
  · rintro ⟨a, member, equality⟩
    exact ⟨a, (same a).mpr member, equality⟩

/-- Repeated delivery does not increase protocol progress. -/
theorem protocolProgress_duplicate (store : Repeat.Store) (thread : Nat) (verb : String)
    (bound : Nat) (A : List Act) :
    protocolProgress store thread verb bound (A ++ A) = protocolProgress store thread verb bound A := by
  apply protocolProgress_setEq
  intro a
  simp

/-- The state-rule result respects the installed bound. -/
theorem protocolProgress_bound (store : Repeat.Store) (thread : Nat) (verb : String)
    (bound : Nat) (A : List Act) : protocolProgress store thread verb bound A ≤ bound :=
  StateProgress.progress_bound _ _ _ _ _

/-- The state-rule result only advances as accepted immutable evidence grows. -/
theorem protocolProgress_monotone {small large : Repeat.Store}
    (growth : Repeat.Extends small large) (thread : Nat) (verb : String) (bound : Nat)
    {A B : List Act} (subset : ∀ a ∈ A, a ∈ B) :
    protocolProgress small thread verb bound A ≤ protocolProgress large thread verb bound B := by
  apply StateProgress.progress_monotone growth
  intro h member
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp member
  exact List.mem_map.mpr ⟨a, subset a ha, rfl⟩

end CBCL.State
