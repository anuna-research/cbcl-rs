import LeanCbcl.InstalledLexer

/-! Universal fidelity of the finite exact-name tracker. This proof concerns
arbitrary input lengths, including tokens longer than every installed name. -/
namespace CBCL.InstalledSyntax.Raw

private theorem mem_le_foldmax (xs : List Nat) (a x : Nat) (h : x ∈ xs) :
    x ≤ xs.foldl max a := by
  have seed (ys : List Nat) (b : Nat) : b ≤ ys.foldl max b := by
    induction ys generalizing b with
    | nil => exact Nat.le_refl _
    | cons y ys ih => exact Nat.le_trans (Nat.le_max_left b y) (ih (max b y))
  induction xs generalizing a with
  | nil => simp at h
  | cons y ys ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_trans (Nat.le_max_right a x) (seed ys (max a x))
    · exact ih (max a y) h

theorem name_length_le_width (ds : List Dialect) (i : Fin (names ds).length) :
    (names ds)[i].toList.length ≤ width ds :=
  mem_le_foldmax _ 0 _ (List.mem_map.mpr ⟨_, List.getElem_mem _, rfl⟩)

private theorem prefix_snoc {xs ys : List Nat} {c : Nat} :
    xs ++ [c] <+: ys ↔ xs <+: ys ∧ ys[xs.length]? = some c := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [eq_comm]
  | cons x xs ih =>
    cases ys with
    | nil => simp
    | cons y ys => simp [ih, and_assoc]

/-- Independent prefix relation; no automaton execution occurs in its RHS. -/
def WordInvariant {ds : List Dialect} (s : State ds) (xs : List Nat) : Prop :=
  s.position.val = min xs.length (width ds+1) ∧
  ∀ i, s.candidates i = true ↔ xs <+: (names ds)[i].toList.map Char.toNat

theorem initial_wordInvariant (ds : List Dialect) : WordInvariant (initial ds) [] := by
  simp [WordInvariant, initial]

theorem wordChar_invariant {ds : List Dialect} (s : State ds) (xs : List Nat) (c : Nat)
    (h : WordInvariant s xs) : WordInvariant (wordChar s c) (xs ++ [c]) := by
  constructor
  · simp only [wordChar, List.length_append, List.length_cons, List.length_nil]
    rw [h.1]
    omega
  · intro i
    simp only [wordChar, Bool.and_eq_true]
    rw [h.2 i, prefix_snoc]
    apply and_congr_right
    intro hp
    have hl := hp.length_le
    have hb := name_length_le_width ds i
    simp only [List.length_map] at hl
    have pos : s.position.val = xs.length := by rw [h.1]; omega
    simp [pos, Option.any_eq_true]

theorem word_invariant (ds : List Dialect) (xs : List Nat) :
    WordInvariant (xs.foldl wordChar (initial ds)) xs := by
  have general (ys : List Nat) (s : State ds) (consumed : List Nat)
      (h : WordInvariant s consumed) : WordInvariant (ys.foldl wordChar s) (consumed ++ ys) := by
    induction ys generalizing s consumed with
    | nil => simpa using h
    | cons y ys ih =>
      simpa only [List.foldl_cons, List.append_assoc, List.singleton_append] using
        ih (wordChar s y) (consumed ++ [y]) (wordChar_invariant s consumed y h)
  simpa using general xs (initial ds) [] (initial_wordInvariant ds)

/-- Exact name equality, for every finite environment and every word length.
    In particular, neither prefixes nor arbitrarily long extensions can alias
    a reserved name, dialect name, or declared performative. -/
theorem nameMatches_word (ds : List Dialect) (xs : List Nat) (i : Fin (names ds).length) :
    nameMatches (xs.foldl wordChar (initial ds)) i = true ↔
      xs = (names ds)[i].toList.map Char.toNat := by
  have h := word_invariant ds xs
  simp only [nameMatches, Bool.and_eq_true, beq_iff_eq]
  rw [h.2 i, h.1]
  constructor
  · rintro ⟨hp, hl⟩
    have hb := name_length_le_width ds i
    have hc := hp.length_le
    simp only [List.length_map] at hc
    apply hp.eq_of_length
    simp only [List.length_map]
    omega
  · intro he
    subst xs
    simp only [List.prefix_rfl, List.length_map, true_and]
    have hb := name_length_le_width ds i
    omega

end CBCL.InstalledSyntax.Raw
