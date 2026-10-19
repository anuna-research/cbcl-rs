import LeanCbcl.FiniteCodec

/-!
# Finite-state restrictions preserve deterministic pushdown recognition

The monitor consumes the same finite-alphabet word as the parser. Its state
is paired with finite parser control; it never sees or changes the stack.
The resulting certificate covers every word, including malformed inputs.
This is intersection with a regular language, not arbitrary post-parse
validation or intersection of two pushdown languages.
-/
namespace CBCL.FormalLanguage

/-- A finite-state monitor over the parser's input alphabet. -/
structure Monitor (alphabetSize stateSize : Nat) where
  initial : Fin stateSize
  transition : Fin stateSize → Fin alphabetSize → Fin stateSize
  finalState : Fin stateSize → Bool

namespace Monitor

/-- Monitor acceptance after complete input consumption. -/
def accepts (D : Monitor a m) (w : List (Fin a)) : Bool :=
  D.finalState (w.foldl D.transition D.initial)

/-- A finite representation of parser and monitor control together. -/
def codec (M : DPDA a q g) (D : Monitor a m) : FiniteCodec (Fin q × Fin m) :=
  (FiniteCodec.mk q (Nat.zero_lt_of_lt M.initialState.isLt) id id (fun _ => rfl)).product
    (FiniteCodec.mk m (Nat.zero_lt_of_lt D.initial.isLt) id id (fun _ => rfl))

/-- Product with the original stack alphabet and a finite control pair. -/
def product (M : DPDA a q g) (D : Monitor a m) : DPDA a (codec M D).size g where
  initialState := (codec M D).encode (M.initialState, D.initial)
  initialSymbol := M.initialSymbol
  transition s t top :=
    let (p, d) := (codec M D).decode s
    (M.transition p t top).map fun (p', push) =>
      ((codec M D).encode (p', D.transition d t), push)
  finalState s :=
    let (p, d) := (codec M D).decode s
    M.finalState p && D.finalState d

/-- Lift a parser configuration while remembering monitor control. -/
def pack (M : DPDA a q g) (D : Monitor a m)
    (c : Option M.Configuration) (d : Fin m) : Option (product M D).Configuration :=
  c.map fun (p, stack) => ((codec M D).encode (p, d), stack)

theorem product_step (M : DPDA a q g) (D : Monitor a m)
    (c : Option M.Configuration) (d : Fin m) (t : Fin a) :
    (product M D).step (pack M D c d) t =
      pack M D (M.step c t) (D.transition d t) := by
  cases c with
  | none => rfl
  | some c =>
    rcases c with ⟨p, stack⟩
    cases stack with
    | nil => rfl
    | cons top rest =>
      simp only [DPDA.step, pack, product, Option.map_some, Bind.bind, Option.bind,
        (codec M D).decode_encode]
      cases M.transition p t top <;> rfl

/-- Exact run correspondence, with no well-formed-input premise. -/
theorem product_run (M : DPDA a q g) (D : Monitor a m)
    (w : List (Fin a)) (c : Option M.Configuration) (d : Fin m) :
    (product M D).runFrom (pack M D c d) w =
      pack M D (M.runFrom c w) (w.foldl D.transition d) := by
  induction w generalizing c d with
  | nil => rfl
  | cons t w ih =>
    simp only [DPDA.runFrom_cons, product_step, ih, List.foldl_cons]

/-- The product recognises precisely the intersection, on all input words. -/
theorem product_accepts (M : DPDA a q g) (D : Monitor a m) (w : List (Fin a)) :
    (product M D).accepts w = (M.accepts w && D.accepts w) := by
  have h := product_run M D w (some M.initial) D.initial
  change (product M D).runFrom (some (product M D).initial) w = _ at h
  unfold DPDA.accepts
  rw [h]
  cases M.runFrom (some M.initial) w with
  | none => rfl
  | some c =>
    rcases c with ⟨p, stack⟩
    simp [pack, product, (codec M D).decode_encode, accepts]

end Monitor

namespace IsRealtimeDCFL

/-- Restriction by a finite monitor preserves the standard finite-machine
certificate. No claim is made for arbitrary semantic predicates. -/
def restrict {L : List (Fin a) → Prop} (h : IsRealtimeDCFL L) (D : Monitor a m) :
    IsRealtimeDCFL (fun w => L w ∧ D.accepts w = true) where
  stateSize := (Monitor.codec h.machine D).size
  stackSize := h.stackSize
  machine := Monitor.product h.machine D
  correct w := by
    rw [Monitor.product_accepts, Bool.and_eq_true, h.correct]

end IsRealtimeDCFL
end CBCL.FormalLanguage
