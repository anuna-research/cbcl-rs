import LeanCbcl.SExpr
import Batteries.Tactic.Lint

/-!
# Finite deterministic pushdown automata

The certificate in this module concerns *all words* over a finite alphabet.
Control states and stack symbols are finite by construction. Each transition
reads exactly one input symbol and replaces only the top stack symbol. An
absent transition rejects; acceptance inspects only the final control state.
There are no epsilon transitions or host-language whole-stack predicates.

This is the machine contract of SPEC-018 CON-1800. It does not by itself
certify the recursive CBCL language or the existing `DetParser` interface.
-/

namespace CBCL.FormalLanguage

/-- A real-time DPDA, a restricted standard DPDA sufficient for visibly
    delimited syntax. Sizes parameterise a machine, never the input length. -/
structure DPDA (alphabetSize stateSize stackSize : Nat) where
  /-- Consume one input symbol and replace the stack top, or reject. -/
  transition : Fin stateSize → Fin alphabetSize → Fin stackSize →
    Option (Fin stateSize × List (Fin stackSize))
  /-- Control state before any input is consumed. -/
  initialState : Fin stateSize
  /-- The sole initial stack symbol. -/
  initialSymbol : Fin stackSize
  /-- Acceptance predicate on the final control state. -/
  finalState : Fin stateSize → Bool

namespace DPDA

/-- Control state and stack for this machine; stack head is the top. -/
@[nolint unusedArguments] -- Keeps M.Configuration notation; only the carrier sizes determine this type.
abbrev Configuration (_M : DPDA a q g) := Fin q × List (Fin g)

/-- A failed computation stays failed, including on subsequent input. -/
def step (M : DPDA a q g) (c : Option M.Configuration) (t : Fin a) :
    Option M.Configuration := do
  let (state, stack) ← c
  let top :: rest := stack | none
  let (next, push) ← M.transition state t top
  pure (next, push ++ rest)

/-- Consume a word from an optional configuration, preserving failure. -/
def runFrom (M : DPDA a q g) (c : Option M.Configuration) (w : List (Fin a)) :
    Option M.Configuration := w.foldl M.step c

/-- Initial control state paired with the singleton initial stack. -/
def initial (M : DPDA a q g) : M.Configuration :=
  (M.initialState, [M.initialSymbol])

/-- Accept exactly when complete consumption ends in an accepting control state. -/
def accepts (M : DPDA a q g) (w : List (Fin a)) : Bool :=
  match M.runFrom (some M.initial) w with
  | none => false
  | some (state, _) => M.finalState state

@[simp] theorem step_none (M : DPDA a q g) (t : Fin a) :
    M.step none t = none := rfl

@[simp] theorem step_empty (M : DPDA a q g) (s : Fin q) (t : Fin a) :
    M.step (some (s, [])) t = none := rfl

@[simp] theorem runFrom_nil (M : DPDA a q g) (c : Option M.Configuration) :
    M.runFrom c [] = c := rfl

@[simp] theorem runFrom_cons (M : DPDA a q g) (c : Option M.Configuration)
    (t : Fin a) (w : List (Fin a)) :
    M.runFrom c (t :: w) = M.runFrom (M.step c t) w := rfl

@[simp] theorem runFrom_none (M : DPDA a q g) (w : List (Fin a)) :
    M.runFrom none w = none := by
  induction w with
  | nil => rfl
  | cons t w ih => simpa using ih

theorem runFrom_append (M : DPDA a q g) (c : Option M.Configuration)
    (u v : List (Fin a)) :
    M.runFrom c (u ++ v) = M.runFrom (M.runFrom c u) v := by
  exact List.foldl_append

/-- Rejection cannot be repaired by a suffix. This includes malformed prefixes. -/
theorem rejects_extension (M : DPDA a q g) (u v : List (Fin a))
    (h : M.runFrom (some M.initial) u = none) :
    M.accepts (u ++ v) = false := by
  simp [accepts, runFrom_append, h]

/-- Simulation transfers a run for arbitrary input, without assuming the word
    is the serialization of an already well-formed syntax tree. -/
theorem simulate (M : DPDA a q g) (N : DPDA a q' g')
    (f : Option M.Configuration → Option N.Configuration)
    (hs : ∀ c t, f (M.step c t) = N.step (f c) t)
    (c : Option M.Configuration) (w : List (Fin a)) :
    f (M.runFrom c w) = N.runFrom (f c) w := by
  induction w generalizing c with
  | nil => rfl
  | cons t w ih =>
    simp only [runFrom_cons, ih, hs]

end DPDA

/-- A finite real-time DPDA recognising exactly a language of arbitrary words.
    This stronger certificate does not accept an AST-only correctness argument. -/
structure IsRealtimeDCFL {alphabetSize : Nat} (L : List (Fin alphabetSize) → Prop) where
  /-- Number of finite control states in the witness. -/
  stateSize : Nat
  /-- Number of finite stack symbols in the witness. -/
  stackSize : Nat
  /-- The concrete finite real-time pushdown recogniser. -/
  machine : DPDA alphabetSize stateSize stackSize
  correct : ∀ w, machine.accepts w = true ↔ L w

namespace IsRealtimeDCFL

/-- Decide membership by executing the certified recogniser. -/
def decide {L : List (Fin a) → Prop} (h : IsRealtimeDCFL L) (w : List (Fin a)) : Bool :=
  h.machine.accepts w

theorem sound {L : List (Fin a) → Prop} (h : IsRealtimeDCFL L) (w : List (Fin a)) :
    h.decide w = true → L w := (h.correct w).mp

theorem complete {L : List (Fin a) → Prop} (h : IsRealtimeDCFL L) (w : List (Fin a)) :
    L w → h.decide w = true := (h.correct w).mpr

end IsRealtimeDCFL
end CBCL.FormalLanguage
