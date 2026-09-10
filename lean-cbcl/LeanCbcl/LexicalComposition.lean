import LeanCbcl.FiniteCodec

/-! SPEC-018 CON-1803. A finite lexer emits at most one atom followed by
one delimiter per character. This suffices for maximal-token lexing with
delimiter lookahead. Atom transitions preserve the stack, so the product is
a real-time DPDA without epsilon transitions or an external end marker. -/
namespace CBCL.FormalLanguage

abbrev Lexeme (k : Nat) := Option (Fin k) × Fin 3

def atomTokens (a : Option (Fin k)) : List (Fin (k+1+1)) :=
  match a with | none => [] | some a => [a.succ.succ]

def delimiter (d : Fin 3) : Option (Fin (k+1+1)) :=
  if d == 1 then some 0 else if d == 2 then some (Fin.succ 0) else none

def emit (e : Lexeme k) : List (Fin (k+1+1)) := atomTokens e.1 ++ (delimiter e.2).toList

structure FiniteLexer (alphabet atoms : Nat) (σ : Type) where
  initial : σ
  step : σ → Fin alphabet → Option (σ × Lexeme atoms)
  finish : σ → Option (Option (Fin atoms))

namespace FiniteLexer

def accumulate (L : FiniteLexer a k σ) (c : Option (σ × List (Fin (k+1+1)))) (t : Fin a) :=
  c.bind fun (s, w) => (L.step s t).map fun (s', e) => (s', w ++ emit e)

def scan (L : FiniteLexer a k σ) (w : List (Fin a)) :=
  w.foldl L.accumulate (some (L.initial, []))

def lex (L : FiniteLexer a k σ) (w : List (Fin a)) : Option (List (Fin (k+1+1))) :=
  (L.scan w).bind fun (s, tokens) => (L.finish s).map fun a => tokens ++ atomTokens a

def language (L : FiniteLexer a k σ) (A : ForestAlgebra k n) (w : List (Fin a)) : Prop :=
  ∃ tokens, L.lex w = some tokens ∧ A.language tokens

end FiniteLexer

namespace ForestAlgebra

def afterAtom (A : ForestAlgebra k n) (s : Fin (n+n)) (a : Option (Fin k)) :=
  match a with | none => s | some a => replace s (A.atom (summary s) a)

def advance (A : ForestAlgebra k n) (s : Fin (n+n)) (top : Fin (n+n+1)) (e : Lexeme k) :=
  match delimiter e.2 with
  | none => some (A.afterAtom s e.1, [top])
  | some t => A.machine.transition (A.afterAtom s e.1) t top

theorem advance_correct (A : ForestAlgebra k n) (s : Fin (n+n)) (top : Fin (n+n+1))
    (rest : List (Fin (n+n+1))) (e : Lexeme k) :
    (A.advance s top e).map (fun (s', push) => (s', push ++ rest)) =
      A.machine.runFrom (some (s, top :: rest)) (emit e) := by
  rcases e with ⟨a, d⟩
  cases a <;> simp only [emit, atomTokens, advance, afterAtom]
  all_goals cases hd : delimiter (k := k) d <;>
    simp [DPDA.runFrom, DPDA.step, machine, Bind.bind, Option.bind]
  all_goals simp only [Option.map]; split <;> simp_all

end ForestAlgebra

namespace FiniteLexer

def controlCodec (C : FiniteCodec σ) (A : ForestAlgebra k n) : FiniteCodec (σ × Fin (n+n)) :=
  C.product {
    size := n+n
    positive := by have := A.empty.isLt; omega
    encode := id
    decode := id
    decode_encode := fun _ => rfl }

def product (L : FiniteLexer a k σ) (C : FiniteCodec σ) (A : ForestAlgebra k n) :
    DPDA a (controlCodec C A).size (n+n+1) where
  initialState := (controlCodec C A).encode (L.initial, A.machine.initialState)
  initialSymbol := 0
  transition q t top :=
    let (l, s) := (controlCodec C A).decode q
    (L.step l t).bind fun (l', e) =>
      (A.advance s top e).map fun (s', push) => ((controlCodec C A).encode (l', s'), push)
  finalState q :=
    let (l, s) := (controlCodec C A).decode q
    match L.finish l with
    | none => false
    | some a => A.machine.finalState (A.afterAtom s a)

def pack (C : FiniteCodec σ) (A : ForestAlgebra k n)
    (c : Option (σ × ForestDecoder.Configuration k)) :
    Option (Fin (controlCodec C A).size × List (Fin (n+n+1))) :=
  c.map fun (l, d) => ((controlCodec C A).encode (l, (A.abstract d).1), (A.abstract d).2)

def referenceStep (L : FiniteLexer a k σ) (c : Option (σ × ForestDecoder.Configuration k)) (t : Fin a) :=
  c.bind fun (l, d) => (L.step l t).bind fun (l', e) =>
    (ForestDecoder.run (some d) (emit e)).map fun d' => (l', d')

theorem product_step (L : FiniteLexer a k σ) (C : FiniteCodec σ) (A : ForestAlgebra k n)
    (c : Option (σ × ForestDecoder.Configuration k)) (t : Fin a) :
    pack C A (L.referenceStep c t) = (L.product C A).step (pack C A c) t := by
  cases c with
  | none => rfl
  | some c =>
    rcases c with ⟨l, d⟩
    obtain ⟨top, rest, hs⟩ := List.exists_cons_of_ne_nil (A.stackSummary_ne_nil d.2)
    have hrun := A.abstract_run (some d)
    cases hl : L.step l t with
    | none => simp [referenceStep, pack, DPDA.step, product, (controlCodec C A).decode_encode, hl,
        ForestAlgebra.abstract, hs]
    | some out =>
      rcases out with ⟨l', e⟩
      have h := hrun (emit e)
      change A.abstractOption (ForestDecoder.run (some d) (emit e)) =
        A.machine.runFrom (some ((A.abstract d).1, A.stackSummary d.2)) (emit e) at h
      rw [hs, ← A.advance_correct] at h
      simp only [referenceStep, hl, Option.bind_some, pack]
      simp only [DPDA.step, product]
      simp [ForestAlgebra.abstract, hs, Bind.bind, Option.bind, Option.map_map] at h ⊢
      simp only [(controlCodec C A).decode_encode, hl]
      cases hr : ForestDecoder.run (some d) (emit e) <;>
        cases ha : A.advance (ForestAlgebra.control (!d.2.isEmpty) (A.foldForest d.1 A.empty)) top e <;>
        simp [hr, ha, ForestAlgebra.abstractOption, ForestAlgebra.abstract, Option.map] at h ⊢
      simp [h.1, h.2]

def decodeAccum (c : Option (σ × List (Fin (k+1+1)))) :
    Option (σ × ForestDecoder.Configuration k) :=
  c.bind fun (l, w) => (ForestDecoder.run (some ([], [])) w).map fun d => (l, d)

 theorem decodeAccum_step (L : FiniteLexer a k σ)
    (c : Option (σ × List (Fin (k+1+1)))) (t : Fin a) :
    decodeAccum (L.accumulate c t) = L.referenceStep (decodeAccum c) t := by
  cases c with
  | none => rfl
  | some c =>
    rcases c with ⟨l, w⟩
    cases hl : L.step l t <;> cases hd : ForestDecoder.run (some ([], [])) w <;>
      simp [accumulate, decodeAccum, referenceStep, hl, hd, ForestDecoder.run_append,
        Option.bind, Option.map]

 theorem decodeAccum_fold (L : FiniteLexer a k σ) (w : List (Fin a))
    (c : Option (σ × List (Fin (k+1+1)))) :
    decodeAccum (w.foldl L.accumulate c) = w.foldl L.referenceStep (decodeAccum c) := by
  induction w generalizing c with
  | nil => rfl
  | cons t w ih => simp only [List.foldl_cons, ih, decodeAccum_step]

 theorem pack_fold (L : FiniteLexer a k σ) (C : FiniteCodec σ) (A : ForestAlgebra k n)
    (w : List (Fin a)) (c : Option (σ × ForestDecoder.Configuration k)) :
    pack C A (w.foldl L.referenceStep c) = (L.product C A).runFrom (pack C A c) w := by
  induction w generalizing c with
  | nil => rfl
  | cons t w ih => simp only [List.foldl_cons, ih, product_step, DPDA.runFrom_cons]

 theorem scan_product (L : FiniteLexer a k σ) (C : FiniteCodec σ) (A : ForestAlgebra k n)
    (w : List (Fin a)) :
    pack C A (decodeAccum (L.scan w)) = (L.product C A).runFrom (some (L.product C A).initial) w := by
  rw [scan, decodeAccum_fold, pack_fold]
  rfl

 theorem atom_finish (A : ForestAlgebra k n) (tokens : List (Fin (k+1+1)))
    (d : ForestDecoder.Configuration k) (h : ForestDecoder.run (some ([], [])) tokens = some d)
    (a : Option (Fin k)) :
    A.machine.accepts (tokens ++ atomTokens a) = A.machine.finalState (A.afterAtom (A.abstract d).1 a) := by
  have hp := A.abstract_run (some ([], [])) tokens
  rw [h] at hp
  change some (A.abstract d) = A.machine.runFrom (some A.machine.initial) tokens at hp
  unfold DPDA.accepts
  rw [DPDA.runFrom_append, ← hp]
  obtain ⟨top, rest, hs⟩ := List.exists_cons_of_ne_nil (A.stackSummary_ne_nil d.2)
  cases a <;> simp [atomTokens, DPDA.runFrom, DPDA.step, ForestAlgebra.abstract,
    hs, ForestAlgebra.afterAtom, ForestAlgebra.machine, Bind.bind, Option.bind]

/-- Exact language equality for arbitrary raw words, including lexical failures. -/
theorem product_accepts (L : FiniteLexer a k σ) (C : FiniteCodec σ) (A : ForestAlgebra k n)
    (w : List (Fin a)) :
    (L.product C A).accepts w = (L.lex w).any A.machine.accepts := by
  unfold DPDA.accepts
  rw [← L.scan_product C A w]
  cases hs : L.scan w with
  | none => simp [hs, pack, decodeAccum, lex]
  | some out =>
    rcases out with ⟨l, tokens⟩
    cases hd : ForestDecoder.run (some ([], [])) tokens with
    | none =>
      have hp := A.abstract_run (some ([], [])) tokens
      rw [hd] at hp
      change none = A.machine.runFrom (some A.machine.initial) tokens at hp
      cases hf : L.finish l <;>
        simp [lex, hs, hf, decodeAccum, hd, pack, DPDA.runFrom_append, ← hp]
    | some d =>
      cases hf : L.finish l <;>
        simp [lex, hs, hf, decodeAccum, hd, pack, product,
          (controlCodec C A).decode_encode]
      exact (atom_finish A tokens d hd _).symm

 def isRealtimeDCFL (L : FiniteLexer a k σ) (C : FiniteCodec σ) (A : ForestAlgebra k n) :
    IsRealtimeDCFL (L.language A) where
  stateSize := (controlCodec C A).size
  stackSize := n+n+1
  machine := L.product C A
  correct w := by
    rw [product_accepts]
    simp only [language, Option.any_eq_true]
    constructor
    · rintro ⟨tokens, hl, ha⟩
      exact ⟨tokens, hl, (A.accepts_iff tokens).mp ha⟩
    · rintro ⟨tokens, hl, ha⟩
      exact ⟨tokens, hl, (A.accepts_iff tokens).mpr ha⟩

end FiniteLexer
end CBCL.FormalLanguage
