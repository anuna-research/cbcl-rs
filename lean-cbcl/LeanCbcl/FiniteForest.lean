import LeanCbcl.FiniteDPDA

/-!
# Finite summaries of forests

An algebra has finitely many summaries for a sequence of expressions. Its
operations consume an atom or a completed list. Parent summaries are saved on
the pushdown stack while a child list is read. The root/inside control bit makes
unfinished lists reject without inspecting the entire stack at acceptance.

This construction is independent of the CBCL grammar instance (SPEC-018
CON-1801); that instance must prove that its summaries implement admission.
-/

namespace CBCL.FormalLanguage

structure ForestAlgebra (atoms summaries : Nat) where
  empty : Fin summaries
  atom : Fin summaries → Fin atoms → Fin summaries
  list : Fin summaries → Fin summaries → Fin summaries
  accept : Fin summaries → Bool

namespace ForestAlgebra

def control {n : Nat} (inside : Bool) (x : Fin n) : Fin (n + n) :=
  if inside then Fin.natAdd n x else Fin.castAdd n x

def summary {n : Nat} : Fin (n + n) → Fin n := Fin.addCases id id

def replace {n : Nat} (s : Fin (n + n)) (x : Fin n) : Fin (n + n) :=
  Fin.addCases (fun _ => control false x) (fun _ => control true x) s

@[simp] theorem summary_control (b : Bool) (x : Fin n) :
    summary (control b x) = x := by
  cases b <;> simp only [control, Bool.false_eq_true, ↓reduceIte, Fin.addCases_left, Fin.addCases_right, summary, id_eq]

@[simp] theorem replace_control (b : Bool) (x y : Fin n) :
    replace (control b x) y = control b y := by
  cases b <;> simp only [control, Bool.false_eq_true, ↓reduceIte, replace, Fin.addCases_left, Fin.addCases_right]

/-- Input 0 opens a list, input 1 closes a list, and `a.succ.succ`
    carries an atom in the finite alphabet. Stack 0 is the bottom marker. -/
def machine (A : ForestAlgebra k n) : DPDA (k + 1 + 1) (n + n) (n + n + 1) where
  initialState := control false A.empty
  initialSymbol := 0
  finalState := Fin.addCases A.accept (fun _ => false)
  transition s t top :=
    Fin.cases
      (some (control true A.empty, [s.succ, top]))
      (fun t' => Fin.cases
        (Fin.addCases (fun _ => none)
          (fun child => Fin.cases none
            (fun parent => some (replace parent (A.list (summary parent) child), [])) top) s)
        (fun a => some (replace s (A.atom (summary s) a), [top])) t') t

@[simp] theorem machine_open (A : ForestAlgebra k n) (s : Fin (n+n))
    (top : Fin (n+n+1)) (rest : List (Fin (n+n+1))) :
    A.machine.step (some (s, top :: rest)) 0 =
      some (control true A.empty, s.succ :: top :: rest) := by
  simp [DPDA.step, machine]

@[simp] theorem machine_atom (A : ForestAlgebra k n) (b : Bool) (x : Fin n)
    (a : Fin k) (top : Fin (n+n+1)) (rest : List (Fin (n+n+1))) :
    A.machine.step (some (control b x, top :: rest)) a.succ.succ =
      some (control b (A.atom x a), top :: rest) := by
  simp [DPDA.step, machine]

@[simp] theorem machine_close (A : ForestAlgebra k n) (b : Bool) (x y : Fin n)
    (rest : List (Fin (n+n+1))) :
    A.machine.step (some (control true y, (control b x).succ :: rest))
      (Fin.succ (0 : Fin (k+1))) =
      some (control b (A.list x y), rest) := by
  dsimp only [DPDA.step, machine, Bind.bind, Option.bind]
  simp only [Fin.cases_succ, Fin.cases_zero]
  simp only [control, ↓reduceIte, Fin.addCases_right]
  change some (replace (control b x) (A.list (summary (control b x)) y), [] ++ rest) = _
  simp only [summary_control, replace_control, List.nil_append]
  rfl

@[simp] theorem machine_close_root (A : ForestAlgebra k n) (x : Fin n)
    (top : Fin (n+n+1)) (rest : List (Fin (n+n+1))) :
    A.machine.step (some (control false x, top :: rest))
      (Fin.succ (0 : Fin (k+1))) = none := by
  dsimp only [DPDA.step, machine, Bind.bind, Option.bind]
  simp only [Fin.cases_succ, Fin.cases_zero, control, Bool.false_eq_true,
    ↓reduceIte, Fin.addCases_left]

end ForestAlgebra
/-- Finite-labelled syntax trees, independent of the automaton run. -/
inductive SyntaxTree (k : Nat) where
  | atom : Fin k → SyntaxTree k
  | node : List (SyntaxTree k) → SyntaxTree k
  deriving Repr

namespace SyntaxTree

def encode : SyntaxTree k → List (Fin (k+1+1))
  | .atom a => [a.succ.succ]
  | .node xs => [0] ++ (xs.map encode).flatten ++ [Fin.succ 0]

def encodeForest (xs : List (SyntaxTree k)) : List (Fin (k+1+1)) :=
  (xs.map encode).flatten

@[simp] theorem encodeForest_nil : encodeForest ([] : List (SyntaxTree k)) = [] := rfl

@[simp] theorem encodeForest_append (xs ys : List (SyntaxTree k)) :
    encodeForest (xs ++ ys) = encodeForest xs ++ encodeForest ys := by
  simp [encodeForest]

@[simp] theorem encodeForest_single (x : SyntaxTree k) : encodeForest [x] = encode x := by
  simp [encodeForest]

end SyntaxTree

namespace ForestDecoder
open SyntaxTree

abbrev Configuration (k : Nat) := List (SyntaxTree k) × List (List (SyntaxTree k))

def encodedPrefix : Configuration k → List (Fin (k+1+1))
  | (xs, []) => encodeForest xs
  | (xs, parent :: rest) => encodedPrefix (parent, rest) ++ [0] ++ encodeForest xs

 theorem encodedPrefix_append (xs ys : List (SyntaxTree k)) (stack : List (List (SyntaxTree k))) :
    encodedPrefix (xs ++ ys, stack) = encodedPrefix (xs, stack) ++ encodeForest ys := by
  cases stack <;> simp [encodedPrefix, List.append_assoc]

/-- This reference decoder reconstructs syntax. It is not the finite machine. -/
def step (c : Option (Configuration k)) (t : Fin (k+1+1)) : Option (Configuration k) :=
  match c with
  | none => none
  | some (xs, stack) => Fin.cases
      (some ([], xs :: stack))
      (fun t' => Fin.cases
        (match stack with
         | [] => none
         | parent :: rest => some (parent ++ [.node xs], rest))
        (fun a => some (xs ++ [.atom a], stack)) t') t

def run (c : Option (Configuration k)) (w : List (Fin (k+1+1))) :
    Option (Configuration k) := w.foldl step c

@[simp] theorem step_none (t : Fin (k+1+1)) : step none t = none := rfl

@[simp] theorem run_none (w : List (Fin (k+1+1))) : run none w = none := by
  induction w with
  | nil => rfl
  | cons t w ih => simpa [run, List.foldl_cons] using ih

 theorem step_encodedPrefix (c d : Configuration k) (t : Fin (k+1+1))
    (h : step (some c) t = some d) : encodedPrefix d = encodedPrefix c ++ [t] := by
  rcases c with ⟨xs, stack⟩
  induction t using Fin.cases with
  | zero =>
    simp only [step, Fin.cases_zero, Option.some.injEq] at h
    subst d
    simp [encodedPrefix]
  | succ t =>
    induction t using Fin.cases with
    | zero =>
      cases stack with
      | nil =>
        simp only [step, Fin.cases_succ, Fin.cases_zero] at h
        cases h
      | cons parent rest =>
        simp only [step, Fin.cases_succ, Fin.cases_zero, Option.some.injEq] at h
        subst d
        simp [encodedPrefix_append, encode, encodedPrefix, encodeForest, List.append_assoc]
    | succ a =>
      simp only [step, Fin.cases_succ, Option.some.injEq] at h
      subst d
      simp [encodedPrefix_append, encode]

 theorem run_encodedPrefix (c d : Configuration k) (w : List (Fin (k+1+1)))
    (h : run (some c) w = some d) : encodedPrefix d = encodedPrefix c ++ w := by
  induction w generalizing c with
  | nil =>
    simp only [run, List.foldl_nil, Option.some.injEq] at h
    subst d
    simp
  | cons t w ih =>
    change run (step (some c) t) w = some d at h
    cases hs : step (some c) t with
    | none => simp [hs] at h
    | some c' =>
      rw [hs] at h
      rw [ih c' h, step_encodedPrefix c c' t hs]
      simp [List.append_assoc]

 theorem run_append (c : Option (Configuration k)) (u v : List (Fin (k+1+1))) :
    run c (u ++ v) = run (run c u) v := List.foldl_append

mutual
 theorem run_tree (x : SyntaxTree k) (xs : List (SyntaxTree k))
    (stack : List (List (SyntaxTree k))) :
    run (some (xs, stack)) x.encode = some (xs ++ [x], stack) := by
  cases x with
  | atom a => simp [encode, run, step]
  | node children =>
    simp only [encode, run_append]
    change run (run (some ([], xs :: stack)) (encodeForest children)) [Fin.succ 0] = _
    rw [run_forest children [] (xs :: stack)]
    simp only [List.nil_append, run, List.foldl_cons, List.foldl_nil, step,
      Fin.cases_succ, Fin.cases_zero]
 termination_by sizeOf x

 theorem run_forest (ys xs : List (SyntaxTree k)) (stack : List (List (SyntaxTree k))) :
    run (some (xs, stack)) (encodeForest ys) = some (xs ++ ys, stack) := by
  cases ys with
  | nil => simp [run]
  | cons y ys =>
    change run (some (xs, stack)) (y.encode ++ encodeForest ys) = _
    rw [run_append, run_tree y xs stack, run_forest ys (xs ++ [y]) stack]
    simp [List.append_assoc]
 termination_by sizeOf ys
end

end ForestDecoder
namespace ForestAlgebra
open SyntaxTree

mutual
 def foldTree (A : ForestAlgebra k n) (s : Fin n) : SyntaxTree k → Fin n
   | .atom a => A.atom s a
   | .node xs => A.list s (A.foldForest xs A.empty)
 def foldForest (A : ForestAlgebra k n) : List (SyntaxTree k) → Fin n → Fin n
   | [], s => s
   | x :: xs, s => A.foldForest xs (A.foldTree s x)
end

@[simp] theorem foldForest_nil (A : ForestAlgebra k n) (s : Fin n) :
    A.foldForest [] s = s := rfl

@[simp] theorem foldForest_append (A : ForestAlgebra k n) (xs ys : List (SyntaxTree k))
    (s : Fin n) : A.foldForest (xs ++ ys) s = A.foldForest ys (A.foldForest xs s) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => exact ih (A.foldTree s x)

@[simp] theorem foldForest_single (A : ForestAlgebra k n) (x : SyntaxTree k) (s : Fin n) :
    A.foldForest [x] s = A.foldTree s x := rfl

def stackSummary (A : ForestAlgebra k n) : List (List (SyntaxTree k)) → List (Fin (n+n+1))
  | [] => [0]
  | parent :: rest => (control (!rest.isEmpty) (A.foldForest parent A.empty)).succ ::
      A.stackSummary rest

 theorem stackSummary_ne_nil (A : ForestAlgebra k n) (stack : List (List (SyntaxTree k))) :
    A.stackSummary stack ≠ [] := by cases stack <;> simp [stackSummary]

def abstract (A : ForestAlgebra k n) (c : ForestDecoder.Configuration k) : A.machine.Configuration :=
  (control (!c.2.isEmpty) (A.foldForest c.1 A.empty), A.stackSummary c.2)

def abstractOption (A : ForestAlgebra k n) (c : Option (ForestDecoder.Configuration k)) :
    Option A.machine.Configuration := c.map A.abstract

 theorem abstract_step (A : ForestAlgebra k n) (c : Option (ForestDecoder.Configuration k))
    (t : Fin (k+1+1)) :
    A.abstractOption (ForestDecoder.step c t) = A.machine.step (A.abstractOption c) t := by
  cases c with
  | none => rfl
  | some c =>
    rcases c with ⟨xs, stack⟩
    induction t using Fin.cases with
    | zero =>
      obtain ⟨top, rest, hs⟩ := List.exists_cons_of_ne_nil (A.stackSummary_ne_nil stack)
      simp only [ForestDecoder.step, Fin.cases_zero, abstractOption, Option.map_some,
        abstract, List.isEmpty_cons, Bool.not_false, stackSummary]
      rw [hs, machine_open]
      rfl
    | succ t =>
      induction t using Fin.cases with
      | zero =>
        cases stack with
        | nil =>
          simp only [ForestDecoder.step, Fin.cases_succ, Fin.cases_zero, abstractOption,
            Option.map_none, Option.map_some, abstract, List.isEmpty_nil, Bool.not_true,
            stackSummary, machine_close_root]
        | cons parent rest =>
          simp only [ForestDecoder.step, Fin.cases_succ, Fin.cases_zero, abstractOption,
            Option.map_some, abstract, List.isEmpty_cons, Bool.not_false, stackSummary,
            machine_close, foldForest_append, foldForest_single, foldTree]
      | succ a =>
        obtain ⟨top, rest, hs⟩ := List.exists_cons_of_ne_nil (A.stackSummary_ne_nil stack)
        simp only [ForestDecoder.step, Fin.cases_succ, abstractOption, Option.map_some,
          abstract, foldForest_append, foldForest_single, foldTree]
        rw [hs, machine_atom]

 theorem abstract_run (A : ForestAlgebra k n) (c : Option (ForestDecoder.Configuration k))
    (w : List (Fin (k+1+1))) :
    A.abstractOption (ForestDecoder.run c w) = A.machine.runFrom (A.abstractOption c) w := by
  induction w generalizing c with
  | nil => rfl
  | cons t w ih =>
    change A.abstractOption (ForestDecoder.run (ForestDecoder.step c t) w) = _
    rw [ih, abstract_step]
    rfl

/-- The independent language: encodings of forests whose finite fold accepts.
    There is no reference to an automaton run in this definition. -/
def language (A : ForestAlgebra k n) (w : List (Fin (k+1+1))) : Prop :=
  ∃ xs, encodeForest xs = w ∧ A.accept (A.foldForest xs A.empty) = true

 theorem accepts_encoding (A : ForestAlgebra k n) (xs : List (SyntaxTree k)) :
    A.machine.accepts (encodeForest xs) = A.accept (A.foldForest xs A.empty) := by
  have h := A.abstract_run (some ([], [])) (encodeForest xs)
  rw [ForestDecoder.run_forest] at h
  change some (control false (A.foldForest xs A.empty), [0]) =
    A.machine.runFrom (some A.machine.initial) (encodeForest xs) at h
  unfold DPDA.accepts
  rw [← h]
  simp only [machine, control, Bool.false_eq_true, ↓reduceIte, Fin.addCases_left]

 theorem accepts_sound (A : ForestAlgebra k n) (w : List (Fin (k+1+1)))
    (ha : A.machine.accepts w = true) : A.language w := by
  have h := A.abstract_run (some ([], [])) w
  change A.abstractOption (ForestDecoder.run (some ([], [])) w) =
    A.machine.runFrom (some A.machine.initial) w at h
  unfold DPDA.accepts at ha
  rw [← h] at ha
  cases hr : ForestDecoder.run (some ([], [])) w with
  | none => simp [hr, abstractOption] at ha
  | some c =>
    rcases c with ⟨xs, stack⟩
    cases stack with
    | nil =>
      have he := ForestDecoder.run_encodedPrefix ([], []) (xs, []) w hr
      simp only [ForestDecoder.encodedPrefix, encodeForest_nil, List.nil_append] at he
      refine ⟨xs, he, ?_⟩
      simpa only [hr, abstractOption, Option.map_some, abstract, List.isEmpty_nil,
        Bool.not_true, machine, control, Bool.false_eq_true, ↓reduceIte, Fin.addCases_left] using ha
    | cons parent rest =>
      simp only [hr, abstractOption, Option.map_some, abstract, List.isEmpty_cons,
        Bool.not_false, machine, control, ↓reduceIte, Fin.addCases_right] at ha
      cases ha

 theorem accepts_iff (A : ForestAlgebra k n) (w : List (Fin (k+1+1))) :
    A.machine.accepts w = true ↔ A.language w := by
  constructor
  · exact A.accepts_sound w
  · rintro ⟨xs, rfl, h⟩
    rw [A.accepts_encoding]
    exact h

/-- Compilation correctness over ALL finite words, including malformed input. -/
def isRealtimeDCFL (A : ForestAlgebra k n) : IsRealtimeDCFL A.language where
  stateSize := n+n
  stackSize := n+n+1
  machine := A.machine
  correct := A.accepts_iff

end ForestAlgebra
end CBCL.FormalLanguage
