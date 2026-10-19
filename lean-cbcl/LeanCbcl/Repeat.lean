import Std

/-!
# Bounded repeat (SPEC-015 REQ-704)

Internal copy names preserve base verbs and Single/Any/All structure. The
executable single-verb resolver formalises `(repeat k tick)`: same-thread causal
ancestry determines position, absent evidence is Unknown, and known bad evidence
is invalid. We prove soundness, completeness, bounds, and valid-stickiness.
General multi-verb/Any/All Rust execution has regression coverage; this module
is not a universal Rust refinement proof. A depth bound is not a message quota.
-/
namespace CBCL.Repeat

/-- Internal copy name, with reversed printed suffixes for nested repeats. -/
structure Name where
  /-- Unindexed wire verb. -/
  base : String
  /-- Copy indices; not sender-supplied fields. -/
  indices : List Nat := []
  deriving DecidableEq, BEq

/-- Add an outer repeat index without changing the base verb. -/
def copy (i : Nat) (n : Name) : Name := ⟨n.base, i :: n.indices⟩

/-- Copying preserves the wire verb and role-annotation lookup key. -/
@[simp] theorem copy_base (i : Nat) (n : Name) : (copy i n).base = n.base := rfl

/-- Distinct copy indices cannot collide, including inside nested repeats. -/
theorem copy_injective {i j : Nat} {a b : Name} :
    copy i a = copy j b ↔ i = j ∧ a = b := by
  cases a; cases b
  simp only [copy, Name.mk.injEq, List.cons.injEq]
  constructor <;> intro h <;> obtain ⟨a, b, c⟩ := h <;> simp_all

/-- Finite Single/Any/All nodes, before internal-name string encoding. -/
inductive Node where
  | single (name : Name)
  | any (names : List Name)
  | all (names : List Name)
  deriving DecidableEq, BEq

/-- Structural renaming preserves fan-in/fan-out seams. -/
def copyNode (i : Nat) : Node → Node
  | .single n => .single (copy i n)
  | .any ns => .any (ns.map (copy i))
  | .all ns => .all (ns.map (copy i))

/-- Nested bodies are expanded before the enclosing copy operation. -/
def expand (k : Nat) (body : List Node) : List Node :=
  (List.range k).flatMap fun i => body.map (copyNode (i + 1))

/-- Expansion produces exactly the size charged to the resource budget. -/
theorem expand_length (k : Nat) (body : List Node) :
    (expand k body).length = k * body.length := by
  have constant (xs : List Nat) :
      (xs.map (fun _ => body.length)).sum = xs.length * body.length := by
    induction xs with
    | nil => simp
    | cons x xs ih => simp [ih, Nat.succ_mul, Nat.add_comm]
  simpa [expand, List.length_flatMap] using constant (List.range k)

/-- Fan-in remains fan-in at iteration seams. -/
theorem copy_all (i : Nat) (ns : List Name) :
    copyNode i (.all ns) = .all (ns.map (copy i)) := rfl

/-- Choice remains choice at iteration seams. -/
theorem copy_any (i : Nat) (ns : List Name) :
    copyNode i (.any ns) = .any (ns.map (copy i)) := rfl

/-- Wire verbs occurring in a node, independently of copy indices. -/
def wireNames : Node → List String
  | .single n => [n.base]
  | .any ns | .all ns => ns.map Name.base

/-- Structural expansion cannot invent or alter a wire performative. -/
theorem copyNode_wireNames (i : Nat) (node : Node) :
    wireNames (copyNode i node) = wireNames node := by
  cases node <;> simp [wireNames, copyNode, copy, List.map_map, Function.comp_def]

/-- Every expanded node belongs to a real body copy inside the declared bound. -/
theorem mem_expand (k : Nat) (body : List Node) (node : Node) :
    node ∈ expand k body ↔
      ∃ i, i < k ∧ ∃ source, source ∈ body ∧ copyNode (i + 1) source = node := by
  simp [expand, List.mem_flatMap, List.mem_map, List.mem_range]

/-- An internal copy cannot collide with an unindexed user name. -/
theorem copy_not_plain (i : Nat) (n : Name) (v : String) :
    copy i n ≠ ⟨v, []⟩ := by
  simp [copy, Name.mk.injEq]

/-- Causal references of a repeated single-verb chain. -/
inductive Cause where
  | begin
  | previous (hash : Nat)
  | absent
  deriving DecidableEq, BEq

/-- Immutable metadata, without application state or numeric payload. -/
structure Evidence where
  /-- Thread isolation is checked on every ancestor. -/
  thread : Nat
  /-- The wire verb remains unindexed. -/
  verb : String
  /-- Causal predecessor. -/
  cause : Cause
  deriving DecidableEq, BEq

/-- Abstract content-addressed store. Authentication is a boundary premise. -/
abbrev Store := Nat → Option Evidence

/-- Missing evidence differs from known-invalid evidence. -/
inductive Result where
  | unknown
  | invalid
  | position (n : Nat)
  deriving DecidableEq, BEq

/-- Fuel-bounded evaluator, including on cyclic or otherwise malformed input.
Fuel at least the repeat bound suffices for every valid chain. -/
def resolve : Nat → Store → Nat → String → Nat → Nat → Result
  | 0, _, _, _, _, _ => .unknown
  | fuel + 1, store, thread, verb, limit, hash =>
    match store hash with
    | none => .unknown
    | some e =>
      if e.thread ≠ thread ∨ e.verb ≠ verb then .invalid
      else match e.cause with
      | .absent => .invalid
      | .begin => if 0 < limit then .position 1 else .invalid
      | .previous pred =>
        match resolve fuel store thread verb limit pred with
        | .unknown => .unknown
        | .invalid => .invalid
        | .position n => if n < limit then .position (n + 1) else .invalid

/-- Declarative evidence for a particular expanded copy; no message-count gate. -/
inductive At (s : Store) (t : Nat) (v : String) (k : Nat) : Nat → Nat → Prop where
  | first (h : Nat) (evidence : s h = some ⟨t, v, .begin⟩)
      (positive : 0 < k) : At s t v k h 1
  | next (h pred n : Nat) (evidence : s h = some ⟨t, v, .previous pred⟩)
      (previous : At s t v k pred n) (within : n < k) : At s t v k h (n + 1)

/-- Valid positions are positive and bounded by the expanded protocol. -/
theorem at_bounds {s : Store} {t : Nat} {v : String} {k h n : Nat}
    (proof : At s t v k h n) : 0 < n ∧ n ≤ k := by
  cases proof <;> omega

/-- Runtime witnesses inhabit actual nodes of the installed single-verb expansion. -/
theorem at_expanded_member {s : Store} {t : Nat} {v : String} {k h n : Nat}
    (proof : At s t v k h n) :
    Node.single ⟨v, [n]⟩ ∈ expand k [.single ⟨v, []⟩] := by
  have bounds := at_bounds proof
  apply (mem_expand k _ _).mpr
  refine ⟨n - 1, by omega, .single ⟨v, []⟩, by simp, ?_⟩
  have index : n - 1 + 1 = n := by omega
  simp [copyNode, copy, index]

/-- A 100-copy chain cannot have a valid 101st position. -/
theorem no_position_101 {s : Store} {t h : Nat} {v : String} :
    ¬ At s t v 100 h 101 := by
  intro proof
  have := at_bounds proof
  omega

/-- Successful evaluation provides a causal witness. -/
theorem resolve_sound (fuel : Nat) {s : Store} {t : Nat} {v : String} {k h n : Nat}
    (success : resolve fuel s t v k h = .position n) : At s t v k h n := by
  induction fuel generalizing h n with
  | zero => simp [resolve] at success
  | succ fuel ih =>
    cases he : s h with
    | none => simp [resolve, he] at success
    | some e =>
      by_cases different : e.thread ≠ t ∨ e.verb ≠ v
      · simp [resolve, he, different] at success
      · have same : e.thread = t ∧ e.verb = v := by simpa using different
        rcases e with ⟨thread, verb, cause⟩
        simp only at same
        obtain ⟨et, ev⟩ := same
        subst thread; subst verb
        cases cause with
        | absent => simp [resolve, he] at success
        | begin =>
          by_cases positive : 0 < k
          · simp [resolve, he, positive] at success
            subst n
            exact .first h he positive
          · simp [resolve, he, positive] at success
        | previous pred =>
          cases hp : resolve fuel s t v k pred with
          | unknown => simp [resolve, he, hp] at success
          | invalid => simp [resolve, he, hp] at success
          | position p =>
            by_cases within : p < k
            · simp [resolve, he, hp, within] at success
              subst n
              exact .next h pred p he (ih hp) within
            · simp [resolve, he, hp, within] at success

/-- Every declarative chain resolves when enough evidence and fuel are present. -/
theorem resolve_complete {s : Store} {t : Nat} {v : String} {k h n : Nat}
    (proof : At s t v k h n) (fuel : Nat) (enough : n ≤ fuel) :
    resolve fuel s t v k h = .position n := by
  induction proof generalizing fuel with
  | first hash evidence positive =>
    cases fuel with
    | zero => omega
    | succ fuel => simp [resolve, evidence, positive]
  | next hash pred n evidence previous within ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have hn : n ≤ fuel := by omega
      simp [resolve, evidence, ih fuel hn, within]

/-- Immutable store growth preserves existing bindings. -/
def Extends (s u : Store) : Prop := ∀ h e, s h = some e → u h = some e

/-- Valid copy positions survive immutable store growth. -/
theorem at_monotone {s u : Store} {t : Nat} {v : String} {k h n : Nat}
    (growth : Extends s u) (proof : At s t v k h n) : At u t v k h n := by
  induction proof with
  | first hash evidence positive => exact .first hash (growth _ _ evidence) positive
  | next hash pred n evidence _ within ih => exact .next hash pred n (growth _ _ evidence) ih within

/-- Executable valid-stickiness, with fuel at least the expansion bound. -/
theorem resolve_stable {s u : Store} {t : Nat} {v : String} {k h n fuel : Nat}
    (growth : Extends s u) (enough : k ≤ fuel)
    (success : resolve fuel s t v k h = .position n) :
    resolve fuel u t v k h = .position n := by
  have witness := resolve_sound fuel success
  exact resolve_complete (at_monotone growth witness) fuel (Nat.le_trans (at_bounds witness).2 enough)

/-- Missing causal references are invalid, never an unconstrained route. -/
theorem absent_invalid (fuel t k h : Nat) (v : String) (s : Store)
    (evidence : s h = some ⟨t, v, .absent⟩) :
    resolve (fuel + 1) s t v k h = .invalid := by simp [resolve, evidence]

/-- Missing evidence is Unknown. -/
theorem missing_unknown (fuel t k h : Nat) (v : String) (s : Store)
    (missing : s h = none) : resolve fuel s t v k h = .unknown := by
  cases fuel <;> simp [resolve, missing]

/-- Two competing messages can both inhabit position 2. -/
example : let s : Store := fun h =>
    if h = 0 then some ⟨0, "tick", .begin⟩
    else if h = 1 ∨ h = 2 then some ⟨0, "tick", .previous 0⟩ else none
    resolve 2 s 0 "tick" 2 1 = .position 2 ∧
    resolve 2 s 0 "tick" 2 2 = .position 2 := by decide

end CBCL.Repeat
