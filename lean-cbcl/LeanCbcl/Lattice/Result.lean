/-!
# Strong Kleene verdict lattice (REQ-510 / CON-510)

`meet` and `join` are conjunction and disjunction in the truth order
`violation < unknown < valid`. They form a bounded distributive lattice,
with `violation` the join identity and `valid` the meet identity.
Both truth tables match SPEC-003 REQ-303, ignoring Rust diagnostic payloads.

The separate knowledge order puts `unknown` below the two incomparable
terminal verdicts. It has no join of the terminals; see `NotALattice.lean`.
Truth-order meet is not the knowledge-order consensus meet.

The legacy valid-is-sticky preorder is retained for the existing verifier
monotonicity and confluence theorems. Strong Kleene operations also preserve
the stricter knowledge order (proved in `NotALattice.lean`).

Mirrors: SPEC-003 REQ-303, SPEC-005 REQ-510 / CON-510, and
`crates/cbcl-core/src/protocol.rs`.
-/

namespace CBCL
namespace Lattice

/-- Bounded distributive lattice laws for strong Kleene conjunction and
    disjunction. This local algebraic interface needs no Mathlib dependency. -/
class BoundedDistribLattice (α : Type u) where
  /-- The meet operation `⊓` (eager verdict conjunction). -/
  meet       : α → α → α
  /-- The join operation `⊔` (eager verdict disjunction). -/
  join       : α → α → α
  /-- The bottom element (two-sided identity of `join`). -/
  bot        : α
  /-- The top element (two-sided identity of `meet`). -/
  top        : α
  meet_assoc : ∀ a b c : α, meet (meet a b) c = meet a (meet b c)
  meet_comm  : ∀ a b : α, meet a b = meet b a
  meet_idem  : ∀ a : α, meet a a = a
  join_assoc : ∀ a b c : α, join (join a b) c = join a (join b c)
  join_comm  : ∀ a b : α, join a b = join b a
  join_idem  : ∀ a : α, join a a = a
  bot_join   : ∀ a : α, join bot a = a
  join_bot   : ∀ a : α, join a bot = a
  top_meet   : ∀ a : α, meet top a = a
  meet_top   : ∀ a : α, meet a top = a
  meet_absorb : ∀ a b : α, meet a (join a b) = a
  join_absorb : ∀ a b : α, join a (meet a b) = a
  meet_distrib : ∀ a b c : α, meet a (join b c) = join (meet a b) (meet a c)
  join_distrib : ∀ a b c : α, join a (meet b c) = meet (join a b) (join a c)

/-- Truth-order lattice meet (`⊓`, conjunction). Used in REQ-513
    (`verify_all_is_meet`) to write the fan-in fold over `(all ...)`
    predecessors. Scoped to the `Lattice` namespace to avoid colliding
    with Mathlib's `Inf` once the `task-mathlib-setup` lands. -/
scoped infixl:69 " ⊓ " => BoundedDistribLattice.meet

/-- Truth-order lattice top (`⊤`, the meet identity / `valid`). Used in REQ-513 as
    the seed of the fan-in fold. Scoped to the `Lattice` namespace
    (see `⊓` above). -/
scoped notation "⊤" => BoundedDistribLattice.top

end Lattice

/-! ## `VerificationResult` — the SPEC-003 three-valued verification result. -/

/-- The three-valued verification result (SPEC-003 ADR-300 / CON-301).

    * `unknown`   — predecessor not (yet) in store.
    * `valid`     — predecessor found, type matches (⊤ for meet).
    * `violation` — predecessor found, type mismatch (or malformed); ⊥ for join. -/
inductive VerificationResult where
  | unknown
  | valid
  | violation
  deriving Repr, DecidableEq

namespace VerificationResult

/-- Conjunction (`⊓`) for `(all ...)` fan-in. Matches SPEC-003 REQ-303
    meet truth table verbatim:
    `Violation ⊓ _ = _ ⊓ Violation = Violation` (Violation absorbs);
    `Unknown ⊓ Valid = Unknown` (cannot confirm conjunction);
    `Valid ⊓ Valid = Valid`;
    `Unknown ⊓ Unknown = Unknown`. -/
def meet : VerificationResult → VerificationResult → VerificationResult
  | violation, _         => violation
  | _,         violation => violation
  | unknown,   _         => unknown
  | _,         unknown   => unknown
  | valid,     valid     => valid

/-- Disjunction (`⊔`) for `(any ...)` predecessors. Matches SPEC-003
    REQ-303 join truth table verbatim:
    `Valid ⊔ _ = _ ⊔ Valid = Valid` (Valid absorbs);
    `Unknown ⊔ Violation = Unknown`;
    `Unknown ⊔ Unknown = Unknown`;
    `Violation ⊔ Violation = Violation`. -/
def join : VerificationResult → VerificationResult → VerificationResult
  | valid,     _         => valid
  | _,         valid     => valid
  | unknown,   _         => unknown
  | _,         unknown   => unknown
  | violation, violation => violation

/-! ### `BoundedDistribLattice` instance — axioms discharged by exhaustive
    case analysis over the 3-element carrier. -/

instance : Lattice.BoundedDistribLattice VerificationResult where
  meet       := meet
  join       := join
  bot        := violation
  top        := valid
  meet_assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  meet_comm  := by intro a b;   cases a <;> cases b <;> rfl
  meet_idem  := by intro a;     cases a <;> rfl
  join_assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  join_comm  := by intro a b;   cases a <;> cases b <;> rfl
  join_idem  := by intro a;     cases a <;> rfl
  bot_join   := by intro a;     cases a <;> rfl
  join_bot   := by intro a;     cases a <;> rfl
  top_meet   := by intro a;     cases a <;> rfl
  meet_top   := by intro a;     cases a <;> rfl
  meet_absorb := by intro a b; cases a <;> cases b <;> rfl
  join_absorb := by intro a b; cases a <;> cases b <;> rfl
  meet_distrib := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  join_distrib := by intro a b c; cases a <;> cases b <;> cases c <;> rfl

/-! ### Truth tables — verbatim from SPEC-003 REQ-303. -/

/-- The 3×3 meet (`⊓`, conjunction) truth table from SPEC-003 REQ-303,
    asserted verbatim. The nine equations correspond row-by-row,
    column-by-column to the markdown table in §REQ-303. -/
theorem result_meet_table :
    (meet unknown   unknown   = unknown)   ∧
    (meet unknown   valid     = unknown)   ∧
    (meet unknown   violation = violation) ∧
    (meet valid     unknown   = unknown)   ∧
    (meet valid     valid     = valid)     ∧
    (meet valid     violation = violation) ∧
    (meet violation unknown   = violation) ∧
    (meet violation valid     = violation) ∧
    (meet violation violation = violation) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

/-- The 3×3 join (`⊔`, disjunction) truth table from SPEC-003 REQ-303,
    asserted verbatim. The nine equations correspond row-by-row,
    column-by-column to the markdown table in §REQ-303. -/
theorem result_join_table :
    (join unknown   unknown   = unknown)   ∧
    (join unknown   valid     = valid)     ∧
    (join unknown   violation = unknown) ∧
    (join valid     unknown   = valid)     ∧
    (join valid     valid     = valid)     ∧
    (join valid     violation = valid)     ∧
    (join violation unknown   = unknown) ∧
    (join violation valid     = valid)     ∧
    (join violation violation = violation) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

/-! ### Legacy valid-is-sticky preorder `⊑`.

    `a ⊑ b ↔ (a = valid → b = valid)` records only preservation of success.
    It is weaker than the knowledge order: unknown and violation are
    equivalent under it. Existing REQ-512 / REQ-514 theorems retain this
    preorder for compatibility; the strong Kleene operations do not require
    weakening the knowledge order. Their knowledge-order monotonicity is
    proved separately in `NotALattice.lean`. -/

/-- `a ⊑ b` — the verification result order under store growth.
    Defined by case match: `valid ⊑ b` iff `b = valid`; otherwise
    `True`. Equivalent to `a = valid → b = valid`. -/
def le : VerificationResult → VerificationResult → Prop
  | valid, valid => True
  | valid, _     => False
  | _,     _     => True

@[inherit_doc] scoped infix:50 " ⊑ " => VerificationResult.le

/-- Reflexivity of `⊑`. -/
theorem le_refl : ∀ a : VerificationResult, a ⊑ a := by
  intro a; cases a <;> exact True.intro

/-- `unknown` sits at (one of) the bottom positions of `⊑`. -/
theorem unknown_le (a : VerificationResult) : unknown ⊑ a := by
  cases a <;> exact True.intro

/-- `violation` is also a bottom-equivalent position of `⊑` —
    transitions out of it are permitted by this weaker order. This does not
    assert that such transitions occur in the strong Kleene algebra. -/
theorem violation_le (a : VerificationResult) : violation ⊑ a := by
  cases a <;> exact True.intro

/-- `valid` is the top of `⊑`: the only thing above `valid` is `valid`. -/
theorem le_valid_iff {a : VerificationResult} : a ⊑ valid ↔ True := by
  cases a <;> simp [le]

/-- `meet` is monotone in both arguments under `⊑`. Discharged by
    exhaustive case analysis over the 3×3×3×3 carrier; cases where a
    hypothesis simplifies to `False` close vacuously via `simp_all`. -/
theorem meet_mono {a b c d : VerificationResult}
    (hac : a ⊑ c) (hbd : b ⊑ d) : meet a b ⊑ meet c d := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all [le, meet]

/-- `join` is monotone in both arguments under `⊑`. Discharged
    analogously to `meet_mono`. -/
theorem join_mono {a b c d : VerificationResult}
    (hac : a ⊑ c) (hbd : b ⊑ d) : join a b ⊑ join c d := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all [le, join]

end VerificationResult

end CBCL
