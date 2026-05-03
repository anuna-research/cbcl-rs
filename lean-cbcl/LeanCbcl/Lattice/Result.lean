/-!
# CBCL Three-Valued Verification Result Lattice (REQ-510 / CON-510)

Models SPEC-003's three-valued verification result as a finite inductive
type `VerificationResult` with constructors `unknown`, `valid`,
`violation`, together with `meet` (⊓, conjunction for `(all ...)` fan-in)
and `join` (⊔, disjunction for `(any ...)` predecessors) operations
matching the truth tables in SPEC-003 REQ-303 verbatim.

## Structure of the lattice

Per SPEC-003 ADR-300 / REQ-303, the bottom `⊥ = unknown` is the identity
for `join` (least element under disjunction). The top `⊤ = valid` is the
identity for `meet` (greatest element under conjunction). Note that this
is the *operational* bounded lattice used for CBCL verification: the meet
and join obey associativity, commutativity, and idempotence — and bottom
/ top are identities of join / meet respectively — but absorption in the
classical lattice sense is **not** required by SPEC-003 (Violation is
absorbing for meet, Valid is absorbing for join, in opposite directions).
The `BoundedLattice` typeclass below records exactly the axioms that the
SPEC-003 truth tables satisfy.

## Mathlib

Per SPEC-005 ADR-510, the dedicated `task-mathlib-setup` (IMPL-005) will
add Mathlib4 as a dependency; at that point this module's local
`BoundedLattice` typeclass will be replaced by `Mathlib.Order.Lattice` /
`Mathlib.Order.BoundedOrder` instances. The public theorems exposed here
(`result_meet_table`, `result_join_table`) will not change.

## Theorems

* `BoundedLattice VerificationResult` instance (axioms discharged by
  exhaustive case analysis over the finite carrier).
* `result_meet_table` — the 3×3 meet truth table (REQ-303).
* `result_join_table` — the 3×3 join truth table (REQ-303).

## Mirrors

- SPEC-003 §"REQ-303: Conjunction and Disjunction on the Result Lattice".
- SPEC-005 §"REQ-510" / §"CON-510".
- Rust `crates/cbcl-core/src/protocol/result.rs` (forthcoming, pinned by
  SHA in `task-verify-skeleton`).
-/

namespace CBCL
namespace Lattice

/-! ## Local `BoundedLattice` typeclass — mirrors `Mathlib.Order.Lattice`
    + `Mathlib.Order.BoundedOrder`.

    The typeclass records the algebraic axioms that the SPEC-003 REQ-303
    truth tables satisfy: `meet` and `join` are each associative,
    commutative, and idempotent; `bot` is the two-sided identity of
    `join`; `top` is the two-sided identity of `meet`. Absorption is
    deliberately omitted — see the module docstring above. -/
class BoundedLattice (α : Type u) where
  meet       : α → α → α
  join       : α → α → α
  bot        : α
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

/-- Lattice meet (`⊓`, conjunction). Used in REQ-513
    (`verify_all_is_meet`) to write the fan-in fold over `(all ...)`
    predecessors. Scoped to the `Lattice` namespace to avoid colliding
    with Mathlib's `Inf` once the `task-mathlib-setup` lands. -/
scoped infixl:69 " ⊓ " => BoundedLattice.meet

/-- Lattice top (`⊤`, the meet identity / `valid`). Used in REQ-513 as
    the seed of the fan-in fold. Scoped to the `Lattice` namespace
    (see `⊓` above). -/
scoped notation "⊤" => BoundedLattice.top

end Lattice

/-! ## `VerificationResult` — the SPEC-003 three-valued verification result. -/

/-- The three-valued verification result (SPEC-003 ADR-300 / CON-301).

    * `unknown`   — predecessor not (yet) in store (⊥ for join).
    * `valid`     — predecessor found, type matches (⊤ for meet).
    * `violation` — predecessor found, type mismatch (or malformed). -/
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
    `Unknown ⊔ Violation = Violation`;
    `Unknown ⊔ Unknown = Unknown`;
    `Violation ⊔ Violation = Violation`. -/
def join : VerificationResult → VerificationResult → VerificationResult
  | unknown,   x         => x
  | valid,     _         => valid
  | violation, valid     => valid
  | violation, _         => violation

/-! ### `BoundedLattice` instance — axioms discharged by exhaustive
    case analysis over the 3-element carrier. -/

instance : Lattice.BoundedLattice VerificationResult where
  meet       := meet
  join       := join
  bot        := unknown
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
    (join unknown   violation = violation) ∧
    (join valid     unknown   = valid)     ∧
    (join valid     valid     = valid)     ∧
    (join valid     violation = valid)     ∧
    (join violation unknown   = violation) ∧
    (join violation valid     = valid)     ∧
    (join violation violation = violation) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

end VerificationResult

end CBCL
