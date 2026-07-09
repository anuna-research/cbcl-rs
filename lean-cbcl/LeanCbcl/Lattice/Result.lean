/-!
# CBCL Three-Valued Verification Result Bisemilattice (REQ-510 / CON-510)

Models SPEC-003's three-valued verification result as a finite inductive
type `VerificationResult` with constructors `unknown`, `valid`,
`violation`, together with `meet` (⊓, conjunction for `(all ...)` fan-in)
and `join` (⊔, disjunction for `(any ...)` predecessors) operations
matching the truth tables in SPEC-003 REQ-303 verbatim.

## Structure of the bisemilattice

Per SPEC-003 ADR-300 / REQ-303, the bottom `⊥ = unknown` is the identity
for `join` (least element under disjunction). The top `⊤ = valid` is the
identity for `meet` (greatest element under conjunction). Note that this
is the *operational* structure used for CBCL verification — a **bounded
bisemilattice**, not a lattice: the meet and join obey associativity,
commutativity, and idempotence — and bottom / top are identities of join
/ meet respectively — but absorption in the classical lattice sense
**fails** for this algebra (Violation is absorbing for meet, Valid is
absorbing for join, in opposite directions), so the two induced
semilattice orders disagree and no single lattice order underlies both
operations. (Under the separate resolved-first knowledge order the type
is a bounded meet-semilattice — see the "Order-theoretic structure"
section below and `Lattice/NotALattice.lean`.)
The `BoundedBisemilattice` typeclass below records exactly the axioms that the
SPEC-003 truth tables satisfy.

## Order-theoretic structure — never a lattice (REQ-510 / ADR-510 / RISK-511)

`VerificationResult` is **not a lattice**. This is a spec correction
(SPEC-005 REQ-510 / ADR-510 / RISK-511), not a Mathlib quirk. There are
two honest readings, both machine-checked in `Lattice/NotALattice.lean`:

* **Bounded meet-semilattice (resolved-first knowledge order).** Under
  the knowledge order `kle` (`unknown ⊥`; `valid`, `violation`
  incomparable and maximal) every pair has a greatest lower bound — the
  *consensus meet* `kmeet` — with bottom `unknown` (`kmeet_is_glb`,
  `unknown_kle`). This order + GLB *does* match the shape of Mathlib's
  `SemilatticeInf` + `OrderBot`; we do not import Mathlib (ADR-510). It
  is **not** a lattice: `valid ⊔ violation` has no least upper bound
  (`no_join_of_terminals` / `not_a_lattice`). NOTE: the GLB `kmeet` is a
  *distinct* operation from the eager `meet` below —
  `kmeet valid violation = unknown` but `meet valid violation =
  violation` (`eager_meet_ne_kmeet`); the deployed conjunction is the
  Kleene min, not the knowledge-order GLB.

* **Bisemilattice (deployed eager algebra).** The `meet`/`join` defined
  in this file (used by `verify`) are each bona-fide semilattice
  operations, but their induced orders disagree and absorption fails
  (`unknown ⊓ (unknown ⊔ violation) = violation ≠ unknown`,
  `eager_absorption_fails`), so under the valid-is-sticky preorder `le`
  they form a **bisemilattice** — also **not** a lattice.

The earlier claim that Mathlib's `SemilatticeInf` "does not apply" was an
overclaim — it applies to the knowledge order — and is removed here. See
the amended ADR-510 / RISK-511 for the full finding.

## Theorems

* `BoundedBisemilattice VerificationResult` instance (axioms discharged by
  exhaustive case analysis over the finite carrier).
* `result_meet_table` — the 3×3 meet truth table (REQ-303).
* `result_join_table` — the 3×3 join truth table (REQ-303).

## Mirrors

- SPEC-003 §"REQ-303: Conjunction and Disjunction — the Result Bisemilattice".
- SPEC-005 §"REQ-510" / §"CON-510".
- Rust `crates/cbcl-core/src/protocol/result.rs` (forthcoming, pinned by
  SHA in `task-verify-skeleton`).
-/

namespace CBCL
namespace Lattice

/-! ## Local `BoundedBisemilattice` typeclass — the eager verdict algebra.

    This typeclass names the deployed *eager verdict algebra* (SPEC-003
    REQ-303): exactly the axioms the two truth tables satisfy — `meet`
    and `join` each associative, commutative, and idempotent; `bot` the
    two-sided identity of `join`; `top` the two-sided identity of `meet`.
    These are the genuine, complete axioms of a **bounded
    bisemilattice**; it is a self-standing algebraic interface, not a
    weakened copy of any Mathlib lattice class with a law struck out.

    Absorption is not an axiom here because it is *false* for this
    algebra (`unknown ⊓ (unknown ⊔ violation) = violation ≠ unknown`) —
    that failure is precisely what makes the carrier a bisemilattice and
    not a lattice (see `Lattice/NotALattice.lean`,
    `eager_absorption_fails`, and the module docstring). Mathlib is not
    imported (ADR-510). -/
class BoundedBisemilattice (α : Type u) where
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

/-- Bisemilattice meet (`⊓`, conjunction). Used in REQ-513
    (`verify_all_is_meet`) to write the fan-in fold over `(all ...)`
    predecessors. Scoped to the `Lattice` namespace to avoid colliding
    with Mathlib's `Inf` once the `task-mathlib-setup` lands. -/
scoped infixl:69 " ⊓ " => BoundedBisemilattice.meet

/-- Bisemilattice top (`⊤`, the meet identity / `valid`). Used in REQ-513 as
    the seed of the fan-in fold. Scoped to the `Lattice` namespace
    (see `⊓` above). -/
scoped notation "⊤" => BoundedBisemilattice.top

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

/-! ### `BoundedBisemilattice` instance — axioms discharged by exhaustive
    case analysis over the 3-element carrier. -/

instance : Lattice.BoundedBisemilattice VerificationResult where
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

/-! ### Knowledge order `⊑` and monotonicity of `meet` / `join`.

    Used by REQ-512 (`verify_monotone`). The order is

    `a ⊑ b  ↔  (a = valid → b = valid)`

    — i.e. **`valid` is sticky** under store growth, while `unknown` and
    `violation` are tentative results that may transition to any other
    state when the store grows. Concretely:

    * `valid ⊑ valid`, but `valid ⋢ unknown` and `valid ⋢ violation`.
    * `unknown ⊑ x` for every `x`.
    * `violation ⊑ x` for every `x`.

    Why not the strict flat order from SPEC-003 §REQ-304 ("once
    `Violation`, never anything else")? That order is monotone for
    leaf `single`-predecessor lookups, but a `(any …)` nested inside
    `(all …)` can transition `violation → valid` *operationally*
    (a sibling becomes `valid`, and `valid` absorbs in `join`). The
    enclosing `meet` then transitions `violation → unknown`. Both
    transitions break the strict flat order. The "`valid` is sticky"
    order accommodates them while still preserving the operationally
    significant invariant — once a verification succeeds (`valid`) it
    stays succeeded — and it makes `meet` and `join` both monotone,
    so the structural-monotonicity argument of SPEC-003 §REQ-304
    composes cleanly through nested causal protocols. -/

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
    transitions out of it are permitted by the order (see module
    docstring above for why this is operationally necessary). -/
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
