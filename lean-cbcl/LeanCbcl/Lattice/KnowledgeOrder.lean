import LeanCbcl.Lattice.Result

/-!
# The knowledge order (REQ-510 / ADR-510 / RISK-511)

The knowledge order `kle` puts `unknown` below the incomparable terminals; it is
a partial order and not a lattice.
Its consensus meet `kmeet` is a greatest lower bound with bottom `unknown`,
but the terminals have no common upper bound. These facts concern the
knowledge order only: strong Kleene `meet` / `join` form a bounded
distributive lattice in the distinct truth order (see `Result.lean`).

Strong Kleene conjunction and disjunction are monotone under `kle`,
although neither computes knowledge-order bounds. In particular,
`meet valid violation = violation` but `kmeet valid violation = unknown`.
-/

namespace CBCL
namespace VerificationResult

open VerificationResult

/-! ## The knowledge order `kle` — a genuine partial order.

    `unknown` is the bottom; `valid` and `violation` are incomparable and
    maximal. This is the *information / resolved-first* order, and it is a
    genuine `PartialOrder` — distinct from the *valid-is-sticky preorder*
    `VerificationResult.le` (`Result.lean`), which is only a preorder
    (`unknown ⊑ violation` and `violation ⊑ unknown` both hold there, so
    that order is not antisymmetric). -/
/-- The knowledge order: `unknown` below both `valid` and `violation`,
    which are incomparable. A genuine partial order on `VerificationResult`. -/
def kle : VerificationResult → VerificationResult → Prop
  | unknown,   _         => True
  | valid,     valid     => True
  | violation, violation => True
  | _,         _         => False

/-- `unknown` is the bottom of the knowledge order. -/
theorem unknown_kle (a : VerificationResult) : kle unknown a := True.intro

/-- Reflexivity of `kle`. -/
theorem kle_refl (a : VerificationResult) : kle a a := by
  cases a <;> exact True.intro

/-- Antisymmetry of `kle` (this is what makes it a *partial* order, not
    merely a preorder). -/
theorem kle_antisymm {a b : VerificationResult}
    (h₁ : kle a b) (h₂ : kle b a) : a = b := by
  cases a <;> cases b <;> simp_all [kle]

/-- Transitivity of `kle`. -/
theorem kle_trans {a b c : VerificationResult}
    (h₁ : kle a b) (h₂ : kle b c) : kle a c := by
  cases a <;> cases b <;> cases c <;> simp_all [kle]

/-- The knowledge order genuinely differs from the valid-is-sticky
    preorder `VerificationResult.le`: `violation` and `valid` are
    incomparable under `kle` but `violation ⊑ valid` holds under `le`. -/
theorem knowledge_order_distinct_from_sticky :
    ¬ kle violation valid ∧ VerificationResult.le violation valid :=
  ⟨fun h => h, True.intro⟩

/-! ## The consensus meet `kmeet` — the greatest lower bound of `kle`.

    `kmeet` is the *information-order* GLB (a.k.a. consensus): agreeing
    resolved verdicts are kept, disagreement collapses to `unknown`.

    NOTE (Mathlib shape, no import — ADR-510): `(kle, kmeet, unknown)`
    is exactly the data of a `SemilatticeInf` + `OrderBot` on
    `VerificationResult` with `a ≤ b := kle a b`, `a ⊓ b := kmeet a b`,
    `⊥ := unknown`; `kmeet_is_glb` + `unknown_kle` discharge the
    `SemilatticeInf`/`OrderBot` fields. We do NOT import Mathlib; this is
    only a note that the order matches that structure.

    NOTE (NOT the eager meet): `kmeet ≠ VerificationResult.meet`; see
    `eager_meet_ne_kmeet`. `kmeet valid violation = unknown`, whereas the
    deployed Kleene conjunction `meet valid violation = violation`. -/
/-- The consensus meet: the greatest lower bound in the knowledge order
    `kle` — agreeing verdicts are kept, disagreement collapses to `unknown`. -/
def kmeet : VerificationResult → VerificationResult → VerificationResult
  | unknown,   _         => unknown
  | _,         unknown   => unknown
  | valid,     valid     => valid
  | violation, violation => violation
  | _,         _         => unknown

/-- `kmeet a b` is a lower bound of `a` under the knowledge order. -/
theorem kmeet_le_left (a b : VerificationResult) : kle (kmeet a b) a := by
  cases a <;> cases b <;> exact True.intro

/-- `kmeet a b` is a lower bound of `b` under the knowledge order. -/
theorem kmeet_le_right (a b : VerificationResult) : kle (kmeet a b) b := by
  cases a <;> cases b <;> exact True.intro

/-- `kmeet a b` is the *greatest* lower bound: any common lower bound `c`
    of `a` and `b` is below `kmeet a b`. -/
theorem kmeet_greatest {a b c : VerificationResult}
    (hca : kle c a) (hcb : kle c b) : kle c (kmeet a b) := by
  cases a <;> cases b <;> cases c <;> simp_all [kle, kmeet]

/-- **REQ-510 (meet-semilattice):** `kmeet` is the greatest lower bound
    under the knowledge order `kle`. Together with `unknown_kle`
    (`unknown` is the bottom) this makes `VerificationResult` a
    **bounded meet-semilattice**. -/
theorem kmeet_is_glb (a b : VerificationResult) :
    kle (kmeet a b) a ∧ kle (kmeet a b) b ∧
      (∀ c, kle c a → kle c b → kle c (kmeet a b)) :=
  ⟨kmeet_le_left a b, kmeet_le_right a b, fun _ => kmeet_greatest⟩

/-! ## Not a lattice — the terminals have no join. -/

/-- **REQ-510 (not a lattice):** under the knowledge order, `valid` and
    `violation` (distinct maximal elements) have **no common upper
    bound**. -/
theorem no_join_of_terminals :
    ¬ ∃ u, kle valid u ∧ kle violation u := by
  rintro ⟨u, hv, hviol⟩
  cases u <;> simp_all [kle]

/-- **REQ-510 (not a lattice):** `valid ⊔ violation` has no least upper
    bound, hence `VerificationResult` is **not** a lattice. Any
    purported LUB `u` would in particular be an upper bound of both
    terminals, contradicting `no_join_of_terminals`. -/
theorem not_a_lattice :
    ¬ ∃ u, (kle valid u ∧ kle violation u) ∧
      (∀ w, kle valid w → kle violation w → kle u w) := by
  rintro ⟨u, ⟨hv, hviol⟩, _⟩
  exact no_join_of_terminals ⟨u, hv, hviol⟩

/-! ## Strong Kleene operations: truth-order laws and knowledge monotonicity. -/

/-- The knowledge-order GLB `kmeet` is genuinely a *different* operation
    from the eager Kleene conjunction `meet` used by `verify`:
    `kmeet valid violation = unknown` but `meet valid violation =
    violation`. This is the machine-checked guard against re-conflating
    "the eager conjunction" with "the knowledge-order greatest lower
    bound" (the imprecision RISK-511 exists to catch). -/
theorem eager_meet_ne_kmeet : meet valid violation ≠ kmeet valid violation := by
  decide

/-- Strong Kleene conjunction absorbs disjunction (truth-order lattice law). -/
theorem meet_absorption (a b : VerificationResult) : meet a (join a b) = a := by
  cases a <;> cases b <;> rfl

/-- Strong Kleene disjunction absorbs conjunction (truth-order lattice law). -/
theorem join_absorption (a b : VerificationResult) : join a (meet a b) = a := by
  cases a <;> cases b <;> rfl

/-- Conjunction distributes over disjunction. -/
theorem meet_distributive (a b c : VerificationResult) :
    meet a (join b c) = join (meet a b) (meet a c) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- Disjunction distributes over conjunction. -/
theorem join_distributive (a b c : VerificationResult) :
    join a (meet b c) = meet (join a b) (join a c) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- Strong Kleene conjunction preserves the knowledge order in both arguments. -/
theorem meet_knowledge_mono {a b c d : VerificationResult}
    (hac : kle a c) (hbd : kle b d) : kle (meet a b) (meet c d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all [kle, meet]

/-- Strong Kleene disjunction preserves the knowledge order in both arguments. -/
theorem join_knowledge_mono {a b c d : VerificationResult}
    (hac : kle a c) (hbd : kle b d) : kle (join a b) (join c d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all [kle, join]

end VerificationResult
end CBCL
