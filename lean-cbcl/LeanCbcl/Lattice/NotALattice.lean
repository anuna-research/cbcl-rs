import LeanCbcl.Lattice.Result

/-!
# `VerificationResult` is a bounded meet-semilattice, and is NOT a lattice

(SPEC-005 REQ-510 / ADR-510 / RISK-511)

This module machine-checks the *true* order-theoretic structure of
`VerificationResult`, replacing the earlier (external-review-flagged)
overclaim that it is a **bounded lattice**. Two facts are proved:

1. **Bounded meet-semilattice under the knowledge order.** Under the
   *knowledge order* `kle` (`unknown ⊥`; `valid`, `violation`
   incomparable and maximal), every pair has a greatest lower bound —
   the *consensus meet* `kmeet` — and `unknown` is the bottom. `kle` is
   a genuine `PartialOrder` (reflexive, antisymmetric, transitive), and
   `kmeet_is_glb` proves `kmeet` is the GLB. This order + GLB matches
   the shape of Mathlib's `SemilatticeInf` + `OrderBot` (see the comment
   on `kmeet` — we do NOT import Mathlib, per ADR-510).

2. **Not a lattice.** `valid` and `violation` are distinct maximal
   elements of `kle`, so they have *no common upper bound*
   (`no_join_of_terminals`); a fortiori no least upper bound
   (`not_a_lattice`). Hence `VerificationResult` is a meet-semilattice
   but **not** a lattice.

## The consensus meet `kmeet` is NOT the eager `verify` meet

CRITICAL (and the point external review turned on): the knowledge-order
GLB `kmeet` is a *different operation* from the eager
`VerificationResult.meet` that `verify` uses. `verify`'s `meet` is the
Kleene conjunction (`violation` absorbs), whose induced order has
`violation`, not `unknown`, at the bottom; it is **not** a lower bound
under the knowledge order. Concretely
`meet valid violation = violation` whereas
`kmeet valid violation = unknown` — proved distinct in
`eager_meet_ne_kmeet`. So one must NOT read SPEC-005 REQ-510's phrase
"`meet` (Conjunction) is the greatest lower bound" as saying the
deployed eager conjunction *is* the knowledge-order GLB; it is not. The
meet-semilattice witness is `kmeet` (this file); the eager `meet`/`join`
live in the separate **bisemilattice** reading (see `Result.lean` and
`eager_absorption_fails` below), which is likewise not a lattice.

## Mirrors

- SPEC-005 §"REQ-510" (amended), §"ADR-510" (amended), §"RISK-511".
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

/-! ## The deployed eager algebra is a bisemilattice, also not a lattice.

    These facts pin the honest characterisation of the operations
    `verify` actually uses (`Result.lean`'s `meet`/`join`). -/

/-- The knowledge-order GLB `kmeet` is genuinely a *different* operation
    from the eager Kleene conjunction `meet` used by `verify`:
    `kmeet valid violation = unknown` but `meet valid violation =
    violation`. This is the machine-checked guard against re-conflating
    "the eager conjunction" with "the knowledge-order greatest lower
    bound" (the imprecision RISK-511 exists to catch). -/
theorem eager_meet_ne_kmeet : meet valid violation ≠ kmeet valid violation := by
  decide

/-- Absorption fails for the eager `meet`/`join`, so the deployed algebra
    is a **bisemilattice**, not a lattice:
    `unknown ⊓ (unknown ⊔ violation) = violation ≠ unknown`. -/
theorem eager_absorption_fails :
    meet unknown (join unknown violation) = violation ∧
      meet unknown (join unknown violation) ≠ unknown := by
  decide

end VerificationResult
end CBCL
