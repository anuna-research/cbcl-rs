import LeanCbcl.Message
import LeanCbcl.Lattice.Result
import LeanCbcl.Lattice.Store

/-!
# CBCL `verify` skeleton (REQ-512 / REQ-513 / REQ-514)

This module lands the Lean-side model that the verify theorems quantify
over: a `CausedBy` description of a message's `:caused-by` field, a
`CausalProtocol` predecessor pattern (`begin | single | any | all`),
and a `verify : Message → CausalProtocol → MessageStore →
VerificationResult` definition mirroring the Rust verifier's match arms.

NO theorems are proved here. This file exists so REQ-512 (monotonicity),
REQ-513 (lattice-homomorphism for fan-in), and REQ-514 (eventual
consistency) can even be *stated* in subsequent tasks.

## Open Question §1 — `Begin` as a primitive

SPEC-005 §"Open Questions" §1 asks whether `begin` should be a top-level
constructor or desugared as `all []` (vacuous fan-in). We lift `Begin`
to a top-level constructor because the desugaring `all []` would
silently drop the message-side `:caused-by` check: under the `meet`
identity, `verify M (.all []) S = .valid` unconditionally, so a message
with `:caused-by some_hash` would be accepted against a step that
should only accept `:caused-by begin`. The two encodings are therefore
not semantically equivalent; the lifted form is the one that preserves
the message-side discriminant inside `verify`'s case analysis (and, as
a side benefit, keeps monotonicity case-analysis trivial for `begin`
and avoids complicating the `(all ...)` homomorphism statement of
REQ-513).

### Structural divergence from Rust

Rust does not have a `Begin` variant in `NodeRef` either; instead it
treats `"begin"` as a magic string appearing inside `NodeRef::Single`
or `NodeRef::Any` predecessor refs (see `verify_causal`'s
`CausedBy::Begin` arm in `crates/cbcl-core/src/protocol.rs`). The Lean
model promotes that magic string to a typed constructor, which is
cleaner to reason about but means `CausalProtocol.begin` does not
correspond to any single `NodeRef` variant. The two encodings agree on
lattice positions (so the parity tests pass) but are not pointwise
equivalent — in particular, the Lean model cannot represent
`NodeRef::Any({"begin", "tell"})` as a single primitive; it would be
encoded as `any [.begin, .single "tell"]`. Mirror-drift could occur if
the Rust string vocabulary is ever extended (e.g. additional reserved
keywords beyond `"begin"`); there is no compiler-level link binding the
two surfaces.

## Mirrors

The verification function mirrors `verify_causal` in
`crates/cbcl-core/src/protocol.rs` (no dedicated `verify.rs` file
exists in the Rust tree — protocol verification lives alongside the
`CausalProtocol` data model). The match-arm structure of
`verify_causal` (single → store lookup; multiple → fan-in meet;
begin → constant Valid; missing-caused-by → Violation) is preserved
here.

Pinned commit SHA at time of mirroring: `5a233c692b1dc79241de2678bf00101c9b703c48`
(parent of `a4de63c`, the commit that landed this skeleton).

## Abstract Message accessor

The existing `CBCL.Message` (from `LeanCbcl/Message.lean`) does not yet
carry a structured `:caused-by` field — that surface-syntax extraction
is the responsibility of the parser-side mechanisation, which is out of
scope for SPEC-005. This module therefore introduces an *abstract*
accessor `Message.causedBy : Message → Option CausedBy` declared as a
Lean `axiom`. The verify theorems treat the accessor as a black box:
case analysis goes via the `Option CausedBy` result, never via the
underlying `params : List SExpr`. When the parser-side mechanisation
lands, the axiom will be replaced by a concrete definition over
`params`; the public API (`verify` and the REQ-512/513/514 theorem
statements) will not change.

The `axiom_audit` task (NFR-511 / TEST-551) is configured to expect
this single abstraction axiom in addition to the `ContentHash` /
`contentHash` axioms already permitted by SPEC-005.
-/

namespace CBCL

open CBCL.Lattice (Set)
open scoped CBCL.Lattice

/-! ## `CausedBy` — three causal patterns mirroring Rust `CausedBy`. -/

/-- The `:caused-by` field of a CBCL message (mirrors Rust
    `crates/cbcl-core/src/message.rs::CausedBy`).

    * `begin`        — `:caused-by begin` (root of a causal chain).
    * `single h`     — `:caused-by <hash>` (one predecessor).
    * `multiple hs`  — `:caused-by (h1 h2 ...)` (fan-in). -/
inductive CausedBy where
  | begin    : CausedBy
  | single   : ContentHash → CausedBy
  | multiple : List ContentHash → CausedBy

/-! ## `CausalProtocol` — the abstract predecessor pattern. -/

/-- Abstract causal protocol predecessor pattern. Mirrors the structure
    of Rust `NodeRef` (Single | Any | All) but lifts `Begin` to a
    top-level constructor per SPEC-005 Open Question §1.

    Recursive: `any` and `all` take *lists of patterns*, so the verify
    theorems can be stated structurally over the pattern algebra
    (REQ-513's `(all p₁ ... pₙ)` is `verify` distributed over the list
    via `meet`). -/
inductive CausalProtocol where
  | begin  : CausalProtocol
  | single : String → CausalProtocol
  | any    : List CausalProtocol → CausalProtocol
  | all    : List CausalProtocol → CausalProtocol

/-! ## `Performative.toName` — surface-syntax name of a performative. -/

/-- Surface-syntax name of a performative (mirrors Rust
    `Performative::name()` in `crates/cbcl-core/src/message.rs`). -/
def Performative.toName : Performative → String
  | .core .tell    => "tell"
  | .core .ask     => "ask"
  | .core .reply   => "reply"
  | .core .error   => "error"
  | .core .ok      => "ok"
  | .core .cancel  => "cancel"
  | .core .hello   => "hello"
  | .core .bye     => "bye"
  | .custom s      => s

/-! ## Abstract `Message.causedBy` accessor.

    Declared as an `axiom` because the existing `CBCL.Message` does not
    carry a structured `:caused-by` field; concrete extraction from
    `params` is deferred to the parser-side mechanisation. See module
    docstring above. -/
axiom Message.causedBy : Message → Option CausedBy

/-! ## `verify` — the function REQ-512/513/514 quantify over. -/

open VerificationResult MessageStore

/-- Verify a message against a causal protocol predecessor pattern,
    given a message store (mirrors `verify_causal` in
    `crates/cbcl-core/src/protocol.rs`).

    Match-arm structure:
    * `begin`         — `:caused-by` must be `begin`; otherwise Violation.
    * `single perf`   — `:caused-by` must be a single hash whose
                         predecessor exists in the store with the named
                         performative; missing predecessor ⇒ Unknown,
                         wrong type ⇒ Violation.
    * `any ps`        — disjunctive fold under `join` (`⊔`); empty list
                         is `unknown` (the `join` identity).
    * `all ps`        — conjunctive fold under `meet` (`⊓`); empty list
                         is `valid` (the `meet` identity). This is the
                         shape that REQ-513's lattice-homomorphism
                         theorem matches `rfl`-cleanly.

    `noncomputable` because `MessageStore.lookup` is classical
    (Open Question §3). The deferred `LookupSpec` task will eventually
    provide a computable refinement; the REQ-512/513/514 theorems do
    not depend on computability. -/
noncomputable def verify : Message → CausalProtocol → MessageStore → VerificationResult
  | m, .begin, _ =>
      match Message.causedBy m with
      | some .begin => .valid
      | _           => .violation
  | m, .single perf, S =>
      match Message.causedBy m with
      | some (.single h) =>
          match MessageStore.lookup h S with
          | some pred =>
              if pred.performative.toName = perf then .valid else .violation
          | none      => .unknown
      | _ => .violation
  | m, .any ps, S =>
      ps.foldr (fun p acc => (verify m p S).join acc) .unknown
  | m, .all ps, S =>
      ps.foldr (fun p acc => (verify m p S).meet acc) .valid

/-! ## REQ-512 / CON-512 — `verify` monotonicity under store growth.

    The central monotonicity theorem for SPEC-005. As the message store
    grows, the verification result can only move *up* in the
    `VerificationResult.le` (`⊑`) order — i.e. once a verification
    has reached `valid`, store growth never overturns it. See the
    docstring on `VerificationResult.le` in `Lattice/Result.lean` for
    why "`valid` is sticky" is the order that makes monotonicity hold
    through arbitrary nestings of `(any …)` inside `(all …)`. -/

open VerificationResult (le_refl unknown_le violation_le meet_mono join_mono)
open scoped VerificationResult

/-- **REQ-512 / CON-512:** `verify` is monotone in the message store
    under the SPEC-003 verification-result order.

    The proof is a well-founded recursion on `sizeOf P`, with case
    analysis over the `verify` match arms:

    * `.begin` — the result is independent of the store, so refl.
    * `.single perf` — splits on the message's `:caused-by` and on the
      result of `MessageStore.lookup`; the only store-sensitive case
      is `lookup S₁ = none` (result `unknown`), which is `unknown ⊑ x`
      for every `x`. The case `lookup S₁ = some pred` discharges via
      `MessageStore.lookup_monotone`, giving `lookup S₂ = some pred`
      (the same witness, by injectivity), so both stores produce the
      same result.
    * `.any ps` — induction on `ps`. Empty list folds to `unknown`,
      monotone. Cons step combines the per-element monotonicity
      (the recursive call at `p`, structurally smaller than `.any ps`)
      with the rest's IH via `join_mono`.
    * `.all ps` — symmetric to `.any`, with `meet_mono`. -/
theorem verify_monotone (M : Message) :
    ∀ (P : CausalProtocol) (S₁ S₂ : MessageStore), S₁ ⊆ S₂ →
    verify M P S₁ ⊑ verify M P S₂
  | .begin, _, _, _ => by
      simp only [verify]
      cases Message.causedBy M with
      | none => exact le_refl _
      | some c => cases c <;> exact le_refl _
  | .single perf, S₁, S₂, hSub => by
      simp only [verify]
      cases Message.causedBy M with
      | none => exact le_refl _
      | some c =>
          cases c with
          | begin => exact le_refl _
          | multiple _ => exact le_refl _
          | single h =>
              -- Inner `match` on `lookup h S` differs between S₁ / S₂.
              dsimp only
              cases hL1 : MessageStore.lookup h S₁ with
              | some pred₁ =>
                  -- `lookup_monotone` carries the witness over to S₂.
                  have hL2 : MessageStore.lookup h S₂ = some pred₁ :=
                    MessageStore.lookup_monotone hSub h pred₁ hL1
                  rw [hL2]
                  dsimp only
                  exact le_refl _
              | none =>
                  -- S₁ side reduces to `unknown`. S₂ side is `unknown`
                  -- (when lookup also fails) or `valid`/`violation`
                  -- (when lookup succeeds). `unknown ⊑ _` holds for
                  -- every right-hand side.
                  dsimp only
                  cases hL2 : MessageStore.lookup h S₂ with
                  | none => dsimp only; exact le_refl _
                  | some pred₂ => dsimp only; split <;> exact unknown_le _
  | .any [], _, _, _ => by
      simp only [verify, List.foldr]; exact le_refl _
  | .any (p :: rest), S₁, S₂, hSub => by
      have eq1 :
          verify M (.any (p :: rest)) S₁
            = (verify M p S₁).join (verify M (.any rest) S₁) := by
        simp only [verify, List.foldr]
      have eq2 :
          verify M (.any (p :: rest)) S₂
            = (verify M p S₂).join (verify M (.any rest) S₂) := by
        simp only [verify, List.foldr]
      rw [eq1, eq2]
      exact join_mono
        (verify_monotone M p S₁ S₂ hSub)
        (verify_monotone M (.any rest) S₁ S₂ hSub)
  | .all [], _, _, _ => by
      simp only [verify, List.foldr]; exact le_refl _
  | .all (p :: rest), S₁, S₂, hSub => by
      have eq1 :
          verify M (.all (p :: rest)) S₁
            = (verify M p S₁).meet (verify M (.all rest) S₁) := by
        simp only [verify, List.foldr]
      have eq2 :
          verify M (.all (p :: rest)) S₂
            = (verify M p S₂).meet (verify M (.all rest) S₂) := by
        simp only [verify, List.foldr]
      rw [eq1, eq2]
      exact meet_mono
        (verify_monotone M p S₁ S₂ hSub)
        (verify_monotone M (.all rest) S₁ S₂ hSub)
termination_by P _ _ _ => sizeOf P
decreasing_by all_goals (simp_wf; omega)

/-! ## REQ-513 / CON-513 — fan-in lattice-homomorphism. -/

/-- **REQ-513 / CON-513:** `verify` distributes over `(all ps)` as the
    `meet`-fold of per-predecessor results, with `⊤ = valid` as the
    fold seed. This is the structural form that lets eventual
    consistency (REQ-514) follow via lattice-homomorphism rather than
    re-induction over the predecessor list.

    Proof: the `.all` arm of `verify` is *literally* the `foldr` on the
    right-hand side, so `simp only [verify]` fires the auto-generated
    equational lemma; what remains is the `BoundedLattice` typeclass
    projection unfolding to `VerificationResult.meet` / `valid` via the
    SPEC-003 instance (REQ-510), which is `rfl`. The associativity of
    meet promised in TEST-513's technique note is therefore not invoked
    at this level — it is recorded by the `BoundedLattice` instance and
    consumed by the downstream REQ-514 proof, where the fold is rotated
    to obtain `S₁ ∪ S₂` from `S₁` and `S₂`. -/
theorem verify_all_is_meet :
    ∀ (M : Message) (preds : List CausalProtocol) (S : MessageStore),
      verify M (CausalProtocol.all preds) S
        = preds.foldr (fun p acc => verify M p S ⊓ acc) ⊤ := by
  intro M preds S
  simp only [verify]
  rfl

/-! ## REQ-514 / CON-514 — eventual consistency under store merge.

    The corollary that ties REQ-512 monotonicity to the SPEC-003 G-Set
    merge: when two stores are unioned, the join of their per-store
    verification results sits below the verification result on the
    merged store. This is the lattice-homomorphism shape of "merging
    knowledge can only confirm, never overturn" — neither replica's
    result can disagree with the post-merge result, since the merged
    store is a superset of each side. -/

/-- **REQ-514 / CON-514:** eventual consistency of `verify` under store
    union.

    Proof: each side embeds into the union (`S₁ ⊆ S₁ ∪ S₂` and
    `S₂ ⊆ S₁ ∪ S₂` are definitional `Or.inl` / `Or.inr`), so
    `verify_monotone` lifts each per-store result up to the union;
    `join_mono` combines them, and the right-hand side collapses by
    `join` idempotence on `verify M P (S₁ ∪ S₂)`. -/
theorem verify_eventually_consistent
    (M : Message) (P : CausalProtocol) (S₁ S₂ : MessageStore) :
    (verify M P S₁).join (verify M P S₂) ⊑ verify M P (S₁ ∪ S₂) := by
  have hSub₁ : S₁ ⊆ (S₁ ∪ S₂ : MessageStore) := fun _ ha => Or.inl ha
  have hSub₂ : S₂ ⊆ (S₁ ∪ S₂ : MessageStore) := fun _ ha => Or.inr ha
  have h₁ := verify_monotone M P S₁ (S₁ ∪ S₂) hSub₁
  have h₂ := verify_monotone M P S₂ (S₁ ∪ S₂) hSub₂
  have hmono := join_mono h₁ h₂
  have hidem :
      (verify M P (S₁ ∪ S₂)).join (verify M P (S₁ ∪ S₂))
        = verify M P (S₁ ∪ S₂) := by
    cases verify M P (S₁ ∪ S₂) <;> rfl
  exact hidem ▸ hmono

end CBCL
