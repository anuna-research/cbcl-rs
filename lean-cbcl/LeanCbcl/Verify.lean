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
constructor or desugared as `all []` (vacuous fan-in). Per the
`task-verify-skeleton` brief, we pick the top-level constructor for
proof simplicity: monotonicity case-analysis is trivial for `begin` (no
store dependence) and the desugaring complicates the `(all ...)`
homomorphism statement of REQ-513.

## Mirrors

The verification function mirrors `verify_causal` in
`crates/cbcl-core/src/protocol.rs` (no dedicated `verify.rs` file
exists in the Rust tree — protocol verification lives alongside the
`CausalProtocol` data model). The match-arm structure of
`verify_causal` (single → store lookup; multiple → fan-in meet;
begin → constant Valid; missing-caused-by → Violation) is preserved
here.

Pinned commit SHA at time of mirroring: `3bde18c5e7b9f790d342aecce871823b35cef8de`
(branch `hence/verify-skeleton-v1`, parent of this task's first commit).

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

end CBCL
