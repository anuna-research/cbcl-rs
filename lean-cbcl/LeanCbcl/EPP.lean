/-
  EPP correspondence — Lean mechanization (safety level).

  Mirrors `proofs/epp-correspondence/proof.tex` (the v4 development reviewed SOUND).
  Self-contained: Lean core only (no mathlib / batteries), so a configuration is a
  predicate `Msg → Prop` (content-addressing is modelled by message identity), and all
  reasoning is membership/implication over these predicates.

  Scope of this module: the safety-level correspondence — Local resolvability,
  Reconciliation (as soundness/completeness), glue-closure, the round-trip identities,
  and the projection family's compatibility (proj-compat), assembled into the EPP
  correspondence bijection at the safety level. The completion (P-complete) layer is
  developed in `EPPCompletion.lean`.
-/

namespace LeanCbcl.EPP

/-- A configuration / store / local run: a set of messages, as a predicate. -/
abbrev Cfg (Msg : Type) := Msg → Prop

/-- The protocol-plus-message model.
    `predRel m p` means `p` is a `:caused-by` predecessor of `m`. -/
structure Proto (Role Perf Msg : Type) where
  perf      : Msg → Perf
  sender    : Msg → Role
  recip     : Msg → Role → Prop
  predRel   : Msg → Msg → Prop
  psender   : Perf → Role
  precip    : Perf → Role → Prop
  legalPred : Perf → Perf → Prop
  clauseOK  : Msg → Prop
  /-- R6 clause (vi): causal locality (type level). -/
  causalLocal : ∀ (t t' : Perf) (r : Role),
    legalPred t t' → (psender t = r ∨ precip t r) → (psender t' = r ∨ precip t' r)

variable {Role Perf Msg : Type} (P : Proto Role Perf Msg)

/-- Message-level endpoint of `m` at role `r`. -/
def endpoint (m : Msg) (r : Role) : Prop := P.sender m = r ∨ P.recip m r

/-- Role conformance: `m`'s roles match `P`'s annotations for `τ(m)`. -/
def conformant (m : Msg) : Prop :=
  P.sender m = P.psender (P.perf m) ∧ (∀ r, P.recip m r ↔ P.precip (P.perf m) r)

/-- Every `:caused-by` predecessor of `m` is present in store `S`. -/
def resolved (S : Cfg Msg) (m : Msg) : Prop := ∀ p, P.predRel m p → S p

/-- No spurious predecessors: every named predecessor's type is legal. -/
def noSpurious (m : Msg) : Prop := ∀ p, P.predRel m p → P.legalPred (P.perf m) (P.perf p)

/-- The store-independent part of a `Valid` verdict (def:rolelocal). -/
def good (m : Msg) : Prop := conformant P m ∧ noSpurious P m ∧ P.clauseOK m

/-- `m` is a `Violation` in store `S`: its predecessors are present but it is not good. -/
def violation (S : Cfg Msg) (m : Msg) : Prop := resolved P S m ∧ ¬ good P m

/-- A configuration is causally down-closed. -/
def closedCfg (C : Cfg Msg) : Prop := ∀ m, C m → ∀ p, P.predRel m p → C p

/-- `C` is `P`-safe: no message in it is a `Violation`. -/
def pSafe (C : Cfg Msg) : Prop := ∀ m, C m → ¬ violation P C m

/-- Run projection: the `r`-relevant messages of `C`, retaining raw `caused-by`. -/
def project (C : Cfg Msg) (r : Role) : Cfg Msg := fun m => C m ∧ endpoint P m r

/-- A local run is locally `P`-safe. -/
def localSafe (L : Cfg Msg) : Prop := ∀ m, L m → ¬ violation P L m

/-- In a `P`-safe closed configuration, every present message is `good`. -/
theorem good_of_safe_closed {C : Cfg Msg} (hcl : closedCfg P C) (hsafe : pSafe P C)
    {m : Msg} (hm : C m) : good P m := by
  have hres : resolved P C m := fun p hp => hcl m hm p hp
  exact (Classical.em (good P m)).elim id (fun hg => absurd ⟨hres, hg⟩ (hsafe m hm))

/-- **Local resolvability** (`lem:localres`).
    In a `P`-safe closed configuration of an R6 protocol, every `caused-by` predecessor
    of `m` is `r`-relevant for each endpoint `r` of `m`, hence lies in `project C r`. -/
theorem localres {C : Cfg Msg} (hcl : closedCfg P C) (hsafe : pSafe P C)
    {m : Msg} (hm : C m) {r : Role} (hr : endpoint P m r) :
    ∀ p, P.predRel m p → project P C r p := by
  intro p hp
  have hpC : C p := hcl m hm p hp
  have hgm : good P m := good_of_safe_closed P hcl hsafe hm
  have hgp : good P p := good_of_safe_closed P hcl hsafe hpC
  have hlegal : P.legalPred (P.perf m) (P.perf p) := hgm.2.1 p hp
  have htm : P.psender (P.perf m) = r ∨ P.precip (P.perf m) r := by
    cases hr with
    | inl h => exact Or.inl (by rw [← hgm.1.1]; exact h)
    | inr h => exact Or.inr ((hgm.1.2 r).1 h)
  have htp := P.causalLocal (P.perf m) (P.perf p) r hlegal htm
  have hep : endpoint P p r := by
    cases htp with
    | inl h => exact Or.inl (by rw [hgp.1.1]; exact h)
    | inr h => exact Or.inr ((hgp.1.2 r).2 h)
  exact ⟨hpC, hep⟩

/-- **Soundness** (`thm:epp`(1), safety): each projection of a `P`-safe closed `C` is
    locally `P`-safe. -/
theorem soundness_safety {C : Cfg Msg} (hsafe : pSafe P C) (r : Role) :
    localSafe P (project P C r) := by
  intro m hm hviol
  apply hsafe m hm.1
  exact ⟨fun p hp => (hviol.1 p hp).1, hviol.2⟩

/-- A compatible family of local runs (Agreement is automatic from message identity). -/
structure Family (P : Proto Role Perf Msg) where
  run  : Role → Cfg Msg
  /-- each run holds only `r`-relevant messages -/
  rel  : ∀ r m, run r m → endpoint P m r
  /-- Coverage(a): a message appears in every endpoint's run -/
  covA : ∀ r r' m, run r m → endpoint P m r' → run r' m
  /-- Coverage(b): each run is causally closed -/
  covB : ∀ r m, run r m → ∀ p, P.predRel m p → run r p

/-- Gluing: the union of the family's runs. -/
def glue (F : Family P) : Cfg Msg := fun m => ∃ r, F.run r m

/-- **Glue is closed** (`lem:glue-closed`). -/
theorem glue_closed (F : Family P) : closedCfg P (glue P F) := by
  intro m hm p hp
  obtain ⟨r, hr⟩ := hm
  exact ⟨r, F.covB r m hr p hp⟩

/-- **Completeness** (`thm:epp`(2), safety): gluing a compatible family of locally
    `P`-safe runs yields a `P`-safe (and closed) configuration. -/
theorem completeness_safety (F : Family P) (hLS : ∀ r, localSafe P (F.run r)) :
    pSafe P (glue P F) ∧ closedCfg P (glue P F) := by
  refine ⟨?_, glue_closed P F⟩
  intro m hm hviol
  obtain ⟨r, hr⟩ := hm
  apply hLS r m hr
  exact ⟨fun p hp => F.covB r m hr p hp, hviol.2⟩

/-- Round-trip, part 1: `glue (project C) = C` (set-level; needs no hypotheses). -/
theorem glue_project_eq {C : Cfg Msg} (m : Msg) :
    (∃ r, project P C r m) ↔ C m := by
  constructor
  · intro h; obtain ⟨_, hCm, _⟩ := h; exact hCm
  · intro hCm; exact ⟨P.sender m, hCm, Or.inl rfl⟩

/-- Round-trip, part 2: `project (glue F) r = run r`. -/
theorem project_glue_eq (F : Family P) (r : Role) (m : Msg) :
    project P (glue P F) r m ↔ F.run r m := by
  constructor
  · intro h
    obtain ⟨⟨r', hr'⟩, hep⟩ := h
    exact F.covA r' r m hr' hep
  · intro h
    exact ⟨⟨r, h⟩, F.rel r m h⟩

/-- **Projection family is compatible** (`lem:proj-compat`). -/
def projFamily {C : Cfg Msg} (hcl : closedCfg P C) (hsafe : pSafe P C) : Family P where
  run  := fun r => project P C r
  rel  := fun _ _ hm => hm.2
  covA := fun _ _ _ hm hep => ⟨hm.1, hep⟩
  covB := fun _ _ hm p hp => localres P hcl hsafe hm.1 hm.2 p hp

/-- **EPP correspondence** (safety level), bundling soundness, completeness, and the
    round-trip identities that make `project`/`glue` mutually inverse. -/
theorem epp_correspondence {C : Cfg Msg} (hcl : closedCfg P C) (hsafe : pSafe P C) :
    (∀ r, localSafe P (project P C r)) ∧
    (pSafe P (glue P (projFamily P hcl hsafe)) ∧ closedCfg P (glue P (projFamily P hcl hsafe))) ∧
    (∀ m, glue P (projFamily P hcl hsafe) m ↔ C m) := by
  refine ⟨fun r => soundness_safety P hsafe r, ?_, ?_⟩
  · exact completeness_safety P (projFamily P hcl hsafe)
      (fun r => soundness_safety P hsafe r)
  · intro m
    -- glue (projFamily) m = (∃ r, project C r m) ↔ C m
    exact glue_project_eq P m

end LeanCbcl.EPP

