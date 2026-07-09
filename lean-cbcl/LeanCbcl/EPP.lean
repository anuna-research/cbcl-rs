/-
  EPP correspondence — Lean mechanization (safety level), faithful verdict model.

  Mirrors `proofs/epp-correspondence/proof.tex`. Self-contained: Lean core only (no
  mathlib / batteries); a configuration is a predicate `Msg → Prop`.

  This version models the genuine THREE-VALUED verdict (`Unknown`/`Valid`/`Violation`)
  as a STORE-DEPENDENT function: a message's clause is evaluated over the predecessor
  *types actually present in the store* (`predTypesPresent`), not a constant. Unknown is
  "a referenced predecessor is absent"; once every referenced predecessor is present the
  verdict is decided, and -- because `caused-by` references are fixed and the store is
  append-only -- both `Valid` and `Violation` are permanent (Proposition mono). The
  reconciliation lemmas establish genuine *verdict equality* (all three of
  Unknown/Valid/Violation agree) between the global store and a projection / gluing, from
  which soundness, completeness, and exactness follow.
-/

namespace LeanCbcl.EPP

/-- A configuration / store / local run. -/
abbrev Cfg (Msg : Type) := Msg → Prop

/-- The three verdicts. -/
inductive Verdict where
  | unknown | valid | violation

/-- The protocol-plus-message model. `predRel m p`: `p` is a `:caused-by` predecessor of
    `m`. `clause t present` is the protocol's predecessor clause for performative `t`
    evaluated against the set `present` of predecessor types currently available
    (this is where `(any)` = "some named type present", `(all)` = "all named types
    present" live). -/
structure Proto (Role Perf Msg : Type) where
  /-- The performative (message type) of a message. -/
  perf      : Msg → Perf
  /-- The sender role of a message. -/
  sender    : Msg → Role
  /-- `recip m r`: role `r` is a recipient of message `m`. -/
  recip     : Msg → Role → Prop
  /-- `predRel m p`: `p` is a `:caused-by` predecessor of `m`. -/
  predRel   : Msg → Msg → Prop
  /-- The protocol-declared sender role of a performative. -/
  psender   : Perf → Role
  /-- `precip t r`: role `r` is a protocol-declared recipient of performative `t`. -/
  precip    : Perf → Role → Prop
  /-- `legalPred t t'`: performative `t'` is a legal predecessor type for `t`. -/
  legalPred : Perf → Perf → Prop
  /-- `clause t present`: the protocol's predecessor clause for performative `t`, evaluated
      against the set `present` of predecessor types currently available. -/
  clause    : Perf → (Perf → Prop) → Prop
  /-- R6 clause (vi): causal locality (type level). -/
  causalLocal : ∀ (t t' : Perf) (r : Role),
    legalPred t t' → (psender t = r ∨ precip t r) → (psender t' = r ∨ precip t' r)

variable {Role Perf Msg : Type} (P : Proto Role Perf Msg)

/-- Message-level endpoint. -/
def endpoint (m : Msg) (r : Role) : Prop := P.sender m = r ∨ P.recip m r

/-- Role conformance. -/
def conformant (m : Msg) : Prop :=
  P.sender m = P.psender (P.perf m) ∧ (∀ r, P.recip m r ↔ P.precip (P.perf m) r)

/-- Every `:caused-by` predecessor of `m` is present in store `S`. -/
def resolved (S : Cfg Msg) (m : Msg) : Prop := ∀ p, P.predRel m p → S p

/-- The predecessor *types* of `m` that are present in store `S`. -/
def predTypesPresent (S : Cfg Msg) (m : Msg) : Perf → Prop :=
  fun t => ∃ p, P.predRel m p ∧ S p ∧ P.perf p = t

/-- No spurious predecessors: every named predecessor's type is legal. -/
def noSpurious (m : Msg) : Prop := ∀ p, P.predRel m p → P.legalPred (P.perf m) (P.perf p)

/-- Store-dependent goodness: conformance, no spurious predecessors, and the clause
    satisfied by the predecessor types *present in `S`*. -/
def good (S : Cfg Msg) (m : Msg) : Prop :=
  conformant P m ∧ noSpurious P m ∧ P.clause (P.perf m) (predTypesPresent P S m)

/-- The three verdicts as predicates (they partition: classically exactly one holds). -/
def isUnknown   (S : Cfg Msg) (m : Msg) : Prop := ¬ resolved P S m
/-- `m` is `Valid` in store `S`: every referenced predecessor is present and `m` is `good`. -/
def isValid     (S : Cfg Msg) (m : Msg) : Prop := resolved P S m ∧ good P S m
/-- `m` is a `Violation` in store `S`: every referenced predecessor is present but `m` is not `good`. -/
def isViolation (S : Cfg Msg) (m : Msg) : Prop := resolved P S m ∧ ¬ good P S m

/-- Causally down-closed configuration. -/
def closedCfg (C : Cfg Msg) : Prop := ∀ m, C m → ∀ p, P.predRel m p → C p
/-- `C` is `P`-safe: no message in it is a `Violation`. -/
def pSafe (C : Cfg Msg) : Prop := ∀ m, C m → ¬ isViolation P C m
/-- Run projection: `r`-relevant messages of `C`, keeping raw `caused-by`. -/
def project (C : Cfg Msg) (r : Role) : Cfg Msg := fun m => C m ∧ endpoint P m r
/-- A local run is locally `P`-safe. -/
def localSafe (L : Cfg Msg) : Prop := ∀ m, L m → ¬ isViolation P L m

/-- **Monotonicity (Proposition mono).** Both `Valid` and `Violation` are stable under
    store growth; only `Unknown` may change. Key fact: once every referenced predecessor
    is present, `predTypesPresent` is fixed (the predecessors are fixed), so the verdict
    cannot change. -/
theorem predTypesPresent_mono {S S' : Cfg Msg} (hSS : ∀ m, S m → S' m)
    {m : Msg} (hres : resolved P S m) :
    predTypesPresent P S m = predTypesPresent P S' m := by
  funext t
  apply propext
  constructor
  · intro h; obtain ⟨p, hpr, hSp, he⟩ := h; exact ⟨p, hpr, hSS p hSp, he⟩
  · intro h; obtain ⟨p, hpr, _, he⟩ := h; exact ⟨p, hpr, hres p hpr, he⟩

theorem valid_stable {S S' : Cfg Msg} (hSS : ∀ m, S m → S' m) {m : Msg}
    (hv : isValid P S m) : isValid P S' m := by
  obtain ⟨hres, hc, hns, hcl⟩ := hv
  refine ⟨fun p hp => hSS p (hres p hp), hc, hns, ?_⟩
  rwa [← predTypesPresent_mono P hSS hres]

theorem violation_stable {S S' : Cfg Msg} (hSS : ∀ m, S m → S' m) {m : Msg}
    (hv : isViolation P S m) : isViolation P S' m := by
  obtain ⟨hres, hng⟩ := hv
  have hres' : resolved P S' m := fun p hp => hSS p (hres p hp)
  refine ⟨hres', ?_⟩
  intro hg'
  apply hng
  obtain ⟨hc, hns, hcl'⟩ := hg'
  exact ⟨hc, hns, by rwa [predTypesPresent_mono P hSS hres]⟩

/-- In a `P`-safe closed configuration every present message is `good`. -/
theorem good_of_safe_closed {C : Cfg Msg} (hcl : closedCfg P C) (hsafe : pSafe P C)
    {m : Msg} (hm : C m) : good P C m := by
  have hres : resolved P C m := fun p hp => hcl m hm p hp
  exact (Classical.em (good P C m)).elim id (fun hg => absurd ⟨hres, hg⟩ (hsafe m hm))

/-- **Local resolvability** (`lem:localres`): every `caused-by` predecessor of `m` is
    `r`-relevant, hence in `project C r`, for each endpoint `r` of `m`. -/
theorem localres {C : Cfg Msg} (hcl : closedCfg P C) (hsafe : pSafe P C)
    {m : Msg} (hm : C m) {r : Role} (hr : endpoint P m r) :
    ∀ p, P.predRel m p → project P C r p := by
  intro p hp
  have hpC : C p := hcl m hm p hp
  have hgm : good P C m := good_of_safe_closed P hcl hsafe hm
  have hgp : good P C p := good_of_safe_closed P hcl hsafe hpC
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

/-- The present predecessor types of `m` coincide between `C` and `project C r`. -/
theorem predTypesPresent_proj {C : Cfg Msg} (hcl : closedCfg P C) (hsafe : pSafe P C)
    {r : Role} {m : Msg} (hm : project P C r m) :
    predTypesPresent P (project P C r) m = predTypesPresent P C m := by
  funext t
  apply propext
  constructor
  · intro h; obtain ⟨p, hpr, hpp, he⟩ := h; exact ⟨p, hpr, hpp.1, he⟩
  · intro h; obtain ⟨p, hpr, _, he⟩ := h
    exact ⟨p, hpr, localres P hcl hsafe hm.1 hm.2 p hpr, he⟩

theorem good_proj {C : Cfg Msg} (hcl : closedCfg P C) (hsafe : pSafe P C)
    {r : Role} {m : Msg} (hm : project P C r m) :
    good P (project P C r) m = good P C m := by
  unfold good
  rw [predTypesPresent_proj P hcl hsafe hm]

theorem resolved_proj {C : Cfg Msg} (hcl : closedCfg P C) (hsafe : pSafe P C)
    {r : Role} {m : Msg} (hm : project P C r m) :
    resolved P (project P C r) m ↔ resolved P C m := by
  constructor
  · intro h p hp; exact (h p hp).1
  · intro _ p hp; exact localres P hcl hsafe hm.1 hm.2 p hp

/-- **Reconciliation (verdict equality)** (`lem:reconcile`(i)): the global and the
    projected store assign `m` the *same* verdict -- all three of Unknown / Valid /
    Violation agree. -/
theorem reconcile_global {C : Cfg Msg} (hcl : closedCfg P C) (hsafe : pSafe P C)
    {r : Role} {m : Msg} (hm : project P C r m) :
    (isUnknown P (project P C r) m ↔ isUnknown P C m) ∧
    (isValid   P (project P C r) m ↔ isValid   P C m) ∧
    (isViolation P (project P C r) m ↔ isViolation P C m) := by
  have hres := resolved_proj P hcl hsafe hm
  have hg := good_proj P hcl hsafe hm
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨fun h h2 => h (hres.2 h2), fun h h2 => h (hres.1 h2)⟩
  · exact ⟨fun ⟨a, b⟩ => ⟨hres.1 a, hg ▸ b⟩, fun ⟨a, b⟩ => ⟨hres.2 a, hg ▸ b⟩⟩
  · exact ⟨fun ⟨a, b⟩ => ⟨hres.1 a, hg ▸ b⟩, fun ⟨a, b⟩ => ⟨hres.2 a, hg ▸ b⟩⟩

/-- **Soundness** (`thm:epp`(1), safety). -/
theorem soundness_safety {C : Cfg Msg} (hcl : closedCfg P C) (hsafe : pSafe P C)
    (r : Role) : localSafe P (project P C r) := by
  intro m hm hviol
  exact hsafe m hm.1 ((reconcile_global P hcl hsafe hm).2.2.1 hviol)

/-- A compatible family of local runs. -/
structure Family (P : Proto Role Perf Msg) where
  /-- `run r` is role `r`'s local run (store). -/
  run  : Role → Cfg Msg
  rel  : ∀ r m, run r m → endpoint P m r
  covA : ∀ r r' m, run r m → endpoint P m r' → run r' m
  covB : ∀ r m, run r m → ∀ p, P.predRel m p → run r p

/-- Gluing: the union of the family's runs. -/
def glue (F : Family P) : Cfg Msg := fun m => ∃ r, F.run r m

theorem glue_closed (F : Family P) : closedCfg P (glue P F) := by
  intro m hm p hp
  obtain ⟨r, hr⟩ := hm
  exact ⟨r, F.covB r m hr p hp⟩

/-- Present predecessor types coincide between a run and the glued store. -/
theorem predTypesPresent_glue (F : Family P) {r : Role} {m : Msg} (hr : F.run r m) :
    predTypesPresent P (F.run r) m = predTypesPresent P (glue P F) m := by
  funext t
  apply propext
  constructor
  · intro h; obtain ⟨p, hpr, hpp, he⟩ := h; exact ⟨p, hpr, ⟨r, hpp⟩, he⟩
  · intro h; obtain ⟨p, hpr, _, he⟩ := h; exact ⟨p, hpr, F.covB r m hr p hpr, he⟩

theorem good_glue (F : Family P) {r : Role} {m : Msg} (hr : F.run r m) :
    good P (F.run r) m = good P (glue P F) m := by
  unfold good
  rw [predTypesPresent_glue P F hr]

/-- Verdict equality between a run and the glued store (validity side). -/
theorem reconcile_glue (F : Family P) {r : Role} {m : Msg} (hr : F.run r m) :
    isValid P (F.run r) m ↔ isValid P (glue P F) m := by
  have hg := good_glue P F hr
  constructor
  · intro h; exact ⟨fun p hp => ⟨r, F.covB r m hr p hp⟩, hg ▸ h.2⟩
  · intro h; exact ⟨fun p hp => F.covB r m hr p hp, hg.symm ▸ h.2⟩

/-- **Completeness** (`thm:epp`(2), safety): gluing a compatible family of locally
    `P`-safe runs yields a `P`-safe, closed configuration. -/
theorem completeness_safety (F : Family P) (hLS : ∀ r, localSafe P (F.run r)) :
    pSafe P (glue P F) ∧ closedCfg P (glue P F) := by
  refine ⟨?_, glue_closed P F⟩
  intro m hm hviol
  obtain ⟨r, hr⟩ := hm
  apply hLS r m hr
  obtain ⟨hres, hng⟩ := hviol
  refine ⟨fun p hp => F.covB r m hr p hp, ?_⟩
  rw [good_glue P F hr]; exact hng

/-- Round-trip, part 1: `glue (project C) = C` (set level). -/
theorem glue_project_eq {C : Cfg Msg} (m : Msg) :
    (∃ r, project P C r m) ↔ C m := by
  constructor
  · intro h; obtain ⟨_, hCm, _⟩ := h; exact hCm
  · intro hCm; exact ⟨P.sender m, hCm, Or.inl rfl⟩

/-- Round-trip, part 2: `project (glue F) r = run r`. -/
theorem project_glue_eq (F : Family P) (r : Role) (m : Msg) :
    project P (glue P F) r m ↔ F.run r m := by
  constructor
  · intro h; obtain ⟨⟨r', hr'⟩, hep⟩ := h; exact F.covA r' r m hr' hep
  · intro h; exact ⟨⟨r, h⟩, F.rel r m h⟩

/-- **Projection family is compatible** (`lem:proj-compat`). -/
def projFamily {C : Cfg Msg} (hcl : closedCfg P C) (hsafe : pSafe P C) : Family P where
  run  := fun r => project P C r
  rel  := fun _ _ hm => hm.2
  covA := fun _ _ _ hm hep => ⟨hm.1, hep⟩
  covB := fun _ _ hm p hp => localres P hcl hsafe hm.1 hm.2 p hp

/-- **EPP correspondence** (safety level): soundness, completeness, round-trip. -/
theorem epp_correspondence {C : Cfg Msg} (hcl : closedCfg P C) (hsafe : pSafe P C) :
    (∀ r, localSafe P (project P C r)) ∧
    (pSafe P (glue P (projFamily P hcl hsafe)) ∧
       closedCfg P (glue P (projFamily P hcl hsafe))) ∧
    (∀ m, glue P (projFamily P hcl hsafe) m ↔ C m) := by
  refine ⟨fun r => soundness_safety P hcl hsafe r, ?_, ?_⟩
  · exact completeness_safety P (projFamily P hcl hsafe)
      (fun r => soundness_safety P hcl hsafe r)
  · intro m; exact glue_project_eq P m

end LeanCbcl.EPP
