/-
  Splicing necessity / type-opacity — Lean mechanization.

  A crisp NECESSITY companion to `LeanCbcl.Projectability`. It answers reviewers
  who called R6(vi) causal locality "thin / a sidestep": the sidestep is FORCED.
  Envelope-widened observation (delivering a predecessor as a full message or a
  type-tagged envelope, i.e. *the predecessor itself in the store*) is the weakest
  sound coordination-free condition under which every `r`-relevant verdict decides;
  content-addressing (a bare `:caused-by` hash) buys nothing here, because a content
  hash is TYPE-OPAQUE.

  ## Definitions reused (stated, not re-proved)

  From `LeanCbcl/EPP.lean` (`namespace LeanCbcl.EPP`):
  * `Cfg Msg := Msg → Prop` — a configuration / store / local run (append-only set).
  * `Verdict` — the three verdicts `unknown | valid | violation`.
  * `endpoint P m r := P.sender m = r ∨ P.recip m r` — `m` is `r`-relevant.
  * `resolved P S m := ∀ p, P.predRel m p → S p` — every cited predecessor present.
  * `predTypesPresent P S m := fun t => ∃ p, P.predRel m p ∧ S p ∧ P.perf p = t`
    — the predecessor *types* visible in the store (this is where a predecessor's
    TYPE enters the verdict; a predecessor absent from the store contributes no type).
  * `good P S m` — conformance ∧ no-spurious-preds ∧ the clause satisfied by
    `predTypesPresent`.
  * `isUnknown P S m := ¬ resolved P S m`,
    `isValid P S m := resolved P S m ∧ good P S m`,
    `isViolation P S m := resolved P S m ∧ ¬ good P S m`.
  * `closedCfg`, `pSafe`, `project P C r := fun m => C m ∧ endpoint P m r`.
  * `localres` — under `causalLocal`, every predecessor of an `r`-relevant message
    is itself `r`-relevant, hence in `project P C r`.

  From `LeanCbcl/Verify.lean` (`namespace CBCL`), the operational meaning of
  "resolve a predecessor" that the abstract `resolved` mirrors:
  * `verify m (.single perf) S` matches the message's `:caused-by` hash `h`, then
    does `MessageStore.lookup h S`; `lookup h S = none ⇒ .unknown`. So a bare
    `:caused-by` hash with NO message in the store does NOT resolve — it yields
    `Unknown`, exactly as `resolved P S m` fails when a cited predecessor `∉ S`.
    Only a predecessor actually *present in the store* (delivered as a full message
    / type-tagged envelope) supplies its performative and lets `verify` reach
    `.valid` / `.violation`. `Verify.lean` also carries axioms (`ContentHash`,
    `Message.causedBy`), so we build on the axiom-clean `EPP` model instead and
    keep to the standard three kernel axioms; the `predRel` citation is the abstract
    "bare hash", and `perf` (the predecessor's type) is precisely what a bare hash
    does NOT expose.

  From `LeanCbcl/Projectability.lean` (`namespace LeanCbcl.Projectability`):
  * `ProtoData` — the fields of `Proto` minus the `causalLocal` proof obligation;
    `…D` notions (`endpointD`, `resolvedD`, `projectD`, `isUnknownD`, `isValidD`,
    `isViolationD`, `closedCfgD`, `pSafeD`, `goodD`, `causalLocality`, `toProto`)
    are definitional copies of the `EPP` notions (bridge lemmas are `Iff.rfl`).
  * `permanently_unknown_of_nonlocal_pred` — if a `:caused-by` predecessor `p` of an
    `r`-relevant `m` is not itself `r`-relevant, `m`'s verdict is `Unknown` in every
    store `r` can reach. This is the lemma the results below repackage as necessity.

  Nothing here adds an axiom: `#print axioms` on each headline theorem reports only
  `propext, Classical.choice, Quot.sound`.
-/
import LeanCbcl.Projectability
import Batteries.Tactic.Lint  -- provides the `@[nolint …]` attribute

namespace LeanCbcl.Splice

open LeanCbcl.EPP
open LeanCbcl.Projectability

/-! ## 1. Type-opacity indistinguishability (the centerpiece)

Two worlds that role `r` cannot tell apart — `r` holds the same messages and the
same set of `:caused-by` hash-commitments (`predRel`) in both — yet an `r`-relevant
message `m` receives DIFFERENT global verdicts, `Valid` vs `Violation`, because the
worlds differ ONLY in the TYPE (`perf`) of an unheld predecessor `b` that occupies
the same causal position (same hash citation). Conclusion: no function of `r`'s full
observation (its held messages, those messages' types — `heldTypes` — and the bare
hashes they cite) computes `m`'s verdict — content-addressing does not confer
branch/type recovery.

The two worlds are two `ProtoData` differing only in the `perf` field at `b`. This
faithfully models "same hash, different preimage type": the `:caused-by` citation
(`predRel`) is identical (the bare hash `r` holds), while the preimage's performative
(`perf b`, which `r` never holds) differs. World 1 is a `P`-safe closed run in which
`m` is `Valid`; world 2 differs only in `b`'s type and makes `m` a `Violation`.
(Both worlds being globally `P`-safe with a `Valid`/`Violation` split is impossible —
`pSafe` forbids the violation outright — which is itself the point: `r` cannot locally
distinguish the safe world from the unsafe one, since the only difference is a
bystander's type.) -/

namespace Example

/-- The two roles of the worked splice example: recipient `rR` and observer `rO`. -/
inductive SRole | rR | rO
/-- The three performative/message types: the message `tM`, its demanded
    predecessor `tG`, and the bystander type `tB`. -/
inductive SPerf | tM | tG | tB
/-- The two concrete messages: `m` (the message under scrutiny) and `b`
    (its cited predecessor / bystander). -/
inductive SMsg  | m  | b

/-- Shared fields (identical in both worlds). `m : rR → ·` of type `tM`, cited by the
    bystander `b : rO → ·`; the clause of `tM` demands a present predecessor of type
    `tG`. -/
def sSender  : SMsg → SRole            | .m => .rR | .b => .rO
/-- The recipient relation of the example: empty (no message has a recipient here). -/
@[nolint unusedArguments]  -- empty relation (constant `False`); the message/role
                           -- arguments are the relation's domain, unused by design.
def sRecip   : SMsg → SRole → Prop   := fun _ _ => False
/-- Predecessor relation: `m` cites `b` (`x = m ∧ y = b`). -/
def sPredRel : SMsg → SMsg → Prop    := fun x y => x = .m ∧ y = .b
/-- The sender role attached to each performative type. -/
def sPsender : SPerf → SRole           | .tM => .rR | .tG => .rO | .tB => .rO
/-- The predicate-recipient relation on performative types: empty by design. -/
@[nolint unusedArguments]  -- empty relation (constant `False`); the perf/role
                           -- arguments are the relation's domain, unused by design.
def sPrecip  : SPerf → SRole → Prop  := fun _ _ => False
/-- Legal-predecessor relation on types: `tM` legally demands `tG`. -/
def sLegal   : SPerf → SPerf → Prop  := fun t t' => t = .tM ∧ t' = .tG
/-- Conformance clause: type `tM` requires a present predecessor of type `tG`. -/
def sClause  : SPerf → (SPerf → Prop) → Prop := fun t present => t = .tM → present .tG

/-- The ONLY differing field: `b`'s type. World 1 gives `b` the expected type `tG`. -/
def sPerf1 : SMsg → SPerf | .m => .tM | .b => .tG
/-- World 2 gives the same-hash preimage `b` the type `tB`. -/
def sPerf2 : SMsg → SPerf | .m => .tM | .b => .tB

/-- World 1. -/
def D₁ : ProtoData SRole SPerf SMsg where
  perf := sPerf1; sender := sSender; recip := sRecip; predRel := sPredRel
  psender := sPsender; precip := sPrecip; legalPred := sLegal; clause := sClause
/-- World 2 — identical to `D₁` except `perf b = tB` rather than `tG`. -/
def D₂ : ProtoData SRole SPerf SMsg where
  perf := sPerf2; sender := sSender; recip := sRecip; predRel := sPredRel
  psender := sPsender; precip := sPrecip; legalPred := sLegal; clause := sClause

/-- The global run: both messages have occurred (same set in both worlds). -/
def Cfull : Cfg SMsg := fun _ => True

/-- `b` is not `rR`-relevant: `rR` neither sends nor receives it. -/
theorem b_unheld : ¬ D₁.endpointD .b .rR :=
  fun h => h.elim (fun h' => SRole.noConfusion h') id

/-- `m` is `good` in world 1: `b` is present with the demanded type `tG`. -/
theorem good_m_D₁ : D₁.goodD Cfull .m :=
  ⟨⟨rfl, fun _ => Iff.rfl⟩,
   (fun _ hp => by obtain ⟨_, rfl⟩ := hp; exact ⟨rfl, rfl⟩),
   (fun _ => ⟨.b, ⟨rfl, rfl⟩, trivial, rfl⟩)⟩

/-- `b` is `good` in world 1 (it cites nothing; its clause is vacuous). -/
theorem good_b_D₁ : D₁.goodD Cfull .b :=
  ⟨⟨rfl, fun _ => Iff.rfl⟩,
   (fun _ hp => absurd hp.1 (fun h => SMsg.noConfusion h)),
   (fun h => SPerf.noConfusion h)⟩

/-- World 1 is closed and `P`-safe: the `Unknown` `rR` sees is a pure knowledge gap. -/
theorem closed_D₁ : D₁.closedCfgD Cfull := fun _ _ _ _ => trivial
theorem closed_D₂ : D₂.closedCfgD Cfull := fun _ _ _ _ => trivial

theorem safe_D₁ : D₁.pSafeD Cfull := by
  intro x _ hv
  cases x with
  | m => exact hv.2 good_m_D₁
  | b => exact hv.2 good_b_D₁

/-- In world 1, `m` is `Valid`. -/
theorem m_valid_D₁ : D₁.isValidD Cfull .m := ⟨fun _ _ => trivial, good_m_D₁⟩

/-- In world 2, `m` is NOT `good`: the clause of `tM` demands a present predecessor of
    type `tG`, but `b` — the sole predecessor, same hash as in world 1 — has type `tB`. -/
theorem not_good_m_D₂ : ¬ D₂.goodD Cfull .m := by
  intro hg
  obtain ⟨p, hpr, _, hperf⟩ := hg.2.2 rfl
  obtain ⟨_, rfl⟩ := hpr
  exact SPerf.noConfusion hperf

/-- In world 2, `m` is a `Violation`. -/
theorem m_violation_D₂ : D₂.isViolationD Cfull .m := ⟨fun _ _ => trivial, not_good_m_D₂⟩

/-- Held-message types agree across the two worlds: the only message `rR` holds is `m`,
    and `perf m = tM` in both. (Only `perf b` — an unheld message — differs.) -/
theorem held_types_agree :
    ∀ z, D₁.projectD Cfull .rR z → D₁.perf z = D₂.perf z := by
  intro z hz
  cases z with
  | m => rfl
  | b => exact absurd hz.2 b_unheld

end Example

/-- Role `r`'s *typed observation* of a run: the relation holding of `(z, t)` exactly when
    `r` holds `z` and `z`'s performative is `t`. Together with the held-message set and
    the cited hashes (`predRel`), this is everything `r` observes — unheld messages
    contribute nothing (in particular not their types). -/
def heldTypes {Role Perf Msg : Type} (D : ProtoData Role Perf Msg) (C : Cfg Msg)
    (r : Role) : Msg → Perf → Prop :=
  fun z t => D.projectD C r z ∧ D.perf z = t

namespace Example

/-- The full typed observation of `rR` — held messages *with their types* — is identical
    across the two worlds (pointwise: unheld messages are in neither relation, and the
    single held message `m` has type `tM` in both). -/
theorem heldTypes_eq : heldTypes D₁ Cfull .rR = heldTypes D₂ Cfull .rR := by
  funext z t
  apply propext
  constructor
  · intro ⟨hz, ht⟩
    exact ⟨hz, (held_types_agree z hz) ▸ ht⟩
  · intro ⟨hz, ht⟩
    exact ⟨hz, (held_types_agree z hz).symm ▸ ht⟩

end Example

open Example in
/-- **Type-opacity indistinguishability.** There are two worlds `D₁, D₂` that role `r`
    cannot distinguish — identical held messages (`projectD` equal), identical
    `:caused-by` hash-commitments (`predRel` equal), identical typed observation
    (`heldTypes` equal: held messages *with their performatives*) — differing ONLY in the
    type (`perf`) of the unheld predecessor `b` (same hash citation), such that `m` is
    `Valid` in world 1 (a closed `P`-safe run) and a `Violation` in world 2.
    Consequently NO function of `r`'s full observation — its held messages, those
    messages' types, and the bare hashes they cite — computes `m`'s verdict:
    content-addressing does not confer branch/type recovery. -/
theorem type_opacity_indistinguishability :
    ∃ (Role Perf Msg : Type) (D₁ D₂ : ProtoData Role Perf Msg)
      (C : Cfg Msg) (r : Role) (m b : Msg),
      -- `r`'s observation is identical across the two worlds:
      D₁.projectD C r = D₂.projectD C r ∧                     -- same held messages
      D₁.predRel = D₂.predRel ∧                               -- same `:caused-by` hashes
      heldTypes D₁ C r = heldTypes D₂ C r ∧                   -- same typed observation
      -- they differ only in the TYPE of the unheld predecessor `b`:
      D₁.predRel m b ∧ ¬ D₁.endpointD b r ∧ D₁.perf b ≠ D₂.perf b ∧
      -- world 1 is a closed `P`-safe run in which `m` is `Valid`:
      D₁.closedCfgD C ∧ D₁.pSafeD C ∧ D₁.isValidD C m ∧
      -- world 2 differs only in `b`'s type; there `m` is a `Violation`:
      D₂.closedCfgD C ∧ D₂.isViolationD C m ∧
      -- CONCLUSION: no decider from `r`'s full observation (held messages + their
      -- types + cited hashes) computes the verdict:
      ¬ ∃ f : (Msg → Prop) → (Msg → Perf → Prop) → (Msg → Msg → Prop) → Msg → Verdict,
          (D₁.isValidD C m →
            f (D₁.projectD C r) (heldTypes D₁ C r) D₁.predRel m = Verdict.valid) ∧
          (D₂.isViolationD C m →
            f (D₂.projectD C r) (heldTypes D₂ C r) D₂.predRel m = Verdict.violation) :=
  ⟨SRole, SPerf, SMsg, D₁, D₂, Cfull, .rR, .m, .b,
   rfl, rfl, heldTypes_eq,
   ⟨rfl, rfl⟩, b_unheld, (fun h => SPerf.noConfusion h),
   closed_D₁, safe_D₁, m_valid_D₁,
   closed_D₂, m_violation_D₂,
   by
     rintro ⟨f, h1, h2⟩
     have h1' := h1 m_valid_D₁
     rw [heldTypes_eq] at h1'
     exact Verdict.noConfusion (h1'.symm.trans (h2 m_violation_D₂))⟩

/-! ## 2. Resolution requires the preimage (necessity)

For a `P`-safe closed `C` and an `r`-relevant `m` whose `:caused-by` predecessor `b`
is not `r`-relevant, `m`'s verdict over any reachable store `L ⊆ project C r` is
`Unknown` unless `b ∈ L`. Resolving a spliced predecessor requires the predecessor
ITSELF in the store (delivered as a full message or type-tagged envelope) — never a
bare hash. This is the necessity direction; the sufficiency direction (all cited
predecessors present ⇒ resolves ⇒ not `Unknown`, and `Valid` if additionally `good`)
is equally short and stated below. -/

/-- **Necessity.** Missing the preimage `b` (a cited predecessor) forces `Unknown`:
    for any store `L ⊆ project C r`, if `b ∉ L` then `m`'s verdict is `Unknown`. -/
-- `_hL` (the store is reachable, `L ⊆ project C r`) is retained to state
-- necessity in the same frame as the sufficiency counterpart below and is
-- part of the axiom-audited statement (see AxiomAudit / #print axioms). The
-- proof establishes the stronger fact that a missing preimage forces
-- `Unknown` for *any* store, so `_hL` is unused — kept for statement scope,
-- not deleted (deleting it would change the audited theorem's statement).
@[nolint unusedArguments]
theorem resolution_requires_preimage
    {Role Perf Msg : Type} {D : ProtoData Role Perf Msg}
    {C : Cfg Msg} {r : Role} {m b : Msg} (hpb : D.predRel m b)
    (L : Cfg Msg) (_hL : ∀ z, L z → D.projectD C r z) (hb : ¬ L b) :
    D.isUnknownD L m :=
  fun hres => hb (hres b hpb)

/-- **Sufficiency.** If every cited predecessor of `m` is present in `L`, then `m` is
    resolved — its verdict is not `Unknown`. -/
theorem resolution_of_preds_held
    {Role Perf Msg : Type} {D : ProtoData Role Perf Msg}
    {L : Cfg Msg} {m : Msg} (hheld : ∀ p, D.predRel m p → L p) :
    ¬ D.isUnknownD L m :=
  fun hu => hu hheld

/-- Sufficiency, verdict form: a resolved and `good` message is `Valid`. -/
theorem valid_of_resolved_good
    {Role Perf Msg : Type} {D : ProtoData Role Perf Msg}
    {L : Cfg Msg} {m : Msg} (hres : D.resolvedD L m) (hg : D.goodD L m) :
    D.isValidD L m :=
  ⟨hres, hg⟩

/-- **Permanent `Unknown` for a spliced (non-`r`-relevant) predecessor.** A direct
    reuse of `permanently_unknown_of_nonlocal_pred`: since `b` is not `r`-relevant it
    is never in any reachable `L ⊆ project C r`, so by `resolution_requires_preimage`
    `m`'s verdict is `Unknown` in every store `r` can ever reach — a bare hash never
    resolves it. -/
theorem spliced_pred_permanently_unknown
    {Role Perf Msg : Type} {D : ProtoData Role Perf Msg}
    {C : Cfg Msg} {r : Role} {m b : Msg}
    (hpb : D.predRel m b) (hbr : ¬ D.endpointD b r) :
    ∀ L : Cfg Msg, (∀ z, L z → D.projectD C r z) → D.isUnknownD L m :=
  permanently_unknown_of_nonlocal_pred hpb hbr

/-! ## 2b. Type-openings suffice for the safety verdict (sufficiency, SPEC-017 grain)

§2's necessity result (`resolution_requires_preimage`) says a cited predecessor must be
*delivered* — present in the store — or the verdict is permanently `Unknown`. This
section is its sufficiency companion at the SPEC-017 grain: it pins down *what* a delivery
must carry. The safety verdict reads the store through exactly two channels — `resolvedD`
(which cited predecessors are present) and `predTypesPresentD` (their *types*) — and
NOTHING ELSE about a message. In `goodD` the store `S` occurs solely inside
`predTypesPresentD`; `conformantD`/`noSpuriousD` are store-independent. Hence a delivered
type-tag authenticating "a predecessor of type `t` is present" (a SPEC-017 *opening* — a
type-tag, not the full Merkle-addressed message) yields the identical `Valid`/`Violation`
verdict to holding the full message. Necessity fixes *that* a tag must arrive; the results
below fix *which* tag is optimal — the type-opening: deliver exactly the type, no more
(full content is verdict-irrelevant), no less (a bare hash is type-opaque, §1). -/

/-- **Safety reads types only (good-ness level).** The `good`/`¬good` split — i.e. the
    `Valid` vs `Violation` distinction among resolved messages — depends on the store ONLY
    through the predecessor *types* present. Two stores presenting `m` the same predecessor
    types assign `m` the same `goodD`. Immediate by construction: `S` occurs in `goodD`
    solely inside `predTypesPresentD` (`conformantD`/`noSpuriousD` are store-independent). -/
theorem safety_reads_types_only
    {Role Perf Msg : Type} {D : ProtoData Role Perf Msg}
    {S S' : Cfg Msg} {m : Msg}
    (h : D.predTypesPresentD S m = D.predTypesPresentD S' m) :
    D.goodD S m = D.goodD S' m := by
  unfold ProtoData.goodD; rw [h]

/-- **Safety verdict reads types only.** Two stores that both resolve `m` and present `m`
    the same predecessor types assign `m` the same safety verdict — identical `isValid`
    and identical `isViolation`. (The only store-dependence beyond `predTypesPresentD` is
    `resolvedD`, which the hypotheses fix on both sides.) -/
theorem verdict_reads_types_only
    {Role Perf Msg : Type} {D : ProtoData Role Perf Msg}
    {S S' : Cfg Msg} {m : Msg}
    (hres : D.resolvedD S m) (hres' : D.resolvedD S' m)
    (h : D.predTypesPresentD S m = D.predTypesPresentD S' m) :
    (D.isValidD S m ↔ D.isValidD S' m) ∧ (D.isViolationD S m ↔ D.isViolationD S' m) := by
  have hg := safety_reads_types_only (D := D) (m := m) h
  refine ⟨?_, ?_⟩
  · unfold ProtoData.isValidD; rw [hg]
    exact ⟨fun x => ⟨hres', x.2⟩, fun x => ⟨hres, x.2⟩⟩
  · unfold ProtoData.isViolationD; rw [hg]
    exact ⟨fun x => ⟨hres', x.2⟩, fun x => ⟨hres, x.2⟩⟩

/-- **Openings suffice.** Model a SPEC-017 *type-opening* delivery abstractly: an opening
    store `Sopen` delivers each cited predecessor's PRESENCE and TYPE — it resolves `m` and
    presents `m` the same predecessor types as the full-message store `Sfull` — while
    carrying no other message content. Then `m`'s safety verdict is IDENTICAL under the
    opening delivery and under the full-message delivery.

    This is the sufficiency counterpart of §2's `resolution_requires_preimage`: necessity
    says *some* tag must arrive at the predecessor's hash; `openings_suffice` says a
    delivered TYPE-tag is enough — the type-opening is the optimal SPEC-017 tag for the
    SAFETY-level verdict. -/
theorem openings_suffice
    {Role Perf Msg : Type} {D : ProtoData Role Perf Msg}
    {Sfull Sopen : Cfg Msg} {m : Msg}
    (hres_full : D.resolvedD Sfull m) (hres_open : D.resolvedD Sopen m)
    (htypes : D.predTypesPresentD Sopen m = D.predTypesPresentD Sfull m) :
    (D.isValidD Sopen m ↔ D.isValidD Sfull m) ∧
    (D.isViolationD Sopen m ↔ D.isViolationD Sfull m) :=
  verdict_reads_types_only hres_open hres_full htypes

/-- The minimal *opening-only* store: it delivers exactly `m`'s cited predecessors — each
    as a type-authenticating opening — and NOTHING else (no non-predecessor message, no
    full content). -/
def openStore {Role Perf Msg : Type} (D : ProtoData Role Perf Msg) (m : Msg) : Cfg Msg :=
  fun z => D.predRel m z

/-- The opening-only store resolves `m` (its openings ARE exactly the cited predecessors). -/
theorem openStore_resolves {Role Perf Msg : Type} (D : ProtoData Role Perf Msg) (m : Msg) :
    D.resolvedD (openStore D m) m := fun _ hp => hp

/-- The opening-only store presents `m` the same predecessor types as ANY store `Sfull`
    that resolves `m` (in particular the full run). -/
theorem openStore_types_eq {Role Perf Msg : Type} (D : ProtoData Role Perf Msg) (m : Msg)
    {Sfull : Cfg Msg} (hfull : D.resolvedD Sfull m) :
    D.predTypesPresentD (openStore D m) m = D.predTypesPresentD Sfull m := by
  funext t; apply propext
  exact ⟨fun ⟨p, hpr, _, he⟩ => ⟨p, hpr, hfull p hpr, he⟩,
         fun ⟨p, hpr, _, he⟩ => ⟨p, hpr, hpr, he⟩⟩

/-- **Openings suffice (concrete).** Over the lean opening-only store — which holds ONLY
    the cited predecessors' type-openings — `m` gets the same safety verdict as over any
    full-message store `Sfull` resolving `m`. Holding the full messages buys no verdict
    information beyond the type-openings; the type-opening is exactly what §2's necessity
    demands be delivered, and nothing more is needed. -/
theorem openings_suffice_concrete
    {Role Perf Msg : Type} {D : ProtoData Role Perf Msg}
    {Sfull : Cfg Msg} {m : Msg} (hfull : D.resolvedD Sfull m) :
    (D.isValidD (openStore D m) m ↔ D.isValidD Sfull m) ∧
    (D.isViolationD (openStore D m) m ↔ D.isViolationD Sfull m) :=
  verdict_reads_types_only (openStore_resolves D m) hfull (openStore_types_eq D m hfull)

/-! ## 3. The weakest sound coordination-free condition (framing)

`predsLocal D C r` — "every `r`-relevant message's `:caused-by` predecessors are all
in `r`'s reachable store `project C r`" — is exactly the condition under which every
`r`-relevant verdict decides (`decidesAll`). Causal locality R6(vi) (`causalLocality`)
is the "no-bystanders" type-level sufficient condition that guarantees `predsLocal`;
`weakest_sound_condition` shows `predsLocal` is both necessary and sufficient, so no
weaker coordination-free condition suffices. Content-addressing a predecessor does
not relax `predsLocal`: by §2 a bare hash never substitutes for the predecessor's
presence. -/

/-- Every `r`-relevant message's cited predecessors lie in `r`'s reachable store. -/
def predsLocal {Role Perf Msg : Type} (D : ProtoData Role Perf Msg)
    (C : Cfg Msg) (r : Role) : Prop :=
  ∀ m, D.projectD C r m → ∀ p, D.predRel m p → D.projectD C r p

/-- Every `r`-relevant verdict decides (is not `Unknown`) at `r`'s eventual store. -/
def decidesAll {Role Perf Msg : Type} (D : ProtoData Role Perf Msg)
    (C : Cfg Msg) (r : Role) : Prop :=
  ∀ m, D.projectD C r m → ¬ D.isUnknownD (D.projectD C r) m

/-- Causal locality R6(vi) is the "no-bystanders" special case: it forces
    `predsLocal`. (This is `localres` of `EPP.lean`, restated over `ProtoData`.) -/
theorem causalLocality_imp_predsLocal
    {Role Perf Msg : Type} {D : ProtoData Role Perf Msg}
    {C : Cfg Msg} {r : Role} (h : D.causalLocality)
    (hcl : D.closedCfgD C) (hsafe : D.pSafeD C) : predsLocal D C r := by
  intro m hm p hp
  exact localres (D.toProto h) hcl hsafe hm.1 hm.2 p hp

/-- **Necessity of `predsLocal`.** If every `r`-relevant verdict decides, then every
    cited predecessor of an `r`-relevant message is in `r`'s reachable store — a
    bystander predecessor would leave its citing message permanently `Unknown`
    (`spliced_pred_permanently_unknown`). -/
theorem predsLocal_necessary
    {Role Perf Msg : Type} {D : ProtoData Role Perf Msg}
    {C : Cfg Msg} {r : Role} (hcl : D.closedCfgD C) (hdec : decidesAll D C r) :
    predsLocal D C r := by
  intro m hm p hp
  refine ⟨hcl m hm.1 p hp, ?_⟩
  exact Classical.byContradiction fun hbr =>
    hdec m hm
      (spliced_pred_permanently_unknown hp hbr (D.projectD C r) (fun _ hz => hz))

/-- **Sufficiency of `predsLocal`.** If every cited predecessor lies in `r`'s reachable
    store, every `r`-relevant verdict decides. -/
theorem decidesAll_of_predsLocal
    {Role Perf Msg : Type} {D : ProtoData Role Perf Msg}
    {C : Cfg Msg} {r : Role} (hpl : predsLocal D C r) : decidesAll D C r :=
  fun m hm hu => hu (fun p hp => hpl m hm p hp)

/-- **Weakest sound condition.** For a closed run, "every `r`-relevant verdict decides"
    is *equivalent* to `predsLocal` (every cited predecessor in `r`'s reachable store).
    Hence envelope-widened observation — the predecessor itself in the store — is the
    weakest sound coordination-free condition; causal locality R6(vi) is the special
    case that guarantees it, and content-addressing (a bare hash) cannot weaken it. -/
theorem weakest_sound_condition
    {Role Perf Msg : Type} {D : ProtoData Role Perf Msg}
    {C : Cfg Msg} {r : Role} (hcl : D.closedCfgD C) :
    decidesAll D C r ↔ predsLocal D C r :=
  ⟨fun hdec => predsLocal_necessary hcl hdec, fun hpl => decidesAll_of_predsLocal hpl⟩

/-! Axiom audit (informational output when this file is compiled). -/
#print axioms type_opacity_indistinguishability
#print axioms resolution_requires_preimage
#print axioms spliced_pred_permanently_unknown
#print axioms weakest_sound_condition
#print axioms safety_reads_types_only
#print axioms verdict_reads_types_only
#print axioms openings_suffice
#print axioms openings_suffice_concrete

end LeanCbcl.Splice
