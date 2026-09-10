/-
  Abstract observation and predecessor-resolution results.

  Equal held-message observations can coexist with different global verdicts when
  the interpretation of an unheld message's type differs. There is no hash function,
  byte encoding, binding assumption, or computational adversary in this model; the
  observation theorem is not a cryptographic impossibility theorem.

  Resolution is defined as presence of every cited predecessor. Consequently
  `decidesAll_iff_predsLocal` characterizes resolution within this store model, not
  minimal communication or optimal evidence among alternative verification schemes.

  Goodness factors through predecessor types; resolved stores exposing equal types
  yield equal verdicts. `openStore` selects actual abstract predecessors in the same
  Msg universe. Authenticating and interpreting concrete field openings requires a
  separate refinement proof. No concrete opening verifier is implemented here.
-/
import LeanCbcl.Projectability
import Batteries.Tactic.Lint  -- provides the `@[nolint …]` attribute

namespace LeanCbcl.Splice

open LeanCbcl.EPP
open LeanCbcl.Projectability

namespace Example

/-- Roles in the observation counterexample. -/
inductive SRole | rR | rO

/-- Performative types in the observation counterexample. -/
inductive SPerf | tM | tG | tB

/-- Messages in the observation counterexample. -/
inductive SMsg  | m  | b

/-- Message senders in both worlds. -/
def sSender  : SMsg → SRole            | .m => .rR | .b => .rO

/-- Neither example message has recipients. -/
@[nolint unusedArguments]  -- empty relation (constant `False`); the message/role
                           -- arguments are the relation's domain, unused by design.
def sRecip   : SMsg → SRole → Prop   := fun _ _ => False

/-- The dependent message cites the bystander. -/
def sPredRel : SMsg → SMsg → Prop    := fun x y => x = .m ∧ y = .b

/-- Declared sender for each example type. -/
def sPsender : SPerf → SRole           | .tM => .rR | .tG => .rO | .tB => .rO

/-- No example type has declared recipients. -/
@[nolint unusedArguments]  -- empty relation (constant `False`); the perf/role
                           -- arguments are the relation's domain, unused by design.
def sPrecip  : SPerf → SRole → Prop  := fun _ _ => False

/-- The dependent type permits the expected predecessor type. -/
def sLegal   : SPerf → SPerf → Prop  := fun t t' => t = .tM ∧ t' = .tG

/-- The dependent type requires a present predecessor of the expected type. -/
def sClause  : SPerf → (SPerf → Prop) → Prop := fun t present => t = .tM → present .tG

/-- The bystander has the expected type in world one. -/
def sPerf1 : SMsg → SPerf | .m => .tM | .b => .tG

/-- The same abstract bystander has another type in world two. -/
def sPerf2 : SMsg → SPerf | .m => .tM | .b => .tB

/-- First interpretation of the example messages. -/
def D₁ : ProtoData SRole SPerf SMsg where
  perf := sPerf1; sender := sSender; recip := sRecip; predRel := sPredRel
  psender := sPsender; precip := sPrecip; legalPred := sLegal; clause := sClause

/-- Second interpretation, changing only the bystander type. -/
def D₂ : ProtoData SRole SPerf SMsg where
  perf := sPerf2; sender := sSender; recip := sRecip; predRel := sPredRel
  psender := sPsender; precip := sPrecip; legalPred := sLegal; clause := sClause

/-- The global store containing both example messages. -/
def Cfull : Cfg SMsg := fun _ => True

theorem b_unheld : ¬ D₁.endpointD .b .rR :=
  fun h => h.elim (fun h' => SRole.noConfusion h') id

theorem good_m_D₁ : D₁.goodD Cfull .m :=
  ⟨⟨rfl, fun _ => Iff.rfl⟩,
   (fun _ hp => by obtain ⟨_, rfl⟩ := hp; exact ⟨rfl, rfl⟩),
   (fun _ => ⟨.b, ⟨rfl, rfl⟩, trivial, rfl⟩)⟩

theorem good_b_D₁ : D₁.goodD Cfull .b :=
  ⟨⟨rfl, fun _ => Iff.rfl⟩,
   (fun _ hp => absurd hp.1 (fun h => SMsg.noConfusion h)),
   (fun h => SPerf.noConfusion h)⟩

theorem closed_D₁ : D₁.closedCfgD Cfull := fun _ _ _ _ => trivial
theorem closed_D₂ : D₂.closedCfgD Cfull := fun _ _ _ _ => trivial

theorem safe_D₁ : D₁.pSafeD Cfull := by
  intro x _ hv
  cases x with
  | m => exact hv.2 good_m_D₁
  | b => exact hv.2 good_b_D₁

theorem m_valid_D₁ : D₁.isValidD Cfull .m := ⟨fun _ _ => trivial, good_m_D₁⟩

theorem not_good_m_D₂ : ¬ D₂.goodD Cfull .m := by
  intro hg
  obtain ⟨p, hpr, _, hperf⟩ := hg.2.2 rfl
  obtain ⟨_, rfl⟩ := hpr
  exact SPerf.noConfusion hperf

theorem m_violation_D₂ : D₂.isViolationD Cfull .m := ⟨fun _ _ => trivial, not_good_m_D₂⟩

theorem held_types_agree :
    ∀ z, D₁.projectD Cfull .rR z → D₁.perf z = D₂.perf z := by
  intro z hz
  cases z with
  | m => rfl
  | b => exact absurd hz.2 b_unheld

end Example

/-- Observed message identities paired with their types at a role. -/
def heldTypes {Role Perf Msg : Type} (D : ProtoData Role Perf Msg) (C : Cfg Msg)
    (r : Role) : Msg → Perf → Prop :=
  fun z t => D.projectD C r z ∧ D.perf z = t

namespace Example

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

/-- Equal abstract observations do not determine a verdict across these two type interpretations. -/
theorem type_opacity_indistinguishability :
    ∃ (Role Perf Msg : Type) (D₁ D₂ : ProtoData Role Perf Msg)
      (C : Cfg Msg) (r : Role) (m b : Msg),
      -- `r`'s observation is identical across the two worlds:
      D₁.projectD C r = D₂.projectD C r ∧                     -- same held messages
      D₁.predRel = D₂.predRel ∧                               -- same abstract citation relation
      heldTypes D₁ C r = heldTypes D₂ C r ∧                   -- same typed observation
      -- they differ only in the TYPE of the unheld predecessor `b`:
      D₁.predRel m b ∧ ¬ D₁.endpointD b r ∧ D₁.perf b ≠ D₂.perf b ∧
      -- world 1 is a closed `P`-safe run in which `m` is `Valid`:
      D₁.closedCfgD C ∧ D₁.pSafeD C ∧ D₁.isValidD C m ∧
      -- world 2 differs only in `b`'s type; there `m` is a `Violation`:
      D₂.closedCfgD C ∧ D₂.isViolationD C m ∧
      -- CONCLUSION: no decider from `r`'s full observation (held messages + their
      -- types + abstract citations) computes the verdict:
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

-- Keep the reachability hypothesis for the intended local-store use; the proof
-- establishes the stronger missing-predecessor result for any store.
/-- Any missing cited predecessor forces Unknown under resolved-first semantics. -/
@[nolint unusedArguments]
theorem resolution_requires_preimage
    {Role Perf Msg : Type} {D : ProtoData Role Perf Msg}
    {C : Cfg Msg} {r : Role} {m b : Msg} (hpb : D.predRel m b)
    (L : Cfg Msg) (_hL : ∀ z, L z → D.projectD C r z) (hb : ¬ L b) :
    D.isUnknownD L m :=
  fun hres => hb (hres b hpb)

theorem resolution_of_preds_held
    {Role Perf Msg : Type} {D : ProtoData Role Perf Msg}
    {L : Cfg Msg} {m : Msg} (hheld : ∀ p, D.predRel m p → L p) :
    ¬ D.isUnknownD L m :=
  fun hu => hu hheld

theorem valid_of_resolved_good
    {Role Perf Msg : Type} {D : ProtoData Role Perf Msg}
    {L : Cfg Msg} {m : Msg} (hres : D.resolvedD L m) (hg : D.goodD L m) :
    D.isValidD L m :=
  ⟨hres, hg⟩

theorem spliced_pred_permanently_unknown
    {Role Perf Msg : Type} {D : ProtoData Role Perf Msg}
    {C : Cfg Msg} {r : Role} {m b : Msg}
    (hpb : D.predRel m b) (hbr : ¬ D.endpointD b r) :
    ∀ L : Cfg Msg, (∀ z, L z → D.projectD C r z) → D.isUnknownD L m :=
  permanently_unknown_of_nonlocal_pred hpb hbr

/-- Goodness depends on the store only through the present predecessor types. -/
theorem safety_reads_types_only
    {Role Perf Msg : Type} {D : ProtoData Role Perf Msg}
    {S S' : Cfg Msg} {m : Msg}
    (h : D.predTypesPresentD S m = D.predTypesPresentD S' m) :
    D.goodD S m = D.goodD S' m := by
  unfold ProtoData.goodD; rw [h]

/-- Resolved stores with equal predecessor types agree on terminal verdicts. -/
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

/-- Semantic interface for an opening interpretation: resolution and type equality are hypotheses. -/
theorem openings_suffice
    {Role Perf Msg : Type} {D : ProtoData Role Perf Msg}
    {Sfull Sopen : Cfg Msg} {m : Msg}
    (hres_full : D.resolvedD Sfull m) (hres_open : D.resolvedD Sopen m)
    (htypes : D.predTypesPresentD Sopen m = D.predTypesPresentD Sfull m) :
    (D.isValidD Sopen m ↔ D.isValidD Sfull m) ∧
    (D.isViolationD Sopen m ↔ D.isViolationD Sfull m) :=
  verdict_reads_types_only hres_open hres_full htypes

/-- The predicate selecting exactly the cited abstract predecessor messages. -/
def openStore {Role Perf Msg : Type} (D : ProtoData Role Perf Msg) (m : Msg) : Cfg Msg :=
  fun z => D.predRel m z

theorem openStore_resolves {Role Perf Msg : Type} (D : ProtoData Role Perf Msg) (m : Msg) :
    D.resolvedD (openStore D m) m := fun _ hp => hp

theorem openStore_types_eq {Role Perf Msg : Type} (D : ProtoData Role Perf Msg) (m : Msg)
    {Sfull : Cfg Msg} (hfull : D.resolvedD Sfull m) :
    D.predTypesPresentD (openStore D m) m = D.predTypesPresentD Sfull m := by
  funext t; apply propext
  exact ⟨fun ⟨p, hpr, _, he⟩ => ⟨p, hpr, hfull p hpr, he⟩,
         fun ⟨p, hpr, _, he⟩ => ⟨p, hpr, hpr, he⟩⟩

/-- The predecessor-only abstract store agrees with any resolving store. -/
theorem openings_suffice_concrete
    {Role Perf Msg : Type} {D : ProtoData Role Perf Msg}
    {Sfull : Cfg Msg} {m : Msg} (hfull : D.resolvedD Sfull m) :
    (D.isValidD (openStore D m) m ↔ D.isValidD Sfull m) ∧
    (D.isViolationD (openStore D m) m ↔ D.isViolationD Sfull m) :=
  verdict_reads_types_only (openStore_resolves D m) hfull (openStore_types_eq D m hfull)

/-- Every relevant message has all its cited predecessors in the local projection. -/
def predsLocal {Role Perf Msg : Type} (D : ProtoData Role Perf Msg)
    (C : Cfg Msg) (r : Role) : Prop :=
  ∀ m, D.projectD C r m → ∀ p, D.predRel m p → D.projectD C r p

/-- Every relevant message resolves in the full local projection. -/
def decidesAll {Role Perf Msg : Type} (D : ProtoData Role Perf Msg)
    (C : Cfg Msg) (r : Role) : Prop :=
  ∀ m, D.projectD C r m → ¬ D.isUnknownD (D.projectD C r) m

theorem causalLocality_imp_predsLocal
    {Role Perf Msg : Type} {D : ProtoData Role Perf Msg}
    {C : Cfg Msg} {r : Role} (h : D.causalLocality)
    (hcl : D.closedCfgD C) (hsafe : D.pSafeD C) : predsLocal D C r := by
  intro m hm p hp
  exact localres (D.toProto h) hcl hsafe hm.1 hm.2 p hp

theorem predsLocal_necessary
    {Role Perf Msg : Type} {D : ProtoData Role Perf Msg}
    {C : Cfg Msg} {r : Role} (hcl : D.closedCfgD C) (hdec : decidesAll D C r) :
    predsLocal D C r := by
  intro m hm p hp
  refine ⟨hcl m hm.1 p hp, ?_⟩
  exact Classical.byContradiction fun hbr =>
    hdec m hm
      (spliced_pred_permanently_unknown hp hbr (D.projectD C r) (fun _ hz => hz))

theorem decidesAll_of_predsLocal
    {Role Perf Msg : Type} {D : ProtoData Role Perf Msg}
    {C : Cfg Msg} {r : Role} (hpl : predsLocal D C r) : decidesAll D C r :=
  fun m hm hu => hu (fun p hp => hpl m hm p hp)

/-- For a closed run, full local resolution is equivalent to local predecessor coverage. -/
theorem decidesAll_iff_predsLocal
    {Role Perf Msg : Type} {D : ProtoData Role Perf Msg}
    {C : Cfg Msg} {r : Role} (hcl : D.closedCfgD C) :
    decidesAll D C r ↔ predsLocal D C r :=
  ⟨fun hdec => predsLocal_necessary hcl hdec, fun hpl => decidesAll_of_predsLocal hpl⟩

#print axioms type_opacity_indistinguishability
#print axioms resolution_requires_preimage
#print axioms spliced_pred_permanently_unknown
#print axioms decidesAll_iff_predsLocal
#print axioms safety_reads_types_only
#print axioms verdict_reads_types_only
#print axioms openings_suffice
#print axioms openings_suffice_concrete

end LeanCbcl.Splice
