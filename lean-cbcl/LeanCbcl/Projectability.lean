/-
  Projectability ≡ local verifiability — mechanization of the paper's Theorem 1
  (`thm:equiv`), restated per the review (M1/M2) with causal locality (R6(vi)) as
  the definition of projectability.

  Builds on `LeanCbcl.EPP` (which bakes causal locality into `Proto.causalLocal`)
  and reuses its definitions (`Cfg`, `endpoint`, `resolved`, `isUnknown`, `isValid`,
  `isViolation`, `project`, `closedCfg`, `pSafe`, `localres`, `resolved_proj`,
  `reconcile_global`) rather than redefining them.

  Modelling choices:
  * A *run* is a closed, `P`-safe configuration `C` (as in `EPP.lean`).
  * A *reachable local store of `r`* is any `L ⊆ project P C r`: `r` reliably holds
    only messages it sent or received, delivered in some order; "eventually
    delivered" is `L = project P C r`.
  * FORWARD (projectable ⇒ locally verifiable): under causal locality,
    (i) `unknown_means_not_yet_arrived`: in any partial local store, an `Unknown`
        `r`-relevant verdict is only ever due to a missing predecessor that is
        itself `r`-relevant — a message `r` *will* see; never a third-party
        message `r` can never observe; and
    (ii) `projectable_eventual_resolution`: at the full local store every
        `r`-relevant verdict is decided (`Valid` or `Violation`, never `Unknown`)
        and *equals* the global verdict.
  * CONVERSE (not projectable ⇒ not locally verifiable): stated over `ProtoData`
    (the fields of `Proto` minus the causal-locality proof obligation, with
    definitional bridge lemmas certifying the semantics is unchanged), since a
    protocol violating R6(vi) cannot be a `Proto` at all.
    `causal_locality_necessary` exhibits a protocol, a closed *safe* global run,
    a role `r` and an `r`-relevant message whose verdict is `Unknown` in *every*
    local store `r` can ever reach: the review's straight-line example
    (`x : A → B`, `y : C → B`, protocol `(then begin x y)`; role `C` must justify
    `y` by the third-party message `x` it never holds).
  * `projectability_iff_local_verifiability` packages both directions.
-/
import LeanCbcl.EPP

namespace LeanCbcl.Projectability

open LeanCbcl.EPP

/-! ## Forward direction: causal locality ⇒ local verifiability

Over `Proto` (hence assuming R6(vi) = `causalLocal`), reusing `EPP.lean`. -/

variable {Role Perf Msg : Type} (P : Proto Role Perf Msg)

/-- **Theorem 1, forward, partial stores** (`thm:equiv`, first claim): in any
    reachable local store `L ⊆ project P C r` of role `r`, if an `r`-relevant
    message's verdict is `Unknown`, the missing predecessor is itself
    `r`-relevant and present in `r`'s eventual store — "`Unknown` then means only
    'a message `r` will see has not yet arrived'", never a third-party message. -/
theorem unknown_means_not_yet_arrived {C : Cfg Msg}
    (hcl : closedCfg P C) (hsafe : pSafe P C)
    {r : Role} {L : Cfg Msg} (hL : ∀ z, L z → project P C r z)
    {m : Msg} (hm : L m) (hu : isUnknown P L m) :
    ∃ p, P.predRel m p ∧ ¬ L p ∧ project P C r p := by
  apply Classical.byContradiction
  intro hne
  apply hu
  intro p hp
  apply Classical.byContradiction
  intro hLp
  exact hne ⟨p, hp, hLp, localres P hcl hsafe (hL m hm).1 (hL m hm).2 p hp⟩

/-- **Theorem 1, forward, eventual stores** (`thm:equiv`, resolution claim): once
    `r`'s relevant messages are all delivered (local store `= project P C r`),
    every `r`-relevant verdict is decided — never `Unknown`, classically `Valid`
    or `Violation` — and *agrees with the global verdict*. -/
theorem projectable_eventual_resolution {C : Cfg Msg}
    (hcl : closedCfg P C) (hsafe : pSafe P C)
    {r : Role} {m : Msg} (hm : project P C r m) :
    ¬ isUnknown P (project P C r) m ∧
    (isValid P (project P C r) m ∨ isViolation P (project P C r) m) ∧
    (isValid P (project P C r) m ↔ isValid P C m) ∧
    (isViolation P (project P C r) m ↔ isViolation P C m) := by
  have hres : resolved P (project P C r) m :=
    (resolved_proj P hcl hsafe hm).2 (fun p hp => hcl m hm.1 p hp)
  refine ⟨fun hu => hu hres, ?_,
    (reconcile_global P hcl hsafe hm).2.1, (reconcile_global P hcl hsafe hm).2.2⟩
  cases Classical.em (good P (project P C r) m) with
  | inl hg => exact Or.inl ⟨hres, hg⟩
  | inr hg => exact Or.inr ⟨hres, hg⟩

/-! ## Protocol data without the causal-locality obligation

A protocol that violates R6(vi) cannot be a `Proto` (the `causalLocal` field is a
proof). `ProtoData` is exactly `Proto` minus that field; `toProto` recovers a
`Proto` from causally local data, and the bridge lemmas below are all `Iff.rfl`:
each `…D` notion is *definitionally* the corresponding `EPP` notion. -/

/-- The raw data of a `Proto`, without the R6(vi) proof obligation. -/
structure ProtoData (Role Perf Msg : Type) where
  perf      : Msg → Perf
  sender    : Msg → Role
  recip     : Msg → Role → Prop
  predRel   : Msg → Msg → Prop
  psender   : Perf → Role
  precip    : Perf → Role → Prop
  legalPred : Perf → Perf → Prop
  clause    : Perf → (Perf → Prop) → Prop

namespace ProtoData

variable {Role Perf Msg : Type} (D : ProtoData Role Perf Msg)

/-- Causal locality, R6 clause (vi) — verbatim the `Proto.causalLocal` field
    (= projectability in the restated Definition 6). -/
def causalLocality : Prop :=
  ∀ (t t' : Perf) (r : Role),
    D.legalPred t t' → (D.psender t = r ∨ D.precip t r) →
      (D.psender t' = r ∨ D.precip t' r)

/-- Causally local protocol data *is* a protocol of the mechanised model. -/
def toProto (h : D.causalLocality) : Proto Role Perf Msg where
  perf := D.perf
  sender := D.sender
  recip := D.recip
  predRel := D.predRel
  psender := D.psender
  precip := D.precip
  legalPred := D.legalPred
  clause := D.clause
  causalLocal := h

/- The `EPP` semantics, verbatim, over `ProtoData` (definitional copies;
   see the bridge lemmas below). -/

def endpointD (m : Msg) (r : Role) : Prop := D.sender m = r ∨ D.recip m r
def resolvedD (S : Cfg Msg) (m : Msg) : Prop := ∀ p, D.predRel m p → S p
def predTypesPresentD (S : Cfg Msg) (m : Msg) : Perf → Prop :=
  fun t => ∃ p, D.predRel m p ∧ S p ∧ D.perf p = t
def conformantD (m : Msg) : Prop :=
  D.sender m = D.psender (D.perf m) ∧ (∀ r, D.recip m r ↔ D.precip (D.perf m) r)
def noSpuriousD (m : Msg) : Prop :=
  ∀ p, D.predRel m p → D.legalPred (D.perf m) (D.perf p)
def goodD (S : Cfg Msg) (m : Msg) : Prop :=
  conformantD D m ∧ noSpuriousD D m ∧ D.clause (D.perf m) (predTypesPresentD D S m)
def isUnknownD (S : Cfg Msg) (m : Msg) : Prop := ¬ resolvedD D S m
def isValidD (S : Cfg Msg) (m : Msg) : Prop := resolvedD D S m ∧ goodD D S m
def isViolationD (S : Cfg Msg) (m : Msg) : Prop := resolvedD D S m ∧ ¬ goodD D S m
def closedCfgD (C : Cfg Msg) : Prop := ∀ m, C m → ∀ p, D.predRel m p → C p
def pSafeD (C : Cfg Msg) : Prop := ∀ m, C m → ¬ isViolationD D C m
def projectD (C : Cfg Msg) (r : Role) : Cfg Msg := fun m => C m ∧ endpointD D m r

/-! Bridge lemmas: under `toProto`, every `…D` notion coincides *definitionally*
with the corresponding `EPP.lean` notion (each proof is `Iff.rfl`). -/

theorem endpointD_toProto (h : D.causalLocality) (m : Msg) (r : Role) :
    D.endpointD m r ↔ endpoint (D.toProto h) m r := Iff.rfl
theorem isUnknownD_toProto (h : D.causalLocality) (S : Cfg Msg) (m : Msg) :
    D.isUnknownD S m ↔ isUnknown (D.toProto h) S m := Iff.rfl
theorem isValidD_toProto (h : D.causalLocality) (S : Cfg Msg) (m : Msg) :
    D.isValidD S m ↔ isValid (D.toProto h) S m := Iff.rfl
theorem isViolationD_toProto (h : D.causalLocality) (S : Cfg Msg) (m : Msg) :
    D.isViolationD S m ↔ isViolation (D.toProto h) S m := Iff.rfl
theorem closedCfgD_toProto (h : D.causalLocality) (C : Cfg Msg) :
    D.closedCfgD C ↔ closedCfg (D.toProto h) C := Iff.rfl
theorem pSafeD_toProto (h : D.causalLocality) (C : Cfg Msg) :
    D.pSafeD C ↔ pSafe (D.toProto h) C := Iff.rfl
theorem projectD_toProto (h : D.causalLocality) (C : Cfg Msg) (r : Role) (m : Msg) :
    D.projectD C r m ↔ project (D.toProto h) C r m := Iff.rfl

end ProtoData

/-- Forward direction restated over `ProtoData` + explicit causal locality
    (via the bridges: the statement is definitionally the `Proto` version). -/
theorem locally_verifiable_of_causalLocality
    {Role Perf Msg : Type} {D : ProtoData Role Perf Msg} (h : D.causalLocality)
    {C : Cfg Msg} (hcl : D.closedCfgD C) (hsafe : D.pSafeD C)
    {r : Role} {m : Msg} (hm : D.projectD C r m) :
    ¬ D.isUnknownD (D.projectD C r) m ∧
    (D.isValidD (D.projectD C r) m ∨ D.isViolationD (D.projectD C r) m) ∧
    (D.isValidD (D.projectD C r) m ↔ D.isValidD C m) ∧
    (D.isViolationD (D.projectD C r) m ↔ D.isViolationD C m) :=
  projectable_eventual_resolution (D.toProto h) hcl hsafe hm

/-! ## Converse: without causal locality, local verifiability fails -/

/-- Message-level engine of the converse: if some `caused-by` predecessor `p` of
    an `r`-relevant message `m` is not itself `r`-relevant, then `m`'s verdict is
    `Unknown` in every store of `r`-relevant messages — permanently, since `r`'s
    reachable stores are exactly the sub-stores of `projectD C r`. -/
theorem permanently_unknown_of_nonlocal_pred
    {Role Perf Msg : Type} {D : ProtoData Role Perf Msg}
    {C : Cfg Msg} {r : Role} {m p : Msg}
    (hp : D.predRel m p) (hpr : ¬ D.endpointD p r) :
    ∀ L : Cfg Msg, (∀ z, L z → D.projectD C r z) → D.isUnknownD L m :=
  fun _ hL hres => hpr (hL p (hres p hp)).2

namespace Counterexample

/-! The review's (M1) straight-line witness: performatives `px : rA → rB` and
`py : rC → rB` with protocol `(then begin px py)` — so `px` is the sole legal
`caused-by` predecessor of `py`. Role `rC` sends `py` yet neither sends nor
receives `px`: causal locality fails at `(py, px, rC)`, and in every store `rC`
can reach, `py`'s verdict is `Unknown` for want of `px`. No choice point is
involved, so the "(a)/(b) choice-point" reading of Definition 6 is vacuous here
while local verifiability still fails — the counterexample of review item M1. -/

inductive XRole | rA | rB | rC
inductive XPerf | px | py
inductive XMsg  | mx | my

/-- The protocol data: `mx : rA → rB` of type `px`; `my : rC → rB` of type `py`,
    caused by `mx`; clause of `py` requires a predecessor of type `px`. -/
def D : ProtoData XRole XPerf XMsg where
  perf := fun m => match m with | .mx => .px | .my => .py
  sender := fun m => match m with | .mx => .rA | .my => .rC
  recip := fun _ r => r = .rB
  predRel := fun m p => m = .my ∧ p = .mx
  psender := fun t => match t with | .px => .rA | .py => .rC
  precip := fun _ r => r = .rB
  legalPred := fun t t' => t = .py ∧ t' = .px
  clause := fun t present => t = .py → present .px

/-- The global run: both messages have occurred. -/
def fullRun : Cfg XMsg := fun _ => True

/-- The protocol is *not* causally local (not projectable onto `rC`):
    `px` is a legal predecessor of the `rC`-sent `py`, but `rC` neither sends
    nor receives `px`. -/
theorem D_not_causalLocal : ¬ D.causalLocality := fun h =>
  match h .py .px .rC ⟨rfl, rfl⟩ (Or.inl rfl) with
  | .inl h' => XRole.noConfusion h'   -- rA = rC
  | .inr h' => XRole.noConfusion h'   -- rC = rB

/-- `mx` is not `rC`-relevant: `rC` never holds it. -/
theorem mx_not_rC_relevant : ¬ D.endpointD .mx .rC := fun h =>
  match h with
  | .inl h' => XRole.noConfusion h'   -- rA = rC
  | .inr h' => XRole.noConfusion h'   -- rC = rB

theorem fullRun_closed : D.closedCfgD fullRun := fun _ _ _ _ => trivial

theorem good_mx : D.goodD fullRun .mx :=
  ⟨⟨rfl, fun _ => Iff.rfl⟩,
   fun _ hp => XMsg.noConfusion hp.1,
   fun h => XPerf.noConfusion h⟩

theorem good_my : D.goodD fullRun .my := by
  refine ⟨⟨rfl, fun _ => Iff.rfl⟩, ?_, ?_⟩
  · intro p hp
    rw [hp.2]
    exact ⟨rfl, rfl⟩
  · intro _
    exact ⟨.mx, ⟨rfl, rfl⟩, trivial, rfl⟩

/-- The global run is safe: the `Unknown` below is a pure knowledge gap, not a
    hidden violation. -/
theorem fullRun_safe : D.pSafeD fullRun := by
  intro m _ hviol
  cases m with
  | mx => exact hviol.2 good_mx
  | my => exact hviol.2 good_my

/-- **Permanent `Unknown`**: in every local store `rC` can ever reach (any
    sub-store of its projection), the verdict of its own message `my` is
    `Unknown` — the justifying `mx` is a third-party message `rC` never holds. -/
theorem my_permanently_unknown :
    ∀ L : Cfg XMsg, (∀ z, L z → D.projectD fullRun .rC z) → D.isUnknownD L .my :=
  permanently_unknown_of_nonlocal_pred ⟨rfl, rfl⟩ mx_not_rC_relevant

end Counterexample

/-- **Theorem 1, converse** (`thm:equiv`, existentially quantified as the review
    requires): there is a protocol violating causal locality, with a closed
    *safe* global run, a role `r`, and an `r`-relevant message occurring in the
    run whose verdict is `Unknown` in every local store `r` can reach —
    permanently `Unknown`. -/
theorem causal_locality_necessary :
    ∃ (Role Perf Msg : Type) (D : ProtoData Role Perf Msg)
      (C : Cfg Msg) (r : Role) (m : Msg),
      ¬ D.causalLocality ∧
      D.closedCfgD C ∧ D.pSafeD C ∧
      C m ∧ D.endpointD m r ∧
      ∀ L : Cfg Msg, (∀ z, L z → D.projectD C r z) → D.isUnknownD L m :=
  ⟨Counterexample.XRole, Counterexample.XPerf, Counterexample.XMsg,
   Counterexample.D, Counterexample.fullRun, .rC, .my,
   Counterexample.D_not_causalLocal,
   Counterexample.fullRun_closed, Counterexample.fullRun_safe,
   trivial, Or.inl rfl,
   Counterexample.my_permanently_unknown⟩

/-- **Theorem 1 (Projectability ≡ local verifiability), both directions.**
    Forward: for *every* causally local protocol, role, closed safe run, and
    `r`-relevant message, the verdict at `r`'s eventual local store is decided
    and equals the global verdict. Converse: absent causal locality this fails —
    witnessed by a protocol, closed safe run, role, and `r`-relevant message
    whose verdict is `Unknown` at every reachable local store of `r`. -/
theorem projectability_iff_local_verifiability :
    (∀ (Role Perf Msg : Type) (D : ProtoData Role Perf Msg),
      D.causalLocality →
      ∀ C : Cfg Msg, D.closedCfgD C → D.pSafeD C →
      ∀ (r : Role) (m : Msg), D.projectD C r m →
        ¬ D.isUnknownD (D.projectD C r) m ∧
        (D.isValidD (D.projectD C r) m ∨ D.isViolationD (D.projectD C r) m) ∧
        (D.isValidD (D.projectD C r) m ↔ D.isValidD C m) ∧
        (D.isViolationD (D.projectD C r) m ↔ D.isViolationD C m))
    ∧
    (∃ (Role Perf Msg : Type) (D : ProtoData Role Perf Msg)
       (C : Cfg Msg) (r : Role) (m : Msg),
      ¬ D.causalLocality ∧
      D.closedCfgD C ∧ D.pSafeD C ∧
      C m ∧ D.endpointD m r ∧
      ∀ L : Cfg Msg, (∀ z, L z → D.projectD C r z) → D.isUnknownD L m) :=
  ⟨fun _ _ _ _ h _ hcl hsafe _ _ hm =>
     locally_verifiable_of_causalLocality h hcl hsafe hm,
   causal_locality_necessary⟩

/-! Axiom audit (informational output when this file is compiled). -/
#print axioms unknown_means_not_yet_arrived
#print axioms projectable_eventual_resolution
#print axioms causal_locality_necessary
#print axioms projectability_iff_local_verifiability

end LeanCbcl.Projectability
