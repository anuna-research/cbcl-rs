/-
  Protocol verification transfer through an explicit agreement interface.

  `AgreesOnRole` assumes equality of message fields and relevant protocol fields.
  These hypotheses suffice to transfer all verdict predicates. This module does not
  define a concrete protocol erasure/splice or prove it satisfies the interface.
  Causal locality constrains legalPred, while clause is independent abstract data;
  identifying a concrete projection requires clause syntax, its interpretation,
  and a proof relating clause references to legalPred. Locality alone does not
  discharge clause_iff in this abstract model. ConcreteProjection.lean supplies the
  concrete syntax and discharges this interface for raw-copy and filtered views.
-/
import LeanCbcl.Projectability

namespace LeanCbcl.ProtoProjection

open LeanCbcl.EPP
open LeanCbcl.Projectability

variable {Role Perf Msg : Type}

/-- Performative-level endpoint: role `r` is the declared sender or a declared recipient
    of performative `t`. (The type-level shadow of `endpointD`.) -/
def typeEndpoint (D : ProtoData Role Perf Msg) (t : Perf) (r : Role) : Prop :=
  D.psender t = r ∨ D.precip t r

/-- Identical message fields and protocol fields at every D-endpoint type for r.
    Fields at other types are unconstrained. Satisfaction by a concrete projection
    is discharged for specific views in ConcreteProjection.lean. -/
structure AgreesOnRole (D Q : ProtoData Role Perf Msg) (r : Role) : Prop where
  perf_eq     : ∀ m, Q.perf m = D.perf m
  sender_eq   : ∀ m, Q.sender m = D.sender m
  recip_iff   : ∀ m r', Q.recip m r' ↔ D.recip m r'
  predRel_iff : ∀ m p, Q.predRel m p ↔ D.predRel m p
  psender_eq  : ∀ t, typeEndpoint D t r → Q.psender t = D.psender t
  precip_iff  : ∀ t r', typeEndpoint D t r → (Q.precip t r' ↔ D.precip t r')
  legal_iff   : ∀ t t', typeEndpoint D t r → (Q.legalPred t t' ↔ D.legalPred t t')
  clause_iff  : ∀ t pres, typeEndpoint D t r → (Q.clause t pres ↔ D.clause t pres)

/-- Every protocol agrees with itself at every role — the trivial projection, and the
    identification `EPP.lean` uses implicitly when it verifies locally against `P`. -/
theorem agreesOnRole_refl (D : ProtoData Role Perf Msg) (r : Role) : AgreesOnRole D D r :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl,
   fun _ _ => rfl, fun _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl⟩

variable {D Q : ProtoData Role Perf Msg} {r : Role}

/-- Message-level endpoints agree (they read only message fields). -/
theorem endpointD_agree (h : AgreesOnRole D Q r) (m : Msg) (r' : Role) :
    Q.endpointD m r' ↔ D.endpointD m r' := by
  unfold ProtoData.endpointD
  rw [h.sender_eq m]
  exact or_congr Iff.rfl (h.recip_iff m r')

/-- Store projections agree: the same messages are `r'`-relevant under `D` and `Q`. -/
theorem projectD_agree (h : AgreesOnRole D Q r) (C : Cfg Msg) (r' : Role) :
    Q.projectD C r' = D.projectD C r' := by
  funext m
  exact propext (and_congr Iff.rfl (endpointD_agree h m r'))

theorem resolvedD_agree (h : AgreesOnRole D Q r) (S : Cfg Msg) (m : Msg) :
    Q.resolvedD S m ↔ D.resolvedD S m := by
  unfold ProtoData.resolvedD
  exact forall_congr' fun p => imp_congr (h.predRel_iff m p) Iff.rfl

theorem predTypesPresentD_agree (h : AgreesOnRole D Q r) (S : Cfg Msg) (m : Msg) :
    Q.predTypesPresentD S m = D.predTypesPresentD S m := by
  funext t
  apply propext
  constructor
  · rintro ⟨p, hpr, hSp, he⟩
    exact ⟨p, (h.predRel_iff m p).1 hpr, hSp, (h.perf_eq p) ▸ he⟩
  · rintro ⟨p, hpr, hSp, he⟩
    exact ⟨p, (h.predRel_iff m p).2 hpr, hSp, (h.perf_eq p).symm ▸ he⟩

/-- A conformant `r`-relevant message has an `r`-endpoint performative — the bridge from
    message-level relevance to the type-level guard of `AgreesOnRole`. -/
theorem typeEndpoint_of_conformant {m : Msg} (hconf : D.conformantD m)
    (hep : D.endpointD m r) : typeEndpoint D (D.perf m) r := by
  cases hep with
  | inl hs => exact Or.inl (hconf.1 ▸ hs)
  | inr hr => exact Or.inr ((hconf.2 r).1 hr)

/-- Goodness agrees on messages of `r`-endpoint performatives, in any store. -/
theorem goodD_agree (h : AgreesOnRole D Q r) {m : Msg}
    (ht : typeEndpoint D (D.perf m) r) (S : Cfg Msg) :
    Q.goodD S m ↔ D.goodD S m := by
  unfold ProtoData.goodD ProtoData.conformantD ProtoData.noSpuriousD
  rw [h.perf_eq m, h.sender_eq m, h.psender_eq _ ht, predTypesPresentD_agree h S m]
  refine and_congr (and_congr Iff.rfl ?_) (and_congr ?_ (h.clause_iff _ _ ht))
  · exact forall_congr' fun r' => iff_congr (h.recip_iff m r') (h.precip_iff _ r' ht)
  · refine forall_congr' fun p => imp_congr (h.predRel_iff m p) ?_
    rw [h.perf_eq p]
    exact h.legal_iff _ _ ht

/-- **Verdict agreement.** Under `AgreesOnRole`, protocols `D` and `Q` assign identical
    verdicts — all three of Unknown / Valid / Violation — to any message whose
    performative is an `r`-endpoint type, in any store. -/
theorem verdict_agree (h : AgreesOnRole D Q r) {m : Msg}
    (ht : typeEndpoint D (D.perf m) r) (S : Cfg Msg) :
    (Q.isUnknownD S m ↔ D.isUnknownD S m) ∧
    (Q.isValidD S m ↔ D.isValidD S m) ∧
    (Q.isViolationD S m ↔ D.isViolationD S m) := by
  have hres := resolvedD_agree h S m
  have hg := goodD_agree h ht S
  exact ⟨not_congr hres, and_congr hres hg, and_congr hres (not_congr hg)⟩

/-- **Local verification over the projected protocol agrees with global verification**
    (`proof.tex` Def. 3 + Lemma reconcile(i), with the projected protocol in the
    statement). Let `D` be causally local, `C` a `P`-safe closed global run, and `Q` any
    protocol agreeing with `D` at `r` (with agreement supplied explicitly). Then for every
    `r`-relevant `m`, the LOCAL verifier — protocol `Q`, store `Q.projectD C r` — decides
    (never `Unknown`), and its `Valid` / `Violation` verdicts are exactly the GLOBAL
    verifier's (protocol `D`, store `C`). -/
theorem local_protocol_verification_agrees (h : AgreesOnRole D Q r)
    (hloc : D.causalLocality) {C : Cfg Msg}
    (hcl : D.closedCfgD C) (hsafe : D.pSafeD C) {m : Msg} (hm : D.projectD C r m) :
    ¬ Q.isUnknownD (Q.projectD C r) m ∧
    (Q.isValidD (Q.projectD C r) m ↔ D.isValidD C m) ∧
    (Q.isViolationD (Q.projectD C r) m ↔ D.isViolationD C m) := by
  -- `m` is good globally (safe + closed), hence conformant, hence of an
  -- `r`-endpoint performative.
  have hgood : D.goodD C m :=
    good_of_safe_closed (D.toProto hloc) hcl hsafe hm.1
  have ht : typeEndpoint D (D.perf m) r := typeEndpoint_of_conformant hgood.1 hm.2
  -- Transfer the local verdict from `Q` to `D` over the (equal) projected store,
  -- then reconcile `D`'s projected store with the global store.
  have hstore : Q.projectD C r = D.projectD C r := projectD_agree h C r
  have hva := verdict_agree h ht (D.projectD C r)
  have hglobal := locally_verifiable_of_causalLocality hloc hcl hsafe hm
  refine ⟨?_, ?_, ?_⟩
  · rw [hstore]
    exact fun hu => hglobal.1 ((hva.1).1 hu)
  · rw [hstore, hva.2.1]
    exact hglobal.2.2.1
  · rw [hstore, hva.2.2]
    exact hglobal.2.2.2

/-! Axiom audit (informational output when this file is compiled). -/
#print axioms verdict_agree
#print axioms local_protocol_verification_agrees

end LeanCbcl.ProtoProjection
