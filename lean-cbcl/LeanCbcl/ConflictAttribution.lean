/-
  Conflict attribution — safety as a static condition for blaming one role.

  The `Proto` model has no exclusive choice: admission reads only a message's own
  predecessors, so two messages that the application treats as mutually exclusive can
  both be `Valid`. This file adds a conflict relation beside the protocol and asks when
  a conflict found in a store can be blamed on a single role. The frame is Singh's safety
  property (AAMAS 2012, "Semantics and Verification of Information-Based Protocols",
  §3.4): conflicting messages from different roles are safe only when a causally prior
  choice by one role separates them. Singh rules double binding out at design time; here
  the same condition makes every runtime conflict an equivocation with a named sender.

  What is proved:

  * A STATIC CONDITION, `LocalChoice`: performatives declared mutually exclusive have the
    same declared sender. It is decided by `checkLocalChoice` over a finite list of
    exclusive pairs (`checkLocalChoice_iff`).
  * ATTRIBUTION (`clash_attributable`, `clash_equivocates`): under `LocalChoice`, if two
    messages of a safe closed configuration clash — their causal cones contain directly
    conflicting messages — then the conflicting pair is present in the configuration and
    was sent by one role. Blame is sound by construction: `Equivocates C r` exhibits two
    present conflicting messages whose sender is `r`.
  * SAFETY FROM CONSISTENCY (`conflictFree_of_no_equivocation`): under `LocalChoice`, a
    safe closed configuration in which no role equivocates has no clash at all. This is
    Singh's safety, conditional on each role's own consistency.
  * LOCAL EVIDENCE (`clash_locally_evident`): a role that is an endpoint of both clashing
    messages already holds the conflicting pair in its own projection, by causal
    locality. It needs no third-party evidence to detect and attribute the conflict.
  * NECESSITY OF THE CONDITION (`AbruptCancel.unattributable`): Singh's Abrupt Cancel.
    Buyer's `cancel` and seller's `goods` are exclusive and have different senders. The
    full configuration is safe and closed, the two messages clash, and no role
    equivocates. Without `LocalChoice` a conflict can have no one to blame.

  Scope notes (read before citing):

  * `Conflicts` is additional data. `conflict` is an abstract relation on messages,
    required only to be typed by `excl`; nothing connects it to the deployed equivocation
    detector, to replacement links, or to state-layer supersession. `excl` is not part of
    the Rust protocol declaration.
  * Conflict does not enter admission. Both members of a conflicting pair are `Valid`
    (they are present in a safe closed configuration), so these theorems concern
    detection and attribution after the fact, not prevention.
  * `LocalChoice` is stated on DIRECT conflicts. A cross-role exclusion that is guarded by
    an earlier same-role choice (Singh's `deliver` against `reject`, guarded by `accept`
    against `reject`) is modelled by declaring only the guard as a direct conflict; the
    cross-role pair is then a clash, and attribution names the role that made the choice.
    No theorem here derives a guard from a protocol declaration.
  * `clash_locally_evident` needs one role to observe both clashing messages. Conflicts
    with no common observer need evidence exchange, which is not modelled.
-/
import LeanCbcl.RoleProgress

namespace LeanCbcl.ConflictAttribution

open LeanCbcl.EPP LeanCbcl.RoleProgress

/-- Conflict data beside a protocol. `excl t t'`: performatives declared mutually
    exclusive. `conflict m m'`: the two messages conflict directly (for example, they make
    exclusive moves in the same enactment). Every direct conflict is between exclusive
    performatives. -/
structure Conflicts {Role Perf Msg : Type} (P : Proto Role Perf Msg) where
  /-- Performatives declared mutually exclusive. -/
  excl : Perf → Perf → Prop
  /-- Direct conflict between messages. -/
  conflict : Msg → Msg → Prop
  typed : ∀ m m', conflict m m' → excl (P.perf m) (P.perf m')

variable {Role Perf Msg : Type} (P : Proto Role Perf Msg) (X : Conflicts P)

/-- **The static condition.** Exclusive performatives have one declared sender: every
    declared choice is made by a single role. -/
def LocalChoice : Prop := ∀ t t', X.excl t t' → P.psender t = P.psender t'

/-- `m` and `m'` clash: their causal cones contain directly conflicting messages. -/
def Clash (m m' : Msg) : Prop := ∃ q q', Cone P m q ∧ Cone P m' q' ∧ X.conflict q q'

/-- Role `r` equivocates in `C`: two directly conflicting messages sent by `r` are
    present. -/
def Equivocates (C : Cfg Msg) (r : Role) : Prop :=
  ∃ q q', C q ∧ C q' ∧ P.sender q = r ∧ P.sender q' = r ∧ X.conflict q q'

/-- No two present messages clash. -/
def ConflictFree (C : Cfg Msg) : Prop := ∀ m m', C m → C m' → ¬ Clash P X m m'

/-! ## Cones in closed configurations -/

/-- A closed configuration contains the cone of each of its messages. -/
theorem cone_present {C : Cfg Msg} (hcl : closedCfg P C) {m q : Msg} (hc : Cone P m q) :
    C m → C q := by
  induction hc with
  | refl m => exact id
  | step hp _ ih => exact fun hm => ih (hcl _ hm _ hp)

/-- In a safe closed configuration, an endpoint of a message is an endpoint of everything
    in its cone (causal locality, iterated). -/
theorem cone_endpoint {C : Cfg Msg} (hcl : closedCfg P C) (hsafe : pSafe P C) {r : Role}
    {m q : Msg} (hc : Cone P m q) : C m → endpoint P m r → endpoint P q r := by
  induction hc with
  | refl m => exact fun _ h => h
  | step hp _ ih =>
    intro hm hr
    obtain ⟨hpC, hep⟩ := localres P hcl hsafe hm hr _ hp
    exact ih hpC hep

/-! ## Attribution -/

/-- **Attribution.** Under `LocalChoice`, a clash between two messages of a safe closed
    configuration traces to a directly conflicting pair that is present in the
    configuration and has a single sender. -/
theorem clash_attributable (hL : LocalChoice P X) {C : Cfg Msg} (hcl : closedCfg P C)
    (hsafe : pSafe P C) {m m' : Msg} (hm : C m) (hm' : C m') (hc : Clash P X m m') :
    ∃ r q q', Cone P m q ∧ Cone P m' q' ∧ X.conflict q q' ∧ C q ∧ C q' ∧
      P.sender q = r ∧ P.sender q' = r := by
  obtain ⟨q, q', hq, hq', hx⟩ := hc
  have hCq : C q := cone_present P hcl hq hm
  have hCq' : C q' := cone_present P hcl hq' hm'
  have hs : P.sender q = P.psender (P.perf q) := (good_of_safe_closed P hcl hsafe hCq).1.1
  have hs' : P.sender q' = P.psender (P.perf q') := (good_of_safe_closed P hcl hsafe hCq').1.1
  exact ⟨P.sender q, q, q', hq, hq', hx, hCq, hCq', rfl,
    by rw [hs', hs]; exact (hL _ _ (X.typed q q' hx)).symm⟩

/-- **Every clash is an equivocation.** Under `LocalChoice`, a clash in a safe closed
    configuration means some role equivocated there. -/
theorem clash_equivocates (hL : LocalChoice P X) {C : Cfg Msg} (hcl : closedCfg P C)
    (hsafe : pSafe P C) {m m' : Msg} (hm : C m) (hm' : C m') (hc : Clash P X m m') :
    ∃ r, Equivocates P X C r := by
  obtain ⟨r, q, q', _, _, hx, hCq, hCq', hs, hs'⟩ :=
    clash_attributable P X hL hcl hsafe hm hm' hc
  exact ⟨r, q, q', hCq, hCq', hs, hs', hx⟩

/-- **Safety from consistency.** Under `LocalChoice`, if no role equivocates then no two
    messages clash. -/
theorem conflictFree_of_no_equivocation (hL : LocalChoice P X) {C : Cfg Msg}
    (hcl : closedCfg P C) (hsafe : pSafe P C) (h : ∀ r, ¬ Equivocates P X C r) :
    ConflictFree P X C := by
  intro m m' hm hm' hc
  obtain ⟨r, hr⟩ := clash_equivocates P X hL hcl hsafe hm hm' hc
  exact h r hr

/-- Both members of an equivocation are `Valid`: conflict is invisible to admission. -/
theorem equivocation_valid {C : Cfg Msg} (hcl : closedCfg P C) (hsafe : pSafe P C)
    {r : Role} (h : Equivocates P X C r) :
    ∃ q q', X.conflict q q' ∧ isValid P C q ∧ isValid P C q' := by
  obtain ⟨q, q', hq, hq', _, _, hx⟩ := h
  exact ⟨q, q', hx, valid_of_safe_closed P hcl hsafe hq, valid_of_safe_closed P hcl hsafe hq'⟩

/-- **Local evidence.** A role that is an endpoint of both clashing messages holds the
    equivocation in its own projection. -/
theorem clash_locally_evident (hL : LocalChoice P X) {C : Cfg Msg} (hcl : closedCfg P C)
    (hsafe : pSafe P C) {m m' : Msg} (hm : C m) (hm' : C m') (hc : Clash P X m m')
    {r : Role} (hr : endpoint P m r) (hr' : endpoint P m' r) :
    ∃ s, Equivocates P X (project P C r) s := by
  obtain ⟨s, q, q', hq, hq', hx, hCq, hCq', hs, hs'⟩ :=
    clash_attributable P X hL hcl hsafe hm hm' hc
  exact ⟨s, q, q', ⟨hCq, cone_endpoint P hcl hsafe hq hm hr⟩,
    ⟨hCq', cone_endpoint P hcl hsafe hq' hm' hr'⟩, hs, hs', hx⟩

/-! ## Deciding the static condition -/

/-- The check over a finite list of exclusive pairs. -/
def checkLocalChoice [DecidableEq Role] (psender : Perf → Role)
    (pairs : List (Perf × Perf)) : Bool :=
  pairs.all (fun x => decide (psender x.1 = psender x.2))

/-- The check decides `LocalChoice` when `pairs` lists the exclusive performatives. -/
theorem checkLocalChoice_iff [DecidableEq Role] (pairs : List (Perf × Perf))
    (hX : ∀ t t', X.excl t t' ↔ (t, t') ∈ pairs) :
    checkLocalChoice P.psender pairs = true ↔ LocalChoice P X := by
  constructor
  · intro h t t' ht
    exact of_decide_eq_true (List.all_eq_true.1 h (t, t') ((hX t t').1 ht))
  · intro h
    exact List.all_eq_true.2 (fun x hx => decide_eq_true (h x.1 x.2 ((hX x.1 x.2).2 hx)))

/-! ## Necessity: Abrupt Cancel

Singh's example of an enactable but unsafe protocol. The buyer orders; then the buyer may
cancel and the seller may send goods. `cancel` and `goods` are exclusive but are decided by
different roles, so `LocalChoice` fails, and the conflict in the full configuration has no
equivocating role. -/

namespace AbruptCancel

/-- The two roles. -/
inductive R where
  | buyer | seller
  deriving DecidableEq

/-- The three performatives; there is one message of each. -/
inductive T where
  | order | cancel | goods
  deriving DecidableEq

/-- Declared sender. -/
def snd : T → R
  | .order => .buyer
  | .cancel => .buyer
  | .goods => .seller

/-- `cancel` and `goods` each cite the `order`; every role receives every message. -/
def proto : Proto R T T where
  perf := id
  sender := snd
  recip := fun _ _ => True
  predRel := fun m p => (m = .cancel ∨ m = .goods) ∧ p = .order
  psender := snd
  precip := fun _ _ => True
  legalPred := fun t t' => (t = .cancel ∨ t = .goods) ∧ t' = .order
  clause := fun t S => (t = .cancel ∨ t = .goods) → S .order
  causalLocal := fun _ _ _ _ _ => Or.inr trivial

/-- `cancel` excludes `goods`. -/
def conflicts : Conflicts proto where
  excl := fun t t' => t = .cancel ∧ t' = .goods
  conflict := fun m m' => m = .cancel ∧ m' = .goods
  typed := fun _ _ h => h

/-- The exclusive pair has two different senders. -/
theorem not_localChoice : ¬ LocalChoice proto conflicts := by
  intro h
  exact nomatch h .cancel .goods ⟨rfl, rfl⟩

/-- The checker agrees. -/
theorem check_fails : checkLocalChoice proto.psender [(T.cancel, T.goods)] = false := by
  decide

/-- **No one to blame.** The configuration holding all three messages is safe and closed,
    `cancel` and `goods` clash, and no role equivocates. -/
theorem unattributable :
    closedCfg proto (fun _ => True) ∧ pSafe proto (fun _ => True) ∧
      Clash proto conflicts .cancel .goods ∧
      ∀ r, ¬ Equivocates proto conflicts (fun _ => True) r := by
  refine ⟨fun _ _ _ _ => trivial, ?_, ⟨.cancel, .goods, Cone.refl _, Cone.refl _, rfl, rfl⟩, ?_⟩
  · intro m _
    refine valid_not_violation proto ⟨fun _ _ => trivial, ⟨rfl, fun _ => Iff.rfl⟩,
      fun _ hp => hp, fun h => ⟨.order, ⟨h, rfl⟩, trivial, rfl⟩⟩
  · intro r ⟨q, q', _, _, hs, hs', hq, hq'⟩
    subst hq hq'
    have e : R.buyer = R.seller := hs.trans hs'.symm
    exact nomatch e

end AbruptCancel

end LeanCbcl.ConflictAttribution
