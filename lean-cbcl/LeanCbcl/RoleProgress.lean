/-
  Role progress — enabledness, deadlock freedom and completion for the EPP model.

  `EPP.lean` / `EPPCompletion.lean` relate ALREADY-COMPLETE configurations and local
  runs. They do not say that an incomplete configuration can be extended: the empty
  configuration is safe and closed whatever the obligations are. This file supplies the
  missing progress layer for the same abstract `Proto` / `Obligations` model. Lean core
  only, no new axioms beyond those `EPP.lean` already uses.

  What is proved:

  * A STATIC CONDITION, `Realizing J O`: every obligation has a witness that is
    `Realizable` — conformant, clause-satisfied by its own predecessors, with finitely
    many predecessors that are hereditarily realizable, all of it work in `J` (the acts
    honest participants have undertaken to perform).
  * ENABLEDNESS (`deadlock_free`): under `Realizing`, any pending obligation in any safe
    closed configuration has an enabled message in the causal cone of one of its
    witnesses, that message is undertaken work (`J`), and it is already justified by its
    SENDER'S OWN projection (`enabled_locally`, from causal locality). So a safe closed
    incomplete configuration is never stuck (`incomplete_has_enabled`).
  * NO DISABLING (`enabled_persistent`): an enabled message stays enabled until it is
    sent, whatever else is sent. This is why no directed-choice restriction is needed in
    THIS model.
  * COMPLETION (`Run.eventually_complete`): in a run whose store only admits
    valid-on-arrival messages and which eventually performs undertaken work once it is
    enabled (weak fairness), every obligation is eventually and permanently discharged;
    with finitely many obligations the store is eventually always `pComplete`.
    Participants outside `J` are unconstrained except that the store admits only valid
    messages.
  * NECESSITY (`realizing_of_complete`): if predecessors are well-founded and finite,
    any `pComplete` configuration witnesses `Realizing`. Hence, for such protocols,
    completion is reachable exactly when the static condition holds.
  * HONESTY IS NOT ENOUGH (`Run.stuck_of_noInitial`): if every clause demands some
    predecessor, no message is ever admitted from the empty store, so every run — however
    honest and fair — is stuck with all obligations pending.
  * A TYPE-LEVEL CHECK (`realizing_of_perfRealizable`): `PerfRealizable` is a least
    fixed point over performatives. Given a message supply (`Supply`), it yields
    message-level realizable witnesses.

  Scope notes (read before citing):

  * The store here is the GLOBAL store. Delivery to roles is not modelled in this file;
    `enabled_locally` shows the sender needs only its own projection, and
    `Bridge.eventually_present_valid` is the separate delivery result.
  * The `Proto` model has no exclusive choice, deadline or resource budget: a clause
    reads only the fixed predecessors of a message, so nothing sent later can invalidate
    an enabled act. Deployed dialects with state-layer admission or budgets can lose
    enabledness in ways this model cannot express; `ConsensusFree/OwnerTermination.lean`
    treats one such lifecycle directly.
  * `Supply` and the witness-closure premise of `realizing_of_perfRealizable` are
    hypotheses, not facts about the deployed message type. No decision procedure for
    `PerfRealizable` is implemented, and nothing here is connected to the Rust runtime.
  * Fairness (`Run.fair`) is assumed, not derived. It is where honesty enters.
-/
import LeanCbcl.EPPCompletion

namespace LeanCbcl.RoleProgress

open LeanCbcl.EPP

variable {Role Perf Msg : Type} (P : Proto Role Perf Msg)

/-! ## Enabled messages -/

/-- All predecessor types of `m`, independent of any store. -/
def predTypes (m : Msg) : Perf → Prop := fun t => ∃ p, P.predRel m p ∧ P.perf p = t

/-- Once `m` is resolved, the present predecessor types are all its predecessor types. -/
theorem predTypesPresent_of_resolved {S : Cfg Msg} {m : Msg} (h : resolved P S m) :
    predTypesPresent P S m = predTypes P m := by
  funext t
  apply propext
  constructor
  · intro ⟨p, hp, _, he⟩; exact ⟨p, hp, he⟩
  · intro ⟨p, hp, he⟩; exact ⟨p, hp, h p hp, he⟩

/-- `m` is enabled in `C`: not yet sent, and it would be `Valid` on arrival. -/
def enabled (C : Cfg Msg) (m : Msg) : Prop := ¬ C m ∧ isValid P C m

theorem valid_not_violation {S : Cfg Msg} {m : Msg} (h : isValid P S m) :
    ¬ isViolation P S m := fun hv => hv.2 h.2

/-- **No disabling.** An enabled message remains enabled until it is sent, whatever else
    is added to the store. -/
theorem enabled_persistent {C C' : Cfg Msg} (h : ∀ x, C x → C' x) {m : Msg}
    (he : enabled P C m) : C' m ∨ enabled P C' m :=
  (Classical.em (C' m)).elim Or.inl (fun hn => Or.inr ⟨hn, valid_stable P h he.2⟩)

/-- The store after sending `m`. -/
def extend (C : Cfg Msg) (m : Msg) : Cfg Msg := fun x => C x ∨ x = m

/-- Sending an enabled message preserves safety and causal closure. -/
theorem extend_safe_closed {C : Cfg Msg} (hcl : closedCfg P C) (hsafe : pSafe P C)
    {m : Msg} (he : enabled P C m) :
    closedCfg P (extend C m) ∧ pSafe P (extend C m) := by
  have hsub : ∀ x, C x → extend C m x := fun x hx => Or.inl hx
  constructor
  · intro x hx p hp
    cases hx with
    | inl hx => exact Or.inl (hcl x hx p hp)
    | inr hx => subst hx; exact Or.inl (he.2.1 p hp)
  · intro x hx
    cases hx with
    | inl hx =>
      exact valid_not_violation P (valid_stable P hsub (valid_of_safe_closed P hcl hsafe hx))
    | inr hx => subst hx; exact valid_not_violation P (valid_stable P hsub he.2)

/-- **Local enabledness.** An enabled message is already `Valid` against its sender's own
    projection: by causal locality every predecessor is sender-relevant. The sender needs
    no third-party knowledge to act. -/
theorem enabled_locally {C : Cfg Msg} (hcl : closedCfg P C) (hsafe : pSafe P C)
    {m : Msg} (he : enabled P C m) : isValid P (project P C (P.sender m)) m := by
  obtain ⟨_, hres, hconf, hns, hclause⟩ := he
  have hloc : ∀ p, P.predRel m p → project P C (P.sender m) p := by
    intro p hp
    have hpC : C p := hres p hp
    have hgp : good P C p := good_of_safe_closed P hcl hsafe hpC
    have htp := P.causalLocal (P.perf m) (P.perf p) (P.sender m) (hns p hp)
      (Or.inl hconf.1.symm)
    refine ⟨hpC, ?_⟩
    cases htp with
    | inl h => exact Or.inl (by rw [hgp.1.1]; exact h)
    | inr h => exact Or.inr ((hgp.1.2 _).2 h)
  refine ⟨hloc, hconf, hns, ?_⟩
  rw [predTypesPresent_of_resolved P hloc, ← predTypesPresent_of_resolved P hres]
  exact hclause

/-! ## The static condition -/

/-- `m` is realizable using work in `J`: `m` itself is in `J`, is conformant, names only
    legal predecessors, has finitely many predecessors, satisfies its clause once they
    are all present, and every predecessor is realizable in turn. Being inductive, the
    predicate forces the ancestry of `m` to be well-founded: no circular wait. -/
inductive Realizable (J : Msg → Prop) : Msg → Prop
  | intro (m : Msg) (ps : List Msg) :
      J m → conformant P m → noSpurious P m →
      (∀ p, P.predRel m p ↔ p ∈ ps) →
      P.clause (P.perf m) (predTypes P m) →
      (∀ p, P.predRel m p → Realizable J p) → Realizable J m

/-- `Cone m q`: `q` is `m` or a causal ancestor of `m`. -/
inductive Cone : Msg → Msg → Prop
  | refl (m : Msg) : Cone m m
  | step {m p q : Msg} : P.predRel m p → Cone p q → Cone m q

/-- Every obligation has a realizable witness. -/
def Realizing (J : Msg → Prop) (O : Obligations P) : Prop :=
  ∀ r W, O.oblig r W → ∃ w, W w ∧ Realizable P J w

/-- A realizable message that has not been sent has an enabled message in its cone. No
    assumption on the store is needed. -/
theorem enabled_of_realizable {J : Msg → Prop} (C : Cfg Msg) {m : Msg}
    (hr : Realizable P J m) : ¬ C m → ∃ q, Cone P m q ∧ enabled P C q ∧ J q := by
  induction hr with
  | intro m ps hJ hconf hns _ hclause _ ih =>
    intro hm
    cases Classical.em (resolved P C m) with
    | inl hres =>
      refine ⟨m, Cone.refl m, ⟨hm, hres, hconf, hns, ?_⟩, hJ⟩
      rw [predTypesPresent_of_resolved P hres]; exact hclause
    | inr hres =>
      have hex : ∃ p, P.predRel m p ∧ ¬ C p := by
        apply Classical.byContradiction
        intro hne
        exact hres (fun p hp => Classical.byContradiction (fun hnp => hne ⟨p, hp, hnp⟩))
      obtain ⟨p, hp, hnp⟩ := hex
      obtain ⟨q, hc, he, hq⟩ := ih p hp hnp
      exact ⟨q, Cone.step hp hc, he, hq⟩

/-- **Enabledness.** Under the static condition, every pending obligation of a safe
    closed configuration has a witness `w` and an enabled message `q` in the cone of `w`
    such that `q` is undertaken work and is justified by its sender's own projection. -/
theorem deadlock_free {J : Msg → Prop} (O : Obligations P) (hR : Realizing P J O)
    {C : Cfg Msg} (hcl : closedCfg P C) (hsafe : pSafe P C)
    {r : Role} {W : Msg → Prop} (hW : O.oblig r W)
    (hpend : ¬ ∃ w, W w ∧ C w ∧ isValid P C w) :
    ∃ w q, W w ∧ Cone P w q ∧ enabled P C q ∧ J q ∧
      isValid P (project P C (P.sender q)) q := by
  obtain ⟨w, hWw, hr⟩ := hR r W hW
  have hnw : ¬ C w := fun hw => hpend ⟨w, hWw, hw, valid_of_safe_closed P hcl hsafe hw⟩
  obtain ⟨q, hc, he, hq⟩ := enabled_of_realizable P C hr hnw
  exact ⟨w, q, hWw, hc, he, hq, enabled_locally P hcl hsafe he⟩

/-- **Deadlock freedom.** A safe closed configuration that is not complete has an enabled
    message that is undertaken work. -/
theorem incomplete_has_enabled {J : Msg → Prop} (O : Obligations P)
    (hR : Realizing P J O) {C : Cfg Msg} (hcl : closedCfg P C) (hsafe : pSafe P C)
    (hinc : ¬ pComplete P O C) : ∃ q, enabled P C q ∧ J q := by
  apply Classical.byContradiction
  intro hno
  apply hinc
  refine ⟨hsafe, hcl, ?_⟩
  intro r W hW
  apply Classical.byContradiction
  intro hpend
  obtain ⟨_, q, _, _, he, hq, _⟩ := deadlock_free P O hR hcl hsafe hW hpend
  exact hno ⟨q, he, hq⟩

/-! ## Runs and completion -/

/-- A run of the global store. Only valid-on-arrival messages are admitted (the monitor),
    possibly many per step and from any participant. `fair` is the honesty-and-fairness
    premise: undertaken work that is enabled is eventually present. -/
structure Run (P : Proto Role Perf Msg) (J : Msg → Prop) where
  /-- The store after `n` steps. -/
  store : Nat → Cfg Msg
  init_closed : closedCfg P (store 0)
  init_safe : pSafe P (store 0)
  mono : ∀ n m, store n m → store (n + 1) m
  sound : ∀ n m, store (n + 1) m → store n m ∨ isValid P (store n) m
  fair : ∀ n m, J m → enabled P (store n) m → ∃ n', store n' m

/-- Finitely many eventually-always facts hold eventually-always together. -/
theorem eventually_always_list {α : Type} (Q : α → Nat → Prop) (l : List α)
    (h : ∀ x, x ∈ l → ∃ n, ∀ n', n ≤ n' → Q x n') :
    ∃ N, ∀ x, x ∈ l → ∀ n', N ≤ n' → Q x n' := by
  induction l with
  | nil => exact ⟨0, fun _ hx => nomatch hx⟩
  | cons a l ih =>
    obtain ⟨n1, h1⟩ := h a (List.mem_cons.2 (Or.inl rfl))
    obtain ⟨n2, h2⟩ := ih (fun x hx => h x (List.mem_cons.2 (Or.inr hx)))
    refine ⟨n1 + n2, fun x hx n' hn => ?_⟩
    cases List.mem_cons.1 hx with
    | inl hxa => subst hxa; exact h1 n' (by omega)
    | inr hxl => exact h2 x hxl n' (by omega)

namespace Run

variable {P} {J : Msg → Prop}

theorem mono_add (R : Run P J) (n k : Nat) {m : Msg} (h : R.store n m) :
    R.store (n + k) m := by
  induction k with
  | zero => exact h
  | succ k ih => exact R.mono _ _ ih

theorem mono_le (R : Run P J) {n n' : Nat} (hle : n ≤ n') {m : Msg}
    (h : R.store n m) : R.store n' m := by
  have h' := R.mono_add n (n' - n) h
  have e : n + (n' - n) = n' := by omega
  rw [e] at h'
  exact h'

/-- Every store of a run is safe and closed. -/
theorem safe_closed (R : Run P J) (n : Nat) :
    closedCfg P (R.store n) ∧ pSafe P (R.store n) := by
  induction n with
  | zero => exact ⟨R.init_closed, R.init_safe⟩
  | succ n ih =>
    obtain ⟨hcl, hsafe⟩ := ih
    have hsub : ∀ x, R.store n x → R.store (n + 1) x := R.mono n
    have hval : ∀ x, R.store (n + 1) x → isValid P (R.store n) x := fun x hx =>
      (R.sound n x hx).elim (fun h => valid_of_safe_closed P hcl hsafe h) id
    constructor
    · intro x hx p hp; exact hsub p ((hval x hx).1 p hp)
    · intro x hx; exact valid_not_violation P (valid_stable P hsub (hval x hx))

/-- A realizable message is eventually present. -/
theorem eventually_present (R : Run P J) {m : Msg} (hr : Realizable P J m) :
    ∃ n, R.store n m := by
  induction hr with
  | intro m ps hJ hconf hns hps hclause _ ih =>
    obtain ⟨N, hN⟩ := eventually_always_list (fun p n => R.store n p) ps (fun p hp => by
      obtain ⟨n, hn⟩ := ih p ((hps p).2 hp)
      exact ⟨n, fun n' hle => R.mono_le hle hn⟩)
    cases Classical.em (R.store N m) with
    | inl h => exact ⟨N, h⟩
    | inr h =>
      have hres : resolved P (R.store N) m :=
        fun p hp => hN p ((hps p).1 hp) N (Nat.le_refl N)
      exact R.fair N m hJ
        ⟨h, hres, hconf, hns, by rw [predTypesPresent_of_resolved P hres]; exact hclause⟩

/-- **Per-obligation completion.** Under the static condition every obligation is
    eventually, and from then on always, discharged. -/
theorem eventually_discharged (R : Run P J) (O : Obligations P) (hR : Realizing P J O)
    {r : Role} {W : Msg → Prop} (hW : O.oblig r W) :
    ∃ n, ∀ n', n ≤ n' → ∃ w, W w ∧ R.store n' w ∧ isValid P (R.store n') w := by
  obtain ⟨w, hWw, hr⟩ := hR r W hW
  obtain ⟨n, hn⟩ := R.eventually_present hr
  refine ⟨n, fun n' hle => ⟨w, hWw, R.mono_le hle hn, ?_⟩⟩
  obtain ⟨hcl, hsafe⟩ := R.safe_closed n'
  exact valid_of_safe_closed P hcl hsafe (R.mono_le hle hn)

/-- **Completion.** With finitely many obligations, the store is eventually always
    `pComplete`. -/
theorem eventually_complete (R : Run P J) (O : Obligations P) (hR : Realizing P J O)
    (obs : List (Role × (Msg → Prop))) (hobs : ∀ r W, O.oblig r W → (r, W) ∈ obs) :
    ∃ n, ∀ n', n ≤ n' → pComplete P O (R.store n') := by
  obtain ⟨N, hN⟩ := eventually_always_list
    (fun (x : Role × (Msg → Prop)) n =>
      O.oblig x.1 x.2 → ∃ w, x.2 w ∧ R.store n w ∧ isValid P (R.store n) w) obs
    (fun x _ => by
      cases Classical.em (O.oblig x.1 x.2) with
      | inl hx =>
        obtain ⟨n, hn⟩ := R.eventually_discharged O hR hx
        exact ⟨n, fun n' hle _ => hn n' hle⟩
      | inr hx => exact ⟨0, fun _ _ h => absurd h hx⟩)
  refine ⟨N, fun n' hle => ?_⟩
  obtain ⟨hcl, hsafe⟩ := R.safe_closed n'
  exact ⟨hsafe, hcl, fun r W hW => hN (r, W) (hobs r W hW) n' hle hW⟩

end Run

/-! ## Necessity of the static condition -/

/-- In a safe closed configuration with well-founded, finite predecessors, every present
    message is realizable using the messages present. -/
theorem realizable_of_safe_closed
    (hwf : WellFounded (fun p m : Msg => P.predRel m p))
    (hfin : ∀ m, ∃ ps : List Msg, ∀ p, P.predRel m p ↔ p ∈ ps)
    {C : Cfg Msg} (hcl : closedCfg P C) (hsafe : pSafe P C) (m : Msg) :
    C m → Realizable P C m := by
  refine hwf.induction (C := fun m => C m → Realizable P C m) m ?_
  intro m ih hm
  obtain ⟨ps, hps⟩ := hfin m
  have hg := good_of_safe_closed P hcl hsafe hm
  have hres : resolved P C m := fun p hp => hcl m hm p hp
  refine Realizable.intro m ps hm hg.1 hg.2.1 hps ?_ (fun p hp => ih p hp (hres p hp))
  rw [← predTypesPresent_of_resolved P hres]; exact hg.2.2

/-- **Necessity.** Any complete configuration witnesses the static condition, with the
    messages it contains as the undertaken work. -/
theorem realizing_of_complete
    (hwf : WellFounded (fun p m : Msg => P.predRel m p))
    (hfin : ∀ m, ∃ ps : List Msg, ∀ p, P.predRel m p ↔ p ∈ ps)
    (O : Obligations P) {C : Cfg Msg} (hc : pComplete P O C) : Realizing P C O := by
  intro r W hW
  obtain ⟨w, hWw, hCw, _⟩ := hc.2.2 r W hW
  exact ⟨w, hWw, realizable_of_safe_closed P hwf hfin hc.2.1 hc.1 w hCw⟩

/-! ## Honesty alone is not enough -/

/-- Every clause demands at least one predecessor type: the protocol has no initial
    performative. -/
def NoInitial : Prop := ∀ t S, P.clause t S → ∃ t', S t'

theorem not_realizable_of_noInitial (h : NoInitial P) {J : Msg → Prop} {m : Msg} :
    ¬ Realizable P J m := by
  intro hr
  induction hr with
  | intro m ps _ _ _ _ hclause _ ih =>
    obtain ⟨_, p, hp, _⟩ := h _ _ hclause
    exact ih p hp

theorem not_valid_of_empty (h : NoInitial P) {S : Cfg Msg} (hS : ∀ x, ¬ S x) (m : Msg) :
    ¬ isValid P S m := by
  intro ⟨_, _, _, hclause⟩
  obtain ⟨_, p, _, hp, _⟩ := h _ _ hclause
  exact hS p hp

/-- **Stuck however honest.** Without an initial performative, a run that starts empty
    stays empty: no participant can ever act without a violation, so every obligation
    stays pending, whatever `J` and fairness say. -/
theorem Run.stuck_of_noInitial (h : NoInitial P) {J : Msg → Prop} (R : Run P J)
    (h0 : ∀ x, ¬ R.store 0 x) : ∀ n x, ¬ R.store n x := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih =>
    intro x hx
    exact (R.sound n x hx).elim (ih x) (not_valid_of_empty P h ih x)

/-! ## A type-level check -/

/-- Performative-level realizability for honest roles `H`: a least fixed point over
    performatives. `t` is realizable when its declared sender is honest and some finite
    set of legal predecessor types, each realizable, satisfies its clause. -/
inductive PerfRealizable (H : Role → Prop) : Perf → Prop
  | intro (t : Perf) (ts : List Perf) :
      H (P.psender t) →
      (∀ t', t' ∈ ts → P.legalPred t t') →
      P.clause t (fun t' => t' ∈ ts) →
      (∀ t', t' ∈ ts → PerfRealizable H t') → PerfRealizable H t

/-- Message supply: for any performative and any finite list of predecessors, a
    conformant message of that type with exactly those predecessors exists. A hypothesis
    about the message type, not a theorem about deployed messages. -/
def Supply : Prop :=
  ∀ (t : Perf) (ps : List Msg),
    ∃ m, P.perf m = t ∧ conformant P m ∧ ∀ p, P.predRel m p ↔ p ∈ ps

theorem pick_list (Q : Msg → Prop) (ts : List Perf)
    (h : ∀ t', t' ∈ ts → ∃ m, P.perf m = t' ∧ Q m) :
    ∃ ps : List Msg, (∀ p, p ∈ ps → Q p ∧ P.perf p ∈ ts) ∧
      (∀ t', t' ∈ ts → ∃ p, p ∈ ps ∧ P.perf p = t') := by
  induction ts with
  | nil => exact ⟨[], (fun _ hp => nomatch hp), (fun _ ht => nomatch ht)⟩
  | cons a ts ih =>
    obtain ⟨m, hm, hQm⟩ := h a (List.mem_cons.2 (Or.inl rfl))
    obtain ⟨ps, h1, h2⟩ := ih (fun t' ht => h t' (List.mem_cons.2 (Or.inr ht)))
    refine ⟨m :: ps, ?_, ?_⟩
    · intro p hp
      cases List.mem_cons.1 hp with
      | inl hpm => subst hpm; exact ⟨hQm, List.mem_cons.2 (Or.inl hm)⟩
      | inr hpl => exact ⟨(h1 p hpl).1, List.mem_cons.2 (Or.inr (h1 p hpl).2)⟩
    · intro t' ht
      cases List.mem_cons.1 ht with
      | inl hta => exact ⟨m, List.mem_cons.2 (Or.inl rfl), hta ▸ hm⟩
      | inr htl =>
        obtain ⟨p, hp, he⟩ := h2 t' htl
        exact ⟨p, List.mem_cons.2 (Or.inr hp), he⟩

/-- Under message supply, a realizable performative has a realizable message whose whole
    cone is sent by honest roles. -/
theorem realizable_of_perfRealizable (hS : Supply P) {H : Role → Prop} {t : Perf}
    (h : PerfRealizable P H t) :
    ∃ m, P.perf m = t ∧ Realizable P (fun m => H (P.sender m)) m := by
  induction h with
  | intro t ts hH hleg hclause _ ih =>
    obtain ⟨ps, h1, h2⟩ := pick_list P (Realizable P (fun m => H (P.sender m))) ts ih
    obtain ⟨m, hm, hconf, hps⟩ := hS t ps
    have hpt : predTypes P m = (fun t' => t' ∈ ts) := by
      funext t'
      apply propext
      constructor
      · intro ⟨p, hp, he⟩; exact he ▸ (h1 p ((hps p).1 hp)).2
      · intro ht
        obtain ⟨p, hp, he⟩ := h2 t' ht
        exact ⟨p, (hps p).2 hp, he⟩
    refine ⟨m, hm, Realizable.intro m ps ?_ hconf ?_ hps ?_
      (fun p hp => (h1 p ((hps p).1 hp)).1)⟩
    · show H (P.sender m)
      rw [hconf.1, hm]; exact hH
    · intro p hp
      rw [hm]; exact hleg _ (h1 p ((hps p).1 hp)).2
    · rw [hm, hpt]; exact hclause

/-- **Type-level sufficiency.** If every obligation is performative-shaped — it names a
    realizable performative and accepts any realizable message of that type — then the
    static condition holds for the work of honest roles. -/
theorem realizing_of_perfRealizable (hS : Supply P) {H : Role → Prop} (O : Obligations P)
    (hO : ∀ r W, O.oblig r W → ∃ t, PerfRealizable P H t ∧
      ∀ m, P.perf m = t → Realizable P (fun m => H (P.sender m)) m → W m) :
    Realizing P (fun m => H (P.sender m)) O := by
  intro r W hW
  obtain ⟨t, ht, hclosed⟩ := hO r W hW
  obtain ⟨m, hm, hr⟩ := realizable_of_perfRealizable P hS ht
  exact ⟨m, hclosed m hm hr, hr⟩

/-! ## Non-vacuity: a request/reply protocol

The premises are jointly satisfiable. Roles, performatives and messages are all `Bool`:
`false` is the request (and its sender), `true` the reply (and its sender). The reply
must cite the request; the obligation is that a reply is present. -/

namespace RequestReply

/-- Request (`false`) then reply (`true`); every role receives every message. -/
def proto : Proto Bool Bool Bool where
  perf := id
  sender := id
  recip := fun _ _ => True
  predRel := fun m p => m = true ∧ p = false
  psender := id
  precip := fun _ _ => True
  legalPred := fun t t' => t = true ∧ t' = false
  clause := fun t S => t = true → S false
  causalLocal := fun _ _ _ _ _ => Or.inr trivial

/-- Every role is owed a reply. -/
def obligations : Obligations proto where
  oblig := fun _ W => W = (fun m => m = true)
  obligRel := fun _ _ _ _ _ => Or.inr trivial

theorem request_realizable : Realizable proto (fun _ => True) false :=
  Realizable.intro false [] trivial ⟨rfl, fun _ => Iff.rfl⟩
    (fun _ hp => nomatch hp.1)
    (fun _ => ⟨(fun hp => nomatch hp.1), (fun hp => nomatch hp)⟩)
    (fun h => nomatch h)
    (fun _ hp => nomatch hp.1)

theorem reply_realizable : Realizable proto (fun _ => True) true :=
  Realizable.intro true [false] trivial ⟨rfl, fun _ => Iff.rfl⟩
    (fun _ hp => ⟨rfl, hp.2⟩)
    (fun _ => ⟨fun hp => List.mem_cons.2 (Or.inl hp.2),
      fun hp => ⟨rfl, (List.mem_cons.1 hp).elim id (fun h => nomatch h)⟩⟩)
    (fun _ => ⟨false, ⟨rfl, rfl⟩, rfl⟩)
    (fun _ hp => hp.2 ▸ request_realizable)

theorem realizing : Realizing proto (fun _ => True) obligations := by
  intro r W hW
  subst hW
  exact ⟨true, rfl, reply_realizable⟩

/-- The request arrives at step 1 and the reply at step 2. -/
def run : Run proto (fun _ => True) where
  store := fun n m => (m = false ∧ 1 ≤ n) ∨ (m = true ∧ 2 ≤ n)
  init_closed := by
    intro m hm
    cases hm with
    | inl h => exact absurd h.2 (by omega)
    | inr h => exact absurd h.2 (by omega)
  init_safe := by
    intro m hm
    cases hm with
    | inl h => exact absurd h.2 (by omega)
    | inr h => exact absurd h.2 (by omega)
  mono := by
    intro n m h
    cases h with
    | inl h => exact Or.inl ⟨h.1, by omega⟩
    | inr h => exact Or.inr ⟨h.1, by omega⟩
  sound := by
    intro n m h
    refine Or.inr ?_
    cases h with
    | inl h =>
      obtain ⟨hm, _⟩ := h
      subst hm
      exact ⟨(fun _ hp => nomatch hp.1), ⟨rfl, fun _ => Iff.rfl⟩,
        (fun _ hp => nomatch hp.1), (fun e => nomatch e)⟩
    | inr h =>
      obtain ⟨hm, hn⟩ := h
      subst hm
      have hreq : (false = false ∧ 1 ≤ n) ∨ (false = true ∧ 2 ≤ n) :=
        Or.inl ⟨rfl, by omega⟩
      exact ⟨fun p hp => hp.2 ▸ hreq, ⟨rfl, fun _ => Iff.rfl⟩,
        fun _ hp => ⟨rfl, hp.2⟩, fun _ => ⟨false, ⟨rfl, rfl⟩, hreq, rfl⟩⟩
  fair := by
    intro n m _ _
    refine ⟨2, ?_⟩
    cases m with
    | false => exact Or.inl ⟨rfl, by omega⟩
    | true => exact Or.inr ⟨rfl, by omega⟩

/-- The general completion theorem applies: this run is eventually always complete. -/
theorem completes : ∃ n, ∀ n', n ≤ n' → pComplete proto obligations (run.store n') :=
  run.eventually_complete obligations realizing
    [(false, fun m => m = true), (true, fun m => m = true)]
    (fun r W hW => by
      subst hW
      cases r with
      | false => exact List.mem_cons.2 (Or.inl rfl)
      | true => exact List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inl rfl))))

/-- The request is an initial performative, so `NoInitial` fails here. -/
theorem not_noInitial : ¬ NoInitial proto := by
  intro h
  obtain ⟨_, ht⟩ := h false (fun _ => False) (fun e => nomatch e)
  exact ht

end RequestReply

end LeanCbcl.RoleProgress
