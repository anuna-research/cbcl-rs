/-
  Enactability — a decision procedure for the static condition of `RoleProgress.lean`.

  `RoleProgress.lean` proves progress from `Realizing`, and offers `PerfRealizable` as a
  type-level sufficient condition, but implements no decision procedure for it. This file
  supplies one for protocols given by a finite clause table, and shows that the type-level
  condition is exact. The frame is Singh's enactability (AAMAS 2012, "Semantics and
  Verification of Information-Based Protocols", Def. 13): a protocol is enactable when
  some viable enactment produces what it declares. Here the unit is a performative, and
  "viable enactment" is a safe closed configuration.

  What is proved:

  * A CHECKER (`Table.enactable`): the least fixed point over a finite list of
    performatives, computed by `perfs.length` rounds of a monotone step.
  * SOUND AND COMPLETE (`Table.enactable_iff`): for a table that `Represents` a protocol
    and whose clause evaluator is monotone, the checker returns `true` on `t` exactly when
    `PerfRealizable P H t`.
  * THE TYPE-LEVEL CONDITION IS EXACT (`perfRealizable_of_realizable`): any message
    realizable by the work of honest roles has a `PerfRealizable` performative. With
    `realizable_of_perfRealizable` this makes `PerfRealizable` necessary as well as
    sufficient, under `Supply`.
  * WHAT THE CHECKER MEANS (`Table.enactable_iff_occurs`): with every role taken as
    willing, a performative passes the check exactly when a message of that performative
    occurs in some safe closed configuration. A performative that fails the check is dead
    in every such configuration (`Table.present_enactable`), whatever participants do.
  * DISCHARGING THE PROGRESS PREMISE (`Table.realizing_of_checkEnactable`,
    `Table.checked_incomplete_has_enabled`): a passing check on the performatives that
    obligations name yields `Realizing`, hence deadlock freedom.

  Scope notes (read before citing):

  * `Represents` is a hypothesis relating a table to an abstract `Proto`. No table is
    derived here from `ConcreteProjection.Protocol` or from the Rust `CausalProtocol`;
    which reading of `Single`/`Any`/`All` the deployed verifier uses is not fixed by this
    file. The clause evaluator must be monotone (`Table.Mono`), which holds for
    `NodeRef.holds` but is assumed, not derived.
  * Enactability is existential and cooperative: it says a performative can occur if the
    roles in `H` do their part. It gives no guarantee against a participant who withholds
    work; that is the fairness premise of `Run`.
  * The `Proto` model has no exclusive choice, so here enactability of the obligations
    already gives completion of fair runs. Singh's separate liveness property (an
    enactable protocol that can reach a state with no completion) needs a model with
    disabling and is not treated.
  * `Supply`, well-founded predecessors and finite predecessors are hypotheses of the
    occurrence theorems, as in `RoleProgress.lean`.
-/
import LeanCbcl.RoleProgress

namespace LeanCbcl.Enactability

open LeanCbcl.EPP LeanCbcl.RoleProgress

/-! ## The type-level condition is exact -/

section Exact

variable {Role Perf Msg : Type} (P : Proto Role Perf Msg)

/-- Realizability is monotone in the undertaken work. -/
theorem realizable_mono {J J' : Msg → Prop} (h : ∀ m, J m → J' m) {m : Msg}
    (hr : Realizable P J m) : Realizable P J' m := by
  induction hr with
  | intro m ps hJ hconf hns hps hclause _ ih =>
    exact Realizable.intro m ps (h m hJ) hconf hns hps hclause ih

/-- **Exactness.** A message realizable by the work of roles in `H` has a performative
    that is realizable at the type level. The converse, under `Supply`, is
    `realizable_of_perfRealizable`. -/
theorem perfRealizable_of_realizable {H : Role → Prop} {m : Msg}
    (hr : Realizable P (fun m => H (P.sender m)) m) : PerfRealizable P H (P.perf m) := by
  induction hr with
  | intro m ps hJ hconf hns hps hclause _ ih =>
    have hpt : predTypes P m = (fun t' => t' ∈ ps.map P.perf) := by
      funext t'
      apply propext
      constructor
      · intro ⟨p, hp, he⟩; exact List.mem_map.2 ⟨p, (hps p).1 hp, he⟩
      · intro ht
        obtain ⟨p, hp, he⟩ := List.mem_map.1 ht
        exact ⟨p, (hps p).2 hp, he⟩
    refine PerfRealizable.intro (P.perf m) (ps.map P.perf) (hconf.1 ▸ hJ) ?_ ?_ ?_
    · intro t' ht
      obtain ⟨p, hp, he⟩ := List.mem_map.1 ht
      exact he ▸ hns p ((hps p).2 hp)
    · rw [← hpt]; exact hclause
    · intro t' ht
      obtain ⟨p, hp, he⟩ := List.mem_map.1 ht
      exact he ▸ ih p ((hps p).2 hp)

/-- A cone extends along one more predecessor edge. -/
theorem cone_snoc {m q p : Msg} (hc : Cone P m q) (hp : P.predRel q p) : Cone P m p := by
  induction hc with
  | refl m => exact Cone.step hp (Cone.refl p)
  | step h _ ih => exact Cone.step h (ih hp)

/-- Everything in the cone of a realizable message is realizable. -/
theorem realizable_of_cone {J : Msg → Prop} {m q : Msg} (hc : Cone P m q) :
    Realizable P J m → Realizable P J q := by
  induction hc with
  | refl m => exact id
  | step hp _ ih =>
    intro hr
    cases hr with
    | intro _ ps _ _ _ _ _ hpreds => exact ih (hpreds _ hp)

/-- A realizable message is valid once its predecessors are present. -/
theorem valid_of_realizable {J : Msg → Prop} {C : Cfg Msg} {m : Msg}
    (hr : Realizable P J m) (hres : resolved P C m) : isValid P C m := by
  cases hr with
  | intro _ ps _ hconf hns _ hclause _ =>
    exact ⟨hres, hconf, hns, by rw [predTypesPresent_of_resolved P hres]; exact hclause⟩

/-- **A realizable message occurs.** Its causal cone is a safe closed configuration. -/
theorem cone_safe_closed {J : Msg → Prop} {m : Msg} (hr : Realizable P J m) :
    closedCfg P (Cone P m) ∧ pSafe P (Cone P m) := by
  refine ⟨fun q hq p hp => cone_snoc P hq hp, fun q hq => ?_⟩
  exact valid_not_violation P
    (valid_of_realizable P (realizable_of_cone P hq hr) (fun p hp => cone_snoc P hq hp))

end Exact

/-! ## Counting lemmas for the fixed-point bound -/

theorem filter_length_le {α : Type} (l : List α) {p q : α → Bool}
    (h : ∀ x, p x = true → q x = true) : (l.filter p).length ≤ (l.filter q).length := by
  induction l with
  | nil => exact Nat.le_refl _
  | cons a l ih =>
    cases hp : p a with
    | true =>
      rw [List.filter_cons_of_pos hp, List.filter_cons_of_pos (h a hp)]
      exact Nat.succ_le_succ ih
    | false =>
      rw [List.filter_cons_of_neg (by simp [hp])]
      cases hq : q a with
      | true =>
        rw [List.filter_cons_of_pos hq]
        exact Nat.le_succ_of_le ih
      | false =>
        rw [List.filter_cons_of_neg (by simp [hq])]
        exact ih

theorem filter_length_lt {α : Type} {l : List α} {p q : α → Bool}
    (h : ∀ x, p x = true → q x = true) {a : α} (ha : a ∈ l) (hq : q a = true)
    (hp : p a = false) : (l.filter p).length < (l.filter q).length := by
  induction l with
  | nil => exact nomatch ha
  | cons b l ih =>
    have hle := filter_length_le l h
    cases List.mem_cons.1 ha with
    | inl hab =>
      subst hab
      rw [List.filter_cons_of_neg (by simp [hp]), List.filter_cons_of_pos hq]
      exact Nat.lt_succ_of_le hle
    | inr hal =>
      have hlt := ih hal
      cases hpb : p b with
      | true =>
        rw [List.filter_cons_of_pos hpb, List.filter_cons_of_pos (h b hpb)]
        exact Nat.succ_lt_succ hlt
      | false =>
        rw [List.filter_cons_of_neg (by simp [hpb])]
        cases hqb : q b with
        | true =>
          rw [List.filter_cons_of_pos hqb]
          exact Nat.lt_succ_of_lt hlt
        | false =>
          rw [List.filter_cons_of_neg (by simp [hqb])]
          exact hlt

/-! ## Finite clause tables and the checker -/

/-- A finite, decidable description of the type level of a protocol. -/
structure Table (Perf : Type) where
  /-- The declared performatives. -/
  perfs : List Perf
  /-- The legal predecessor types of a performative. -/
  deps : Perf → List Perf
  /-- The predecessor clause of a performative, evaluated on a set of available types. -/
  sat : Perf → (Perf → Bool) → Bool
  /-- Whether the declared sender of a performative is a role whose work is assumed. -/
  honest : Perf → Bool

namespace Table

variable {Perf : Type} (T : Table Perf)

/-- The clause evaluator is monotone in the available types. -/
def Mono : Prop :=
  ∀ t (R R' : Perf → Bool), (∀ t', R t' = true → R' t' = true) →
    T.sat t R = true → T.sat t R' = true

variable [DecidableEq Perf]

/-- The types available to `t`: its legal predecessors already known enactable. -/
def avail (R : Perf → Bool) (t : Perf) : Perf → Bool :=
  fun t' => decide (t' ∈ T.deps t) && R t'

/-- One round: `t` becomes enactable when it is declared, its sender's work is assumed,
    and its clause is satisfied by enactable legal predecessors. -/
def step (R : Perf → Bool) : Perf → Bool :=
  fun t => R t || (decide (t ∈ T.perfs) && T.honest t && T.sat t (T.avail R t))

/-- `n` rounds from the empty set. -/
def iter : Nat → Perf → Bool
  | 0 => fun _ => false
  | n + 1 => T.step (iter n)

/-- **The checker.** One round per declared performative reaches the least fixed point
    (`fixed`). -/
def enactable (t : Perf) : Bool := T.iter T.perfs.length t

/-- All of `goals` are enactable. -/
def checkEnactable (goals : List Perf) : Bool := goals.all T.enactable

theorem step_le (R : Perf → Bool) (t : Perf) (h : R t = true) : T.step R t = true := by
  simp [step, h]

theorem iter_succ_le (n : Nat) (t : Perf) (h : T.iter n t = true) :
    T.iter (n + 1) t = true := T.step_le _ t h

theorem step_new {R : Perf → Bool} {t : Perf} (h : T.step R t = true) (hn : R t = false) :
    t ∈ T.perfs ∧ T.honest t = true ∧ T.sat t (T.avail R t) = true := by
  simp only [step, hn, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- The number of declared performatives found enactable after `n` rounds. -/
def count (n : Nat) : Nat := (T.perfs.filter (T.iter n)).length

theorem count_le (n : Nat) : T.count n ≤ T.perfs.length := List.length_filter_le _ _

/-- A round either changes nothing or finds a new declared performative. -/
theorem stable_or_grows (n : Nat) :
    T.iter (n + 1) = T.iter n ∨ T.count n < T.count (n + 1) := by
  cases Classical.em (∀ t, T.iter (n + 1) t = T.iter n t) with
  | inl h => exact Or.inl (funext h)
  | inr h =>
    have hex : ∃ t, T.iter (n + 1) t ≠ T.iter n t :=
      Classical.byContradiction fun hne =>
        h fun t => Classical.byContradiction fun ht => hne ⟨t, ht⟩
    obtain ⟨t, ht⟩ := hex
    have hn : T.iter n t = false := by
      cases hv : T.iter n t with
      | false => rfl
      | true => exact absurd ((T.iter_succ_le n t hv).trans hv.symm) ht
    have hs : T.iter (n + 1) t = true := by
      cases hv : T.iter (n + 1) t with
      | true => rfl
      | false => exact absurd (hv.trans hn.symm) ht
    exact Or.inr (filter_length_lt (T.iter_succ_le n) (T.step_new hs hn).1 hs hn)

theorem stable_add {n : Nat} (h : T.iter (n + 1) = T.iter n) (k : Nat) :
    T.iter (n + k) = T.iter n := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show T.step (T.iter (n + k)) = T.iter n
    rw [ih]; exact h

theorem exists_stable (n : Nat) :
    (∃ k, k ≤ n ∧ T.iter (k + 1) = T.iter k) ∨ n + 1 ≤ T.count (n + 1) := by
  induction n with
  | zero =>
    cases T.stable_or_grows 0 with
    | inl h => exact Or.inl ⟨0, Nat.le_refl 0, h⟩
    | inr h => exact Or.inr (by omega)
  | succ n ih =>
    cases ih with
    | inl h =>
      obtain ⟨k, hk, he⟩ := h
      exact Or.inl ⟨k, by omega, he⟩
    | inr h =>
      cases T.stable_or_grows (n + 1) with
      | inl he => exact Or.inl ⟨n + 1, Nat.le_refl _, he⟩
      | inr hg => exact Or.inr (by omega)

/-- **Fixed point.** After one round per declared performative, another round changes
    nothing. -/
theorem fixed : T.step (T.iter T.perfs.length) = T.iter T.perfs.length := by
  cases T.exists_stable T.perfs.length with
  | inl h =>
    obtain ⟨k, hk, he⟩ := h
    have e : k + (T.perfs.length - k) = T.perfs.length := by omega
    have h1 := T.stable_add he (T.perfs.length - k)
    rw [e] at h1
    rw [h1]; exact he
  | inr h => exact absurd (T.count_le (T.perfs.length + 1)) (by omega)

/-- A declared performative whose clause is satisfied by enactable predecessors is
    enactable. -/
theorem enactable_of_sat {t : Perf} (hp : t ∈ T.perfs) (hh : T.honest t = true)
    (hs : T.sat t (T.avail (T.iter T.perfs.length) t) = true) : T.enactable t = true := by
  have hstep : T.step (T.iter T.perfs.length) t = true := by
    simp [step, hp, hh, hs]
  rw [T.fixed] at hstep
  exact hstep

/-! ## Soundness and completeness -/

/-- The table `T` describes the type level of `P`, with `honest` deciding membership of
    the declared sender in `H`. A hypothesis: nothing here derives a table from a deployed
    protocol declaration. -/
structure Represents {Role Msg : Type} (T : Table Perf) (P : Proto Role Perf Msg)
    (H : Role → Prop) : Prop where
  honest : ∀ t, T.honest t = true ↔ H (P.psender t)
  legal : ∀ t t', P.legalPred t t' ↔ t' ∈ T.deps t
  clause : ∀ t (ts : List Perf), (∀ t', t' ∈ ts → t' ∈ T.deps t) →
    (P.clause t (fun t' => t' ∈ ts) ↔
      t ∈ T.perfs ∧ T.sat t (fun t' => decide (t' ∈ ts)) = true)

variable {T} {Role Msg : Type} {P : Proto Role Perf Msg} {H : Role → Prop}

theorem iter_sound (hT : Represents T P H) :
    ∀ n t, T.iter n t = true → PerfRealizable P H t := by
  intro n
  induction n with
  | zero => intro t h; exact nomatch h
  | succ n ih =>
    intro t h
    cases hv : T.iter n t with
    | true => exact ih t hv
    | false =>
      obtain ⟨hp, hh, hs⟩ := T.step_new h hv
      have hmem : ∀ t', t' ∈ (T.deps t).filter (T.iter n) ↔
          t' ∈ T.deps t ∧ T.iter n t' = true := fun t' => List.mem_filter
      have heq : (fun t' => decide (t' ∈ (T.deps t).filter (T.iter n))) =
          T.avail (T.iter n) t := by
        funext t'
        simp [avail, hmem]
      refine PerfRealizable.intro t ((T.deps t).filter (T.iter n)) ((hT.honest t).1 hh)
        (fun t' ht' => (hT.legal t t').2 ((hmem t').1 ht').1) ?_
        (fun t' ht' => ih t' ((hmem t').1 ht').2)
      exact (hT.clause t _ (fun t' ht' => ((hmem t').1 ht').1)).2 ⟨hp, by rw [heq]; exact hs⟩

/-- **Soundness.** A performative the checker accepts is realizable at the type level. -/
theorem enactable_sound (hT : Represents T P H) {t : Perf} (h : T.enactable t = true) :
    PerfRealizable P H t := iter_sound hT _ t h

/-- **Completeness.** With a monotone clause evaluator, the checker accepts every
    performative that is realizable at the type level. -/
theorem enactable_complete (hT : Represents T P H) (hmono : T.Mono) {t : Perf}
    (h : PerfRealizable P H t) : T.enactable t = true := by
  induction h with
  | intro t ts hH hleg hclause _ ih =>
    have hdeps : ∀ t', t' ∈ ts → t' ∈ T.deps t := fun t' ht' => (hT.legal t t').1 (hleg t' ht')
    obtain ⟨hp, hs⟩ := (hT.clause t ts hdeps).1 hclause
    have hs' : T.sat t (T.avail (T.iter T.perfs.length) t) = true := by
      refine hmono t _ _ (fun t' ht' => ?_) hs
      have hm : t' ∈ ts := of_decide_eq_true ht'
      have hi : T.iter T.perfs.length t' = true := ih t' hm
      simp [avail, hdeps t' hm, hi]
    have hstep : T.step (T.iter T.perfs.length) t = true := by
      simp [step, hp, (hT.honest t).2 hH, hs']
    rw [T.fixed] at hstep
    exact hstep

/-- **The checker decides the type-level condition.** -/
theorem enactable_iff (hT : Represents T P H) (hmono : T.Mono) (t : Perf) :
    T.enactable t = true ↔ PerfRealizable P H t :=
  ⟨enactable_sound hT, enactable_complete hT hmono⟩

/-! ## What the check means -/

/-- **Dead performatives stay dead.** With every role taken as willing, any message
    present in a safe closed configuration has a performative the checker accepts. So a
    performative that fails the check occurs in no such configuration. -/
theorem present_enactable (hT : Represents T P (fun _ => True)) (hmono : T.Mono)
    (hwf : WellFounded (fun p m : Msg => P.predRel m p))
    (hfin : ∀ m, ∃ ps : List Msg, ∀ p, P.predRel m p ↔ p ∈ ps)
    {C : Cfg Msg} (hcl : closedCfg P C) (hsafe : pSafe P C) {m : Msg} (hm : C m) :
    T.enactable (P.perf m) = true := by
  have hr : Realizable P (fun m => (fun _ : Role => True) (P.sender m)) m :=
    realizable_mono P (fun _ _ => trivial) (realizable_of_safe_closed P hwf hfin hcl hsafe m hm)
  exact enactable_complete hT hmono (perfRealizable_of_realizable P hr)

/-- **Enactability is occurrence.** With every role taken as willing and messages in
    supply, the checker accepts `t` exactly when a message of performative `t` occurs in
    some safe closed configuration. -/
theorem enactable_iff_occurs (hT : Represents T P (fun _ => True)) (hmono : T.Mono)
    (hS : Supply P) (hwf : WellFounded (fun p m : Msg => P.predRel m p))
    (hfin : ∀ m, ∃ ps : List Msg, ∀ p, P.predRel m p ↔ p ∈ ps) (t : Perf) :
    T.enactable t = true ↔
      ∃ (C : Cfg Msg) (m : Msg), closedCfg P C ∧ pSafe P C ∧ C m ∧ P.perf m = t := by
  constructor
  · intro h
    obtain ⟨m, hm, hr⟩ := realizable_of_perfRealizable P hS (enactable_sound hT h)
    obtain ⟨hcl, hsafe⟩ := cone_safe_closed P hr
    exact ⟨Cone P m, m, hcl, hsafe, Cone.refl m, hm⟩
  · intro ⟨C, m, hcl, hsafe, hm, ht⟩
    exact ht ▸ present_enactable hT hmono hwf hfin hcl hsafe hm

/-! ## Discharging the progress premise -/

/-- **From the check to the static condition.** If every obligation names a performative
    in `goals` and accepts any realizable message of it, a passing check gives
    `Realizing` for the work of the roles in `H`. -/
theorem realizing_of_checkEnactable (hT : Represents T P H) (hS : Supply P)
    (O : Obligations P) (goals : List Perf) (hc : T.checkEnactable goals = true)
    (hO : ∀ r W, O.oblig r W → ∃ t, t ∈ goals ∧
      ∀ m, P.perf m = t → Realizable P (fun m => H (P.sender m)) m → W m) :
    Realizing P (fun m => H (P.sender m)) O := by
  refine realizing_of_perfRealizable P hS O (fun r W hW => ?_)
  obtain ⟨t, ht, hw⟩ := hO r W hW
  exact ⟨t, enactable_sound hT (List.all_eq_true.1 hc t ht), hw⟩

/-- **Checked deadlock freedom.** Under a passing check, a safe closed configuration that
    is not complete has an enabled message sent by a role in `H`. -/
theorem checked_incomplete_has_enabled (hT : Represents T P H) (hS : Supply P)
    (O : Obligations P) (goals : List Perf) (hc : T.checkEnactable goals = true)
    (hO : ∀ r W, O.oblig r W → ∃ t, t ∈ goals ∧
      ∀ m, P.perf m = t → Realizable P (fun m => H (P.sender m)) m → W m)
    {C : Cfg Msg} (hcl : closedCfg P C) (hsafe : pSafe P C) (hinc : ¬ pComplete P O C) :
    ∃ q, enabled P C q ∧ H (P.sender q) :=
  incomplete_has_enabled P O (realizing_of_checkEnactable hT hS O goals hc hO) hcl hsafe hinc

end Table

/-! ## Non-vacuity: the request/reply protocol and a circular wait

The table below represents `RoleProgress.RequestReply.proto`, and the checker accepts both
of its performatives. `circular` makes the request wait on the reply as well: the checker
rejects both, which is the type-level form of `NoInitial`. -/

namespace Examples

open RoleProgress.RequestReply

/-- Request (`false`) has no predecessors; reply (`true`) needs the request. -/
def requestReply : Table Bool where
  perfs := [false, true]
  deps := fun t => if t then [false] else []
  sat := fun t R => !t || R false
  honest := fun _ => true

theorem requestReply_mono : requestReply.Mono := by
  intro t R R' h hs
  cases t with
  | false => rfl
  | true => exact h false hs

theorem requestReply_represents : Table.Represents requestReply proto (fun _ => True) where
  honest := fun _ => ⟨fun _ => trivial, fun _ => rfl⟩
  legal := by
    intro t t'
    cases t <;> cases t' <;> simp [proto, requestReply]
  clause := by
    intro t ts _
    cases t <;> simp [proto, requestReply]

theorem requestReply_enactable : requestReply.checkEnactable [false, true] = true := by
  decide

/-- Both performatives wait on each other. -/
def circular : Table Bool where
  perfs := [false, true]
  deps := fun t => [!t]
  sat := fun t R => R (!t)
  honest := fun _ => true

theorem circular_not_enactable :
    circular.enactable false = false ∧ circular.enactable true = false := by
  decide

end Examples

end LeanCbcl.Enactability
