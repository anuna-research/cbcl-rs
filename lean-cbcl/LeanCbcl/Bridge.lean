/-
  The temporal bridge — executions, not only ideal snapshots.

  Three referees asked for the same missing piece: the run-level EPP correspondence
  (`EPP.lean`: `P`-safe closed global configurations ≅ compatible families of local runs)
  is stated over *ideal* local stores (the full projections), while a running endpoint
  holds a partial projection, delivered in some order. Predicate stores need not be
  finite. Limit correspondence requires exhaustion; finite-time resolution additionally
  requires finite predecessor support, as in `eventually_present_valid`.

  * A `Schedule P C r` is a delivery schedule for role `r` against a global configuration
    `C`: a monotone (append-only) chain of local stores `store : Nat → Cfg Msg` with
    `store n ⊆ store (n+1) ⊆ project P C r` whose union exhausts the projection
    (`exhaust`). Eventual delivery is *only* exhaustion — no ordering, fairness, or
    causal-delivery assumption is made.

  * `bridge_stability`: along any schedule, resolved verdicts are stable and truthful.
    If a message's verdict over `store n` is resolved (`Valid` or
    `Violation` under the resolved-first three-valued semantics of `EPP.lean`), then that
    same verdict already holds (i) at every later time `n' ≥ n` (no retraction along the
    execution), (ii) at the limit store `⋃ n, store n`, (iii) at the ideal projection
    `project P C r`, and (iv) — by the reconciliation lemma `reconcile_global` — globally
    over `C`. A locally resolved verdict at any finite time IS the limit verdict.

  * `bridge_compatibility`: the limit family `{⋃ n, (L r).store n}_r = {project P C r}_r`
    is a compatible family (an `EPP.Family`, reusing the exactness direction `projFamily`
    — not reproved), each of its runs is locally safe, it glues back to exactly `C`
    (`glue_project_eq`), and projecting the gluing recovers each run (`project_glue_eq`).

  * `temporal_bridge`: the composite, citable statement — for every `P`-safe closed `C`
    and *every* family of delivery schedules (one per role), the schedules' limits are
    exactly the projection family, every finite-time resolved verdict embeds unchanged
    into that limit (hence into the Theorem-2 bijection), and the limit family glues to
    `C` with both round-trip identities. Executions → compatible family → `C`.

  The limit and stability arguments reuse results from `EPP.lean` (`valid_stable`, `violation_stable`,
  `reconcile_global`, `soundness_safety`, `projFamily`, `glue_project_eq`,
  `project_glue_eq`); finite-time resolution uses a finite list covering the cited predecessors and
  a maximum-arrival-time argument. No new axioms.
-/
import LeanCbcl.EPP

namespace LeanCbcl.Bridge

open LeanCbcl.EPP

variable {Role Perf Msg : Type}

/-- **Delivery schedule** for role `r` against global configuration `C`: a monotone
    chain of local stores, each contained in the projection `project P C r`, whose
    union exhausts the projection. Eventual delivery = exhaustion; no assumption is
    made about delivery *order* (in particular, none about causal order). -/
structure Schedule (P : Proto Role Perf Msg) (C : Cfg Msg) (r : Role) where
  /-- The local store held by `r` at time `n`. -/
  store   : Nat → Cfg Msg
  /-- Stores are append-only: `store n ⊆ store (n+1)`. -/
  mono    : ∀ n m, store n m → store (n + 1) m
  /-- Every store is a sub-store of the ideal projection: `store n ⊆ project P C r`.
      This is part of what "conformant execution" means — the endpoint never holds a
      message outside its projection, so misdelivered or fabricated messages are outside
      the bridge's scope by definition. -/
  bounded : ∀ n m, store n m → project P C r m
  /-- Eventual delivery: every `r`-relevant message of `C` arrives at some finite time. -/
  exhaust : ∀ m, project P C r m → ∃ n, store n m

namespace Schedule

variable {P : Proto Role Perf Msg} {C : Cfg Msg} {r : Role}

/-- Monotonicity closed under `≤`: `store n ⊆ store n'` whenever `n ≤ n'`. -/
theorem store_le (L : Schedule P C r) {n n' : Nat} (h : n ≤ n')
    {m : Msg} (hm : L.store n m) : L.store n' m := by
  induction h with
  | refl => exact hm
  | step _ ih => exact L.mono _ _ ih

/-- The limit store of a schedule: `⋃ n, store n` (as a predicate). -/
def limit (L : Schedule P C r) : Cfg Msg := fun m => ∃ n, L.store n m

/-- Every time-indexed store embeds in the limit. -/
theorem store_le_limit (L : Schedule P C r) (n : Nat) :
    ∀ m, L.store n m → L.limit m := fun _ hm => ⟨n, hm⟩

/-- **The limit of any delivery schedule is exactly the ideal projection.**
    `⋃ n, store n = project P C r` — regardless of delivery order. -/
theorem limit_eq (L : Schedule P C r) : L.limit = project P C r := by
  funext m
  apply propext
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h
    exact L.bounded n m hn
  · exact L.exhaust m

/-- Every finite list of eventually delivered messages is held together from
    some finite time onward. No finiteness of the entire store is required. -/
theorem eventually_holds_list (L : Schedule P C r) (xs : List Msg)
    (hx : ∀ x, x ∈ xs → project P C r x) :
    ∃ n, ∀ n', n ≤ n' → ∀ x, x ∈ xs → L.store n' x := by
  induction xs with
  | nil => exact ⟨0, by simp⟩
  | cons x xs ih =>
    obtain ⟨nx, hnx⟩ := L.exhaust x (hx x (by simp))
    obtain ⟨ns, hns⟩ := ih (fun y hy => hx y (by simp [hy]))
    refine ⟨max nx ns, ?_⟩
    intro n hn y hy
    rcases List.mem_cons.mp hy with he | ht
    · subst y
      exact L.store_le (Nat.le_trans (Nat.le_max_left _ _) hn) hnx
    · exact hns n (Nat.le_trans (Nat.le_max_right _ _) hn) y ht

end Schedule

variable (P : Proto Role Perf Msg)

/-- A message has finite predecessor support when a finite list covers every
    citation. The list may contain duplicates; no decidable message equality is needed. -/
def FinitePredecessors (m : Msg) : Prop :=
  ∃ xs : List Msg, ∀ p, P.predRel m p → p ∈ xs

/-- In a safe closed run, a relevant message with finitely many cited predecessors
    is eventually present and Valid at every later time. This strengthens limit
    correspondence to finite-time resolution under an explicit finiteness hypothesis. -/
theorem eventually_present_valid {C : Cfg Msg}
    (hcl : closedCfg P C) (hsafe : pSafe P C) {r : Role}
    (L : Schedule P C r) {m : Msg} (hm : project P C r m)
    (hfinite : FinitePredecessors P m) :
    ∃ n, ∀ n', n ≤ n' → L.store n' m ∧ isValid P (L.store n') m := by
  classical
  obtain ⟨xs, hxs⟩ := hfinite
  let needed := xs.filter (fun p => P.predRel m p)
  have hneeded : ∀ p, p ∈ needed → project P C r p := by
    intro p hp
    exact localres P hcl hsafe hm.1 hm.2 p (by simpa using (List.mem_filter.mp hp).2)
  obtain ⟨n, hn⟩ := L.eventually_holds_list (m :: needed) (by
    intro p hp
    rcases List.mem_cons.mp hp with he | ht
    · simpa [he] using hm
    · exact hneeded p ht)
  refine ⟨n, ?_⟩
  intro n' hnn
  have hres : resolved P (L.store n') m := by
    intro p hp
    exact hn n' hnn p (List.mem_cons.mpr (Or.inr
      (List.mem_filter.mpr ⟨hxs p hp, by simpa using hp⟩)))
  have hgood := good_of_safe_closed P hcl hsafe hm.1
  have heq := predTypesPresent_mono P (fun p hp => (L.bounded n' p hp).1) hres
  refine ⟨hn n' hnn m (by simp), hres, hgood.1, hgood.2.1, ?_⟩
  rw [heq]
  exact hgood.2.2

/-- **Theorem (bridge, stability): resolved verdicts along a schedule are stable and
    truthful.** Let `C` be `P`-safe and closed, `L` a delivery schedule for role `r`,
    and `m` a message held by `r` at time `n`. If `m`'s verdict over `L.store n` is resolved — `Valid` or `Violation` under the resolved-first semantics
    — then the *same* verdict holds at every later time, at the limit store, at the
    ideal projection, and (via `reconcile_global`) globally over `C`. A locally
    resolved verdict at any finite time is already the limit verdict: no retraction
    along any execution. -/
theorem bridge_stability {C : Cfg Msg} (hcl : closedCfg P C) (hsafe : pSafe P C)
    {r : Role} (L : Schedule P C r) {n : Nat} {m : Msg} (hm : L.store n m) :
    (isValid P (L.store n) m →
        (∀ n', n ≤ n' → isValid P (L.store n') m) ∧
        isValid P L.limit m ∧
        isValid P (project P C r) m ∧
        isValid P C m) ∧
    (isViolation P (L.store n) m →
        (∀ n', n ≤ n' → isViolation P (L.store n') m) ∧
        isViolation P L.limit m ∧
        isViolation P (project P C r) m ∧
        isViolation P C m) := by
  have hproj : project P C r m := L.bounded n m hm
  constructor
  · intro hv
    have hvP : isValid P (project P C r) m := valid_stable P (L.bounded n) hv
    exact ⟨fun n' hn' => valid_stable P (fun z hz => L.store_le hn' hz) hv,
           valid_stable P (L.store_le_limit n) hv,
           hvP,
           (reconcile_global P hcl hsafe hproj).2.1.1 hvP⟩
  · intro hv
    have hvP : isViolation P (project P C r) m := violation_stable P (L.bounded n) hv
    exact ⟨fun n' hn' => violation_stable P (fun z hz => L.store_le hn' hz) hv,
           violation_stable P (L.store_le_limit n) hv,
           hvP,
           (reconcile_global P hcl hsafe hproj).2.2.1 hvP⟩

/-- **Theorem (bridge, compatibility): the limit family is compatible and glues to
    `C`.** Given a delivery schedule for every role, the family of limit stores
    `{⋃ n, (L r).store n}_r` is a compatible family in the sense of the run-level
    correspondence (an `EPP.Family` — the witness is `projFamily`, reusing the
    exactness direction rather than reproving it), each of its runs is locally safe,
    it glues back to exactly `C`, and projecting the gluing recovers each run. -/
theorem bridge_compatibility {C : Cfg Msg} (hcl : closedCfg P C) (hsafe : pSafe P C)
    (L : ∀ r : Role, Schedule P C r) :
    ∃ F : Family P,
      (∀ r, F.run r = (L r).limit) ∧
      (∀ r, localSafe P (F.run r)) ∧
      (∀ m, glue P F m ↔ C m) ∧
      (∀ r m, project P (glue P F) r m ↔ F.run r m) := by
  refine ⟨projFamily P hcl hsafe, ?_, ?_, ?_, ?_⟩
  · intro r
    exact ((L r).limit_eq).symm
  · intro r
    exact soundness_safety P hcl hsafe r
  · intro m
    exact glue_project_eq P m
  · intro r m
    exact project_glue_eq P (projFamily P hcl hsafe) r m

/-- **The temporal bridge (composite, citable form): executions → compatible family
    → `C`.** For every `P`-safe closed global configuration `C` and *every* family of
    delivery schedules `L` (one per role, arbitrary delivery order, eventual delivery
    only):

    1. *(limits)* each schedule's limit is exactly the ideal projection —
       `⋃ n, (L r).store n = project P C r`;
    2. *(finite-time verdict embedding)* every verdict resolved at any finite time
       along any schedule is stable (never retracted at later times) and coincides
       with the limit verdict, the projection verdict, and the global verdict over
       `C` — so finite-time verdicts embed unchanged into the run-level bijection
       taken at the limit;
    3. *(compatibility and gluing)* the limit family is a compatible family of
       locally safe runs that glues back to exactly `C`, with the projection of the
       gluing recovering each run — i.e. the limit family is precisely a point of the
       Theorem-2 bijection whose gluing is `C`. -/
theorem temporal_bridge {C : Cfg Msg} (hcl : closedCfg P C) (hsafe : pSafe P C)
    (L : ∀ r : Role, Schedule P C r) :
    -- (1) limits are the projections
    (∀ r, (L r).limit = project P C r) ∧
    -- (2) finite-time resolved verdicts embed into the limit
    (∀ (r : Role) (n : Nat) (m : Msg), (L r).store n m →
        (isValid P ((L r).store n) m →
            (∀ n', n ≤ n' → isValid P ((L r).store n') m) ∧
            isValid P (L r).limit m ∧
            isValid P (project P C r) m ∧
            isValid P C m) ∧
        (isViolation P ((L r).store n) m →
            (∀ n', n ≤ n' → isViolation P ((L r).store n') m) ∧
            isViolation P (L r).limit m ∧
            isViolation P (project P C r) m ∧
            isViolation P C m)) ∧
    -- (3) the limit family is compatible, locally safe, and glues to C exactly
    (∃ F : Family P,
        (∀ r, F.run r = (L r).limit) ∧
        (∀ r, localSafe P (F.run r)) ∧
        (∀ m, glue P F m ↔ C m) ∧
        (∀ r m, project P (glue P F) r m ↔ F.run r m)) := by
  refine ⟨fun r => (L r).limit_eq, ?_, bridge_compatibility P hcl hsafe L⟩
  intro r n m hm
  exact bridge_stability P hcl hsafe (L r) hm

/-! A counterexample showing why exhaustion alone does not imply finite-time
resolution: message zero cites every positive natural-number message. -/
namespace InfinitePredecessorsExample

/-- A one-role protocol whose message zero cites every positive message. -/
def proto : Proto Unit Unit Nat where
  perf := fun _ => ()
  sender := fun _ => ()
  recip := fun _ _ => False
  predRel := fun m p => m = 0 ∧ 0 < p
  psender := fun _ => ()
  precip := fun _ _ => False
  legalPred := fun _ _ => True
  clause := fun _ _ => True
  causalLocal := fun _ _ _ _ hr => hr

/-- The infinite global store. -/
def full : Cfg Nat := fun _ => True

/-- Deliver message k at time k; every time-indexed store is a finite prefix. -/
def delivery : Schedule proto full () where
  store := fun n m => m ≤ n
  mono := fun _ _ hm => Nat.le_trans hm (Nat.le_succ _)
  bounded := fun _ _ _ => ⟨trivial, Or.inl rfl⟩
  exhaust := fun m _ => ⟨m, Nat.le_refl m⟩

/-- All predecessors are in the global store. -/
theorem full_closed : closedCfg proto full := fun _ _ _ _ => trivial

/-- The infinite run is safe; missing local predecessors are knowledge gaps. -/
theorem full_safe : pSafe proto full := by
  intro m _ hv
  exact hv.2 ⟨⟨rfl, fun _ => Iff.rfl⟩, fun _ _ => trivial, trivial⟩

/-- The dependent message is present but Unknown at every finite time. -/
theorem always_unknown (n : Nat) :
    delivery.store n 0 ∧ isUnknown proto (delivery.store n) 0 := by
  refine ⟨Nat.zero_le n, ?_⟩
  intro hres
  have h := hres (n + 1) ⟨rfl, Nat.zero_lt_succ n⟩
  exact Nat.not_succ_le_self n h

/-- Exhaustion and a safe closed run do not supply finite predecessor support. -/
theorem not_finite_predecessors : ¬ FinitePredecessors proto 0 := by
  intro hf
  obtain ⟨n, hn⟩ := eventually_present_valid proto full_closed full_safe delivery
    ⟨trivial, Or.inl rfl⟩ hf
  exact (always_unknown n).2 (hn n (Nat.le_refl n)).2.1

end InfinitePredecessorsExample

/-! Axiom audit (informational output when this file is compiled). -/
#print axioms InfinitePredecessorsExample.always_unknown
#print axioms InfinitePredecessorsExample.not_finite_predecessors
#print axioms eventually_present_valid
#print axioms bridge_stability
#print axioms bridge_compatibility
#print axioms temporal_bridge

end LeanCbcl.Bridge
