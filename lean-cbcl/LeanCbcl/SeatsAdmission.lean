import LeanCbcl.EPP
import LeanCbcl.Seats

/-
  SPEC-020 capability seats — the admission verdict over an authority past, the
  conservative extension of SPEC-014, and the anchor walk.

  Mirrors SPEC-020 v0.7.1 REQ-2024 (admission monotonicity), REQ-2034 (conservative
  extension) and the Terminology entry "Anchor walk" (REQ-2046). Builds on
  `LeanCbcl/EPP.lean` (the SPEC-014 three-valued verdict) and `LeanCbcl/Seats.lean`
  (the warrant-state function). Lean core only.

  What is modelled. SPEC-020 adds to a SPEC-014 message a content-fixed authority past
  `A(m)`, a designated warrant, and three checks over `A(m)` alone: the warrant is live in
  the warrant state of `A(m)`'s meta acts, the signer holds it, and it permits the act.
  The admission verdict is `Unknown` until the SPEC-014 predecessors and `A(m)` are all
  present, then `Valid` when the SPEC-014 clause and the warrant checks both hold, and
  `Violation` otherwise.

  What is proved.
  * `valid_stable`, `violation_stable` — REQ-2024: the verdict is permanent once decided;
    store growth never changes `Valid` or `Violation`. The warrant checks read only `A(m)`,
    which content fixes, so this reduces to SPEC-014's own stability.
  * `conservative` — REQ-2034: in a policy-free thread, for a message that is not a meta
    act and carries no authority token, the three verdicts coincide with SPEC-014's on
    every causally closed store. The warrant checks are discharged by `Seats.live_empty`:
    over no meta acts, exactly the root warrants are live.
  * `walk_stops`, `walk_back` — the anchor walk terminates and ends at the first message
    that is not an act of the walked seat, which it reaches through same-seat predecessors.
    Termination is well-founded recursion on the predecessor relation; content
    addressing makes that relation well founded, which the walk takes as a hypothesis.

  What is NOT modelled: how `metaActs` is computed from a set of messages (the admission
  of the meta acts themselves, REQ-2007–2012, REQ-2040, REQ-2045), narrowing (REQ-2009),
  chain length (REQ-2011), the anchor's own validity and `MixedRounds` (REQ-2046), and
  discharge arithmetic (REQ-2047). Those stay with the Rust core and its tests.
-/

namespace LeanCbcl.Seats.Admission

open LeanCbcl.EPP (Cfg Proto)

variable {Role Perf Msg Warrant Grant : Type}

/-- What SPEC-020 adds to a SPEC-014 protocol. Every field is fixed by message content:
    `past m` is `A(m)`, `metaActs C` the meta acts admitted among the messages `C`,
    `warrant m` the designated warrant (REQ-2013: the sender's root warrant when none is
    named), `holds m X` that `m`'s signer holds `X` (REQ-2016), and `permits X t` that
    `X`'s act set contains performative `t` (REQ-2020). -/
structure Auth (Perf Msg Warrant Grant : Type) where
  past : Msg → Cfg Msg
  metaActs : Cfg Msg → MetaSet Warrant Grant
  warrant : Msg → Warrant
  holds : Msg → Warrant → Prop
  permits : Warrant → Perf → Prop

variable (P : Proto Role Perf Msg) (F : Forest Warrant Grant) (A : Auth Perf Msg Warrant Grant)

/-- `A(m)` is present in store `C`. -/
def pastPresent (C : Cfg Msg) (m : Msg) : Prop := ∀ p, A.past m p → C p

/-- The warrant checks of REQ-2013–2020, over `A(m)` alone. -/
def warrantGood (m : Msg) : Prop :=
  live F (A.metaActs (A.past m)) (A.warrant m) ∧
  A.holds m (A.warrant m) ∧ A.permits (A.warrant m) (P.perf m)

/-- Resolved: SPEC-014's predecessors and `A(m)` are present. -/
def resolved (C : Cfg Msg) (m : Msg) : Prop := EPP.resolved P C m ∧ pastPresent A C m

/-- The three SPEC-020 verdicts. -/
def isUnknown (C : Cfg Msg) (m : Msg) : Prop := ¬ resolved P A C m
def isValid (C : Cfg Msg) (m : Msg) : Prop :=
  resolved P A C m ∧ EPP.good P C m ∧ warrantGood P F A m
def isViolation (C : Cfg Msg) (m : Msg) : Prop :=
  resolved P A C m ∧ ¬ (EPP.good P C m ∧ warrantGood P F A m)

/-! ### REQ-2024: admission monotonicity -/

theorem resolved_stable {C C' : Cfg Msg} (hCC : ∀ m, C m → C' m) {m : Msg}
    (h : resolved P A C m) : resolved P A C' m :=
  ⟨fun p hp => hCC p (h.1 p hp), fun p hp => hCC p (h.2 p hp)⟩

/-- Store growth never changes `Valid`. -/
theorem valid_stable {C C' : Cfg Msg} (hCC : ∀ m, C m → C' m) {m : Msg}
    (hv : isValid P F A C m) : isValid P F A C' m := by
  obtain ⟨hres, hg, hw⟩ := hv
  have h14 := EPP.valid_stable P hCC (⟨hres.1, hg⟩ : EPP.isValid P C m)
  exact ⟨resolved_stable P A hCC hres, h14.2, hw⟩

/-- Store growth never changes `Violation`. -/
theorem violation_stable {C C' : Cfg Msg} (hCC : ∀ m, C m → C' m) {m : Msg}
    (hv : isViolation P F A C m) : isViolation P F A C' m := by
  obtain ⟨hres, hng⟩ := hv
  refine ⟨resolved_stable P A hCC hres, fun ⟨hg', hw⟩ => hng ⟨?_, hw⟩⟩
  exact Classical.byContradiction fun hg =>
    (EPP.violation_stable P hCC (⟨hres.1, hg⟩ : EPP.isViolation P C m)).2 hg'

/-! ### REQ-2034: conservative extension -/

/-- Causal ancestry through `:caused-by` alone. -/
inductive causalPast (m : Msg) : Msg → Prop
  | pred {p} : P.predRel m p → causalPast m p
  | step {p q} : causalPast m p → P.predRel p q → causalPast m q

/-- The hypotheses of REQ-2034 for one message `m`, each tied to its clause: the dialect
    has no policy, so nothing admits a meta act (REQ-2001) and the meta-act set of any
    authority past is empty; `m` carries no `:warrant`, so its designated warrant is the
    sender's root warrant (REQ-2013); the signature binds the signer to the cast's key, which
    SPEC-014 REQ-613 already checks; a root warrant carries every act of its role
    (Terminology "Warrant attributes"); and `m` carries no `:seen` or `:anchor` and links
    only within its thread, so `A(m)` is its causal past. -/
structure PolicyFree (m : Msg) : Prop where
  empty : A.metaActs (A.past m) = MetaSet.empty
  root : F.rootWarrant (A.warrant m)
  holds : A.holds m (A.warrant m)
  permits : A.permits (A.warrant m) (P.perf m)
  past_causal : ∀ p, A.past m p ↔ causalPast P m p

/-- Under REQ-2034's hypotheses the warrant checks hold outright. -/
theorem warrantGood_of_policyFree {m : Msg} (h : PolicyFree P F A m) : warrantGood P F A m :=
  ⟨by rw [h.empty]; exact (live_empty F).2 h.root, h.holds, h.permits⟩

/-- On a causally closed store, `A(m)` present is SPEC-014 resolvedness. -/
theorem pastPresent_iff_resolved {C : Cfg Msg} (hcl : EPP.closedCfg P C) {m : Msg}
    (h : PolicyFree P F A m) : pastPresent A C m ↔ EPP.resolved P C m := by
  constructor
  · intro hp p hpr
    exact hp p ((h.past_causal p).2 (causalPast.pred hpr))
  · intro hres p hp
    have hc := (h.past_causal p).1 hp
    clear hp
    induction hc with
    | pred hpr => exact hres _ hpr
    | step _ hpr ih => exact hcl _ ih _ hpr

/-- REQ-2034: the three verdicts coincide with SPEC-014's. -/
theorem conservative {C : Cfg Msg} (hcl : EPP.closedCfg P C) {m : Msg}
    (h : PolicyFree P F A m) :
    (isValid P F A C m ↔ EPP.isValid P C m) ∧
    (isViolation P F A C m ↔ EPP.isViolation P C m) ∧
    (isUnknown P A C m ↔ EPP.isUnknown P C m) := by
  have hw := warrantGood_of_policyFree P F A h
  have hres : resolved P A C m ↔ EPP.resolved P C m :=
    ⟨fun r => r.1, fun r => ⟨r, (pastPresent_iff_resolved P F A hcl h).2 r⟩⟩
  refine ⟨⟨fun ⟨r, g, _⟩ => ⟨hres.1 r, g⟩, fun ⟨r, g⟩ => ⟨hres.2 r, g, hw⟩⟩, ?_, ?_⟩
  · exact ⟨fun ⟨r, ng⟩ => ⟨hres.1 r, fun g => ng ⟨g, hw⟩⟩,
      fun ⟨r, ng⟩ => ⟨hres.2 r, fun ⟨g, _⟩ => ng g⟩⟩
  · exact ⟨fun nr r => nr (hres.2 r), fun nr r => nr (hres.1 r)⟩

/-- `isValid` implies SPEC-014 `isValid` on any store, with no hypothesis: SPEC-020 only
    ever adds checks. -/
theorem valid_implies_epp {C : Cfg Msg} {m : Msg} (h : isValid P F A C m) : EPP.isValid P C m :=
  ⟨h.1.1, h.2.1⟩

end LeanCbcl.Seats.Admission

/-! ### The anchor walk (Terminology; REQ-2046) -/

namespace LeanCbcl.Seats.AnchorWalk

variable {Msg : Type} (next : Msg → Option Msg) (sameSeat : Msg → Msg → Prop)

/-- `Pred a b`: `a` is the single protocol predecessor of `b`. -/
def Pred (a b : Msg) : Prop := next b = some a

open Classical in
/-- The anchor walk: follow the single protocol predecessor while it is an act of the same
    seat; stop at the first other message. Well-founded recursion on `Pred`, which content
    addressing makes well founded (no message names its own hash). -/
noncomputable def walk (wf : WellFounded (Pred next)) : Msg → Msg :=
  wf.fix fun m rec =>
    match h : next m with
    | some p => if sameSeat m p then rec p h else m
    | none => m

variable (wf : WellFounded (Pred next))

theorem walk_none {m : Msg} (h : next m = none) : walk next sameSeat wf m = m := by
  unfold walk; rw [WellFounded.fix_eq]; split <;> simp_all

theorem walk_same {m p : Msg} (h : next m = some p) (hs : sameSeat m p) :
    walk next sameSeat wf m = walk next sameSeat wf p := by
  unfold walk; rw [WellFounded.fix_eq]
  split
  · rename_i heq; rw [h] at heq; cases heq; exact if_pos hs
  · rename_i heq; rw [h] at heq; cases heq

theorem walk_other {m p : Msg} (h : next m = some p) (hs : ¬ sameSeat m p) :
    walk next sameSeat wf m = m := by
  unfold walk; rw [WellFounded.fix_eq]; split <;> simp_all

/-- The walk ends at the root of the thread, or at a message whose predecessor is not an
    act of the same seat: "the first other message". -/
theorem walk_stops (m : Msg) :
    next (walk next sameSeat wf m) = none ∨
    ∃ p, next (walk next sameSeat wf m) = some p ∧ ¬ sameSeat (walk next sameSeat wf m) p := by
  induction m using wf.induction with
  | _ m ih =>
    cases h : next m with
    | none => rw [walk_none next sameSeat wf h]; exact Or.inl h
    | some p =>
      by_cases hs : sameSeat m p
      · rw [walk_same next sameSeat wf h hs]; exact ih p h
      · rw [walk_other next sameSeat wf h hs]; exact Or.inr ⟨p, h, hs⟩

/-- `Back m q`: `q` is `m` or reached from it through same-seat predecessors. -/
inductive Back (m : Msg) : Msg → Prop
  | refl : Back m m
  | step {p q} : Back m p → next p = some q → sameSeat p q → Back m q

/-- The walk's end is `m` or lies in `m`'s causal past, reached through acts of the same
    seat. -/
theorem walk_back (m : Msg) : Back next sameSeat m (walk next sameSeat wf m) := by
  induction m using wf.induction with
  | _ m ih =>
    cases h : next m with
    | none => rw [walk_none next sameSeat wf h]; exact Back.refl
    | some p =>
      by_cases hs : sameSeat m p
      · rw [walk_same next sameSeat wf h hs]
        have hb := ih p h
        clear ih
        generalize walk next sameSeat wf p = q at hb ⊢
        induction hb with
        | refl => exact Back.step Back.refl h hs
        | step _ hn hs' ih' => exact Back.step ih' hn hs'
      · rw [walk_other next sameSeat wf h hs]; exact Back.refl

end LeanCbcl.Seats.AnchorWalk
