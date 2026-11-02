import LeanCbcl.ConsensusFree.Liveness

/-! SPEC-033: permanent cutover and full-capacity owned continuation.
Fixed catalogues, ideal authentication, one resource scope. Not a Rust/network
source-equivalence claim. -/
namespace CBCL.ConsensusFree.OwnedLifecycle
open CBCL.ValidatorBudget CBCL.SealedCheckpoint
open CBCL.ConsensusFree.MultiParent.Liveness (WeakFair fair_bit finite_eventually)
variable {V O K N R f : Nat}
@[simp] theorem two_other_right [DecidableEq α] [DecidableEq β]
    (fn : α → β → γ) (a : α) (b : β) (v : γ) (x : α) (y : β) (hne : y ≠ b) :
    two fn a b v x y = fn x y := by
  by_cases hx : x = a <;> simp_all [two, setAt]

structure Root (O R : Nat) where
  held : Fin O → Bool
  refunded : Fin O → Bool
  credited : Fin O → Bool
  allocation : Fin R → Nat
  authorized : Bool
structure Config (V O K N R f : Nat) where
  old : MultiParent.Config V O R f
  root : Fin K → Root O R
  source : Fin N → Fin K
  rank : Fin N → Nat
  held : Fin N → Fin N → Bool
  credited : Fin N → Fin N → Bool
  allocation : Fin N → Fin R → Nat
  cost : Fin N → Fin R → Nat
  credit : Fin N → Fin R → Nat
  authorized : Fin N → Bool
  /-- Disjoint external transaction catalogue, each entry verified as an effects
  QC in this context, crediting this scope. Root imports are excluded. -/
  incoming : Fin N → Fin R → Nat
  incomingAuthenticated : Fin N → Bool
  imports : Fin N → Fin N → Bool
  /-- Permanent cancellation votes made before this continuation was activated. -/
  priorFences : Fin N → Nat → Bool
  older : ∀ x y, held y x = true → rank x < rank y
  sameRoot : ∀ x y, held y x = true → source x = source y
  creditsOlder : ∀ x y, credited y x = true → rank x < rank y
  book : ∀ x d, (allocation x d : Int) = (root (source x)).allocation d +
    isum (List.finRange N) (fun y => if credited x y then (credit y d : Int) else 0) +
    isum (List.finRange N) (fun y => if imports x y then (incoming y d : Int) else 0) -
    isum (List.finRange N) (fun y => if held x y then (cost y d : Int) else 0)
structure State (V O K N : Nat) where
  old : MultiParent.State V O
  received : Fin N → Bool
  closed : Nat → Bool
  seals : Fin K → Nat → Bool
  votes : Fin N → Nat → Bool
  effects : Fin N → Nat → Bool
def initial : State V O K N :=
  ⟨MultiParent.initial, fun _ => false, fun _ => false, fun _ _ => false, fun _ _ => false, fun _ _ => false⟩
def quorum (c : Config V O K N R f) (votes : Nat → Bool) : Bool := MultiParent.quorum c.old votes
def sealCert (c : Config V O K N R f) (s : State V O K N) (k : Fin K) := quorum c (s.seals k)
def opCert (c : Config V O K N R f) (s : State V O K N) (x : Fin N) := quorum c (s.votes x)
def finalCert (c : Config V O K N R f) (s : State V O K N) (x : Fin N) := quorum c (s.effects x)
def RootValid (c : Config V O K N R f) (s : State V O K N) (k : Fin K) : Prop :=
  (c.root k).authorized = true ∧
  (∀ x, (c.root k).refunded x = true → (c.root k).held x = true ∧ MultiParent.cancelCert c.old s.old x = true) ∧
  (∀ x, (c.root k).credited x = true → MultiParent.finalCert c.old s.old x = true) ∧
  (∀ x, (c.root k).held x = true → MultiParent.finalCert c.old s.old x = true ∨ MultiParent.cancelCert c.old s.old x = true) ∧
  (∀ d, ((c.root k).allocation d : Int) = c.old.initial d +
    isum (List.finRange O) (fun x => if (c.root k).credited x then (c.old.credit x d : Int) else 0) -
    isum (List.finRange O) (fun x => if (c.root k).held x then (c.old.cost x d : Int) else 0) +
    isum (List.finRange O) (fun x => if (c.root k).refunded x then (c.old.cost x d : Int) else 0))
instance : Decidable (RootValid c s k) := by unfold RootValid; infer_instance
def closeState (s : State V O K N) (k : Fin K) (w : Nat) : State V O K N :=
  {s with closed := setAt s.closed w true, seals := two s.seals k w true}
def sign (s : State V O K N) (x : Fin N) (w : Nat) : State V O K N :=
  {s with votes := two s.votes x w true}
def effect (s : State V O K N) (x : Fin N) (w : Nat) : State V O K N :=
  {s with effects := two s.effects x w true}
def SealAllowed (c : Config V O K N R f) (s : State V O K N) (k : Fin K) (w : Nat) : Prop :=
  w ∈ c.old.committee.core → RootValid c s k ∧
    (s.closed w = false ∨ s.seals k w = true) ∧
    ∀ x, s.old.signatures x w = true → (c.root k).held x = true
instance : Decidable (SealAllowed c s k w) := by unfold SealAllowed; infer_instance
def SignAllowed (c : Config V O K N R f) (s : State V O K N) (x : Fin N) (w : Nat) : Prop :=
  w ∈ c.old.committee.core → c.authorized x = true ∧ sealCert c s (c.source x) = true ∧
    (∀ y, s.votes y w = true → y = x ∨ c.held x y = true) ∧
    (∀ y, c.credited x y = true → finalCert c s y = true) ∧
    (∀ i, c.imports x i = true → s.received i = true) ∧
    (∀ d, c.cost x d ≤ c.allocation x d) ∧ c.priorFences x w = false
instance : Decidable (SignAllowed c s x w) := by unfold SignAllowed; infer_instance
inductive Step (c : Config V O K N R f) : State V O K N → State V O K N → Prop where
  | old {s t} (step : MultiParent.Step c.old s.old t)
      (closed : ∀ w, w ∈ c.old.committee.core → s.closed w = true →
        ∀ x, t.signatures x w = s.old.signatures x w) : Step c s {s with old := t}
  | close (s k w) (allowed : SealAllowed c s k w) : Step c s (closeState s k w)
  | sign (s x w) (allowed : SignAllowed c s x w) : Step c s (sign s x w)
  | effect (s x w) (allowed : w ∈ c.old.committee.core → opCert c s x = true) : Step c s (effect s x w)
  | receipt (s) (i : Fin N) (verified : c.incomingAuthenticated i = true) :
      Step c s {s with received := setAt s.received i true}
  | replay (s) : Step c s s
structure Invariant (c : Config V O K N R f) (s : State V O K N) : Prop where
  old : MultiParent.Invariant c.old s.old
  closure : ∀ k w, w ∈ c.old.committee.core → s.seals k w = true → s.closed w = true
  cover : ∀ k w, w ∈ c.old.committee.core → s.seals k w = true →
    ∀ x, s.old.signatures x w = true → (c.root k).held x = true
  unique : ∀ a b w, w ∈ c.old.committee.core → s.seals a w = true → s.seals b w = true → a = b
  lineage : ∀ a b w, w ∈ c.old.committee.core → s.votes a w = true → s.votes b w = true →
    a = b ∨ c.held a b = true ∨ c.held b a = true
  capacity : ∀ x w, w ∈ c.old.committee.core → s.votes x w = true → ∀ d, c.cost x d ≤ c.allocation x d
  effects : ∀ x w, w ∈ c.old.committee.core → s.effects x w = true → opCert c s x = true
theorem quorum_mono (c : Config V O K N R f) (a b : Nat → Bool)
    (sub : ∀ w, a w = true → b w = true)
    (q : quorum c a = true) : quorum c b = true := MultiParent.quorum_mono c.old a b sub q
@[simp] theorem initial_invariant (c : Config V O K N R f) : Invariant c initial := by
  refine ⟨MultiParent.initial_invariant c.old, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals intros; contradiction
theorem step_invariant (h : Invariant c s) (st : Step c s t) : Invariant c t := by
  cases st with
  | old base frozen =>
    refine ⟨MultiParent.step_invariant h.old base, h.closure, ?_, h.unique, h.lineage, h.capacity, h.effects⟩
    intro k w hw sealVote x signed
    exact h.cover k w hw sealVote x (by rw [← frozen w hw (h.closure k w hw sealVote) x]; exact signed)
  | close k w allowed =>
    refine ⟨h.old, ?_, ?_, ?_, h.lineage, h.capacity, h.effects⟩
    · intro j u hu vote
      by_cases uw : u = w
      · subst u; simp [closeState, setAt]
      · simpa [closeState, setAt, uw] using h.closure j u hu (by simpa [closeState, uw] using vote)
    · intro j u hu vote x signed
      by_cases uw : u = w
      · subst u
        by_cases jk : j = k
        · subst j; exact (allowed hu).2.2 x signed
        · exact h.cover j w hu (by simpa [closeState, two, setAt, apply_ite, jk] using vote) x signed
      · exact h.cover j u hu (by simpa [closeState, uw] using vote) x signed
    · intro a b u hu va vb
      by_cases uw : u = w
      · subst u
        have oldOrNew : ∀ j, (closeState s k w).seals j w = true → j = k ∨ s.seals j w = true := by
          intro j vj
          by_cases jk : j = k
          · exact Or.inl jk
          · exact Or.inr (by simpa [closeState, two, setAt, apply_ite, jk] using vj)
        rcases (allowed hu).2.1 with fresh | prior
        · have only : ∀ j, (closeState s k w).seals j w = true → j = k := by
            intro j vj
            rcases oldOrNew j vj with eq | old
            · exact eq
            · have closed := h.closure j w hu old; simp [fresh] at closed
          exact (only a va).trans (only b vb).symm
        · have same : ∀ j, (closeState s k w).seals j w = true → j = k := by
            intro j vj
            rcases oldOrNew j vj with eq | old
            · exact eq
            · exact h.unique j k w hu old prior
          exact (same a va).trans (same b vb).symm
      · exact h.unique a b u hu (by simpa [closeState, uw] using va)
          (by simpa [closeState, uw] using vb)
  | sign x w allowed =>
    have mono : ∀ y u, s.votes y u = true → (sign s x w).votes y u = true := by
      intro y u vote; exact MultiParent.two_mono _ _ _ _ _ vote
    refine ⟨h.old, h.closure, h.cover, h.unique, ?_, ?_, ?_⟩
    · intro a b u hu va vb
      by_cases uw : u = w
      · subst u
        by_cases ax : a = x
        · subst a
          by_cases bx : b = x
          · exact Or.inl bx.symm
          · have old : s.votes b w = true := by simpa [sign, two, setAt, apply_ite, bx] using vb
            rcases (allowed hu).2.2.1 b old with eq | held
            · exact Or.inl eq.symm
            · exact Or.inr (Or.inl held)
        · have olda : s.votes a w = true := by simpa [sign, two, setAt, apply_ite, ax] using va
          by_cases bx : b = x
          · subst b
            rcases (allowed hu).2.2.1 a olda with eq | held
            · exact Or.inl eq
            · exact Or.inr (Or.inr held)
          · exact h.lineage a b w hu olda (by simpa [sign, two, setAt, apply_ite, bx] using vb)
      · exact h.lineage a b u hu (by simpa [sign, uw] using va)
          (by simpa [sign, uw] using vb)
    · intro a u hu vote
      by_cases uw : u = w
      · subst u
        by_cases ax : a = x
        · subst a; exact (allowed hu).2.2.2.2.2.1
        · exact h.capacity a w hu (by simpa [sign, two, setAt, apply_ite, ax] using vote)
      · exact h.capacity a u hu (by simpa [sign, uw] using vote)
    · intro a u hu vote
      exact quorum_mono c _ _ (mono a) (h.effects a u hu vote)
  | effect x w allowed =>
    refine ⟨h.old, h.closure, h.cover, h.unique, h.lineage, h.capacity, ?_⟩
    intro a u hu vote
    by_cases uw : u = w
    · subst u
      by_cases ax : a = x
      · subst a; exact allowed hu
      · exact h.effects a w hu (by simpa [effect, two, setAt, apply_ite, ax] using vote)
    · exact h.effects a u hu (by simpa [effect, uw] using vote)
  | receipt => exact ⟨h.old, h.closure, h.cover, h.unique, h.lineage, h.capacity, h.effects⟩
  | replay => exact h

inductive Run (c : Config V O K N R f) : State V O K N → State V O K N → Prop where
  | refl (s) : Run c s s
  | next : Run c s t → Step c t u → Run c s u

theorem run_invariant (run : Run c initial s) : Invariant c s := by
  induction run with
  | refl => exact initial_invariant c
  | next _ st ih => exact step_invariant ih st

theorem step_seals (st : Step c s t) : ∀ k w, s.seals k w = true → t.seals k w = true := by
  cases st <;> intro k w vote <;> first | exact vote | exact MultiParent.two_mono _ _ _ _ _ vote

theorem step_votes (st : Step c s t) : ∀ x w, s.votes x w = true → t.votes x w = true := by
  cases st <;> intro x w vote <;> first | exact vote | exact MultiParent.two_mono _ _ _ _ _ vote

theorem step_effects (st : Step c s t) : ∀ x w, s.effects x w = true → t.effects x w = true := by
  cases st <;> intro x w vote <;> first | exact vote | exact MultiParent.two_mono _ _ _ _ _ vote

private theorem root_valid_old (valid : RootValid c s k)
    (st : MultiParent.Step c.old s.old b) : RootValid c {s with old := b} k := by
  obtain ⟨auth, refunds, credits, settled, books⟩ := valid
  have j := MultiParent.step_journals st
  have fq := fun x q => MultiParent.quorum_mono c.old _ _ (j.effects x) q
  have cq := fun x q => MultiParent.quorum_mono c.old _ _ (j.fences x) q
  refine ⟨auth, ?_, ?_, ?_, books⟩
  · intro x hx; exact ⟨(refunds x hx).1, cq x (refunds x hx).2⟩
  · intro x hx; exact fq x (credits x hx)
  · intro x hx; rcases settled x hx with final | cancel
    · exact Or.inl (fq x final)
    · exact Or.inr (cq x cancel)

structure Evidence (c : Config V O K N R f) (s : State V O K N) : Prop where
  roots : ∀ k w, w ∈ c.old.committee.core → s.seals k w = true → RootValid c s k
  source : ∀ x w, w ∈ c.old.committee.core → s.votes x w = true → sealCert c s (c.source x) = true
  credits : ∀ x w, w ∈ c.old.committee.core → s.votes x w = true →
    ∀ y, c.credited x y = true → finalCert c s y = true
  external : ∀ x w, w ∈ c.old.committee.core → s.votes x w = true →
    ∀ i, c.imports x i = true → s.received i = true
  receipts : ∀ i, s.received i = true → c.incomingAuthenticated i = true
  authorized : ∀ x w, w ∈ c.old.committee.core → s.votes x w = true → c.authorized x = true

private theorem evidence_step (h : Evidence c s) (st : Step c s t) : Evidence c t := by
  have sq := fun k q => quorum_mono c _ _ (step_seals st k) q
  have fq := fun x q => quorum_mono c _ _ (step_effects st x) q
  cases st with
  | old step frozen =>
    exact ⟨fun k w hw vote => root_valid_old (h.roots k w hw vote) step,
      h.source, h.credits, h.external, h.receipts, h.authorized⟩
  | close k w allowed =>
    refine ⟨?_, ?_, h.credits, h.external, h.receipts, h.authorized⟩
    · intro j u hu vote
      by_cases uw : u = w
      · subst u
        by_cases jk : j = k
        · subst j; exact (allowed hu).1
        · exact h.roots j w hu (by simpa [closeState, two, setAt, jk] using vote)
      · exact h.roots j u hu (by simpa [closeState, uw] using vote)
    · intro x u hu vote; exact sq _ (h.source x u hu vote)
  | sign x w allowed =>
    refine ⟨h.roots, ?_, ?_, ?_, h.receipts, ?_⟩
    · intro y u hu vote
      by_cases uw : u = w
      · subst u
        by_cases yx : y = x
        · subst y; exact (allowed hu).2.1
        · exact h.source y w hu (by simpa [sign, two, setAt, yx] using vote)
      · exact h.source y u hu (by simpa [sign, uw] using vote)
    · intro y u hu vote
      by_cases uw : u = w
      · subst u
        by_cases yx : y = x
        · subst y; exact (allowed hu).2.2.2.1
        · exact h.credits y w hu (by simpa [sign, two, setAt, yx] using vote)
      · exact h.credits y u hu (by simpa [sign, uw] using vote)
    · intro y u hu vote
      by_cases uw : u = w
      · subst u
        by_cases yx : y = x
        · subst y; exact (allowed hu).2.2.2.2.1
        · exact h.external y w hu (by simpa [sign, two, setAt, yx] using vote)
      · exact h.external y u hu (by simpa [sign, uw] using vote)
    · intro y u hu vote
      by_cases uw : u = w
      · subst u
        by_cases yx : y = x
        · subst y; exact (allowed hu).1
        · exact h.authorized y w hu (by simpa [sign, two, setAt, yx] using vote)
      · exact h.authorized y u hu (by simpa [sign, uw] using vote)
  | effect x w allowed =>
    exact ⟨h.roots, h.source, fun y u hu vote z hz => fq z (h.credits y u hu vote z hz), h.external, h.receipts, h.authorized⟩
  | receipt i verified =>
    refine ⟨h.roots, h.source, h.credits, ?_, ?_, h.authorized⟩
    · intro x w hw vote j hj
      have prior := h.external x w hw vote j hj
      by_cases ji : j = i <;> simp_all [setAt]
    · intro j hj
      by_cases ji : j = i
      · subst j; exact verified
      · exact h.receipts j (by simpa [setAt, ji] using hj)
  | replay => exact h

theorem run_evidence (run : Run c initial s) : Evidence c s := by
  induction run with
  | refl => constructor <;> intros <;> contradiction
  | next _ st ih => exact evidence_step ih st

/-- Retained preactivation fences cannot later be overwritten by owned signing. -/
theorem run_unfenced (run : Run c initial s) (x : Fin N) (w : Nat)
    (hw : w ∈ c.old.committee.core) (vote : s.votes x w = true) : c.priorFences x w = false := by
  induction run with
  | refl => simp [initial] at vote
  | next prior st ih =>
    cases st with
    | sign y u allowed =>
      by_cases xy : x = y
      · subst y
        by_cases wu : w = u
        · subst u; exact (allowed hw).2.2.2.2.2.2
        · exact ih (by simpa [sign, wu] using vote)
      · exact ih (by simpa [sign, two, setAt, xy] using vote)
    | old => exact ih vote
    | close => exact ih vote
    | effect => exact ih vote
    | receipt => exact ih vote
    | replay => exact ih vote

theorem prior_cancel_excludes_owned (run : Run c initial s)
    (cancelled : quorum c (c.priorFences x) = true) : opCert c s x = false := by
  cases op : opCert c s x with
  | false => rfl
  | true =>
    obtain ⟨w, hw, signed, fenced⟩ := honest_intersection c.old.committee _ _ (of_decide_eq_true op) (of_decide_eq_true cancelled)
    have absent := run_unfenced run x w hw signed
    simp [absent] at fenced

theorem certified_root_valid (e : Evidence c s) (q : sealCert c s k = true) : RootValid c s k := by
  obtain ⟨w, hw, vote, _⟩ := honest_intersection c.old.committee _ _ (of_decide_eq_true q) (of_decide_eq_true q)
  exact e.roots k w hw vote

theorem certified_source (e : Evidence c s) (q : opCert c s x = true) : sealCert c s (c.source x) = true := by
  obtain ⟨w, hw, vote, _⟩ := honest_intersection c.old.committee _ _ (of_decide_eq_true q) (of_decide_eq_true q)
  exact e.source x w hw vote

theorem certified_credits (e : Evidence c s) (q : opCert c s x = true) :
    ∀ y, c.credited x y = true → finalCert c s y = true := by
  obtain ⟨w, hw, vote, _⟩ := honest_intersection c.old.committee _ _ (of_decide_eq_true q) (of_decide_eq_true q)
  exact e.credits x w hw vote

theorem final_operation (h : Invariant c s) (q : finalCert c s x = true) : opCert c s x = true := by
  obtain ⟨w, hw, vote, _⟩ := honest_intersection c.old.committee _ _ (of_decide_eq_true q) (of_decide_eq_true q)
  exact h.effects x w hw vote

theorem old_covered (h : Invariant c s) (q : sealCert c s k = true)
    (oldQ : MultiParent.operationCert c.old s.old x = true) : (c.root k).held x = true := by
  obtain ⟨w, hw, hv, ho⟩ := honest_intersection c.old.committee _ _ (of_decide_eq_true q) (of_decide_eq_true oldQ)
  exact h.cover k w hw hv x ho
theorem root_unique (h : Invariant c s) (a : sealCert c s i = true) (b : sealCert c s j = true) : i = j := by
  obtain ⟨w, hw, ha, hb⟩ := honest_intersection c.old.committee _ _ (of_decide_eq_true a) (of_decide_eq_true b)
  exact h.unique i j w hw ha hb
theorem certified_lineage (h : Invariant c s) (a : opCert c s x = true) (b : opCert c s y = true) :
    x = y ∨ c.held x y = true ∨ c.held y x = true := by
  obtain ⟨w, hw, ha, hb⟩ := honest_intersection c.old.committee _ _ (of_decide_eq_true a) (of_decide_eq_true b)
  exact h.lineage x y w hw ha hb
theorem certified_slot_unique (h : Invariant c s) (a : opCert c s x = true) (b : opCert c s y = true)
    (rank : c.rank x = c.rank y) : x = y := by
  rcases certified_lineage h a b with eq | held | held
  · exact eq
  · have := c.older y x held; omega
  · have := c.older x y held; omega
theorem certified_funded (h : Invariant c s) (a : opCert c s x = true) (d : Fin R) : c.cost x d ≤ c.allocation x d := by
  obtain ⟨w, hw, ha, _⟩ := honest_intersection c.old.committee _ _ (of_decide_eq_true a) (of_decide_eq_true a)
  exact h.capacity x w hw ha d
theorem certified_book (h : Invariant c s) (a : opCert c s x = true) (d : Fin R) :
    (c.cost x d : Int) + isum (List.finRange N) (fun y => if c.held x y then (c.cost y d : Int) else 0) ≤
    (c.root (c.source x)).allocation d + isum (List.finRange N) (fun y => if c.credited x y then (c.credit y d : Int) else 0) +
      isum (List.finRange N) (fun i => if c.imports x i then (c.incoming i d : Int) else 0) := by
  have cap := certified_funded h a d
  have book := c.book x d
  omega
private theorem max_witness (xs : List α) (p : α → Bool) (rank : α → Nat) :
    (∀ x ∈ xs, p x = false) ∨ ∃ m ∈ xs, p m = true ∧ ∀ x ∈ xs, p x = true → rank x ≤ rank m := by
  induction xs with
  | nil => exact Or.inl (by simp)
  | cons x xs ih =>
    rcases ih with empty | ⟨m,hm,pm,bound⟩
    · cases hx : p x with
      | false => exact Or.inl (by intro y hy; rcases List.mem_cons.mp hy with rfl | hy; exact hx; exact empty y hy)
      | true => exact Or.inr ⟨x,by simp,hx,by
          intro y hy py
          rcases List.mem_cons.mp hy with rfl | hy
          · exact Nat.le_refl _
          · have := empty y hy; simp_all⟩
    · cases hx : p x with
      | false => exact Or.inr ⟨m,by simp [hm],pm,by
          intro y hy py
          rcases List.mem_cons.mp hy with rfl | hy
          · simp_all
          · exact bound y hy py⟩
      | true =>
        by_cases le : rank x ≤ rank m
        · exact Or.inr ⟨m,by simp [hm],pm,by
            intro y hy py
            rcases List.mem_cons.mp hy with rfl | hy
            · exact le
            · exact bound y hy py⟩
        · exact Or.inr ⟨x,by simp,hx,by
            intro y hy py
            rcases List.mem_cons.mp hy with rfl | hy
            · exact Nat.le_refl _
            · have := bound y hy py; omega⟩

private theorem isum_mono (xs : List α) (a b : α → Int)
    (le : ∀ x ∈ xs, a x ≤ b x) : isum xs a ≤ isum xs b := by
  induction xs with
  | nil => simp [isum]
  | cons x xs ih =>
    have head := le x (by simp)
    have tail := ih (fun y hy => le y (by simp [hy]))
    simp only [isum]; omega

private theorem isum_zero (xs : List α) : isum xs (fun _ => 0) = 0 := by
  induction xs <;> simp_all [isum]

private theorem isum_single (m : Fin N) (value : Int) :
    isum (List.finRange N) (fun x => if x = m then value else 0) = value := by
  change isum (List.finRange N) (setAt (fun _ => 0) m value) = value
  rw [isum_update _ _ m value (finRange_unique N) (by simp)]
  simp [isum_zero]

def newDebit (c : Config V O K N R f) (s : State V O K N) (d : Fin R) : Int :=
  isum (List.finRange N) (fun x => if finalCert c s x then (c.cost x d : Int) else 0)
def newCredit (c : Config V O K N R f) (s : State V O K N) (d : Fin R) : Int :=
  isum (List.finRange N) (fun x => if finalCert c s x then (c.credit x d : Int) else 0)

def receivedCredit (c : Config V O K N R f) (s : State V O K N) (d : Fin R) : Int :=
  isum (List.finRange N) (fun i => if s.received i then (c.incoming i d : Int) else 0)

/-- Highest certified rank is a finite proof witness, never a runtime oracle. -/
theorem new_funding_bound (h : Invariant c s) (e : Evidence c s)
    (m : Fin N) (fm : finalCert c s m = true)
    (highest : ∀ x, finalCert c s x = true → c.rank x ≤ c.rank m) (d : Fin R) :
    newDebit c s d ≤ (c.root (c.source m)).allocation d + newCredit c s d + receivedCredit c s d := by
  have qm := final_operation h fm
  have debits : newDebit c s d ≤
      isum (List.finRange N) (fun x => if c.held m x then (c.cost x d : Int) else 0) + c.cost m d := by
    have pointwise : newDebit c s d ≤ isum (List.finRange N) (fun x =>
        (if c.held m x then (c.cost x d : Int) else 0) + (if x = m then (c.cost m d : Int) else 0)) := by
      apply isum_mono
      intro x _
      by_cases fx : finalCert c s x = true
      · by_cases xm : x = m
        · subst x; simp [fx]; split <;> omega
        · have carried : c.held m x = true := by
            rcases certified_lineage h (final_operation h fx) qm with eq | backwards | forwards
            · contradiction
            · have := c.older m x backwards
              have := highest x fx
              omega
            · exact forwards
          simp [fx, xm, carried]
      · simp [fx]; split <;> split <;> omega
    rw [isum_add, isum_single] at pointwise
    exact pointwise
  have credits : isum (List.finRange N) (fun x => if c.credited m x then (c.credit x d : Int) else 0) ≤ newCredit c s d := by
    apply isum_mono
    intro x _
    by_cases hx : c.credited m x = true
    · simp [hx, certified_credits e qm x hx]
    · simp [hx]; split <;> omega
  have external : isum (List.finRange N) (fun i => if c.imports m i then (c.incoming i d : Int) else 0) ≤ receivedCredit c s d := by
    obtain ⟨w, hw, vote, _⟩ := honest_intersection c.old.committee _ _ (of_decide_eq_true qm) (of_decide_eq_true qm)
    apply isum_mono
    intro i _
    by_cases hi : c.imports m i = true
    · simp [hi, e.external m w hw vote i hi]
    · simp [hi]; split <;> omega
  have funded := certified_book h qm d
  omega

/-- All old certificates, including late ones, fit the sealed root's exact books.
Canceled held costs are refunded; they cannot also be finalized. -/
theorem old_funding_bound {c : Config V O K N R f} {s : State V O K N} (h : Invariant c s) (e : Evidence c s)
    (q : sealCert c s k = true) (d : Fin R) :
    (c.root k).allocation d + (MultiParent.totalDebit c.old s.old d : Int) ≤
      c.old.initial d + (MultiParent.totalCredit c.old s.old d : Int) := by
  obtain ⟨_, refunds, credits, _, books⟩ := certified_root_valid e q
  have spent : (MultiParent.totalDebit c.old s.old d : Int) +
      isum (List.finRange O) (fun x => if (c.root k).refunded x then (c.old.cost x d : Int) else 0) ≤
      isum (List.finRange O) (fun x => if (c.root k).held x then (c.old.cost x d : Int) else 0) := by
    unfold MultiParent.totalDebit
    rw [← marked_cast, ← isum_add]
    apply isum_mono
    intro x _
    have carry : MultiParent.finalCert c.old s.old x = true → (c.root k).held x = true :=
      fun hx => old_covered h q (MultiParent.final_operation h.old hx)
    have noBoth : ¬ (MultiParent.finalCert c.old s.old x = true ∧ (c.root k).refunded x = true) := by
      intro ⟨hx, hr⟩
      exact MultiParent.final_cancel_exclusive h.old hx (refunds x hr).2
    cases hf : MultiParent.finalCert c.old s.old x <;>
      cases hr : (c.root k).refunded x <;> cases hh : (c.root k).held x <;> simp_all
  have imported : isum (List.finRange O) (fun x => if (c.root k).credited x then (c.old.credit x d : Int) else 0) ≤
      (MultiParent.totalCredit c.old s.old d : Int) := by
    unfold MultiParent.totalCredit
    rw [← marked_cast]
    apply isum_mono
    intro x _
    by_cases hc : (c.root k).credited x = true
    · simp [hc, credits x hc]
    · simp [hc]; split <;> omega
  have book := books d
  omega

/-- Global numeric safety composes the old machine and new full-capacity phase.
No balance frontier is consulted by a local guard. -/
theorem resource_nonnegative {c : Config V O K N R f} {s : State V O K N} (run : Run c initial s) (d : Fin R) :
    0 ≤ MultiParent.balance c.old s.old d + newCredit c s d + receivedCredit c s d - newDebit c s d := by
  have h := run_invariant run
  have e := run_evidence run
  rcases max_witness (List.finRange N) (finalCert c s) c.rank with empty | ⟨m, _, fm, highest⟩
  · have zeroDebit : newDebit c s d = 0 := by
      unfold newDebit
      have eq : (fun x => if finalCert c s x then (c.cost x d : Int) else 0) = fun _ => 0 := by
        funext x; simp [empty x (by simp)]
      rw [eq, isum_zero]
    have nonnegCredit : 0 ≤ newCredit c s d := by
      unfold newCredit; apply isum_nonneg; intro x _; split <;> omega
    have ext : 0 ≤ receivedCredit c s d := by
      unfold receivedCredit; apply isum_nonneg; intro i _; split <;> omega
    have old := MultiParent.resource_nonnegative h.old d
    omega
  · have bound := new_funding_bound h e m fm (fun x hx => highest x (by simp) hx) d
    have old := old_funding_bound h e (certified_source e (final_operation h fm)) d
    unfold MultiParent.balance at *
    omega


/-- Fair scheduling is over concrete local actions, not certificates. -/
inductive Action (K N : Nat) where
  | close (k : Fin K) (w : Nat)
  | sign (x : Fin N) (w : Nat)
  | effect (x : Fin N) (w : Nat)
  | other
  deriving DecidableEq

def Enabled (c : Config V O K N R f) (s : State V O K N) : Action K N → Prop
  | .close k w => s.seals k w = false ∧ SealAllowed c s k w
  | .sign x w => s.votes x w = false ∧ SignAllowed c s x w
  | .effect x w => s.effects x w = false ∧ (w ∈ c.old.committee.core → opCert c s x = true)
  | .other => True

instance (c : Config V O K N R f) (s : State V O K N) (a : Action K N) : Decidable (Enabled c s a) := by
  cases a <;> unfold Enabled <;> infer_instance

def applyAction (s : State V O K N) : Action K N → State V O K N
  | .close k w => closeState s k w
  | .sign x w => sign s x w
  | .effect x w => effect s x w
  | .other => s

/-- The old subsystem may advance between these service actions. -/
structure Service (c : Config V O K N R f) where
  state : Nat → State V O K N
  action : Nat → Action K N
  starts : state 0 = initial
  step : ∀ n, Step c (state n) (state (n+1))
  accepted : ∀ n, action n ≠ .other → Enabled c (state n) (action n) ∧
    state (n+1) = applyAction (state n) (action n)
  fair : ∀ a, (match a with | .close _ w | .sign _ w | .effect _ w => w ∈ c.old.committee.core | .other => False) → ∀ start, (∀ n, start ≤ n → Enabled c (state n) a) →
    ∃ n, start ≤ n ∧ action n = a

theorem Service.reachable (e : Service c) (n : Nat) : Run c initial (e.state n) := by
  induction n with
  | zero => rw [e.starts]; exact .refl _
  | succ n ih => exact .next ih (e.step n)

private theorem service_bit (e : Service c) (a : Action K N) (p : State V O K N → Bool)
    (honest : match a with | .close _ w | .sign _ w | .effect _ w => w ∈ c.old.committee.core | .other => False)
    (ready : ∃ start, ∀ n, start ≤ n → p (e.state n) = false → Enabled c (e.state n) a)
    (sets : ∀ n, e.action n = a → p (e.state (n+1)) = true)
    (mono : ∀ n, p (e.state n) = true → p (e.state (n+1)) = true) :
    ∃ start, ∀ n, start ≤ n → p (e.state n) = true := by
  classical
  by_cases done : ∃ n, p (e.state n) = true
  · obtain ⟨n, hn⟩ := done
    exact ⟨n, CBCL.ConsensusFree.MultiParent.Liveness.persists _ mono hn⟩
  · have absent : ∀ n, p (e.state n) = false := by
      intro n; cases h : p (e.state n) <;> simp_all
    obtain ⟨start, ready⟩ := ready
    obtain ⟨n, _, chosen⟩ := e.fair a honest start (fun n hn => ready n hn (absent n))
    exact False.elim (done ⟨n+1, sets n chosen⟩)

/-- A coherent owner's frozen, completely drained manifest enables honest seals.
The premises describe history/authorization, never an assumed seal certificate. -/
theorem eventually_sealed (e : Service c) (k : Fin K)
    (drained : ∃ start, ∀ n, start ≤ n → RootValid c (e.state n) k ∧
      (∀ w ∈ c.old.committee.core, (e.state n).closed w = false ∨ (e.state n).seals k w = true) ∧
      (∀ w ∈ c.old.committee.core, ∀ x, (e.state n).old.signatures x w = true → (c.root k).held x = true)) :
    ∃ start, ∀ n, start ≤ n → sealCert c (e.state n) k = true := by
  have each : ∀ w ∈ c.old.committee.core, ∃ start, ∀ n, start ≤ n → (e.state n).seals k w = true := by
    intro w hw
    apply service_bit e (.close k w) (fun s => s.seals k w) hw
    · obtain ⟨start, hd⟩ := drained
      exact ⟨start, fun n hn absent => ⟨absent, fun _ => ⟨(hd n hn).1, (hd n hn).2.1 w hw, (hd n hn).2.2 w hw⟩⟩⟩
    · intro n chosen
      have accepted := (e.accepted n (by simp [chosen])).2
      simp [chosen, applyAction] at accepted
      simp [accepted, closeState, two, setAt]
    · intro n; exact step_seals (e.step n) k w
  obtain ⟨start, hs⟩ := finite_eventually c.old.committee.core _ each
  exact ⟨start, fun n hn => MultiParent.Liveness.core_forms_quorum c.old _ (hs n hn)⟩

/-- The owner proposes one funded next operation and includes every prior vote.
Fair honest service then supplies both quorums without Byzantine participation.
The full allocation guard admits a final unit as well as a full-balance debit. -/
theorem eventually_final (e : Service c) (x : Fin N)
    (uncancelled : ∀ w ∈ c.old.committee.core, c.priorFences x w = false)
    (sealed : ∃ start, ∀ n, start ≤ n → sealCert c (e.state n) (c.source x) = true)
    (owner : ∃ start, ∀ n, start ≤ n → c.authorized x = true ∧
      (∀ w ∈ c.old.committee.core, (e.state n).votes x w = false → ∀ y, (e.state n).votes y w = true → y = x ∨ c.held x y = true) ∧
      (∀ y, c.credited x y = true → finalCert c (e.state n) y = true) ∧
      (∀ i, c.imports x i = true → (e.state n).received i = true) ∧
      (∀ d, c.cost x d ≤ c.allocation x d)) :
    ∃ start, ∀ n, start ≤ n → finalCert c (e.state n) x = true := by
  obtain ⟨a, ha⟩ := sealed
  obtain ⟨b, hb⟩ := owner
  have each : ∀ w ∈ c.old.committee.core, ∃ start, ∀ n, start ≤ n → (e.state n).votes x w = true := by
    intro w hw
    apply service_bit e (.sign x w) (fun s => s.votes x w) hw
    · refine ⟨max a b, fun n hn absent => ⟨absent, fun _ => ?_⟩⟩
      exact ⟨(hb n (by omega)).1, ha n (by omega), (hb n (by omega)).2.1 w hw absent,
        (hb n (by omega)).2.2.1, (hb n (by omega)).2.2.2.1, (hb n (by omega)).2.2.2.2, uncancelled w hw⟩
    · intro n chosen
      have accepted := (e.accepted n (by simp [chosen])).2
      simp [chosen, applyAction] at accepted
      simp [accepted, sign, two, setAt]
    · intro n; exact step_votes (e.step n) x w
  obtain ⟨v, hv⟩ := finite_eventually c.old.committee.core _ each
  have operation : ∀ n, v ≤ n → opCert c (e.state n) x = true :=
    fun n hn => MultiParent.Liveness.core_forms_quorum c.old _ (hv n hn)
  have effects : ∀ w ∈ c.old.committee.core, ∃ start, ∀ n, start ≤ n → (e.state n).effects x w = true := by
    intro w hw
    apply service_bit e (.effect x w) (fun s => s.effects x w) hw
    · exact ⟨v, fun n hn absent => ⟨absent, fun _ => operation n hn⟩⟩
    · intro n chosen
      have accepted := (e.accepted n (by simp [chosen])).2
      simp [chosen, applyAction] at accepted
      simp [accepted, effect, two, setAt]
    · intro n; exact step_effects (e.step n) x w
  obtain ⟨t, ht⟩ := finite_eventually c.old.committee.core _ effects
  exact ⟨t, fun n hn => MultiParent.Liveness.core_forms_quorum c.old _ (ht n hn)⟩

/-- Observer delivery is separate from vote existence. Messages are authenticated
and retained; eventual delivery has no timing bound. -/
structure Observer (c : Config V O K N R f) (states : Nat → State V O K N)
    (votes : State V O K N → Nat → Bool) where
  received : Nat → Nat → Bool
  sound : ∀ n w, received n w = true → votes (states n) w = true
  retained : ∀ n w, received n w = true → received (n+1) w = true
  delivered : ∀ w ∈ c.old.committee.core, ∀ n, votes (states n) w = true →
    ∃ m, n ≤ m ∧ received m w = true

theorem observed_quorum (e : Service c) (votes : State V O K N → Nat → Bool)
    (observer : Observer c e.state votes)
    (each : ∀ w ∈ c.old.committee.core, ∃ start, ∀ n, start ≤ n → votes (e.state n) w = true) :
    ∃ start, ∀ n, start ≤ n → quorum c (observer.received n) = true := by
  have delivered : ∀ w ∈ c.old.committee.core, ∃ start, ∀ n, start ≤ n → observer.received n w = true := by
    intro w hw
    obtain ⟨t, ht⟩ := each w hw
    obtain ⟨m, _, hm⟩ := observer.delivered w hw t (ht t (by omega))
    exact ⟨m, MultiParent.Liveness.persists _ (fun n => observer.retained n w) hm⟩
  obtain ⟨t, ht⟩ := finite_eventually c.old.committee.core _ delivered
  exact ⟨t, fun n hn => MultiParent.Liveness.core_forms_quorum c.old _ (ht n hn)⟩

def perform (c : Config V O K N R f) (s : State V O K N) (a : Action K N) : Option (State V O K N) :=
  if Enabled c s a then some (applyAction s a) else none

theorem perform_sound (h : perform c s a = some t) : Step c s t := by
  unfold perform at h
  split at h
  next enabled =>
    have eq : applyAction s a = t := Option.some.inj h
    subst t
    cases a with
    | close k w => exact .close _ _ _ enabled.2
    | sign x w => exact .sign _ _ _ enabled.2
    | effect x w => exact .effect _ _ _ enabled.2
    | other => exact .replay _
  next disabled => contradiction

def execute (c : Config V O K N R f) (s : State V O K N) : List (Action K N) → Option (State V O K N)
  | [] => some s
  | a :: rest => (perform c s a).bind (fun t => execute c t rest)


/-- Closure cannot appear without a persistent seal vote. -/
theorem closed_origin (run : Run c initial s) :
    ∀ w, s.closed w = true → ∃ k, s.seals k w = true := by
  induction run with
  | refl => simp [initial]
  | next prior st ih =>
    cases st with
    | close k u allowed =>
      intro w hw
      by_cases wu : w = u
      · subst w; exact ⟨k, by simp [closeState, two, setAt]⟩
      · obtain ⟨j, hj⟩ := ih w (by simpa [closeState, setAt, wu] using hw)
        exact ⟨j, by simpa [closeState, wu] using hj⟩
    | old => exact ih
    | sign => exact ih
    | effect => exact ih
    | receipt => exact ih
    | replay => exact ih

/-- One coherent owner signs exactly one seal intent; no winner selection is
assumed of validators. This derives the closure-readiness condition. -/
theorem correct_owner_closure (e : Service c) (k : Fin K)
    (uniqueIntent : ∀ j, (c.root j).authorized = true → j = k)
    (n w : Nat) (hw : w ∈ c.old.committee.core) :
    (e.state n).closed w = false ∨ (e.state n).seals k w = true := by
  cases hc : (e.state n).closed w with
  | false => exact Or.inl rfl
  | true =>
    obtain ⟨j, hj⟩ := closed_origin (e.reachable n) w hc
    have valid := (run_evidence (e.reachable n)).roots j w hw hj
    have eq := uniqueIntent j valid.1
    subst j; exact Or.inr hj

private theorem finite_catalogue (xs : List α) (p : Nat → α → Prop)
    (each : ∀ x ∈ xs, ∃ start, ∀ n, start ≤ n → p n x) :
    ∃ start, ∀ n, start ≤ n → ∀ x ∈ xs, p n x := by
  induction xs with
  | nil => exact ⟨0, by simp⟩
  | cons x xs ih =>
    obtain ⟨a, ha⟩ := each x (by simp)
    obtain ⟨b, hb⟩ := ih (fun y hy => each y (by simp [hy]))
    refine ⟨max a b, ?_⟩
    intro n hn y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ha n (by omega)
    · exact hb n (by omega) y hy

/-- A frozen finite submitted catalogue inside the concurrent envelope actually
 drains. The old execution is the projection of the same initialized service;
there is no assumed terminal certificate and no cancellation race. -/
theorem finite_batch_drains {c : Config V O K N R f} (e : Service c) (old : MultiParent.Liveness.Execution c.old)
    (projection : ∀ n, old.state n = (e.state n).old)
    (authorized : ∀ x, c.old.authorized x = true)
    (noCancel : ∀ x, c.old.cancelAuthorized x = false)
    (stable : ∀ x n w, w ∈ c.old.committee.core → (old.state n).active w = c.old.opVersion x)
    (envelope : ∀ x, MultiParent.Liveness.FitsEnvelope c.old (c.old.opVersion x))
    (signFair : ∀ x w, w ∈ c.old.committee.core → MultiParent.Liveness.WeakFair old.command
      (fun n => MultiParent.Liveness.SignEnabled c.old (old.state n) x w) (.sign x w))
    (effectFair : ∀ x w, w ∈ c.old.committee.core → MultiParent.Liveness.WeakFair old.command
      (fun n => MultiParent.Liveness.EffectEnabled c.old (old.state n) x w) (.effect x w)) :
    ∃ start, ∀ n, start ≤ n → ∀ x, MultiParent.finalCert c.old (e.state n).old x = true := by
  have each : ∀ x ∈ List.finRange O, ∃ start, ∀ n, start ≤ n → MultiParent.finalCert c.old (e.state n).old x = true := by
    intro x _
    obtain ⟨t, ht⟩ := MultiParent.Liveness.envelope_eventual_finality old x
      (authorized x) (noCancel x) (stable x) (envelope x) (signFair x) (effectFair x)
    exact ⟨t, by simpa only [projection] using ht⟩
  obtain ⟨t, ht⟩ := finite_catalogue (List.finRange O) _ each
  exact ⟨t, fun n hn x => ht n hn x (by simp)⟩

/-- Complete drained books plus a single authorized intent derive seal enabling.
`drain` is supplied by finite_batch_drains, not assumed as a seal certificate. -/
theorem seal_after_drain (e : Service c) (k : Fin K)
    (drain : ∃ start, ∀ n, start ≤ n → ∀ x, MultiParent.finalCert c.old (e.state n).old x = true)
    (authorized : (c.root k).authorized = true)
    (uniqueIntent : ∀ j, (c.root j).authorized = true → j = k)
    (held : ∀ x, (c.root k).held x = true)
    (noRefund : ∀ x, (c.root k).refunded x = false)
    (books : ∀ d, ((c.root k).allocation d : Int) = c.old.initial d +
      isum (List.finRange O) (fun x => if (c.root k).credited x then (c.old.credit x d : Int) else 0) -
      isum (List.finRange O) (fun x => if (c.root k).held x then (c.old.cost x d : Int) else 0) +
      isum (List.finRange O) (fun x => if (c.root k).refunded x then (c.old.cost x d : Int) else 0)) :
    ∃ start, ∀ n, start ≤ n → sealCert c (e.state n) k = true := by
  apply eventually_sealed e k
  obtain ⟨t, ht⟩ := drain
  refine ⟨t, fun n hn => ⟨?_, correct_owner_closure e k uniqueIntent n, ?_⟩⟩
  · exact ⟨authorized, by simp [noRefund], fun x _ => ht n hn x,
      fun x _ => Or.inl (ht n hn x), books⟩
  · exact fun _ _ x _ => held x

/-- Formed effects votes are eventually observed by the owner as an actual
verifiable quorum. Reachability links progress and numeric safety domains. -/
theorem client_observes_finality (e : Service c) (x : Fin N)
    (observer : Observer c e.state (fun s => s.effects x))
    (finalized : ∃ start, ∀ n, start ≤ n → finalCert c (e.state n) x = true) :
    ∃ start, ∀ n, start ≤ n → quorum c (observer.received n) = true := by
  obtain ⟨t, ht⟩ := finalized
  apply observed_quorum e _ observer
  intro w hw
  apply service_bit e (.effect x w) (fun s => s.effects x w) hw
  · exact ⟨t, fun n hn absent => ⟨absent, fun _ =>
      final_operation (run_invariant (e.reachable n)) (ht n hn)⟩⟩
  · intro n chosen
    have accepted := (e.accepted n (by simp [chosen])).2
    simp [chosen, applyAction] at accepted
    simp [accepted, effect, two, setAt]
  · intro n; exact step_effects (e.step n) x w

theorem Run.trans (first : Run c s t) (second : Run c t u) : Run c s u := by
  induction second with
  | refl => exact first
  | next _ st ih => exact .next ih st

/-- Every accepted executable trace is a run of the proved transition system. -/
theorem execute_sound {c : Config V O K N R f} {s t : State V O K N}
    {actions : List (Action K N)} (ok : execute c s actions = some t) : Run c s t := by
  induction actions generalizing s with
  | nil => simp [execute] at ok; subst t; exact .refl _
  | cons a rest ih =>
    cases h : perform c s a with
    | none => simp [execute, h] at ok
    | some mid =>
      have tail : execute c mid rest = some t := by simpa [execute, h] using ok
      exact Run.trans (.next (.refl _) (perform_sound h)) (ih tail)

namespace Witness
private def committee : Committee 1 where
  core := [0, 1, 2]
  others := [3]
  distinct := by decide
  core_size := by decide
  other_size := by decide
private def old (balance : Nat) : MultiParent.Config 0 0 R 1 where
  graph := ⟨fun _ => []⟩
  committee := committee
  manifest := fun _ => ⟨fun _ => false, fun _ => false, fun _ => false, fun _ => balance, true⟩
  initial := fun _ => balance
  opVersion := Fin.elim0
  cost := Fin.elim0
  credit := Fin.elim0
  authorized := Fin.elim0
  cancelAuthorized := Fin.elim0
  disjoint := fun tx => Fin.elim0 tx

def unit : Config 0 0 1 1 1 1 where
  old := old 1
  root := fun _ => ⟨fun _ => false, fun _ => false, fun _ => false, fun _ => 1, true⟩
  source := fun _ => 0
  rank := fun _ => 0
  held := fun _ _ => false
  credited := fun _ _ => false
  allocation := fun _ _ => 1
  cost := fun _ _ => 1
  credit := fun _ _ => 0
  authorized := fun _ => true
  incoming := fun _ _ => 0
  incomingAuthenticated := fun _ => false
  imports := fun _ _ => false
  priorFences := fun _ _ => false
  older := by intros; contradiction
  sameRoot := by intros; rfl
  creditsOlder := by intros; contradiction
  book := by decide

def spendDown : Config 0 0 1 2 1 1 where
  old := old 5
  root := fun _ => ⟨fun _ => false, fun _ => false, fun _ => false, fun _ => 5, true⟩
  source := fun _ => 0
  rank := Fin.val
  held := fun x y => decide (y.val < x.val)
  credited := fun _ _ => false
  allocation := fun x _ => if x.val = 0 then 5 else 1
  cost := fun x _ => if x.val = 0 then 4 else 1
  credit := fun _ _ => 0
  authorized := fun _ => true
  incoming := fun _ _ => 0
  incomingAuthenticated := fun _ => false
  imports := fun _ _ => false
  priorFences := fun _ _ => false
  older := by intros x y h; exact of_decide_eq_true h
  sameRoot := by intros; rfl
  creditsOlder := by intros; contradiction
  book := by decide

def handoff : List (Action 1 N) := [.close 0 0, .close 0 1, .close 0 2]
def spend (x : Fin N) : List (Action K N) :=
  [.sign x 0, .sign x 1, .sign x 2, .effect x 0, .effect x 1, .effect x 2]

def unitEnd := execute unit initial (handoff ++ spend 0)
def downEnd := execute spendDown initial (handoff ++ spend 0 ++ spend 1)
example : unitEnd.isSome = true := by decide
example : finalCert unit (unitEnd.getD initial) 0 = true := by decide
example : (unitEnd.getD initial).seals 0 3 = false ∧ (unitEnd.getD initial).votes 0 3 = false := by decide
example : downEnd.isSome = true := by decide
example : finalCert spendDown (downEnd.getD initial) 0 = true ∧ finalCert spendDown (downEnd.getD initial) 1 = true := by decide
example : newDebit spendDown (downEnd.getD initial) 0 = 5 := by decide
example : ¬ SignAllowed spendDown (downEnd.getD initial) 0 0 := by decide

/-- Burn rights to create headroom, mint against it, then spend all rights. -/
def cycle : Config 0 0 1 3 2 1 where
  old := { (old 5) with
    initial := fun d => if d.val = 0 then 5 else 0
    manifest := fun _ => ⟨fun _ => false, fun _ => false, fun _ => false, (fun d => if d.val = 0 then 5 else 0), true⟩ }
  root := fun _ => ⟨fun _ => false, fun _ => false, fun _ => false, fun d => if d.val = 0 then 5 else 0, true⟩
  source := fun _ => 0
  rank := Fin.val
  held := fun x y => decide (y.val < x.val)
  credited := fun x y => decide (y.val < x.val ∧ y.val < 2)
  allocation := fun x d => if x.val = 1 then (if d.val = 1 then 5 else 0) else (if d.val = 0 then 5 else 0)
  cost := fun x d => if x.val = 1 then (if d.val = 1 then 5 else 0) else (if d.val = 0 then 5 else 0)
  credit := fun x d => if x.val = 0 then (if d.val = 1 then 5 else 0) else if x.val = 1 then (if d.val = 0 then 5 else 0) else 0
  authorized := fun _ => true
  incoming := fun _ _ => 0
  incomingAuthenticated := fun _ => false
  imports := fun _ _ => false
  priorFences := fun _ _ => false
  older := by intros x y h; exact of_decide_eq_true h
  sameRoot := by intros; rfl
  creditsOlder := by intros x y h; exact (of_decide_eq_true h).1
  book := by decide

def cycleEnd := execute cycle initial (handoff ++ spend 0 ++ spend 1 ++ spend 2)
example : cycleEnd.isSome = true := by decide
example : finalCert cycle (cycleEnd.getD initial) 2 = true := by decide
example : MultiParent.balance cycle.old (cycleEnd.getD initial).old 0 + newCredit cycle (cycleEnd.getD initial) 0 - newDebit cycle (cycleEnd.getD initial) 0 = 0 := by decide

def lateIncoming : Config 0 0 1 1 1 1 := { unit with
  incoming := fun _ _ => 1
  incomingAuthenticated := fun _ => true
  imports := fun _ _ => true
  allocation := fun _ _ => 2
  cost := fun _ _ => 2
  book := by decide }
def beforeIncoming := (execute lateIncoming initial handoff).getD initial
def afterIncoming : State 0 0 1 1 := {beforeIncoming with received := fun _ => true}
example : ¬ SignAllowed lateIncoming beforeIncoming 0 0 := by decide
example : Step lateIncoming beforeIncoming afterIncoming := by
  have hs : setAt beforeIncoming.received 0 true = fun _ => true := by
    funext i
    have eq : i = 0 := Subsingleton.elim i 0
    subst i; simp [setAt]
  simpa only [afterIncoming, hs] using (Step.receipt (c := lateIncoming) beforeIncoming 0 (by decide))
example : (execute lateIncoming afterIncoming (spend 0)).isSome = true := by decide
example : (execute lateIncoming afterIncoming (spend 0)).map (fun s =>
  MultiParent.balance lateIncoming.old s.old 0 + receivedCredit lateIncoming s 0 + newCredit lateIncoming s 0 - newDebit lateIncoming s 0) = some 0 := by decide

/-- A silent fourth validator is compatible with useful-action fairness: all
honest work has become disabled after the finite completion script. -/
example : ∀ w ∈ unit.old.committee.core,
    ¬ Enabled unit (unitEnd.getD initial) (.close 0 w) ∧
    ¬ Enabled unit (unitEnd.getD initial) (.sign 0 w) ∧
    ¬ Enabled unit (unitEnd.getD initial) (.effect 0 w) := by
  intro w hw
  have casesW : w = 0 ∨ w = 1 ∨ w = 2 := by simpa [unit, old, committee] using hw
  rcases casesW with rfl | rfl | rfl <;> decide

def prefenced : Config 0 0 1 1 1 1 := {unit with priorFences := fun _ _ => true}
example : ¬ SignAllowed prefenced ((execute prefenced initial handoff).getD initial) 0 0 := by decide

end Witness

end CBCL.ConsensusFree.OwnedLifecycle
