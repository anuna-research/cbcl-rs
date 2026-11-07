import LeanCbcl.StateKernelQueries

/-!
Compact initial and plain LWW-register continuation (SPEC-035 / IMPL-027).
Only bounded witnesses/winner are runtime state; `history` below is ghost data.
Typed clock recognition and order-preserving signer/address ranks are inputs.
This is a model proof, not an extraction/correspondence proof for Rust, parsing,
canonicalization, cryptography, coverage proofs, durability or admission.

Initial witnesses need not be the least two by address. Rust chooses the least
pair for canonical serialized summaries; this model proves only the semantic
witness invariant and continuation, not exact byte/state correspondence. Plain
LWW has no observed-replacement or domain semantics here. A `none` clock excludes
an act; natural-number clocks/ranks assume the host's stable, order-preserving
interpretation of bounded wire evidence. Neither clocks nor ranks are generated.
-/
namespace CBCL.CheckpointCompact
open CBCL.State CBCL.StateKernelSemantics CBCL.StateKernelQueries

/-- Repeated native identities denote identical authenticated acts. -/
def IdentityConsistent (history : List Act) : Prop :=
  ∀ a ∈ history, ∀ b ∈ history, a.addr = b.addr → a = b

/-- A delivery is fresh or identical to every prior act with its identity. -/
def Compatible (history : List Act) (a : Act) : Prop :=
  ∀ b ∈ history, b.addr = a.addr → b = a

/-- Host-verified pre-update coverage; the summary never computes this flag. -/
def ExactCoverage (history : List Act) (a : Act) (covered : Bool) : Prop :=
  covered = true ↔ ∃ b ∈ history, b.addr = a.addr

theorem covered_member {H : List Act} {a : Act} {covered : Bool}
    (coverage : ExactCoverage H a covered) (compatible : Compatible H a)
    (seen : covered = true) : a ∈ H := by
  obtain ⟨b, hb, same⟩ := coverage.mp seen
  rw [compatible b hb same] at hb
  exact hb

theorem consistent_cons {H : List Act} {a : Act}
    (h : IdentityConsistent H) (compatible : Compatible H a) :
    IdentityConsistent (a :: H) := by
  intro x hx y hy same
  rcases List.mem_cons.mp hx with hxa | hxH
  · subst x
    rcases List.mem_cons.mp hy with hya | hyH
    · exact hya.symm
    · exact (compatible y hyH same.symm).symm
  · rcases List.mem_cons.mp hy with hya | hyH
    · subst y; exact compatible x hxH same
    · exact h x hxH y hyH same

/-- Ghost history; identical redeliveries may appear repeatedly. -/
def extend : List Act → List (Act × Bool) → List Act
  | H, [] => H
  | H, (a, _) :: tail => extend (a :: H) tail

/-- A concrete local input contract, not a continuation-law hypothesis. -/
def ValidTail : List Act → List (Act × Bool) → Prop
  | _, [] => True
  | H, (a, covered) :: tail =>
      ExactCoverage H a covered ∧ Compatible H a ∧ ValidTail (a :: H) tail

namespace Initial

/-- Two distinct opener witnesses suffice to establish permanent ambiguity. -/
inductive Summary where
  /-- No eligible opener has been observed. -/
  | empty
  /-- One distinct opener identity has been observed; retain its act. -/
  | one (a : Act)
  /-- Retain two opener witnesses; the invariant requires distinct addresses. -/
  | many (a b : Act)
  deriving DecidableEq

/-- Expose at most two retained opener witnesses, without ghost history or an
address-sorting guarantee; the invariant establishes eligibility and distinctness. -/
def witnesses : Summary → List Act
  | .empty => []
  | .one a => [a]
  | .many a b => [a,b]

/-- Consume one admitted act using externally verified pre-update coverage. Skip
covered identities and other verbs; retain the first witness or a distinct second
witness, after which ambiguity remains established. -/
def step (verb : String) (s : Summary) (a : Act) (covered : Bool) : Summary :=
  if covered then s else if a.verb != verb then s else
    match s with
    | .empty => .one a
    | .one b => if a.addr = b.addr then s else .many b a
    | .many _ _ => s

/-- Truthful witnesses of zero/one/at-least-two distinct eligible identities. -/
def Invariant (verb : String) (H : List Act) : Summary → Prop
  | .empty => ∀ a ∈ H, a.verb ≠ verb
  | .one a => a ∈ H ∧ a.verb = verb ∧ ∀ b ∈ H, b.verb = verb → b = a
  | .many a b => a ∈ H ∧ b ∈ H ∧ a.verb = verb ∧ b.verb = verb ∧ a.addr ≠ b.addr

theorem bounded (s : Summary) : (witnesses s).length ≤ 2 := by
  cases s <;> simp [witnesses]

theorem empty_invariant (verb : String) : Invariant verb [] .empty := by
  simp [Invariant]

theorem extend_seen {verb : String} {H : List Act} {s : Summary} {a : Act}
    (inv : Invariant verb H s) (seen : a ∈ H) : Invariant verb (a :: H) s := by
  cases s <;> simp only [Invariant, List.mem_cons] at * <;> grind

theorem step_preserves {verb : String} {H : List Act} {s : Summary} {a : Act}
    {covered : Bool} (inv : Invariant verb H s)
    (coverage : ExactCoverage H a covered) (compatible : Compatible H a) :
    Invariant verb (a :: H) (step verb s a covered) := by
  by_cases seen : covered = true
  · simpa [step, seen] using extend_seen inv (covered_member coverage compatible seen)
  · by_cases eligible : a.verb = verb
    · cases s with
      | empty => simp [step, seen, eligible, Invariant] at *; grind
      | one b =>
          by_cases same : a.addr = b.addr
          · have ab : a = b := (compatible b inv.1 same.symm).symm
            subst a
            simpa [step, seen] using extend_seen inv inv.1
          · have next : Invariant verb (a :: H) (.many b a) :=
              ⟨by simp [inv.1], by simp, inv.2.1, eligible, Ne.symm same⟩
            simpa [step, seen, eligible, same] using next
      | many b c => simp [step, seen, eligible, Invariant] at *; grind
    · cases s <;> simp [step, seen, eligible, Invariant] at * <;> grind

/-- Render uses the existing distinct-sole selector, then native projection. -/
def render (field : String) (s : Summary) : Cell :=
  project field false (sole (witnesses s))

theorem sole_eq {verb : String} {H : List Act} {s : Summary}
    (inv : Invariant verb H s) : sole (witnesses s) = sole (acts verb H) := by
  apply (sole_complete (acts verb H) _).mp
  cases s with
  | empty =>
      simp only [witnesses, sole, SoleMeaning]
      rintro ⟨a, member, _⟩
      have h := List.mem_filter.mp member
      exact inv a h.1 (by simpa using h.2)
  | one a =>
      simp only [witnesses, sole, List.all_nil, ite_true, SoleMeaning]
      exact ⟨by simpa [acts] using And.intro inv.1 inv.2.1,
        fun b hb => inv.2.2 b (List.mem_filter.mp hb).1 (by simpa using (List.mem_filter.mp hb).2)⟩
  | many a b =>
      have distinct : b ≠ a := fun eq => inv.2.2.2.2 (congrArg Act.addr eq.symm)
      simp only [witnesses, sole, List.all_cons, List.all_nil, Bool.and_true]
      simp only [beq_iff_eq, distinct, ↓reduceIte, SoleMeaning]
      rintro ⟨x, _, uniform⟩
      have ax := uniform a (by simpa [acts] using And.intro inv.1 inv.2.2.1)
      have bx := uniform b (by simpa [acts] using And.intro inv.2.1 inv.2.2.2.1)
      exact distinct (bx.trans ax.symm)

theorem render_eq {verb : String} {H : List Act} {s : Summary}
    (inv : Invariant verb H s) (field : String) :
    render field s = project field false (sole (acts verb H)) := by
  unfold render; rw [sole_eq inv]

/-- Apply a finite delivery tail to bounded initializer state. Each pair carries
an act and its verified coverage flag; runtime execution never takes history. -/
def run (verb : String) : Summary → List (Act × Bool) → Summary
  | s, [] => s
  | s, (a, covered) :: tail => run verb (step verb s a covered) tail

theorem run_preserves {verb : String} {H : List Act} {s : Summary}
    {tail : List (Act × Bool)} (inv : Invariant verb H s) (valid : ValidTail H tail) :
    Invariant verb (extend H tail) (run verb s tail) := by
  induction tail generalizing H s with
  | nil => exact inv
  | cons event tail ih =>
      rcases event with ⟨a, covered⟩
      exact ih (step_preserves inv valid.1 valid.2.1) valid.2.2

/-- Arbitrary-tail continuation, derived from truthful bounded witnesses. -/
theorem continuation {verb : String} {H : List Act} {s : Summary}
    {tail : List (Act × Bool)} (inv : Invariant verb H s) (valid : ValidTail H tail)
    (field : String) : render field (run verb s tail) =
      project field false (sole (acts verb (extend H tail))) :=
  render_eq (run_preserves inv valid) field

theorem witness_verb {verb : String} {H : List Act} {s : Summary}
    (inv : Invariant verb H s) {a : Act} (member : a ∈ witnesses s) : a.verb = verb := by
  cases s with
  | empty => simp [witnesses] at member
  | one b =>
      have same : a = b := by simpa [witnesses] using member
      subst a; exact inv.2.1
  | many b c =>
      simp only [witnesses, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact inv.2.2.1
      · exact inv.2.2.2.1

theorem acts_witnesses_eq {verb : String} {H : List Act} {s : Summary}
    (inv : Invariant verb H s) : acts verb (witnesses s) = witnesses s := by
  apply List.filter_eq_self.mpr
  intro a ha
  exact beq_iff_eq.mpr (witness_verb inv ha)

/-- Native initial selector endpoint for composition over retained live acts. -/
theorem sole_acts_eq {verb : String} {H : List Act} {s : Summary}
    (inv : Invariant verb H s) :
    sole (acts verb (witnesses s)) = sole (acts verb H) := by
  rw [acts_witnesses_eq inv]; exact sole_eq inv

theorem distinct_witnesses {verb : String} {H : List Act} {s : Summary}
    (inv : Invariant verb H s) : ((witnesses s).map Act.addr).Nodup := by
  cases s with
  | empty => simp [witnesses]
  | one a => simp [witnesses]
  | many a b => simpa [witnesses] using inv.2.2.2.2

theorem duplicate_noop (verb : String) (s : Summary) (a : Act) :
    step verb s a true = s := by simp [step]

theorem step_render_eq {verb : String} {H : List Act} {s : Summary} {a : Act}
    {covered : Bool} (inv : Invariant verb H s) (coverage : ExactCoverage H a covered)
    (compatible : Compatible H a) (field : String) :
    render field (step verb s a covered) = project field false (sole (acts verb (a :: H))) :=
  render_eq (step_preserves inv coverage compatible) field

/-- Genesis-to-arbitrary-tail result with only local input contracts. -/
theorem from_genesis (verb field : String) (tail : List (Act × Bool))
    (valid : ValidTail [] tail) : render field (run verb .empty tail) =
    project field false (sole (acts verb (extend [] tail))) :=
  continuation (empty_invariant verb) valid field

/-- Field-independent arbitrary-tail endpoint for dependent rule composition. -/
theorem continuation_sole_acts {verb : String} {H : List Act} {s : Summary}
    {tail : List (Act × Bool)} (inv : Invariant verb H s) (valid : ValidTail H tail) :
    sole (acts verb (witnesses (run verb s tail))) = sole (acts verb (extend H tail)) :=
  sole_acts_eq (run_preserves inv valid)

end Initial

namespace LwwRegister

/-- An act paired with immutable physical/logical, signer-rank and address evidence. -/
abbrev Candidate := HlcRegister.Candidate Act
/-- Runtime plain-LWW state: no eligible candidate, or one retained greatest candidate. -/
abbrev Summary := Option Candidate

/-- Select a maximum from the incoming eligible candidate and the retained winner;
at most two candidates are inspected and at most one is retained. -/
def merge (s : Summary) (a : Candidate) : Summary :=
  HlcRegister.pick (a :: s.toList)

/-- The sole retained candidate dominates every prior eligible candidate. -/
def Invariant (clock : Clock) (rank : SignerRank) (verb field : String)
    (H : List Act) (s : Summary) : Prop :=
  HlcRegister.Specification (StateKernelQueries.candidates clock rank (.hlc field) (acts verb H)) s

/-- Admit an act to arbitration only when its verb matches and the supplied
clock recognizer returns physical/logical evidence for the configured field. -/
def incoming (clock : Clock) (rank : SignerRank) (verb field : String)
    (a : Act) : Option Candidate :=
  if a.verb = verb then decorate clock rank (.hlc field) a else none

/-- Skip an externally verified covered delivery; otherwise merge an eligible
incoming candidate with the retained winner. Nonwriters and invalid clocks are no-ops. -/
def step (clock : Clock) (rank : SignerRank) (verb field : String)
    (s : Summary) (a : Act) (covered : Bool) : Summary :=
  if covered then s else match incoming clock rank verb field a with
    | none => s
    | some candidate => merge s candidate

theorem bounded (s : Summary) : s.toList.length ≤ 1 := by
  cases s <;> simp

/-- The maximum of a new candidate and a prior maximum is a maximum of the
full enlarged candidate set. No continuation equation is assumed. -/
theorem merge_preserves {H : List Candidate} {s : Summary} (a : Candidate)
    (inv : HlcRegister.Specification H s) :
    HlcRegister.Specification (a :: H) (merge s a) := by
  cases s with
  | none =>
      change H = [] at inv
      subst H
      exact HlcRegister.pick_satisfies [a]
  | some old =>
      change HlcRegister.Greatest H old at inv
      by_cases le : HlcRegister.LE a.key old.key
      · have next : HlcRegister.Greatest (a :: H) old := by
          refine ⟨List.mem_cons_of_mem a inv.1, ?_⟩
          intro b hb
          rcases List.mem_cons.mp hb with rfl | hb
          · exact le
          · exact inv.2 b hb
        simpa [merge, HlcRegister.pick, le] using next
      · have reverse : HlcRegister.LE old.key a.key :=
          (HlcRegister.le_total a.key old.key).resolve_left le
        have next : HlcRegister.Greatest (a :: H) a := by
          refine ⟨List.mem_cons_self, ?_⟩
          intro b hb
          rcases List.mem_cons.mp hb with rfl | hb
          · exact HlcRegister.le_refl _
          · exact HlcRegister.le_trans (inv.2 b hb) reverse
        simpa [merge, HlcRegister.pick, le] using next

theorem specification_congr {A B : List Candidate}
    (same : ∀ a, a ∈ A ↔ a ∈ B) (s : Summary) :
    HlcRegister.Specification A s ↔ HlcRegister.Specification B s := by
  cases s with
  | none =>
      change (A = []) ↔ (B = [])
      constructor
      · intro h; apply List.eq_nil_iff_forall_not_mem.mpr
        intro a ha; have := (same a).mpr ha; simp [h] at this
      · intro h; apply List.eq_nil_iff_forall_not_mem.mpr
        intro a ha; have := (same a).mp ha; simp [h] at this
  | some a => simp only [HlcRegister.Specification, HlcRegister.Greatest, same]

theorem candidates_cons (clock : Clock) (rank : SignerRank) (verb field : String)
    (a : Act) (H : List Act) :
    StateKernelQueries.candidates clock rank (.hlc field) (acts verb (a :: H)) =
      (incoming clock rank verb field a).toList ++
        StateKernelQueries.candidates clock rank (.hlc field) (acts verb H) := by
  by_cases eligible : a.verb = verb
  · cases h : decorate clock rank (.hlc field) a <;>
      simp [acts, StateKernelQueries.candidates, incoming, eligible, h]
  · simp [acts, StateKernelQueries.candidates, incoming, eligible]

theorem empty_invariant (clock : Clock) (rank : SignerRank) (verb field : String) :
    Invariant clock rank verb field [] none := by
  rfl

theorem step_preserves {clock : Clock} {rank : SignerRank} {verb field : String}
    {H : List Act} {s : Summary} {a : Act} {covered : Bool}
    (inv : Invariant clock rank verb field H s)
    (coverage : ExactCoverage H a covered) (compatible : Compatible H a) :
    Invariant clock rank verb field (a :: H)
      (step clock rank verb field s a covered) := by
  by_cases seen : covered = true
  · have member := covered_member coverage compatible seen
    have same : ∀ c, c ∈ StateKernelQueries.candidates clock rank (.hlc field) (acts verb (a :: H)) ↔
        c ∈ StateKernelQueries.candidates clock rank (.hlc field) (acts verb H) := by
      intro c
      simp only [candidate_member, acts, List.mem_filter, List.mem_cons]
      grind
    have next := (specification_congr same s).mpr inv
    simpa [step, seen, Invariant] using next
  · unfold Invariant at *
    rw [candidates_cons]
    cases fresh : incoming clock rank verb field a with
    | none => simpa [step, seen, fresh] using inv
    | some candidate =>
        simpa [step, seen, fresh] using merge_preserves candidate inv

/-- Consistent native histories induce consistent decorated eligible StateKernelQueries.candidates. -/
theorem candidates_consistent {H : List Act} (consistent : IdentityConsistent H)
    (clock : Clock) (rank : SignerRank) (verb field : String) :
    HlcRegister.Consistent (StateKernelQueries.candidates clock rank (.hlc field) (acts verb H)) := by
  intro x hx y hy same
  obtain ⟨a, ha, da⟩ := List.mem_filterMap.mp hx
  obtain ⟨b, hb, db⟩ := List.mem_filterMap.mp hy
  have ax := (decorate_correct clock rank (.hlc field) a x).mp da
  have by' := (decorate_correct clock rank (.hlc field) b y).mp db
  have xa : x.key.address = a.addr := by
    exact evidence_address ax.2
  have yb : y.key.address = b.addr := by
    exact evidence_address by'.2
  have ab := consistent a (List.mem_filter.mp ha).1 b (List.mem_filter.mp hb).1
    (xa.symm.trans (same.trans yb))
  subst b
  exact Option.some.inj (da.symm.trans db)

/-- Project the requested payload from the retained winner using the existing
state-kernel projection, including absent-winner and missing-field results. -/
def render (payload : String) (s : Summary) : Cell :=
  project payload false (s.map HlcRegister.Candidate.value)

theorem pick_eq {clock : Clock} {rank : SignerRank} {verb field : String}
    {H : List Act} {s : Summary} (consistent : IdentityConsistent H)
    (inv : Invariant clock rank verb field H s) :
    s = HlcRegister.pick (StateKernelQueries.candidates clock rank (.hlc field) (acts verb H)) :=
  (HlcRegister.pick_correct (candidates_consistent consistent clock rank verb field) s).mp inv

/-- Equality with the existing clock-aware kernel query, including absent clocks. -/
theorem render_eq {clock : Clock} {rank : SignerRank} {verb field : String}
    {H : List Act} {s : Summary} (consistent : IdentityConsistent H)
    (inv : Invariant clock rank verb field H s) (payload : String) :
    render payload s = project payload false
      (choose clock rank (.hlc field) (acts verb H)) := by
  unfold render choose
  rw [pick_eq consistent inv]

/-- Process an arbitrary finite tail with one fixed clock recognizer and signer
ranking. Each step uses its supplied coverage flag and only the compact winner state. -/
def run (clock : Clock) (rank : SignerRank) (verb field : String) :
    Summary → List (Act × Bool) → Summary
  | s, [] => s
  | s, (a, covered) :: tail => run clock rank verb field
      (step clock rank verb field s a covered) tail

theorem run_preserves {clock : Clock} {rank : SignerRank} {verb field : String}
    {H : List Act} {s : Summary} {tail : List (Act × Bool)}
    (consistent : IdentityConsistent H) (inv : Invariant clock rank verb field H s)
    (valid : ValidTail H tail) :
    IdentityConsistent (extend H tail) ∧
      Invariant clock rank verb field (extend H tail) (run clock rank verb field s tail) := by
  induction tail generalizing H s with
  | nil => exact ⟨consistent, inv⟩
  | cons event tail ih =>
      rcases event with ⟨a, covered⟩
      exact ih (consistent_cons consistent valid.2.1)
        (step_preserves inv valid.1 valid.2.1) valid.2.2

/-- Arbitrary-tail equality follows from dominance and immutable identity input. -/
theorem continuation {clock : Clock} {rank : SignerRank} {verb field : String}
    {H : List Act} {s : Summary} {tail : List (Act × Bool)}
    (consistent : IdentityConsistent H) (inv : Invariant clock rank verb field H s)
    (valid : ValidTail H tail) (payload : String) :
    render payload (run clock rank verb field s tail) = project payload false
      (choose clock rank (.hlc field) (acts verb (extend H tail))) := by
  obtain ⟨nextConsistent, nextInv⟩ := run_preserves consistent inv valid
  exact render_eq nextConsistent nextInv payload

/-- The runtime payload table contains zero or one act, not ghost history. -/
def liveActs (s : Summary) : List Act := s.toList.map HlcRegister.Candidate.value

theorem live_bounded (s : Summary) : (liveActs s).length ≤ 1 := by
  simp only [liveActs, List.length_map]
  exact bounded s

/-- Every retained winner has recognized clock evidence and an admitted origin. -/
theorem winner_eligible {clock : Clock} {rank : SignerRank} {verb field : String}
    {H : List Act} {candidate : Candidate}
    (inv : Invariant clock rank verb field H (some candidate)) :
    candidate.value ∈ acts verb H ∧
      ∃ physical logical, clock field candidate.value = some (physical, logical) ∧
      candidate.key = ⟨physical, logical, rank candidate.value.signer, candidate.value.addr⟩ := by
  exact (candidate_member clock rank (.hlc field) (acts verb H) candidate).mp inv.1

/-- Every retained live act already belongs to the configured writer verb. -/
theorem acts_live_eq {clock : Clock} {rank : SignerRank} {verb field : String}
    {H : List Act} {s : Summary} (inv : Invariant clock rank verb field H s) :
    acts verb (liveActs s) = liveActs s := by
  cases s with
  | none => rfl
  | some candidate =>
      have eligible := (List.mem_filter.mp (winner_eligible inv).1).2
      simpa [acts, liveActs] using eligible

/-- Retained winner is a fixed point of the existing native chooser. -/
theorem choose_retained {clock : Clock} {rank : SignerRank} {verb field : String}
    {H : List Act} {s : Summary} (inv : Invariant clock rank verb field H s) :
    choose clock rank (.hlc field) (liveActs s) = s.map HlcRegister.Candidate.value := by
  cases s with
  | none => simp [choose, liveActs, StateKernelQueries.candidates, HlcRegister.pick]
  | some c =>
      have eligible := winner_eligible inv
      have decorated : decorate clock rank (.hlc field) c.value = some c :=
        (decorate_correct clock rank (.hlc field) c.value c).mpr ⟨rfl, eligible.2⟩
      simp [choose, liveActs, StateKernelQueries.candidates, decorated, HlcRegister.pick]

/-- Native LWW selector endpoint for composition over retained live acts. -/
theorem choose_live_eq {clock : Clock} {rank : SignerRank} {verb field : String}
    {H : List Act} {s : Summary} (consistent : IdentityConsistent H)
    (inv : Invariant clock rank verb field H s) :
    choose clock rank (.hlc field) (liveActs s) =
      choose clock rank (.hlc field) (acts verb H) := by
  rw [choose_retained inv]
  exact congrArg (fun selected => selected.map HlcRegister.Candidate.value) (pick_eq consistent inv)

/-- Exact native `.verb` selection endpoint for scalar-expression composition. -/
theorem choose_acts_live_eq {clock : Clock} {rank : SignerRank} {verb field : String}
    {H : List Act} {s : Summary} (consistent : IdentityConsistent H)
    (inv : Invariant clock rank verb field H s) :
    choose clock rank (.hlc field) (acts verb (liveActs s)) =
      choose clock rank (.hlc field) (acts verb H) := by
  rw [acts_live_eq inv]
  exact choose_live_eq consistent inv

theorem duplicate_noop (clock : Clock) (rank : SignerRank) (verb field : String)
    (s : Summary) (a : Act) : step clock rank verb field s a true = s := by simp [step]

theorem stale_noop (old incoming : Candidate) (le : HlcRegister.LE incoming.key old.key) :
    merge (some old) incoming = some old := by simp [merge, HlcRegister.pick, le]

theorem ineligible_noop (clock : Clock) (rank : SignerRank) (verb field : String)
    (s : Summary) (a : Act) (h : incoming clock rank verb field a = none) :
    step clock rank verb field s a false = s := by simp [step, h]

theorem step_render_eq {clock : Clock} {rank : SignerRank} {verb field : String}
    {H : List Act} {s : Summary} {a : Act} {covered : Bool}
    (consistent : IdentityConsistent H) (inv : Invariant clock rank verb field H s)
    (coverage : ExactCoverage H a covered) (compatible : Compatible H a) (payload : String) :
    render payload (step clock rank verb field s a covered) = project payload false
      (choose clock rank (.hlc field) (acts verb (a :: H))) :=
  render_eq (consistent_cons consistent compatible) (step_preserves inv coverage compatible) payload

/-- Genesis-to-arbitrary-tail result, with no assumed history/summary equality. -/
theorem from_genesis (clock : Clock) (rank : SignerRank) (verb field payload : String)
    (tail : List (Act × Bool)) (valid : ValidTail [] tail) :
    render payload (run clock rank verb field none tail) = project payload false
      (choose clock rank (.hlc field) (acts verb (extend [] tail))) := by
  apply continuation (inv := empty_invariant clock rank verb field) (valid := valid)
  simp [IdentityConsistent]

/-- Field-independent arbitrary-tail endpoint for dependent rule composition. -/
theorem continuation_choose {clock : Clock} {rank : SignerRank} {verb field : String}
    {H : List Act} {s : Summary} {tail : List (Act × Bool)}
    (consistent : IdentityConsistent H) (inv : Invariant clock rank verb field H s)
    (valid : ValidTail H tail) :
    choose clock rank (.hlc field) (liveActs (run clock rank verb field s tail)) =
      choose clock rank (.hlc field) (acts verb (extend H tail)) := by
  obtain ⟨nextConsistent, nextInv⟩ := run_preserves consistent inv valid
  exact choose_live_eq nextConsistent nextInv

end LwwRegister

end CBCL.CheckpointCompact

