import LeanCbcl.StateKernelSEC

/-!
Compact rule-scoped checkpoint continuation. History occurs only in the logical
invariant and reference fold, never in Row. Coverage is an authenticated membership
oracle for accepted identities, not a proof of snapshot truth. The concrete
representation below retains live contributions and unseen scoped suppressions.
-/
namespace CBCL.CheckpointSummary
open State StateKernelSemantics StateKernelQueries StateKernel StateKernelSEC

/-- Global scope, a typed key, or an authenticated signer encoded as a string. -/
abbrev Scope := Option Val

/-- Static writer/replacer classification and immutable replacement-scope projection. -/
structure Config where
  /-- Whether an accepted act contributes a value to this row. -/
  writer : Act → Bool
  /-- Whether an accepted act may suppress named contributions in this row. -/
  replacing : Act → Bool
  /-- The key or signer scope used to compare writer and replacement acts. -/
  scope : Act → Scope

/-- Sufficient data: surviving contributions and unseen scoped replacement targets. -/
structure Row where
  /-- Surviving writer bodies; never an archive of all accepted acts. -/
  live : List Act
  /-- Replacement references retained only while their target identity is unseen. -/
  pending : List (Scope × Nat)

/-- Reference coverage is used in proofs; execution receives an oracle. -/
def covered (H : List Act) (id : Nat) : Bool := H.any (fun a => a.addr == id)

@[simp] theorem covered_iff (H : List Act) (id : Nat) :
    covered H id = true ↔ ∃ a ∈ H, a.addr = id := by
  simp [covered, List.any_eq_true]

/-- One incoming act can suppress only named identities in its own rule scope. -/
def retires (c : Config) (r w : Act) : Bool :=
  c.replacing r && decide (c.scope r = c.scope w) && r.replaces.contains w.addr

/-- Declarative suppression ranges over all accepted acts, including retired ones. -/
def Replaced (c : Config) (H : List Act) (w : Act) : Prop :=
  ∃ r ∈ H, retires c r w = true

/-- No history list is stored in a compact row. -/
def Invariant (c : Config) (H : List Act) (s : Row) : Prop :=
  (∀ w, w ∈ s.live ↔ w ∈ H ∧ c.writer w = true ∧ ¬ Replaced c H w) ∧
  (∀ k id, (k, id) ∈ s.pending ↔ covered H id = false ∧
    ∃ r ∈ H, c.replacing r = true ∧ c.scope r = k ∧ id ∈ r.replaces)

/-- The same update order as the runtime: duplicate guard; pending lookup and
resolution; insertion; same-scope removal; unseen-reference retention. -/
def step (c : Config) (coverage : Nat → Bool) (s : Row) (e : Act) : Row :=
  if coverage e.addr then s else
  let inserted := if c.writer e = true ∧ (c.scope e, e.addr) ∉ s.pending
    then e :: s.live else s.live
  let old := s.pending.filter (fun p => p.2 != e.addr)
  let refs := if c.replacing e then
    e.replaces.filterMap (fun id =>
      if id ≠ e.addr ∧ coverage id = false then some (c.scope e, id) else none)
    else []
  ⟨inserted.filter (fun w => !retires c e w), (old ++ refs).foldr List.insert []⟩

/-- The initial row has no contributions and no suppression evidence. -/
def empty : Row := ⟨[], []⟩

theorem empty_invariant (c : Config) : Invariant c [] empty := by
  simp [Invariant, empty, Replaced, covered]

@[simp] theorem replaced_cons (c : Config) (H : List Act) (e w : Act) :
    Replaced c (e :: H) w ↔ retires c e w = true ∨ Replaced c H w := by
  simp [Replaced, List.mem_cons, or_and_right, exists_or]

@[simp] theorem covered_cons (H : List Act) (e : Act) (id : Nat) :
    covered (e :: H) id = (e.addr == id || covered H id) := rfl

/-- A fresh arrival's old suppression is exactly the pending lookup. -/
theorem pending_arrival {c : Config} {H : List Act} {s : Row} {e : Act}
    (valid : Invariant c H s) (fresh : covered H e.addr = false) :
    (c.scope e, e.addr) ∈ s.pending ↔ Replaced c H e := by
  rw [valid.2, fresh]
  simp [Replaced, retires, Bool.and_eq_true, and_assoc]

@[simp] theorem mem_pairs (xs : List (Scope × Nat)) (p : Scope × Nat) :
    p ∈ xs.foldr List.insert [] ↔ p ∈ xs := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [List.foldr, ih]

/-- Exact pending-membership equation, independent of the history invariant. -/
theorem pending_step (c : Config) (coverage : Nat → Bool) (s : Row) (e : Act)
    (fresh : coverage e.addr = false) (k : Scope) (id : Nat) :
    (k, id) ∈ (step c coverage s e).pending ↔
      ((k, id) ∈ s.pending ∧ id ≠ e.addr) ∨
      (c.replacing e = true ∧ c.scope e = k ∧ id ∈ e.replaces ∧
        id ≠ e.addr ∧ coverage id = false) := by
  simp only [step, fresh, Bool.false_eq_true, ↓reduceIte, mem_pairs,
    List.mem_append, List.mem_filter, bne_iff_ne]
  cases hr : c.replacing e <;> simp [List.mem_filterMap] <;> grind

/-- Fresh-step preservation proves both live rows and pruning of seen targets. -/
theorem step_preserves {c : Config} {H : List Act} {s : Row} {e : Act}
    (valid : Invariant c H s) (fresh : covered H e.addr = false) :
    Invariant c (e :: H) (step c (covered H) s e) := by
  have absent : e ∉ H := by
    intro member
    have h := (covered_iff H e.addr).mpr ⟨e, member, rfl⟩
    simp [fresh] at h
  constructor
  · intro w
    have lookup := pending_arrival valid fresh
    by_cases insert : c.writer e = true ∧ (c.scope e, e.addr) ∉ s.pending
    · simp [step, fresh, insert, valid.1, replaced_cons]
      by_cases same : w = e
      · subst w; simp_all
      · simp_all; grind
    · simp [step, fresh, insert, valid.1, replaced_cons]
      by_cases same : w = e
      · subst w
        have no_candidate : ¬ (c.writer e = true ∧ ¬ Replaced c H e) := by
          simpa only [lookup] using insert
        simp_all
      · simp_all; grind
  · intro k id
    rw [pending_step c (covered H) s e fresh, valid.2]
    simp only [covered_cons, Bool.or_eq_false_iff, beq_eq_false_iff_ne,
      List.mem_cons]
    constructor
    · rintro (⟨⟨notCovered, r, member, replacing, scope, named⟩, notSelf⟩ |
        ⟨replacing, scope, named, notSelf, notCovered⟩)
      · exact ⟨⟨Ne.symm notSelf, notCovered⟩, r, Or.inr member, replacing, scope, named⟩
      · exact ⟨⟨Ne.symm notSelf, notCovered⟩, e, Or.inl rfl, replacing, scope, named⟩
    · rintro ⟨⟨notSelf, notCovered⟩, r, member, replacing, scope, named⟩
      rcases member with rfl | member
      · exact Or.inr ⟨replacing, scope, named, Ne.symm notSelf, notCovered⟩
      · exact Or.inl ⟨⟨notCovered, r, member, replacing, scope, named⟩, Ne.symm notSelf⟩

/-- A covered replay does not need its historical body to leave state unchanged. -/
theorem duplicate_noop (c : Config) (coverage : Nat → Bool) (s : Row) (e : Act)
    (duplicate : coverage e.addr = true) : step c coverage s e = s := by
  simp [step, duplicate]

/-- Native current() scope: global when unkeyed, exact typed key otherwise. -/
def Config.current (verb : String) (key delete : Option String) : Config :=
  ⟨fun a => a.verb == verb,
    fun a => a.verb == verb || delete.any (fun d => a.verb == d), keyOf key⟩

/-- Native currentOwn() is scoped by authenticated signer, not payload sender. -/
def Config.own (verb : String) : Config :=
  ⟨fun a => a.verb == verb, fun a => a.verb == verb,
    fun a => some (.str a.signer)⟩

theorem current_replaced (v : String) (k d : Option String) (H : List Act) (w : Act) :
    Replaced (.current v k d) H w ↔
      ∃ r ∈ replacers v d H, keyOf k r = keyOf k w ∧ w.addr ∈ r.replaces := by
  cases d <;> simp [Replaced, retires, Config.current, replacers, acts,
    Bool.and_eq_true, Bool.or_eq_true, Option.any, and_assoc] <;> grind

theorem live_current {v : String} {k d : Option String} {H : List Act} {s : Row}
    (valid : Invariant (.current v k d) H s) : SetEq s.live (current v k d H) := by
  intro w
  rw [valid.1, mem_current_iff, current_replaced]
  simp only [Config.current, beq_iff_eq, acts, List.mem_filter]
  grind

theorem live_own {v : String} {H : List Act} {s : Row}
    (valid : Invariant (.own v) H s) : SetEq s.live (currentOwn v H) := by
  intro w
  rw [valid.1, mem_currentOwn_iff]
  simp only [Replaced, retires, Config.own, Bool.and_eq_true, decide_eq_true_eq,
    Option.some.injEq, Val.str.injEq, List.contains_iff_mem, acts, List.mem_filter, beq_iff_eq]
  grind

/-- Re-folding the retained current row cannot resurrect a removed contributor. -/
theorem current_live_fixed {v : String} {k d : Option String} {H : List Act} {s : Row}
    (valid : Invariant (.current v k d) H s) : SetEq (current v k d s.live) s.live := by
  intro w
  rw [mem_current_iff]
  constructor
  · intro h; exact (List.mem_filter.mp h.1).1
  · intro member
    have hw := (valid.1 w).mp member
    refine ⟨List.mem_filter.mpr ⟨member, by simpa [Config.current] using hw.2.1⟩, ?_⟩
    intro r hr key named
    apply hw.2.2
    rw [current_replaced]
    refine ⟨r, ?_, key, named⟩
    have sub : ∀ x ∈ s.live, x ∈ H := fun x hx => ((valid.1 x).mp hx).1
    cases d with
    | none =>
      have hr' : r ∈ acts v s.live := by simpa [replacers] using hr
      have both := List.mem_filter.mp hr'
      simpa [replacers, acts] using And.intro (sub r both.1) both.2
    | some dv =>
      simp only [replacers, List.mem_append, acts, List.mem_filter] at hr ⊢
      exact hr.elim (fun h => Or.inl ⟨sub r h.1, h.2⟩) (fun h => Or.inr ⟨sub r h.1, h.2⟩)

theorem own_live_fixed {v : String} {H : List Act} {s : Row}
    (valid : Invariant (.own v) H s) : SetEq (currentOwn v s.live) s.live := by
  intro w
  rw [mem_currentOwn_iff]
  constructor
  · intro h; exact (List.mem_filter.mp h.1).1
  · intro member
    have hw := (valid.1 w).mp member
    refine ⟨List.mem_filter.mpr ⟨member, by simpa [Config.own] using hw.2.1⟩, ?_⟩
    intro r hr signer named
    have rmember := (List.mem_filter.mp hr).1
    have rverb := (List.mem_filter.mp hr).2
    apply hw.2.2
    refine ⟨r, ((valid.1 r).mp rmember).1, ?_⟩
    simp [retires, Config.own, rverb, signer, named]

/-- The reference accepted store suppresses identities, not whole act bodies. -/
def ingest (H : List Act) (e : Act) : List Act :=
  if covered H e.addr then H else e :: H

/-- Reference accepted-store replay, separate from compact state maintenance. -/
def replay (H tail : List Act) : List Act := tail.foldl ingest H

/-- Reference deduplication by accepted identity from an initially empty store. -/
def normalize (H : List Act) : List Act := replay [] H

/-- Coverage storage contains identities, never past act bodies. -/
def insertCoverage (coverage : Nat → Bool) (address : Nat) : Nat → Bool :=
  fun id => address == id || coverage id

theorem ingest_unique {H : List Act} (unique : NodupAddr H) (e : Act) :
    NodupAddr (ingest H e) := by
  by_cases duplicate : covered H e.addr = true
  · simpa [ingest, duplicate] using unique
  · have fresh : covered H e.addr = false := Bool.eq_false_iff.mpr duplicate
    simp only [ingest, fresh, Bool.false_eq_true, ↓reduceIte, NodupAddr, List.map_cons,
      List.nodup_cons, List.mem_map]
    refine ⟨?_, unique⟩
    rintro ⟨a, member, address⟩
    exact duplicate ((covered_iff H e.addr).mpr ⟨a, member, address⟩)

theorem replay_unique {H : List Act} (unique : NodupAddr H) (tail : List Act) :
    NodupAddr (replay H tail) := by
  induction tail generalizing H with
  | nil => exact unique
  | cons e rest ih => exact ih (ingest_unique unique e)

theorem normalize_unique (H : List Act) : NodupAddr (normalize H) :=
  replay_unique (by simp [NodupAddr]) H

theorem replay_append (H A B : List Act) : replay H (A ++ B) = replay (replay H A) B := by
  simp [replay, List.foldl_append]

theorem normalize_append (H D : List Act) : normalize (H ++ D) = replay (normalize H) D :=
  replay_append [] H D

/-- Exact membership oracle supplied to the pure update. -/
structure RowState where
  /-- Membership oracle over accepted identities, not a cache of their bodies. -/
  coverage : Nat → Bool
  /-- The rule-local compact contribution and suppression data. -/
  row : Row

/-- Genesis state with empty identity coverage and an empty row. -/
def RowState.empty : RowState := ⟨fun _ => false, CheckpointSummary.empty⟩

/-- Apply one recognized act, preserving the duplicate no-op and coverage boundary. -/
def RowState.step (c : Config) (s : RowState) (e : Act) : RowState :=
  if s.coverage e.addr then s else
    ⟨insertCoverage s.coverage e.addr, CheckpointSummary.step c s.coverage s.row e⟩

/-- Process an arbitrary finite tail using only the current compact state. -/
def RowState.advance (c : Config) (s : RowState) (tail : List Act) : RowState :=
  tail.foldl (RowState.step c) s

/-- Ghost relation tying exact coverage and sufficient row data to an accepted history. -/
def RowState.Valid (c : Config) (H : List Act) (s : RowState) : Prop :=
  (∀ id, s.coverage id = covered H id) ∧ Invariant c H s.row

theorem row_empty_valid (c : Config) : RowState.Valid c [] RowState.empty := by
  exact ⟨fun _ => rfl, empty_invariant c⟩

theorem row_step_valid {c : Config} {H : List Act} {s : RowState}
    (valid : s.Valid c H) (e : Act) : (s.step c e).Valid c (ingest H e) := by
  by_cases duplicate : covered H e.addr = true
  · simpa [RowState.step, valid.1, ingest, duplicate] using valid
  · have fresh : covered H e.addr = false := Bool.eq_false_iff.mpr duplicate
    simp only [RowState.step, valid.1, fresh, Bool.false_eq_true, ↓reduceIte,
      ingest, RowState.Valid]
    have coverage : s.coverage = covered H := funext valid.1
    exact ⟨fun id => by simp [insertCoverage, valid.1],
      by simpa [coverage] using step_preserves valid.2 fresh⟩

/-- Arbitrary tail length, not bounded testing or an assumed continuation law. -/
theorem row_advance_valid {c : Config} {H : List Act} {s : RowState}
    (valid : s.Valid c H) (tail : List Act) : (s.advance c tail).Valid c (replay H tail) := by
  induction tail generalizing H s with
  | nil => exact valid
  | cons e rest ih => exact ih (row_step_valid valid e)

/-- Construct a compact checkpoint by incremental maintenance from genesis. -/
def RowState.checkpoint (c : Config) (H : List Act) : RowState :=
  RowState.empty.advance c H

theorem checkpoint_valid (c : Config) (H : List Act) :
    (RowState.checkpoint c H).Valid c (normalize H) :=
  row_advance_valid (row_empty_valid c) H

/-- Resuming a constructed compact checkpoint describes exactly full replay's set. -/
theorem checkpoint_continuation (c : Config) (H tail : List Act) :
    ((RowState.checkpoint c H).advance c tail).Valid c (normalize (H ++ tail)) := by
  rw [normalize_append]
  exact row_advance_valid (checkpoint_valid c H) tail

end CBCL.CheckpointSummary
