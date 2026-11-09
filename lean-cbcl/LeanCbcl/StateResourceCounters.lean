import LeanCbcl.StateResourceKahn

/-! Mutable native Kahn counters versus unprocessed dependency identities.
The waiting-map child lists are the inverse of the recognized, deduplicated
parent lists; popping a parent decrements each listed child exactly once. -/
namespace CBCL.StateResourceCounters

/-- Count parent identities that have not yet been processed. -/
def outstanding (parents processed : List Nat) : Nat :=
  (parents.filter (fun parent => !processed.contains parent)).length

theorem outstanding_cons (first : Nat) (rest processed : List Nat) :
    outstanding (first :: rest) processed =
      (if first ∈ processed then 0 else 1) + outstanding rest processed := by
  by_cases member : first ∈ processed <;> simp [outstanding,member,Nat.add_comm]

theorem outstanding_nil (parents : List Nat) : outstanding parents [] = parents.length := by
  induction parents with
  | nil => rfl
  | cons first rest ih => simp [outstanding_cons,ih,Nat.add_comm]

theorem outstanding_positive (parents processed : List Nat) (parent : Nat)
    (member : parent ∈ parents) (fresh : parent ∉ processed) : 0 < outstanding parents processed := by
  have selected : parent ∈ parents.filter (fun parent => !processed.contains parent) :=
    List.mem_filter.mpr ⟨member,by simp [fresh]⟩
  by_cases zero : outstanding parents processed = 0
  · have nil : parents.filter (fun parent => !processed.contains parent) = [] := List.length_eq_zero_iff.mp zero
    rw [nil] at selected
    contradiction
  · omega

theorem outstanding_after_pop (parents processed : List Nat) (parent : Nat)
    (unique : parents.Nodup) (fresh : parent ∉ processed) :
    outstanding parents (parent :: processed) =
      outstanding parents processed - if parent ∈ parents then 1 else 0 := by
  induction parents with
  | nil => simp [outstanding]
  | cons first rest ih =>
    obtain ⟨absent,tailUnique⟩ := List.nodup_cons.mp unique
    have tail := ih tailUnique
    by_cases same : parent = first
    · subst first
      simp [outstanding_cons,fresh,absent] at tail ⊢
      omega
    · have unequal : first ≠ parent := Ne.symm same
      by_cases member : parent ∈ rest
      · have positive := outstanding_positive rest processed parent member fresh
        by_cases prior : first ∈ processed <;>
          simp [outstanding_cons,prior,same,unequal,member] at tail ⊢ <;> omega
      · by_cases prior : first ∈ processed <;>
          simp [outstanding_cons,prior,same,unequal,member] at tail ⊢ <;> omega

/-- The unprocessed children waiting for a given parent identity. -/
def waiting (known : List Nat) (parents : Nat → List Nat) (processed : List Nat) (parent : Nat) : List Nat :=
  if parent ∈ processed then [] else known.filter (fun child => (parents child).contains parent)

/-- Decrement one child's outstanding-parent counter. -/
def decrement (counts : Nat → Nat) (child : Nat) : Nat → Nat :=
  fun address => if address = child then counts address - 1 else counts address

/-- Decrement the counters of every waiting child. -/
def decrementAll (counts : Nat → Nat) (children : List Nat) : Nat → Nat := children.foldl decrement counts

theorem decrementAll_value (counts : Nat → Nat) (children : List Nat) (address : Nat) :
    decrementAll counts children address = counts address - children.count address := by
  induction children generalizing counts with
  | nil => simp [decrementAll]
  | cons child rest ih =>
    simp only [decrementAll,List.foldl_cons]
    change decrementAll (decrement counts child) rest address = _
    rw [ih]
    by_cases same : address = child
    · subst address
      simp [decrement,List.count_cons_self,Nat.sub_sub,Nat.add_comm]
    · simp [decrement,same,List.count_cons,beq_eq_false_iff_ne.mpr (Ne.symm same)]


theorem count_unique (values : List Nat) (unique : values.Nodup) (address : Nat) :
    values.count address = if address ∈ values then 1 else 0 := by
  induction values with
  | nil => simp
  | cons first rest ih =>
    obtain ⟨absent,tailUnique⟩ := List.nodup_cons.mp unique
    by_cases same : address = first
    · subst address
      simp [List.count_cons_self,ih tailUnique,absent]
    · simp [List.count_cons,beq_eq_false_iff_ne.mpr (Ne.symm same),ih tailUnique,same]

/-- Mutable counters equal the number of unprocessed dependencies. -/
def CountersAgree (known : List Nat) (parents : Nat → List Nat) (processed : List Nat) (counts : Nat → Nat) : Prop :=
  ∀ child ∈ known, counts child = outstanding (parents child) processed

/-- The actual waiting-list decrement loop preserves the exact number of
unreleased parents. This applies also when the structural pass releases a
missing external parent without inventing any resource summary. -/
theorem waiting_pop_refinement (known : List Nat) (parents : Nat → List Nat) (processed : List Nat)
    (counts : Nat → Nat) (parent : Nat) (uniqueKnown : known.Nodup)
    (uniqueParents : ∀ child ∈ known, (parents child).Nodup) (fresh : parent ∉ processed)
    (invariant : CountersAgree known parents processed counts) :
    CountersAgree known parents (parent :: processed)
      (decrementAll counts (waiting known parents processed parent)) := by
  intro child member
  have childrenUnique : (waiting known parents processed parent).Nodup := by
    simp only [waiting,if_neg fresh]
    exact uniqueKnown.sublist List.filter_sublist
  have childWaiting : child ∈ waiting known parents processed parent ↔ parent ∈ parents child := by
    simp [waiting,fresh,member]
  rw [decrementAll_value,invariant child member,count_unique _ childrenUnique,
    outstanding_after_pop (parents child) processed parent (uniqueParents child member) fresh]
  simp only [childWaiting]

theorem waiting_after_pop (known : List Nat) (parents : Nat → List Nat) (processed : List Nat)
    (parent other : Nat) :
    waiting known parents (parent :: processed) other =
      if other = parent then [] else waiting known parents processed other := by
  by_cases same : other = parent <;> simp [waiting,same]

theorem zero_count_ready (parents processed : List Nat) :
    outstanding parents processed = 0 ↔ ∀ parent ∈ parents, parent ∈ processed := by
  simp [outstanding,List.length_eq_zero_iff,List.filter_eq_nil_iff]

theorem waiting_decrement_safe (known : List Nat) (parents : Nat → List Nat) (processed : List Nat)
    (counts : Nat → Nat) (parent child : Nat) (fresh : parent ∉ processed)
    (invariant : CountersAgree known parents processed counts)
    (member : child ∈ waiting known parents processed parent) : 0 < counts child := by
  have selected : child ∈ known ∧ parent ∈ parents child := by simpa [waiting,fresh] using member
  rw [invariant child selected.1]
  exact outstanding_positive (parents child) processed parent selected.2 fresh


/-- The processed identities are closed under dependencies. -/
def ProcessedClosed (parents : Nat → List Nat) (processed : List Nat) : Prop :=
  ∀ child ∈ processed, ∀ parent ∈ parents child, parent ∈ processed

/-- The mutable ready queue agrees with zero outstanding counters. -/
def ReadyAgree (known processed : List Nat) (counts : Nat → Nat) (ready : Nat → Bool) : Prop :=
  ∀ child ∈ known, ready child = true ↔ child ∉ processed ∧ counts child = 0

/-- Update the ready queue after releasing a parent. -/
def readyAfterPop (ready : Nat → Bool) (counts : Nat → Nat) (children : List Nat) (parent : Nat) : Nat → Bool :=
  fun child => if child = parent then false else
    ready child || (children.contains child && decide (decrementAll counts children child = 0))

theorem processed_closed_after_pop (known : List Nat) (parents : Nat → List Nat) (processed : List Nat)
    (counts : Nat → Nat) (ready : Nat → Bool) (parent : Nat)
    (invariant : CountersAgree known parents processed counts) (readyInv : ReadyAgree known processed counts ready)
    (closed : ProcessedClosed parents processed) (accepted : parent ∈ known) (selected : ready parent = true) :
    ProcessedClosed parents (parent :: processed) := by
  intro child member dependency edge
  rcases List.mem_cons.mp member with same | old
  · subst child
    have zero := (readyInv parent accepted).mp selected
    have released := (zero_count_ready (parents parent) processed).mp ((invariant parent accepted).symm.trans zero.2)
    exact List.mem_cons_of_mem parent (released dependency edge)
  · exact List.mem_cons_of_mem parent (closed child old dependency edge)

/-- Actual ready-set removal/insertion agrees with zero counters after the
waiting-list decrement loop, rather than assuming an independent readiness
oracle. Previously processed children cannot still wait for this fresh parent. -/
theorem ready_pop_refinement (known : List Nat) (parents : Nat → List Nat) (processed : List Nat)
    (counts : Nat → Nat) (ready : Nat → Bool) (parent : Nat) (uniqueKnown : known.Nodup)
    (fresh : parent ∉ processed) (closed : ProcessedClosed parents processed)
    (countInv : CountersAgree known parents processed counts) (readyInv : ReadyAgree known processed counts ready) :
    ReadyAgree known (parent :: processed)
      (decrementAll counts (waiting known parents processed parent))
      (readyAfterPop ready counts (waiting known parents processed parent) parent) := by
  intro child member
  let children := waiting known parents processed parent
  have uniqueChildren : children.Nodup := by
    simp only [children,waiting,if_neg fresh]
    exact uniqueKnown.sublist List.filter_sublist
  by_cases same : child = parent
  · subst child
    simp [readyAfterPop]
  · by_cases waitingChild : child ∈ children
    · have edge : parent ∈ parents child := by simpa [children,waiting,fresh,member] using waitingChild
      have notProcessed : child ∉ processed := by
        intro old
        exact fresh (closed child old parent edge)
      have positive : 0 < counts child := waiting_decrement_safe known parents processed counts parent child fresh countInv waitingChild
      have notReady : ready child = false := by
        cases selected : ready child with
        | false => rfl
        | true => have zero := ((readyInv child member).mp selected).2; omega
      simp [readyAfterPop,same,waitingChild,notProcessed,notReady,children]
    · have unchanged : decrementAll counts children child = counts child := by
        rw [decrementAll_value,count_unique children uniqueChildren]
        simp [waitingChild]
      have before := readyInv child member
      simpa [ReadyAgree,readyAfterPop,same,waitingChild,unchanged,children] using before


/-- The native mutable Kahn worklist state. -/
structure Worklist where
  /-- The identities already released by the worklist. -/
  processed : List Nat
  /-- The outstanding-parent counters indexed by child identity. -/
  counts : Nat → Nat
  /-- The inverse dependency lists indexed by parent identity. -/
  waiters : Nat → List Nat
  /-- The identities queued for processing. -/
  ready : Nat → Bool

/-- Counters, waiters, readiness, and processed closure agree with the dependency graph. -/
structure Invariant (known : List Nat) (parents : Nat → List Nat) (state : Worklist) : Prop where
  counters : CountersAgree known parents state.processed state.counts
  waiting : ∀ parent, state.waiters parent = StateResourceCounters.waiting known parents state.processed parent
  readiness : ReadyAgree known state.processed state.counts state.ready
  closed : ProcessedClosed parents state.processed

/-- Initialize counters, waiting lists, and the ready queue. -/
def initWorklist (known : List Nat) (parents : Nat → List Nat) : Worklist :=
  ⟨[],fun child => (parents child).length,waiting known parents [],
    fun child => known.contains child && decide ((parents child).length = 0)⟩

/-- Release one identity and update its waiting children. -/
def pop (state : Worklist) (parent : Nat) : Worklist :=
  let children := state.waiters parent
  ⟨parent :: state.processed,decrementAll state.counts children,
    fun address => if address = parent then [] else state.waiters address,
    readyAfterPop state.ready state.counts children parent⟩

theorem initialize_invariant (known : List Nat) (parents : Nat → List Nat) :
    Invariant known parents (initWorklist known parents) := by
  constructor
  · intro child _; simp [initWorklist,outstanding_nil]
  · intro parent; rfl
  · intro child member; simp [initWorklist,member]
  · intro _ member; contradiction

/-- All native counter, waiting-map and ready-set operations preserve their
shared dependency interpretation. Readiness is derived from those operations. -/
theorem pop_invariant (known : List Nat) (parents : Nat → List Nat) (state : Worklist) (parent : Nat)
    (invariant : Invariant known parents state) (unique : known.Nodup)
    (uniqueParents : ∀ child ∈ known, (parents child).Nodup)
    (accepted : parent ∈ known) (selected : state.ready parent = true) :
    Invariant known parents (pop state parent) := by
  have fresh := ((invariant.readiness parent accepted).mp selected).1
  have children := invariant.waiting parent
  constructor
  · simpa [pop,children] using waiting_pop_refinement known parents state.processed state.counts parent unique uniqueParents fresh invariant.counters
  · intro address
    simp only [pop]
    rw [invariant.waiting address,waiting_after_pop]
  · simpa [pop,children] using ready_pop_refinement known parents state.processed state.counts state.ready parent unique fresh invariant.closed invariant.counters invariant.readiness
  · exact processed_closed_after_pop known parents state.processed state.counts state.ready parent
      invariant.counters invariant.readiness invariant.closed accepted selected

/-- Run at most the supplied number of worklist steps. -/
def runFuel (known : List Nat) : Nat → Worklist → Worklist
  | 0,state => state
  | fuel+1,state => match known.find? state.ready with
    | none => state
    | some parent => runFuel known fuel (pop state parent)

/-- The complete executable native waiting-map/ready-set traversal preserves
its dependency meaning from the concrete initializer. -/
theorem runFuel_invariant (known : List Nat) (parents : Nat → List Nat) (fuel : Nat) (state : Worklist)
    (invariant : Invariant known parents state) (unique : known.Nodup)
    (uniqueParents : ∀ child ∈ known, (parents child).Nodup) :
    Invariant known parents (runFuel known fuel state) := by
  induction fuel generalizing state with
  | zero => exact invariant
  | succ fuel ih =>
    simp only [runFuel]
    cases found : known.find? state.ready with
    | none => exact invariant
    | some parent =>
      exact ih (pop state parent) (pop_invariant known parents state parent invariant unique uniqueParents
        (List.mem_of_find?_eq_some found) (List.find?_some found))

theorem native_counters_invariant (known : List Nat) (parents : Nat → List Nat)
    (unique : known.Nodup) (uniqueParents : ∀ child ∈ known, (parents child).Nodup) :
    Invariant known parents (runFuel known known.length (initWorklist known parents)) :=
  runFuel_invariant known parents known.length (initWorklist known parents) (initialize_invariant known parents) unique uniqueParents


/-- No further eligible worklist step remains. -/
def Saturated (known : List Nat) (state : Worklist) : Prop :=
  ∀ child ∈ known, state.ready child = false

theorem runFuel_saturated (known : List Nat) (parents : Nat → List Nat) (fuel : Nat) (state : Worklist)
    (invariant : Invariant known parents state) (unique : known.Nodup)
    (uniqueParents : ∀ child ∈ known, (parents child).Nodup)
    (processedUnique : state.processed.Nodup) (inside : state.processed ⊆ known)
    (enough : known.length ≤ fuel + state.processed.length) : Saturated known (runFuel known fuel state) := by
  induction fuel generalizing state with
  | zero =>
    intro child member
    change state.ready child = false
    cases selected : state.ready child with
    | false => rfl
    | true =>
      have fresh := ((invariant.readiness child member).mp selected).1
      have enlarged : (child :: state.processed).Nodup := List.nodup_cons.mpr ⟨fresh,processedUnique⟩
      have bounded := (List.subperm_of_subset enlarged (by intro node hn; rcases List.mem_cons.mp hn with rfl | old; exact member; exact inside old)).length_le
      simp only [List.length_cons] at bounded
      omega
  | succ fuel ih =>
    simp only [runFuel]
    cases found : known.find? state.ready with
    | none =>
      intro child member
      change state.ready child = false
      cases selected : state.ready child with
      | false => rfl
      | true => exact False.elim (List.find?_eq_none.mp found child member selected)
    | some parent =>
      have accepted := List.mem_of_find?_eq_some found
      have selected := List.find?_some found
      have fresh := ((invariant.readiness parent accepted).mp selected).1
      apply ih (pop state parent) (pop_invariant known parents state parent invariant unique uniqueParents accepted selected)
      · exact List.nodup_cons.mpr ⟨fresh,processedUnique⟩
      · intro child member
        rcases List.mem_cons.mp member with rfl | old
        · exact accepted
        · exact inside old
      · change known.length ≤ fuel + (parent :: state.processed).length
        simp only [List.length_cons]
        omega

theorem native_saturated (known : List Nat) (parents : Nat → List Nat)
    (unique : known.Nodup) (uniqueParents : ∀ child ∈ known, (parents child).Nodup) :
    Saturated known (runFuel known known.length (initWorklist known parents)) :=
  runFuel_saturated known parents known.length (initWorklist known parents) (initialize_invariant known parents)
    unique uniqueParents (by simp [initWorklist]) (by intro _ h; contradiction) (by simp [initWorklist])

theorem saturated_processes_ready (known : List Nat) (parents : Nat → List Nat) (state : Worklist)
    (invariant : Invariant known parents state) (saturated : Saturated known state) :
    ∀ child ∈ known, (∀ parent ∈ parents child, parent ∈ state.processed) → child ∈ state.processed := by
  intro child member released
  by_cases present : child ∈ state.processed
  · exact present
  · have zero := (zero_count_ready (parents child) state.processed).mpr released
    have count : state.counts child = 0 := (invariant.counters child member).trans zero
    have ready := (invariant.readiness child member).mpr ⟨present,count⟩
    rw [saturated child member] at ready
    contradiction

/-- Actual executable mutable counters cannot hide a dependency-closed
component behind an unrelated missing external reference. -/
theorem native_closed_component_processed (known component : List Nat) (parents : Nat → List Nat)
    (unique : known.Nodup) (uniqueParents : ∀ child ∈ known, (parents child).Nodup)
    (structural : StateResourceKahn.nativeKahn parents known = []) (inside : component ⊆ known)
    (closed : ∀ child ∈ component, ∀ parent ∈ parents child, parent ∈ component) :
    component ⊆ (runFuel known known.length (initWorklist known parents)).processed :=
  StateResourceKahn.native_closed_component_processed parents known component _ unique structural inside closed
    (saturated_processes_ready known parents _ (native_counters_invariant known parents unique uniqueParents)
      (native_saturated known parents unique uniqueParents))


/-- Releasing an absent external reference updates the full structural queue
without requiring or constructing a resource summary for that identity. -/
theorem release_missing_invariant (known : List Nat) (parents : Nat → List Nat) (state : Worklist) (parent : Nat)
    (invariant : Invariant known parents state) (unique : known.Nodup)
    (uniqueParents : ∀ child ∈ known, (parents child).Nodup)
    (noOutgoing : parents parent = []) (fresh : parent ∉ state.processed) :
    Invariant known parents (pop state parent) := by
  have children := invariant.waiting parent
  constructor
  · simpa [pop,children] using waiting_pop_refinement known parents state.processed state.counts parent unique uniqueParents fresh invariant.counters
  · intro address
    simp only [pop]
    rw [invariant.waiting address,waiting_after_pop]
  · simpa [pop,children] using ready_pop_refinement known parents state.processed state.counts state.ready parent unique fresh invariant.closed invariant.counters invariant.readiness
  · intro child member dependency edge
    rcases List.mem_cons.mp member with same | old
    · subst child
      rw [noOutgoing] at edge
      contradiction
    · exact List.mem_cons_of_mem parent (invariant.closed child old dependency edge)

end CBCL.StateResourceCounters
