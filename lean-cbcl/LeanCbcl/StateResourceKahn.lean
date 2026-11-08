import LeanCbcl.StateResourceSummary

/-! Native structural Kahn pass. External missing references are released by
that pass; the graph below contains exactly the known resource operations.
The proof is schedule-independent and therefore also applies after the budget
pass has already removed some dependency-closed components. -/
namespace CBCL.StateResourceKahn

inductive Reach {α : Type} (parents : α → List α) (nodes : List α) : α → α → Prop where
  | edge {a b} : a ∈ nodes → b ∈ nodes → b ∈ parents a → Reach parents nodes a b
  | cons {a b c} : a ∈ nodes → b ∈ parents a → Reach parents nodes b c → Reach parents nodes a c

def HasCycle {α : Type} (parents : α → List α) (nodes : List α) : Prop :=
  ∃ node, Reach parents nodes node node

theorem Reach.source {α : Type} {parents : α → List α} {nodes : List α} {a b : α}
    (path : Reach parents nodes a b) : a ∈ nodes := by cases path <;> assumption

theorem Reach.target {α : Type} {parents : α → List α} {nodes : List α} {a b : α}
    (path : Reach parents nodes a b) : b ∈ nodes := by
  induction path with
  | edge _ target _ => exact target
  | cons _ _ _ ih => exact ih

theorem Reach.trans {α : Type} {parents : α → List α} {nodes : List α} {a b c : α}
    (left : Reach parents nodes a b) (right : Reach parents nodes b c) : Reach parents nodes a c := by
  induction left with
  | edge source _ link => exact .cons source link right
  | cons source link _ ih => exact .cons source link (ih right)

theorem Reach.mono {α : Type} {parents : α → List α} {A B : List α}
    (inside : A ⊆ B) {a b : α} (path : Reach parents A a b) : Reach parents B a b := by
  induction path with
  | edge ha hb link => exact .edge (inside ha) (inside hb) link
  | cons ha link _ ih => exact .cons (inside ha) link ih

def walk {α : Type} (next : α → α) : α → Nat → List α
  | node, 0 => [node]
  | node, n+1 => node :: walk next (next node) n

theorem walk_length {α : Type} (next : α → α) (node : α) (n : Nat) :
    (walk next node n).length = n+1 := by
  induction n generalizing node with
  | zero => rfl
  | succ n ih => simp [walk,ih]

theorem walk_inside {α : Type} {next : α → α} {nodes : List α}
    (closed : ∀ node ∈ nodes, next node ∈ nodes) {start : α} (inside : start ∈ nodes) (n : Nat) :
    walk next start n ⊆ nodes := by
  induction n generalizing start with
  | zero => simpa [walk] using inside
  | succ n ih =>
    intro node member
    rcases List.mem_cons.mp member with same | later
    · simpa [same] using inside
    · exact ih (closed start inside) later

theorem walk_reaches {α : Type} {next : α → α} {parents : α → List α} {nodes : List α}
    (closed : ∀ node ∈ nodes, next node ∈ nodes)
    (edge : ∀ node ∈ nodes, next node ∈ parents node)
    {start : α} (inside : start ∈ nodes) (n : Nat) {node : α} (member : node ∈ walk next start n) :
    node = start ∨ Reach parents nodes start node := by
  induction n generalizing start with
  | zero => exact Or.inl (by simpa [walk] using member)
  | succ n ih =>
    rcases List.mem_cons.mp member with same | later
    · exact Or.inl same
    · have first : Reach parents nodes start (next start) := .edge inside (closed start inside) (edge start inside)
      rcases ih (closed start inside) later with same | path
      · exact Or.inr (same ▸ first)
      · exact Or.inr (first.trans path)

theorem walk_nodup_without_cycles {α : Type} {next : α → α} {parents : α → List α} {nodes : List α}
    (closed : ∀ node ∈ nodes, next node ∈ nodes)
    (edge : ∀ node ∈ nodes, next node ∈ parents node)
    (acyclic : ¬HasCycle parents nodes) {start : α} (inside : start ∈ nodes) (n : Nat) :
    (walk next start n).Nodup := by
  induction n generalizing start with
  | zero => simp [walk]
  | succ n ih =>
    refine List.nodup_cons.mpr ⟨?_,ih (closed start inside)⟩
    intro repeated
    have first : Reach parents nodes start (next start) := .edge inside (closed start inside) (edge start inside)
    rcases walk_reaches closed edge (closed start inside) n repeated with same | path
    · exact acyclic ⟨start,by simpa only [← same] using first⟩
    · exact acyclic ⟨start,first.trans path⟩

/-- A finite nonempty graph in which every node has a parent contains a cycle.
The proof constructs a walk too long to be a duplicate-free subset. -/
theorem closed_parent_cycle {α : Type} [DecidableEq α] {parents : α → List α} {nodes : List α}
    (nonempty : nodes ≠ []) (blocked : ∀ node ∈ nodes, ∃ parent ∈ nodes, parent ∈ parents node) :
    HasCycle parents nodes := by
  classical
  by_cases cycle : HasCycle parents nodes
  · exact cycle
  · let next : α → α := fun node => if h : node ∈ nodes then Classical.choose (blocked node h) else node
    have closed : ∀ node ∈ nodes, next node ∈ nodes := by
      intro node member
      simpa [next,member] using (Classical.choose_spec (blocked node member)).1
    have edge : ∀ node ∈ nodes, next node ∈ parents node := by
      intro node member
      simpa [next,member] using (Classical.choose_spec (blocked node member)).2
    cases nodes with
    | nil => contradiction
    | cons start rest =>
      have inside : start ∈ start :: rest := by simp
      have unique := walk_nodup_without_cycles closed edge cycle inside (start :: rest).length
      have subset := walk_inside closed inside (start :: rest).length
      obtain ⟨chosen,perm,sub⟩ := List.subperm_of_subset unique subset
      have lengths := perm.length_eq
      have bounded := sub.length_le
      have long := walk_length next start (start :: rest).length
      omega

def Ready {α : Type} (parents : α → List α) (remaining : List α) (node : α) : Prop :=
  node ∈ remaining ∧ ∀ parent ∈ remaining, parent ∉ parents node

def Saturated {α : Type} (parents : α → List α) (remaining : List α) : Prop :=
  ∀ node, ¬Ready parents remaining node

theorem ready_cannot_reach {α : Type} {parents : α → List α} {remaining : List α} {a b : α}
    (ready : Ready parents remaining a) : ¬Reach parents remaining a b := by
  intro path
  cases path with
  | edge _ hb link => exact ready.2 _ hb link
  | cons _ link rest => exact ready.2 _ rest.source link

theorem reach_erase_ready {α : Type} [DecidableEq α] {parents : α → List α} {remaining : List α}
    {removed a b : α} (ready : Ready parents remaining removed)
    (differentA : a ≠ removed) (differentB : b ≠ removed)
    (path : Reach parents remaining a b) : Reach parents (remaining.erase removed) a b := by
  induction path with
  | edge ha hb link =>
    exact .edge ((List.mem_erase_of_ne differentA).mpr ha) ((List.mem_erase_of_ne differentB).mpr hb) link
  | @cons a parent b ha link rest ih =>
    have different : parent ≠ removed := by
      intro same
      subst parent
      exact ready_cannot_reach ready rest
    exact .cons ((List.mem_erase_of_ne differentA).mpr ha) link (ih different differentB)

theorem cycle_erase_ready {α : Type} [DecidableEq α] {parents : α → List α} {remaining : List α}
    {removed : α} (ready : Ready parents remaining removed) :
    HasCycle parents (remaining.erase removed) ↔ HasCycle parents remaining := by
  constructor
  · rintro ⟨node,path⟩
    exact ⟨node,path.mono List.erase_subset⟩
  · rintro ⟨node,path⟩
    have different : node ≠ removed := by
      intro same
      subst node
      exact ready_cannot_reach ready path
    exact ⟨node,reach_erase_ready ready different different path⟩

inductive RemovalTrace {α : Type} [DecidableEq α] (parents : α → List α) : List α → List α → Prop where
  | start (nodes) : RemovalTrace parents nodes nodes
  | remove {initial remaining node} : RemovalTrace parents initial remaining → Ready parents remaining node →
      RemovalTrace parents initial (remaining.erase node)

theorem RemovalTrace.cycle_iff {α : Type} [DecidableEq α] {parents : α → List α} {initial remaining : List α}
    (trace : RemovalTrace parents initial remaining) : HasCycle parents remaining ↔ HasCycle parents initial := by
  induction trace with
  | start => rfl
  | remove _ ready ih => exact (cycle_erase_ready ready).trans ih

theorem saturated_cycle_iff_nonempty {α : Type} [DecidableEq α] {parents : α → List α} {remaining : List α}
    (saturated : Saturated parents remaining) : HasCycle parents remaining ↔ remaining ≠ [] := by
  constructor
  · rintro ⟨node,path⟩ empty
    simpa [empty] using path.source
  · intro nonempty
    apply closed_parent_cycle nonempty
    intro node member
    by_cases blocked : ∃ parent ∈ remaining, parent ∈ parents node
    · exact blocked
    · exact False.elim (saturated node ⟨member,fun p hp edge => blocked ⟨p,hp,edge⟩⟩)

/-- Top-level classification of the native structural pass: its remaining
nonempty test is precisely a cycle witness in the original known graph. -/
theorem native_kahn_cycle_iff {α : Type} [DecidableEq α] {parents : α → List α} {initial remaining : List α}
    (trace : RemovalTrace parents initial remaining) (saturated : Saturated parents remaining) :
    remaining ≠ [] ↔ HasCycle parents initial :=
  (saturated_cycle_iff_nonempty saturated).symm.trans trace.cycle_iff

def readyCheck {α : Type} [DecidableEq α] (parents : α → List α)
    (remaining : List α) (node : α) : Bool :=
  (parents node).all (fun parent => !remaining.contains parent)

theorem readyCheck_iff {α : Type} [DecidableEq α] (parents : α → List α)
    (remaining : List α) (node : α) : readyCheck parents remaining node = true ↔
      ∀ parent ∈ remaining, parent ∉ parents node := by
  simp only [readyCheck,List.all_eq_true,Bool.not_eq_true',List.contains_eq_mem,decide_eq_false_iff_not]
  constructor
  · intro noParent parent inside link
    exact noParent parent link inside
  · intro noParent parent link inside
    exact noParent parent inside link

def reduceFuel {α : Type} [DecidableEq α] (parents : α → List α) : Nat → List α → List α
  | 0, remaining => remaining
  | fuel+1, remaining => match remaining.find? (readyCheck parents remaining) with
    | none => remaining
    | some node => reduceFuel parents fuel (remaining.erase node)

theorem RemovalTrace.trans {α : Type} [DecidableEq α] {parents : α → List α} {A B C : List α}
    (left : RemovalTrace parents A B) (right : RemovalTrace parents B C) : RemovalTrace parents A C := by
  induction right with
  | start => exact left
  | remove _ ready ih => exact .remove ih ready

theorem reduce_trace {α : Type} [DecidableEq α] (parents : α → List α) (fuel : Nat) (nodes : List α) :
    RemovalTrace parents nodes (reduceFuel parents fuel nodes) := by
  induction fuel generalizing nodes with
  | zero => exact .start nodes
  | succ fuel ih =>
    simp only [reduceFuel]
    cases found : nodes.find? (readyCheck parents nodes) with
    | none => exact .start nodes
    | some node =>
      have member := List.mem_of_find?_eq_some found
      have ready := (readyCheck_iff parents nodes node).mp (List.find?_some found)
      exact (RemovalTrace.remove (.start nodes) ⟨member,ready⟩).trans (ih (nodes.erase node))

theorem reduce_saturated {α : Type} [DecidableEq α] (parents : α → List α) (fuel : Nat) (nodes : List α)
    (enough : nodes.length ≤ fuel) : Saturated parents (reduceFuel parents fuel nodes) := by
  induction fuel generalizing nodes with
  | zero =>
    cases nodes with
    | nil => simp [reduceFuel,Saturated,Ready]
    | cons _ _ => simp at enough
  | succ fuel ih =>
    simp only [reduceFuel]
    cases found : nodes.find? (readyCheck parents nodes) with
    | none =>
      intro node ready
      exact List.find?_eq_none.mp found node ready.1 ((readyCheck_iff parents nodes node).mpr ready.2)
    | some node =>
      have size := List.length_erase_of_mem (List.mem_of_find?_eq_some found)
      exact ih (nodes.erase node) (by omega)

/-- Executable native structural cycle classification, with the graph's own
finite bound rather than an assumed completed/saturated worklist. -/
def nativeKahn {α : Type} [DecidableEq α] (parents : α → List α) (nodes : List α) : List α :=
  reduceFuel parents nodes.length nodes

theorem nativeKahn_cycle_iff {α : Type} [DecidableEq α] (parents : α → List α) (nodes : List α) :
    nativeKahn parents nodes ≠ [] ↔ HasCycle parents nodes :=
  native_kahn_cycle_iff (reduce_trace parents nodes.length nodes)
    (reduce_saturated parents nodes.length nodes (Nat.le_refl _))

/-- Any dependency-closed ranked component has been processed at a saturated
budget pass. Missing references in a different component cannot suppress it. -/
theorem closed_component_processed {α : Type} {parents : α → List α} {nodes component processed : List α}
    (inside : component ⊆ nodes) (rank : α → Nat)
    (closed : ∀ node ∈ component, ∀ parent ∈ parents node, parent ∈ component)
    (lower : ∀ node ∈ component, ∀ parent ∈ parents node, rank parent < rank node)
    (saturated : ∀ node ∈ nodes, (∀ parent ∈ parents node, parent ∈ processed) → node ∈ processed) :
    component ⊆ processed := by
  intro node member
  have all : ∀ height, ∀ node ∈ component, rank node = height → node ∈ processed := by
    intro height
    induction height using Nat.strongRecOn with
    | ind height ih =>
      intro current hc equal
      apply saturated current (inside hc)
      intro parent edge
      exact ih (rank parent) (by simpa [equal] using lower current hc parent edge)
        parent (closed current hc parent edge) rfl
  exact all (rank node) node member rfl

def removalOrder {α : Type} [DecidableEq α] (parents : α → List α) : Nat → List α → List α
  | 0, _ => []
  | fuel+1, remaining => match remaining.find? (readyCheck parents remaining) with
    | none => []
    | some node => node :: removalOrder parents fuel (remaining.erase node)

theorem order_partition {α : Type} [DecidableEq α] (parents : α → List α) (fuel : Nat) (nodes : List α) :
    nodes.Perm (removalOrder parents fuel nodes ++ reduceFuel parents fuel nodes) := by
  induction fuel generalizing nodes with
  | zero => exact List.Perm.refl _
  | succ fuel ih =>
    simp only [removalOrder,reduceFuel]
    cases found : nodes.find? (readyCheck parents nodes) with
    | none => exact List.Perm.refl _
    | some node =>
      exact (List.perm_cons_erase (List.mem_of_find?_eq_some found)).trans ((ih (nodes.erase node)).cons node)

def Topological {α : Type} (parents : α → List α) : List α → Prop
  | [] => True
  | node :: rest => (∀ parent ∈ node :: rest, parent ∉ parents node) ∧ Topological parents rest

theorem removalOrder_topological {α : Type} [DecidableEq α] (parents : α → List α) (fuel : Nat) (nodes : List α) :
    Topological parents (removalOrder parents fuel nodes) := by
  induction fuel generalizing nodes with
  | zero => trivial
  | succ fuel ih =>
    simp only [removalOrder]
    cases found : nodes.find? (readyCheck parents nodes) with
    | none => trivial
    | some node =>
      have ready := (readyCheck_iff parents nodes node).mp (List.find?_some found)
      refine ⟨?_,ih (nodes.erase node)⟩
      intro parent member
      apply ready parent
      rcases List.mem_cons.mp member with same | tail
      · simpa [same] using List.mem_of_find?_eq_some found
      · have inPartition := (order_partition parents fuel (nodes.erase node)).mem_iff.mpr
          (List.mem_append_left _ tail)
        exact List.erase_subset inPartition

theorem topological_rank {α : Type} [DecidableEq α] {parents : α → List α} {order : List α}
    (unique : order.Nodup) (topological : Topological parents order) :
    ∀ child ∈ order, ∀ parent ∈ order, parent ∈ parents child → order.idxOf parent < order.idxOf child := by
  induction order with
  | nil => simp
  | cons head rest ih =>
    intro child hc parent hp edge
    have hu := List.nodup_cons.mp unique
    rcases List.mem_cons.mp hc with same | childInside
    · subst child
      exact False.elim (topological.1 parent hp edge)
    · have childNe : head ≠ child := by intro same; subst child; exact hu.1 childInside
      rcases List.mem_cons.mp hp with same | parentInside
      · subst parent
        simp [List.idxOf_cons,beq_eq_false_iff_ne.mpr childNe]
      · have parentNe : head ≠ parent := by intro same; subst parent; exact hu.1 parentInside
        simpa [List.idxOf_cons,beq_eq_false_iff_ne.mpr childNe,beq_eq_false_iff_ne.mpr parentNe] using ih hu.2 topological.2 child childInside parent parentInside edge

/-- A successful executable structural pass supplies its own dependency rank;
no acyclicity/topological-order oracle is accepted from the caller. -/
theorem nativeKahn_rank {α : Type} [DecidableEq α] (parents : α → List α) (nodes : List α)
    (unique : nodes.Nodup) (success : nativeKahn parents nodes = []) :
    ∃ rank : α → Nat, ∀ child ∈ nodes, ∀ parent ∈ nodes, parent ∈ parents child → rank parent < rank child := by
  have permutation := order_partition parents nodes.length nodes
  change reduceFuel parents nodes.length nodes = [] at success
  rw [success,List.append_nil] at permutation
  refine ⟨fun node => (removalOrder parents nodes.length nodes).idxOf node,?_⟩
  intro child hc parent hp edge
  exact topological_rank (permutation.nodup unique) (removalOrder_topological parents nodes.length nodes)
    child (permutation.mem_iff.mp hc) parent (permutation.mem_iff.mp hp) edge

/-- The budget-pass saturation premise checks ALL escrow references, including
missing external ones. Closure of this component discharges those references;
a structural pass that releases unrelated missing references supplies the rank. -/
theorem native_closed_component_processed {α : Type} [DecidableEq α] (parents : α → List α)
    (nodes component processed : List α) (unique : nodes.Nodup)
    (structural : nativeKahn parents nodes = []) (inside : component ⊆ nodes)
    (closed : ∀ node ∈ component, ∀ parent ∈ parents node, parent ∈ component)
    (budgetSaturated : ∀ node ∈ nodes, (∀ parent ∈ parents node, parent ∈ processed) → node ∈ processed) :
    component ⊆ processed := by
  obtain ⟨rank,lower⟩ := nativeKahn_rank parents nodes unique structural
  exact closed_component_processed inside rank closed
    (fun node hn parent edge => lower node (inside hn) parent (inside (closed node hn parent edge)) edge)
    budgetSaturated

/-- First-pass readiness keeps unknown external references blocked. The
initializer reference has already been removed from the parent list, exactly
as in the native dependency counters. -/
def budgetReadyCheck {α : Type} [DecidableEq α] (parents : α → List α)
    (known remaining : List α) (node : α) : Bool :=
  (parents node).all (fun parent => known.contains parent && !remaining.contains parent)

def budgetReduceFuel {α : Type} [DecidableEq α] (parents : α → List α) (known : List α) : Nat → List α → List α
  | 0, remaining => remaining
  | fuel+1, remaining => match remaining.find? (budgetReadyCheck parents known remaining) with
    | none => remaining
    | some node => budgetReduceFuel parents known fuel (remaining.erase node)

def BudgetSaturated {α : Type} [DecidableEq α] (parents : α → List α) (known remaining : List α) : Prop :=
  ∀ node ∈ remaining, budgetReadyCheck parents known remaining node = false

theorem budget_reduce_saturated {α : Type} [DecidableEq α] (parents : α → List α) (known : List α)
    (fuel : Nat) (remaining : List α) (enough : remaining.length ≤ fuel) :
    BudgetSaturated parents known (budgetReduceFuel parents known fuel remaining) := by
  induction fuel generalizing remaining with
  | zero =>
    cases remaining with
    | nil => simp [budgetReduceFuel,BudgetSaturated]
    | cons _ _ => simp at enough
  | succ fuel ih =>
    simp only [budgetReduceFuel]
    cases found : remaining.find? (budgetReadyCheck parents known remaining) with
    | none =>
      intro node member
      cases check : budgetReadyCheck parents known remaining node with
      | false => rfl
      | true => exact False.elim (List.find?_eq_none.mp found node member check)
    | some node =>
      have length := List.length_erase_of_mem (List.mem_of_find?_eq_some found)
      exact ih (remaining.erase node) (by omega)

def nativeBudgetRemaining {α : Type} [DecidableEq α] (parents : α → List α) (known : List α) : List α :=
  budgetReduceFuel parents known known.length known

def nativeBudgetProcessed {α : Type} [DecidableEq α] (parents : α → List α) (known : List α) : List α :=
  known.filter (fun node => !(nativeBudgetRemaining parents known).contains node)

theorem native_budget_saturation {α : Type} [DecidableEq α] (parents : α → List α) (known : List α) :
    ∀ node ∈ known, (∀ parent ∈ parents node, parent ∈ nativeBudgetProcessed parents known) →
      node ∈ nativeBudgetProcessed parents known := by
  intro node member allParents
  by_cases remaining : node ∈ nativeBudgetRemaining parents known
  · have ready : budgetReadyCheck parents known (nativeBudgetRemaining parents known) node = true := by
      apply List.all_eq_true.mpr
      intro parent edge
      have processed := List.mem_filter.mp (allParents parent edge)
      simp only [Bool.and_eq_true,List.contains_iff]
      exact ⟨processed.1,processed.2⟩
    have saturated := budget_reduce_saturated parents known known.length known (Nat.le_refl _)
    have noReady := saturated node remaining
    change budgetReadyCheck parents known (nativeBudgetRemaining parents known) node = false at noReady
    rw [ready] at noReady
    contradiction
  · simp [nativeBudgetProcessed,remaining]
    exact member

/-- Executable first pass plus executable structural pass: a closed component
is processed even while an unrelated component waits for absent references.
No caller-supplied saturation or dependency-rank premise remains. -/
theorem native_no_hidden_closed_component {α : Type} [DecidableEq α] (parents : α → List α)
    (known component : List α) (unique : known.Nodup) (acyclic : nativeKahn parents known = [])
    (inside : component ⊆ known)
    (closed : ∀ node ∈ component, ∀ parent ∈ parents node, parent ∈ component) :
    component ⊆ nativeBudgetProcessed parents known :=
  native_closed_component_processed parents known component (nativeBudgetProcessed parents known)
    unique acyclic inside closed (native_budget_saturation parents known)

end CBCL.StateResourceKahn
