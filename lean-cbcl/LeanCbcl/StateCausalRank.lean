import LeanCbcl.StateExecutableFreeze

/-! Causal search ranks are separate from semantic addresses. Recognition uses
an explicit topological input order without renumbering acts or HLC tie keys. -/
namespace CBCL.StateCausalRank
open State StateLift StateLVar StateExecutableFreeze

/-- A causal rank changes no act identity or address comparison. -/
def RankedBy (history : List Act) (rank : Act → Nat) : Prop :=
  ∀ child ∈ history, ∀ parent ∈ history, parent.addr ∈ child.preds → rank parent < rank child

/-- Backward search completeness depends on causal rank, not address order. -/
theorem reachable_complete_by (fuel : Nat) (history : List Act) (rank : Act → Nat)
    (ranked : RankedBy history rank) (a freezer : Act) (member : freezer ∈ history)
    (path : Ancestor (fun act => act ∈ history) a freezer) (bound : rank freezer < fuel) :
    reachable fuel history a freezer = true := by
  induction fuel generalizing freezer with
  | zero => omega
  | succ fuel ih =>
    simp only [reachable,Bool.and_eq_true,List.contains_iff_mem,Bool.or_eq_true,beq_iff_eq,List.any_eq_true]
    refine ⟨member,?_⟩
    rcases ancestor_last path with same | ⟨parent,present,edge,earlier⟩
    · exact Or.inl same
    · have lower := ranked freezer member parent present edge
      exact Or.inr ⟨parent,present,by simpa using edge,ih parent present earlier (by omega)⟩

/-- Obtain ranks from supplied history order, retaining original addresses. -/
def position (history : List Act) (act : Act) : Nat := (history.map Act.addr).idxOf act.addr

/-- Recognize whether the supplied order is topological for present edges. -/
def check (history : List Act) : Bool := history.all (fun child => history.all (fun parent =>
  !child.preds.contains parent.addr || decide (position history parent < position history child)))

/-- Recognition constructs the separate rank premise. -/
theorem check_sound (history : List Act) (checked : check history = true) :
    RankedBy history (position history) := by
  intro child childIn parent parentIn edge
  have row := List.all_eq_true.mp (List.all_eq_true.mp checked child childIn) parent parentIn
  simpa [List.contains_iff_mem,edge] using row

-- SIMPLIFY: this proof reference reuses bounded path enumeration, which can
-- revisit shared paths exponentially. It is not the NFR-3800 native cost model;
-- use memoized reachability before expanding the executable oracle profile.
/-- Finite-history fuel is independent of hash magnitude. -/
def ancestor (history : List Act) (a freezer : Act) : Bool :=
  reachable (history.length + 1) history a freezer

/-- Exact ancestry for recognized topological orders of arbitrary addresses. -/
theorem ancestor_iff (history : List Act) (checked : check history = true)
    (a freezer : Act) (member : freezer ∈ history) :
    ancestor history a freezer = true ↔ Ancestor (fun act => act ∈ history) a freezer := by
  constructor
  · exact reachable_sound _ _ _ _
  · intro path
    have bound := List.idxOf_lt_length_of_mem (List.mem_map.mpr ⟨freezer,member,rfl⟩ : freezer.addr ∈ history.map Act.addr)
    apply reachable_complete_by _ history (position history) (check_sound history checked) a freezer member path
    simp only [List.length_map] at bound
    unfold position
    omega

/-- Exact cuts preserve input order and semantic addresses. -/
def cut (history : List Act) (freezer : Act) : List Act := history.filter (fun a => ancestor history a freezer)

theorem cut_refinement (history : List Act) (checked : check history = true)
    (freezer : Act) (member : freezer ∈ history) :
    cut history freezer = causalCut (fun act => act ∈ history) history freezer := by
  classical
  apply List.filter_congr
  intro act _
  have same := ancestor_iff history checked act freezer member
  cases computed : ancestor history act freezer <;> simp_all

/-- A checked topological witness establishes causal rank for any delivery order
with the same accepted vertices. Addresses and history order are untouched. -/
theorem ranked_from_order (history order : List Act) (checked : check order = true)
    (covered : ∀ act ∈ history, act ∈ order) : StateExecutableFreeze.Ranked history := by
  refine ⟨position order,?_⟩
  intro child childIn parent parentIn edge
  exact check_sound order checked child (covered child childIn) parent (covered parent parentIn) edge

/-- A vertex is ready when no cited predecessor remains in the pending graph. -/
def ready (pending : List Act) (act : Act) : Bool :=
  act.preds.all (fun address => !(pending.any (fun parent => parent.addr == address)))

/-- Bounded Kahn witness construction; the result is checked independently.
This proof-oracle helper does not replace the native graph algorithm. -/
def orderFuel : Nat → List Act → List Act → Option (List Act)
  | 0, [], ordered => some ordered
  | 0, _::_, _ => none
  | _+1, [], ordered => some ordered
  | fuel+1, pending, ordered =>
    match pending.find? (ready pending) with
    | none => none
    | some root => orderFuel fuel (pending.filter (fun act => act != root)) (ordered ++ [root])

/-- Recognize a checked finite causal rank without imposing address ordering.
Both coverage directions and the candidate order are recognized before use. -/
def causalCheck (history : List Act) : Bool :=
  match orderFuel (history.length+1) history [] with
  | none => false
  | some order => history.all order.contains && order.all history.contains && check order

/-- A successful graph recognition constructs the actual search rank premise. -/
theorem causalCheck_sound (history : List Act) (checked : causalCheck history = true) :
    StateExecutableFreeze.Ranked history := by
  cases ordered : orderFuel (history.length+1) history [] with
  | none => simp [causalCheck,ordered] at checked
  | some order =>
    have recognized : (history.all order.contains = true ∧ order.all history.contains = true) ∧ check order = true := by
      simpa only [causalCheck,ordered,Bool.and_eq_true] using checked
    apply ranked_from_order history order recognized.2
    intro act member
    exact List.contains_iff_mem.mp (List.all_eq_true.mp recognized.1.1 act member)

/-- Descending semantic addresses still admit a valid causal order. -/
def descending : List Act := [⟨99,"open","@a",[],[],[]⟩,⟨2,"close","@a",[99],[],[]⟩]

theorem descending_check : check descending = true := by decide

theorem descending_cut : (cut descending descending[1]).map Act.addr = [99,2] := by decide

/-- The integrated checker accepts descending addresses in reverse delivery. -/
theorem descending_reverse_checked : causalCheck descending.reverse = true := by decide

/-- Integrated production scope queries preserve original descending addresses. -/
theorem descending_integrated_cut :
    (StateExecutableFreeze.cut descending.reverse descending[1]).map Act.addr = [2,99] := by decide

/-- A causal cycle is rejected instead of manufacturing a finite rank. -/
theorem cycle_rejected : causalCheck [⟨9,"open","@a",[2],[],[]⟩,⟨2,"close","@a",[9],[],[]⟩] = false := by decide

end CBCL.StateCausalRank
