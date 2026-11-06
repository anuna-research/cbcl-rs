import Init.Data.List.Nat.Range
import LeanCbcl.StateKernelDelivery

/-! SPEC-037 nonvacuity and starvation checks using a real two-act dependency chain. -/
namespace CBCL.StateKernelSECTests
open CBCL.State CBCL.AdmissionStratification CBCL.StateRefinement
open CBCL.StateRefinement.Examples CBCL.StateKernelDelivery

/-- The finite valid history is an increment followed by a dependent decrement. -/
def history : ValidHistory admission where
  contains a := a = inc7 ∨ a = dec3
  dependencies a := if a = dec3 then [inc7] else []
  rank a := if a = dec3 then 1 else 0
  closed := by
    intro a valid b member
    split at member
    · simp only [List.mem_singleton] at member; subst b; exact Or.inl rfl
    · simp at member
  lower := by
    intro a valid b member
    split at member
    · simp only [List.mem_singleton] at member; subst b
      simp_all [inc7, dec3]
    · simp at member
  no_reject := by
    intro A sub a valid
    change (if a.preds.all (fun p => (A.map skel).any (fun b => b.addr == p))
      then Verdict.accepted else Verdict.pending) ≠ .rejected
    split <;> decide
  enabled := by
    intro A sub a valid deps
    rcases valid with rfl | rfl
    · simp [Admission.admit, admission, inc7]
    · have parent : inc7 ∈ A := deps inc7 (by simp [inc7, dec3])
      have witnessed : (A.map skel).any (fun b => b.addr == 10) = true := by
        apply List.any_eq_true.mpr
        exact ⟨skel inc7, List.mem_map.mpr ⟨inc7, parent, rfl⟩, by decide⟩
      simp only [Admission.admit, admission, dec3]
      simp only [List.all_cons, List.all_nil, Bool.and_true]
      rw [witnessed]
      rfl

/-- Child-before-parent delivery then scheduled acceptance of parent and child. -/
def run : Nat → Execution
  | 0 => initial
  | 1 => childReceived
  | 2 => bothReceived
  | 3 => parentAccepted
  | _ => bothAccepted
/-- The two acceptance transitions are actual labels, all other steps are silent. -/
def events : Nat → Option Act
  | 2 => some inc7
  | 3 => some dec3
  | _ => none

theorem run_behavior : Behavior admission (fun _ => True) run events := by
  refine ⟨rfl, ?_⟩
  intro n
  cases n with
  | zero => exact receive_child
  | succ n => cases n with
    | zero => exact receive_parent
    | succ n => cases n with
      | zero => exact accept_parent
      | succ n => cases n with
        | zero => exact accept_child
        | succ n => exact .idle bothAccepted

/-- This fully instantiated fair replica demonstrates consistency of all premises. -/
def replica : Replica admission (fun _ => True) history where
  run := run
  events := events
  behavior := run_behavior
  valid_receipts := by
    intro n a member
    cases n with
    | zero => simp [run, initial] at member
    | succ n => cases n with
      | zero => simp [run, childReceived, initial] at member; exact Or.inr member
      | succ n =>
          have bodies : (run (n + 2)).received = [inc7, dec3] := by
            cases n with
            | zero => rfl
            | succ n => cases n <;> rfl
          rw [bodies] at member
          simpa [history] using member
  delivery := by
    intro a valid
    exact ⟨2, by simpa [run, bothReceived, childReceived, history] using valid⟩
  fair := by
    intro a t enabled
    have pending := (enabled (max t 4) (Nat.le_max_left _ _)).1
    have completed : run (max t 4) = bothAccepted := by
      have lower : 4 ≤ max t 4 := Nat.le_max_right _ _
      match h : max t 4 with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    rw [completed] at pending
    simp [bothAccepted] at pending

/-- The general liveness theorem applies to the dependent child, not only roots. -/
theorem child_eventually_accepted : ∃ t, ∀ n, t ≤ n → dec3 ∈ (replica.run n).accepted :=
  eventual_acceptance replica dec3 (Or.inr rfl)

/-- An otherwise legal infinite execution can starve both received acts. -/
def starved : Nat → Execution
  | 0 => initial
  | 1 => childReceived
  | _ => bothReceived

theorem starved_behavior : Behavior admission (fun _ => True) starved (fun _ => none) := by
  refine ⟨rfl, ?_⟩
  intro n
  cases n with
  | zero => exact receive_child
  | succ n => cases n with
    | zero => exact receive_parent
    | succ n => exact .idle bothReceived

theorem starved_no_acceptance (n : Nat) : (starved n).accepted = [] := by
  cases n with
  | zero => rfl
  | succ n => cases n <;> rfl

/-- This starving execution violates transition fairness despite delivering both acts. -/
theorem starved_not_fair : ¬ (∀ a t,
    (∀ n, t ≤ n → a ∈ (starved n).pending ∧ admission.admit (starved n).accepted a = .accepted) →
    ∃ n, t ≤ n ∧ (none : Option Act) = some a) := by
  intro fair
  obtain ⟨n, _, impossible⟩ := fair inc7 2 (by
    intro n hn
    have complete : starved n = bothReceived := by
      cases n with
      | zero => omega
      | succ n => cases n with
        | zero => omega
        | succ n => rfl
    rw [complete]
    constructor <;> decide)
  contradiction

/-- Increasing unique-address histories model ongoing new writes. -/
def ticks (n : Nat) : List Act :=
  (List.range n).map (fun address => ⟨address, "tick", "writer", [], [], []⟩)

/-- These snapshots respect the accepted-store uniqueness invariant. -/
theorem ticks_unique (n : Nat) : NodupAddr (ticks n) := by
  simp only [NodupAddr, ticks, List.map_map, Function.comp_def ]
  change (List.map id (List.range n)).Nodup
  rw [List.map_id]
  exact List.nodup_range

/-- The kernel count can grow forever when writes do not stop. -/
theorem ticks_count (c : CBCL.StateKernelSEC.Context) (n : Nat) :
    CBCL.StateKernel.evaluate (c.input (ticks n)) [] (.count (.verb "tick")) =
      .integer (Int.ofNat n) := by
  simp [CBCL.StateKernel.evaluate, CBCL.StateKernelSEC.Context.input,
    CBCL.StateKernelSemantics.admitted, CBCL.StateKernelSemantics.select,
    acts, size, ticks, List.filter_map]
  rw [List.filter_eq_self.mpr (by simp), List.length_range]


/-- No single final count is forced for this growing sequence of valid snapshots. -/
theorem ongoing_writes_need_not_stabilize (c : CBCL.StateKernelSEC.Context) :
    ¬ (∃ t, ∀ n, t ≤ n →
      CBCL.StateKernel.evaluate (c.input (ticks n)) [] (.count (.verb "tick")) =
      CBCL.StateKernel.evaluate (c.input (ticks t)) [] (.count (.verb "tick"))) := by
  rintro ⟨t, stable⟩
  have impossible := stable (t + 1) (by omega)
  simp only [ticks_count, CBCL.StateKernel.Observation.integer.injEq] at impossible
  have equal := Int.ofNat.inj impossible
  omega

end CBCL.StateKernelSECTests
