import LeanCbcl.StateInstalledCompiler

/-! A factored native term retains one current-state operation. Its ordinary
source display and raw threshold reads are both generated from that operation;
freezing decorates the display without replacing current-carrier reads. Guards
are a closed data-preserving inventory, not a second display callback. -/
namespace CBCL.StateInstalledTerm
open State StateLift StateLVar StateObservation StateObservationPlan StateInstalledCompiler

/-- A data-preserving terminal-error guard on an installed source. -/
inductive Guard where
  | certified (spec : ErrorSpec)
  | domain (opener field : String)
  | resource (config : CheckpointEvidence.ResourceConfig) (decode : Act → CheckpointEvidence.ResourceData)
  | threshold (spec : ThresholdSpec)

/-- Attach this error guard to an installed source. -/
def Guard.apply {V : Type} : Guard → Source V → Source V
  | .certified spec, source => .guardCertified spec source
  | .domain opener field, source => .guardDomain opener field source
  | .resource config decode, source => .resource config decode source
  | .threshold spec, source => .guardThreshold spec source

/-- An executable raw-carrier read test and installed-alternative check. -/
structure Policy (V C : Type) where
  /-- Test one alternative against the current raw carrier. -/
  test : V → C → Bool
  /-- Check whether the installed alternative list is admissible. -/
  check : List V → Bool

/-- A source factored through a retained carrier with bottom and merge laws. -/
structure Term (V : Type) where
  /-- The lattice carrier used by this source. -/
  Carrier : Type
  /-- The retained carrier computed from the accepted-act set. -/
  state : FinSet Act → Carrier
  /-- Render the retained carrier as the displayed value. -/
  project : Carrier → V
  /-- The independently proved terminal-error guards for the source. -/
  guards : List Guard
  /-- The join and bottom operations, with their lattice laws. -/
  algebra : JoinSemilatticeBot Carrier
  state_bottom : letI := algebra; state ⊥ = ⊥
  state_merge : letI := algebra; ∀ left right, state (left ⊔ right) = state left ⊔ state right

/-- Construct the guarded observation source from retained source metadata. -/
def source {V : Type} (term : Term V) : Source V :=
  term.guards.foldr Guard.apply (.snapshot (fun carrier => term.project (term.state carrier)))

theorem guard_data {V : Type} (world : Act → Prop) (guard : Guard) (source : Source V) (A : List Act) :
    data world (sourcePlan (guard.apply source)) A = data world (sourcePlan source) A := by
  cases guard <;> rfl

/-- Current display and raw-query state cannot diverge at the source factory. -/
theorem source_state_coherence {V : Type} (world : Act → Prop) (term : Term V) (A : List Act) :
    data world (sourcePlan (source term)) A = .snapshot (term.project (term.state (rawHistory A))) := by
  obtain ⟨Carrier,state,project,guards,_,_,_⟩ := term
  induction guards with
  | nil => rfl
  | cons guard rest ih =>
    change data world (sourcePlan (guard.apply (rest.foldr Guard.apply (.snapshot (fun carrier => project (state carrier)))))) A = _
    rw [guard_data]
    exact ih

/-- Native terms preserve raw-history joins; snapshot projections are allowed
to revise and are deliberately outside this algebraic obligation. -/
theorem accepted_history_merge {V : Type} (term : Term V) (A B : List Act) :
    letI := term.algebra
    term.state (rawHistory (A++B)) = term.state (rawHistory A) ⊔ term.state (rawHistory B) := by
  letI := term.algebra
  rw [rawHistory_union,term.state_merge]

end CBCL.StateInstalledTerm
