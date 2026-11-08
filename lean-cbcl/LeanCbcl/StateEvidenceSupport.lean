import LeanCbcl.StateObservationPlan

/-! Accepted-act support for finite conflict evidence. These lemmas establish
provenance, not fault reproduction from witness identities without context. -/
set_option autoImplicit false
namespace CBCL.StateEvidenceSupport
open State StateLift StateLVar StateObservation

/-- Every reported identity belongs to an act in the accepted source history. -/
def Supported (A : List Act) (evidence : Evidence) : Prop :=
  ∀ id ∈ evidence, id ∈ A.map Act.addr

/-- Combining supported error channels preserves accepted provenance. -/
theorem union_supported {A : List Act} {left right : Evidence}
    (hl : Supported A left) (hr : Supported A right) : Supported A (left ∪ right) := by
  intro id member
  exact member.elim (hl id) (hr id)

/-- Optional error union cannot invent evidence outside either source channel. -/
theorem union_error_supported (A : List Act) (left right : Error)
    (hl : ∀ e, left = some e → Supported A e)
    (hr : ∀ e, right = some e → Supported A e) :
    ∀ e, unionError left right = some e → Supported A e := by
  cases left with
  | none => simpa only [unionError] using hr
  | some first =>
    cases right with
    | none => simpa only [unionError] using hl
    | some second =>
      intro e observed
      have same : first ∪ second = e := Option.some.inj observed
      subst e
      exact union_supported (hl first rfl) (hr second rfl)

/-- Sole-value carrier joins retain only identities contributed by accepted acts. -/
theorem sole_lift_supported (contribution : Act → Sole)
    (localSupport : ∀ act id, id ∈ Sole.evidence (contribution act) → id = act.addr)
    (A : List Act) : Supported A (Sole.evidence (lift contribution A)) := by
  induction A with
  | nil => simp [Supported,lift_nil,Sole.evidence,JoinSemilatticeBot.bot]
  | cons act rest ih =>
    intro id member
    rw [lift_cons,sole_evidence_join] at member
    rcases member with head | tail
    · rw [localSupport act id head]
      simp
    · exact List.mem_cons_of_mem act.addr (ih id tail)

/-- Context faults report accepted root identities, including malformed roots. -/
theorem context_read_supported (decode : Act → Option Val) (A : List Act) (e : Evidence)
    (fault : StateContext.read decode A = .fault e) : Supported A e := by
  have supports := sole_lift_supported (StateContext.contribution decode) (by
    intro act id
    unfold StateContext.contribution
    split <;> simp [Sole.evidence]) A
  have same := StateContext.fault_evidence fault
  rw [same]
  exact supports

/-- The context-to-error adapter preserves the accepted witness boundary. -/
theorem context_error_supported (decode : Act → Option Val) (A : List Act) (e : Evidence)
    (fault : contextError (StateContext.read decode A) = some e) : Supported A e := by
  cases observed : StateContext.read decode A with
  | pending | value _ => simp [observed,contextError] at fault
  | fault actual =>
    have same : actual = e := by simpa [observed,contextError] using fault
    subst e
    exact context_read_supported decode A actual observed

/-- Conflicting initializer evidence names only accepted opener acts. -/
theorem domain_error_supported (opener field : String) (A : List Act) (e : Evidence)
    (fault : domainError opener field A = some e) : Supported A e := by
  cases observed : initialCarrier opener field A with
  | bot | one _ _ => simp [domainError,observed] at fault
  | top actual =>
    have same : actual = e := by simpa [domainError,observed] using fault
    subst e
    intro id member
    have inside : id ∈ Sole.evidence (initialCarrier opener field A) := by simpa [observed,Sole.evidence] using member
    obtain ⟨act,accepted,_,identity⟩ := (opener_evidence opener field A id).mp inside
    exact List.mem_map.mpr ⟨act,accepted,identity⟩

/-- Concrete resource certificates keep only accepted contextual identities. -/
theorem resource_error_supported (config : CheckpointEvidence.ResourceConfig)
    (decode : Act → CheckpointEvidence.ResourceData) (A : List Act) (e : Evidence)
    (fault : StateResource.faultRead config decode A = some e) : Supported A e := by
  unfold StateResource.faultRead at fault
  split at fault
  · have same := Option.some.inj fault
    subst e
    intro id member
    exact StateResource.evidence_accepted config decode A member
  · contradiction

/-- Accepted support constructs an exact finite evidence realization. It does
not assume that the supplied evidence predicate already has an enumeration. -/
theorem finite_realization (A : List Act) (e : Evidence) (support : Supported A e) :
    ∃ ids : List Nat, ∀ id, id ∈ ids ↔ id ∈ e := by
  classical
  refine ⟨(A.map Act.addr).filter (fun id => decide (id ∈ e)),?_⟩
  intro id
  simp only [List.mem_filter,decide_eq_true_eq]
  exact ⟨And.right,fun member => ⟨support id member,member⟩⟩

/-- Freeze-specific witnesses are drawn from the accepted source history. -/
theorem freeze_evidence_supported (world : Act → Prop) (verb : String)
    (contributes : Act → Prop) (policy : Bool) (A : List Act) :
    Supported A (freezeEvidence world verb contributes policy A) := by
  rintro id ⟨a,b,conflict,which⟩
  have accepted := freeze_witness_accepted conflict
  rcases which with left | right
  · exact List.mem_map.mpr ⟨a,accepted.1,left.symm⟩
  · exact List.mem_map.mpr ⟨b,accepted.2,right.symm⟩

/-- Adding freeze checks preserves supported raw evidence. -/
theorem freeze_fault_supported (world : Act → Prop) (verb : String)
    (contributes : Act → Prop) (policy : Bool) (A : List Act) (raw : Error)
    (support : ∀ e, raw = some e → Supported A e) :
    ∀ e, freezeFault world verb contributes policy raw A = some e → Supported A e := by
  classical
  intro e fault
  unfold freezeFault at fault
  split at fault
  · have same := Option.some.inj fault
    subst e
    apply union_supported
    · cases raw with
      | none => simp [Supported]
      | some actual => exact support actual rfl
    · exact freeze_evidence_supported world verb contributes policy A
  · contradiction

/-- Every closed observation path preserves accepted evidence, including certified extensions with mandatory provenance proofs. -/
theorem errors_supported (world : Act → Prop) (path : Path)
    (A : List Act) :
    ∀ e, errors world path A = some e → Supported A e := by
  induction path with
  | clear => simp [errors]
  | certified spec => exact fun _ fault => spec.support fault
  | context decode => exact context_error_supported decode A
  | domain opener field => exact domain_error_supported opener field A
  | resource config decode => exact resource_error_supported config decode A
  | threshold spec =>
    intro e fault
    unfold errors thresholdError at fault
    split at fault
    · have same := Option.some.inj fault
      subst e
      rintro id ⟨act,accepted,identity⟩
      exact List.mem_map.mpr ⟨act,accepted,identity⟩
    · contradiction
  | join left right ihLeft ihRight =>
    exact union_error_supported A _ _ ihLeft ihRight
  | freeze verb contributes policy source ih =>
    exact freeze_fault_supported world verb contributes policy A _ ih

/-- Supported composed observations admit exact finite witness enumeration. -/
theorem errors_finite (world : Act → Prop) (path : Path)
    (A : List Act) (e : Evidence)
    (fault : errors world path A = some e) :
    ∃ ids : List Nat, ∀ id, id ∈ ids ↔ id ∈ e :=
  finite_realization A e (errors_supported world path A e fault)

/-- No certified guard can report an identity on an empty accepted history.
This rules out the formerly admissible constant universal-evidence guard. -/
theorem certified_empty_evidence (spec : ErrorSpec) (e : Evidence)
    (fault : spec.read [] = some e) : ∀ id, id ∉ e := by
  intro id member
  have impossible := spec.support fault id member
  simp at impossible

/-- A fault rendered by any typed observation plan has accepted support. -/
theorem observation_supported {V : Type} (world : Act → Prop)
    (plan : StateObservationPlan.Plan V) (A : List Act) (e : Evidence)
    (fault : StateObservationPlan.observe world plan A = .fault e) : Supported A e := by
  unfold StateObservationPlan.observe at fault
  cases observed : errors world (StateObservationPlan.path plan) A with
  | none => simp [observed] at fault
  | some actual =>
    have same : actual = e := by simpa [observed] using fault
    subst e
    exact errors_supported world _ A actual observed

/-- The complete typed observation, rather than only a primitive checker,
reports an exactly enumerable finite set of accepted witness identities. -/
theorem observation_finite {V : Type} (world : Act → Prop)
    (plan : StateObservationPlan.Plan V) (A : List Act) (e : Evidence)
    (fault : StateObservationPlan.observe world plan A = .fault e) :
    ∃ ids : List Nat, ∀ id, id ∈ ids ↔ id ∈ e :=
  finite_realization A e (observation_supported world plan A e fault)

end CBCL.StateEvidenceSupport
