import LeanCbcl.StateInstalledFinite
import LeanCbcl.StateContextReplay

/-! Replay of installed finite guards. Domain error certificates preserve raw
writers independently of data selection. -/
set_option autoImplicit false
namespace CBCL.StateFiniteReplay
open State StateLift StateLVar StateObservation StateWitnessReplay
open StateInstalledDomains StateInstalledFinite

/-- Both supported domain-source factories have sufficient fault certificates.
Roster domains do not observe opener metadata. -/
theorem domain_source_replays (source : DomainSource) (A B : List Act) :
    Replays (StateInstalledDomains.errorSpec source).read A B := by
  cases source with
  | initial opener field => exact domain_replays opener field A B
  | roster profile role =>
    exact StateContextReplay.context_spec_replays (StateInstalledContext.evidenceInput profile) false A B
      (by intro impossible; contradiction)

/-- Domain guard folding preserves replay for every applicable declaration. -/
theorem domain_spec_replays (field : Field) (A B : List Act) :
    Replays (domainSpec field).read A B := by
  unfold domainSpec
  generalize field.domains.filter (fun domain => domain.verb == field.verb) = domains
  induction domains with
  | nil => intro e impossible accepted; contradiction
  | cons domain rest ih =>
    exact StateContextReplay.join_replays _ _ A B (domain_source_replays domain.source A B) ih

/-- A contribution's domain value comes from a recognized support act. -/
theorem contribution_supports (source : DomainSource) (act : Act) (value : Val)
    (member : value ∈ StateInstalledDomains.contribution source act) : supports source act = true := by
  cases source with
  | initial opener field =>
    cases matching : act.verb == opener with
    | false =>
      simp only [StateInstalledDomains.contribution,matching,Bool.false_eq_true,ite_false] at member
      exact False.elim (FinSet.not_mem_bot member)
    | true => simpa [supports] using matching
  | roster profile role =>
    cases root : act.preds.isEmpty with
    | false =>
      simp only [StateInstalledDomains.contribution,root,Bool.false_eq_true,ite_false] at member
      exact False.elim (FinSet.not_mem_bot member)
    | true => simpa [supports] using root

/-- Domain-support identities themselves survive receipt of their named acts. -/
theorem domain_evidence_replays (field : Field) {A B : List Act}
    (accepted : Accepts A (domainEvidence field A) B) :
    ∀ id ∈ domainEvidence field A, id ∈ domainEvidence field B := by
  rintro id ⟨domain,declared,verb,act,inside,supporting,identity⟩
  have present := accepted act inside ⟨domain,declared,verb,act,inside,supporting,rfl⟩
  exact ⟨domain,declared,verb,act,present,supporting,identity⟩

/-- Reported domain context preserves a named writer's eligibility even when
its initializer is concurrent rather than a causal ancestor. -/
theorem selected_replays (field : Field) {A B : List Act}
    (context : Accepts A (domainEvidence field A) B)
    (act : Act) (before : act ∈ selected field A) (accepted : act ∈ B) :
    act ∈ selected field B := by
  obtain ⟨oldSelection,verb⟩ := List.mem_filter.mp before
  have sourceVerb : act.verb = field.verb := by simpa using verb
  have checked := (List.mem_filter.mp oldSelection).2
  apply List.mem_filter.mpr
  refine ⟨List.mem_filter.mpr ⟨accepted,List.all_eq_true.mpr ?_⟩,verb⟩
  intro domain declared
  have eligibleBefore := List.all_eq_true.mp checked domain declared
  by_cases matching : act.verb = domain.verb
  · cases fieldValue : act.get domain.key with
    | none => simp [eligible,matching,fieldValue] at eligibleBefore
    | some value =>
      have member : value ∈ allowed domain.source A := by
        simpa [eligible,matching,fieldValue,FinSet.contains_eq_true] using eligibleBefore
      obtain ⟨witness,inside,contributed⟩ := (mem_lift (StateInstalledDomains.contribution domain.source)).mp member
      have present := context witness inside ⟨domain,declared,matching.symm.trans sourceVerb,
        witness,inside,contribution_supports domain.source witness value contributed,rfl⟩
      have later : value ∈ allowed domain.source B :=
        (mem_lift (StateInstalledDomains.contribution domain.source)).mpr ⟨witness,present,contributed⟩
      simpa [eligible,matching,fieldValue,FinSet.contains_eq_true] using later
  · simp [eligible,beq_eq_false_iff_ne.mpr matching]

/-- A domain diagnosis retains raw writers and the complete replay context. -/
theorem domain_error_replays (field : Field) (A B : List Act) :
    Replays (domainErrorSpec field).read A B := by
  intro e fault accepted
  change (match (domainSpec field).read A with
    | none => none
    | some initial => some (initial ∪ (writers field A ∪ domainEvidence field A))) = some e at fault
  cases old : (domainSpec field).read A with
  | none => simp [old] at fault
  | some initial =>
    have same : initial ∪ (writers field A ∪ domainEvidence field A) = e := by simpa [old] using fault
    subst e
    obtain ⟨later,current,contains⟩ := domain_spec_replays field A B initial old (accepts_union_left accepted)
    have context := accepts_union_right (accepts_union_right accepted)
    refine ⟨later ∪ (writers field B ∪ domainEvidence field B),?_,?_⟩
    · change (match (domainSpec field).read B with
        | none => none
        | some evidence => some (evidence ∪ (writers field B ∪ domainEvidence field B))) = _
      simp [current]
    · intro id member
      rcases member with original | writer | support
      · exact Or.inl (contains id original)
      · obtain ⟨act,inside,identity,verb,nonbottom⟩ := writer
        have present := (accepts_union_left (accepts_union_right accepted)) act inside
          ⟨act,inside,rfl,verb,nonbottom⟩
        exact Or.inr (Or.inl ⟨act,present,identity,verb,nonbottom⟩)
      · exact Or.inr (Or.inr (domain_evidence_replays field context id support))

/-- The actual finite top certificate reproduces its carrier and all evidence,
without a causal-domain dominance assumption or whole-history inclusion. -/
theorem top_error_replays (field : Field) (A B : List Act) :
    Replays (topErrorSpec field).read A B := by
  letI := StateFiniteTable.algebra field.table
  intro e fault accepted
  change (if state field A = field.table.table.top then
    some (writers field (selected field A) ∪ domainEvidence field A) else none) = some e at fault
  split at fault
  · rename_i conflict
    have same := Option.some.inj fault
    subst e
    have context := accepts_union_right accepted
    have transfer : ∀ act ∈ selected field A, contribution field act ≠ field.table.table.bottom → act ∈ selected field B := by
      intro act member nonbottom
      have verb : act.verb = field.verb := by simpa using (List.mem_filter.mp member).2
      have received := (accepts_union_left accepted) act (selected_inside field A act member)
        ⟨act,member,rfl,verb,nonbottom⟩
      exact selected_replays field context act member received
    have absorbed : state field A ⊔ state field B = state field B := by
      apply lift_join_of_forall
      intro act member
      by_cases bottom : contribution field act = field.table.table.bottom
      · rw [bottom]
        exact bot_join _
      · exact join_lift_of_mem _ (transfer act member bottom)
    have current : state field B = field.table.table.top := by
      apply top_below
      simpa only [conflict] using absorbed
    refine ⟨writers field (selected field B) ∪ domainEvidence field B,by simp [topErrorSpec,current],?_⟩
    intro id member
    rcases member with writer | support
    · obtain ⟨act,member,identity,verb,nonbottom⟩ := writer
      exact Or.inl ⟨act,transfer act member nonbottom,identity,verb,nonbottom⟩
    · exact Or.inr (domain_evidence_replays field context id support)
  · contradiction

/-- The installed finite guard's exact native error union replays from every
reported writer and domain-support act, including concurrent initializers. -/
theorem finite_error_replays (field : Field) (A B : List Act) :
    Replays (StateInstalledFinite.errorSpec field).read A B :=
  StateContextReplay.join_replays _ _ A B (domain_error_replays field A B) (top_error_replays field A B)

end CBCL.StateFiniteReplay
