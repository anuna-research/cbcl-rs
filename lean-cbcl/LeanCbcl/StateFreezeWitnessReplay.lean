import LeanCbcl.StateAuthoredReplay

/-! Witness replay for freshly materialized contributor predicates. A domain
support missing from a freezer's cut is itself a reported late contribution;
causal admission supplies support inside the cut. -/
set_option autoImplicit false
namespace CBCL.StateFreezeWitnessReplay
open State StateLift StateLVar StateObservation StateWitnessReplay
open StateAuthoredBindings StateInstalledDomains

/-- A domain support is either restored by the accepted freezer's causal past
or named by its own late-contribution witness. No full-history receipt is used. -/
theorem domain_support_received (world : Act → Prop) (domains : List Domain) (names : List String)
    (verb : String) (policy : Bool) {A B : List Act} {freezer : Act}
    (closed : CausallyClosed world B) (first : Earliest world verb A freezer)
    (freezerAccepted : freezer ∈ B) (faultPolicy : policy = true)
    (accepted : Accepts A (freezeEvidence world verb (contributes domains A (.verbs names)) policy A) B)
    (domain : Domain) (declared : domain ∈ domains) (relevant : domain.verb ∈ names)
    (support : Act) (inside : support ∈ A) (supporting : supports domain.source support = true) : support ∈ B := by
  classical
  by_cases past : Ancestor world support freezer
  · exact ancestor_accepted closed past freezerAccepted
  · have contributing : contributes domains A (.verbs names) support :=
      Or.inr ⟨domain,declared,relevant,support,inside,supporting,rfl⟩
    have conflict : FreezeConflict world verb (contributes domains A (.verbs names)) policy A freezer support :=
      .late first inside contributing past faultPolicy
    exact accepted support inside ⟨freezer,support,conflict,Or.inr rfl⟩

/-- Restoring applicable support contributions preserves a selected writer,
even when the initializer and writer are causally concurrent. -/
theorem selected_received (domains : List Domain) (names : List String) {A B : List Act}
    (context : ∀ domain ∈ domains, domain.verb ∈ names → ∀ support ∈ A,
      supports domain.source support = true → support ∈ B)
    (writer : Act) (selected : writer ∈ select domains A) (relevant : writer.verb ∈ names)
    (accepted : writer ∈ B) : writer ∈ select domains B := by
  have checked := (List.mem_filter.mp selected).2
  apply List.mem_filter.mpr
  refine ⟨accepted,List.all_eq_true.mpr ?_⟩
  intro domain declared
  have before := List.all_eq_true.mp checked domain declared
  by_cases matching : writer.verb = domain.verb
  · cases field : writer.get domain.key with
    | none => simp [eligible,matching,field] at before
    | some value =>
      have member : value ∈ allowed domain.source A := by
        simpa [eligible,matching,field,FinSet.contains_eq_true] using before
      obtain ⟨support,inside,contributed⟩ := (mem_lift (contribution domain.source)).mp member
      have present := context domain declared (by simpa [← matching] using relevant) support inside
        (StateFiniteReplay.contribution_supports domain.source support value contributed)
      have later : value ∈ allowed domain.source B :=
        (mem_lift (contribution domain.source)).mpr ⟨support,present,contributed⟩
      simpa [eligible,matching,field,FinSet.contains_eq_true] using later
  · simp [eligible,beq_eq_false_iff_ne.mpr matching]

/-- A reported late writer remains a contributor after the receiver rebuilds
its footprint from only the witness and restored causal context. -/
theorem contributor_received (world : Act → Prop) (domains : List Domain) (footprint : Footprint)
    (verb : String) (policy : Bool) {A B : List Act} {freezer writer : Act}
    (unique : NodupAddr A) (closed : CausallyClosed world B)
    (first : Earliest world verb A freezer) (freezerAccepted : freezer ∈ B)
    (faultPolicy : policy = true) (writerInside : writer ∈ A) (writerAccepted : writer ∈ B)
    (contributing : contributes domains A footprint writer)
    (accepted : Accepts A (freezeEvidence world verb (contributes domains A footprint) policy A) B) :
    contributes domains B footprint writer := by
  cases footprint with
  | all => exact List.mem_map.mpr ⟨writer,writerAccepted,rfl⟩
  | rawVerbs names =>
    obtain ⟨source,inside,relevant,identity⟩ := contributing
    have same := unique.eq_of_addr inside writerInside identity
    subst source
    exact ⟨writer,writerAccepted,relevant,rfl⟩
  | verbs names =>
    rcases contributing with ⟨source,selected,relevant,identity⟩ | ⟨domain,declared,relevant,source,inside,supporting,identity⟩
    · have same := unique.eq_of_addr (List.mem_filter.mp selected).1 writerInside identity
      subst source
      have restored := selected_received domains names
        (fun domain declared relevant support inside supporting =>
          domain_support_received world domains names verb policy closed first freezerAccepted faultPolicy accepted
            domain declared relevant support inside supporting)
        writer selected relevant writerAccepted
      exact Or.inl ⟨writer,restored,relevant,rfl⟩
    · have same := unique.eq_of_addr inside writerInside identity
      subst source
      exact Or.inr ⟨domain,declared,relevant,writer,writerAccepted,supporting,rfl⟩

/-- Every reported freeze pair reproduces under the receiver's freshly
materialized contributor predicate. -/
theorem conflict_replays (world : Act → Prop) (domains : List Domain) (footprint : Footprint)
    (verb : String) (policy : Bool) {A B : List Act} {a b : Act}
    (unique : NodupAddr A) (sourceClosed : CausallyClosed world A) (receiverClosed : CausallyClosed world B)
    (accepted : Accepts A (freezeEvidence world verb (contributes domains A footprint) policy A) B)
    (conflict : FreezeConflict world verb (contributes domains A footprint) policy A a b) :
    FreezeConflict world verb (contributes domains B footprint) policy B a b := by
  have original := freeze_witness_accepted conflict
  have left := accepted a original.1 ⟨a,b,conflict,Or.inl rfl⟩
  have right := accepted b original.2 ⟨a,b,conflict,Or.inr rfl⟩
  cases conflict with
  | concurrent first second different =>
    exact .concurrent (earliest_transfer sourceClosed first left) (earliest_transfer sourceClosed second right) different
  | late first inside contributing outside faultPolicy =>
    exact .late (earliest_transfer sourceClosed first left) right
      (contributor_received world domains footprint verb policy unique receiverClosed first left faultPolicy
        inside right contributing accepted) outside faultPolicy

/-- All collected evidence survives fresh materialization, not only a first
diagnostic's chosen pair. -/
theorem evidence_replays (world : Act → Prop) (domains : List Domain) (footprint : Footprint)
    (verb : String) (policy : Bool) {A B : List Act}
    (unique : NodupAddr A) (sourceClosed : CausallyClosed world A) (receiverClosed : CausallyClosed world B)
    (accepted : Accepts A (freezeEvidence world verb (contributes domains A footprint) policy A) B) :
    ∀ id ∈ freezeEvidence world verb (contributes domains A footprint) policy A,
      id ∈ freezeEvidence world verb (contributes domains B footprint) policy B := by
  rintro id ⟨a,b,conflict,which⟩
  exact ⟨a,b,conflict_replays world domains footprint verb policy unique sourceClosed receiverClosed accepted conflict,which⟩

/-- Replay between possibly different source error paths at fixed histories. -/
def CrossReplays (A B : List Act) (left right : Error) : Prop :=
  ∀ e, left = some e → Accepts A e B →
    ∃ enlarged, right = some enlarged ∧ ∀ id ∈ e, id ∈ enlarged

/-- A complete freeze fault replays across fresh contributor materialization,
including both its raw dependency errors and every collected freeze witness. -/
theorem freeze_fault_replays (world : Act → Prop) (domains : List Domain) (footprint : Footprint)
    (verb : String) (policy : Bool) {A B : List Act} (rawLeft rawRight : Error)
    (unique : NodupAddr A) (sourceClosed : CausallyClosed world A) (receiverClosed : CausallyClosed world B)
    (rawReplay : CrossReplays A B rawLeft rawRight) :
    CrossReplays A B
      (freezeFault world verb (contributes domains A footprint) policy rawLeft A)
      (freezeFault world verb (contributes domains B footprint) policy rawRight B) := by
  classical
  intro e fault accepted
  unfold freezeFault at fault ⊢
  split at fault
  · rename_i reason
    have same := Option.some.inj fault
    subst e
    have rawAccepted := accepts_union_left accepted
    have freezeAccepted := accepts_union_right accepted
    have freezeGrows := evidence_replays world domains footprint verb policy unique sourceClosed receiverClosed freezeAccepted
    have rawGrows : ∀ old, rawLeft = some old → ∃ later, rawRight = some later ∧ ∀ id ∈ old, id ∈ later := by
      intro old observed
      apply rawReplay old observed
      simpa [observed] using rawAccepted
    have currentReason : rawRight.isSome ∨ ∃ a b,
        FreezeConflict world verb (contributes domains B footprint) policy B a b := by
      rcases reason with rawFault | ⟨a,b,conflict⟩
      · cases observed : rawLeft with
        | none => simp [observed] at rawFault
        | some old =>
          obtain ⟨later,current,_⟩ := rawGrows old observed
          exact Or.inl (by simp [current])
      · exact Or.inr ⟨a,b,conflict_replays world domains footprint verb policy
          unique sourceClosed receiverClosed freezeAccepted conflict⟩
    refine ⟨rawRight.getD ∅ ∪ freezeEvidence world verb (contributes domains B footprint) policy B,
      if_pos currentReason,?_⟩
    intro id member
    rcases member with rawMember | freezeMember
    · cases observed : rawLeft with
      | none =>
        have impossible : id ∈ (∅ : Evidence) := by simpa [observed] using rawMember
        exact False.elim impossible
      | some old =>
        obtain ⟨later,current,contains⟩ := rawGrows old observed
        exact Or.inl (by simpa [current] using contains id (by simpa [observed] using rawMember))
    · exact Or.inr (freezeGrows id freezeMember)
  · contradiction

end CBCL.StateFreezeWitnessReplay
