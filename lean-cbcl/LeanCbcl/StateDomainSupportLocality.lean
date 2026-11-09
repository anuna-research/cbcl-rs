import LeanCbcl.StateAuthoredBindings

/-! Domain support is part of a field's retained freeze footprint. Healthy fault
freezes preserve all applicable initializer/roster evidence and selected writers,
so domain-locality does not depend on an unproved protocol-opener ancestry gate. -/
namespace CBCL.StateDomainSupportLocality
open State StateLift StateLVar StateObservation StateInstalledDomains

/-- Any value admitted by a domain comes from an actual supporting act. -/
theorem contribution_supported (source : DomainSource) (act : Act) (value : Val)
    (member : value ∈ contribution source act) : supports source act = true := by
  cases source with
  | initial opener field =>
    cases matching : act.verb == opener with
    | false =>
      simp only [contribution,matching,Bool.false_eq_true,ite_false] at member
      exact False.elim (FinSet.not_mem_bot member)
    | true => simpa [supports] using matching
  | roster profile role =>
    cases root : act.preds.isEmpty with
    | false =>
      simp only [contribution,root,Bool.false_eq_true,ite_false] at member
      exact False.elim (FinSet.not_mem_bot member)
    | true => simpa [supports] using root

/-- A subhistory retaining all domain support retains exactly its allowed set. -/
theorem allowed_support_locality (source : DomainSource) (whole cut : List Act)
    (inside : ∀ act ∈ cut, act ∈ whole)
    (covered : ∀ act ∈ whole, supports source act = true → act ∈ cut) :
    allowed source cut = allowed source whole := by
  apply FinSet.ext
  intro value
  constructor
  · intro member
    obtain ⟨act,present,contributes⟩ := (mem_lift (contribution source)).mp member
    exact (mem_lift (contribution source)).mpr ⟨act,inside act present,contributes⟩
  · intro member
    obtain ⟨act,present,contributes⟩ := (mem_lift (contribution source)).mp member
    exact (mem_lift (contribution source)).mpr
      ⟨act,covered act present (contribution_supported source act value contributes),contributes⟩

/-- Every retained contributor is in a healthy fault freezer's exact cut. -/
theorem healthy_contributor_cut (whole : List Act) (freezeVerb : String) (contributes : Act → Prop)
    (freezer : Act) (first : Earliest (fun act => act ∈ whole) freezeVerb whole freezer)
    (healthy : freezeFault (fun act => act ∈ whole) freezeVerb contributes true none whole = none)
    (act : Act) (member : act ∈ whole) (contributing : contributes act) :
    act ∈ causalCut (fun act => act ∈ whole) whole freezer := by
  classical
  apply List.mem_filter.mpr
  refine ⟨member,decide_eq_true ?_⟩
  apply Classical.byContradiction
  intro absent
  have conflict : ∃ a b, FreezeConflict (fun act => act ∈ whole) freezeVerb contributes true whole a b :=
    ⟨freezer,act,.late first member contributing absent rfl⟩
  simp [freezeFault,conflict] at healthy

/-- Actual authored footprints retain every applicable domain's support, so
healthy fault cuts preserve allowed membership for initial and roster domains. -/
theorem domain_allowed_cut (domains : List Domain) (names : List String) (whole : List Act)
    (freezeVerb : String) (freezer : Act) (first : Earliest (fun act => act ∈ whole) freezeVerb whole freezer)
    (healthy : freezeFault (fun act => act ∈ whole) freezeVerb
      (StateAuthoredBindings.contributes domains whole (.verbs names)) true none whole = none)
    (domain : Domain) (declared : domain ∈ domains) (relevant : domain.verb ∈ names) :
    allowed domain.source (causalCut (fun act => act ∈ whole) whole freezer) = allowed domain.source whole := by
  apply allowed_support_locality
  · intro act member; exact (List.mem_filter.mp member).1
  · intro act member supporting
    apply healthy_contributor_cut whole freezeVerb _ freezer first healthy act member
    exact Or.inr ⟨domain,declared,relevant,act,member,supporting,rfl⟩

/-- The original source verbs selected after all domain constraints. -/
def selected (domains : List Domain) (names : List String) (whole : List Act) : List Act :=
  (select domains whole).filter (fun act => names.contains act.verb)

/-- A healthy authored fault freeze preserves the complete selected source
history for any number of initializer and sealed-roster domains. -/
theorem selected_cut (domains : List Domain) (names : List String) (whole : List Act)
    (freezeVerb : String) (freezer : Act) (first : Earliest (fun act => act ∈ whole) freezeVerb whole freezer)
    (healthy : freezeFault (fun act => act ∈ whole) freezeVerb
      (StateAuthoredBindings.contributes domains whole (.verbs names)) true none whole = none) :
    selected domains names (causalCut (fun act => act ∈ whole) whole freezer) = selected domains names whole := by
  classical
  have predicates : ∀ act, act.verb ∈ names →
      domains.all (fun domain => eligible domain (causalCut (fun act => act ∈ whole) whole freezer) act) =
        domains.all (fun domain => eligible domain whole act) := by
    intro act relevant
    have same : ∀ domain ∈ domains,
        eligible domain (causalCut (fun act => act ∈ whole) whole freezer) act = eligible domain whole act := by
      intro domain declared
      by_cases verb : act.verb = domain.verb
      · have allowed := domain_allowed_cut domains names whole freezeVerb freezer first healthy domain declared (verb ▸ relevant)
        simp only [eligible]
        rw [allowed]
      · simp [eligible,verb]
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro accepted
      apply List.all_eq_true.mpr
      intro domain declared
      rw [← same domain declared]
      exact List.all_eq_true.mp accepted domain declared
    · intro accepted
      apply List.all_eq_true.mpr
      intro domain declared
      rw [same domain declared]
      exact List.all_eq_true.mp accepted domain declared
  simp only [selected,select,causalCut,List.filter_filter]
  apply List.filter_congr
  intro act accepted
  by_cases relevant : act.verb ∈ names
  · have known : names.contains act.verb = true := List.contains_iff_mem.mpr relevant
    have predicatesHere := predicates act relevant
    simp only [causalCut] at predicatesHere
    rw [predicatesHere]
    by_cases eligible : domains.all (fun domain => StateInstalledDomains.eligible domain whole act) = true
    · have chosen : act ∈ select domains whole := List.mem_filter.mpr ⟨accepted,eligible⟩
      have inside := healthy_contributor_cut whole freezeVerb _ freezer first healthy act accepted (Or.inl ⟨act,chosen,relevant,rfl⟩)
      have ancestor := (List.mem_filter.mp inside).2
      simp only [known,eligible,ancestor,Bool.true_and,Bool.and_true]
    · have rejected := Bool.eq_false_iff.mpr eligible
      simp only [known,rejected,Bool.true_and,Bool.false_and,Bool.and_false]
  · have unknown : names.contains act.verb = false := by simpa using relevant
    simp only [unknown,Bool.false_and]

/-- Retained selected source history grows as accepted domain evidence grows. -/
theorem selected_grows (domains : List Domain) (names : List String) {A B : List Act}
    (growth : ∀ act ∈ A, act ∈ B) : ∀ act ∈ selected domains names A, act ∈ selected domains names B := by
  intro act member
  obtain ⟨eligible,verb⟩ := List.mem_filter.mp member
  exact List.mem_filter.mpr ⟨StateInstalledDomains.selected_grows domains growth act eligible,verb⟩

/-- The actual distinct count of selected source acts is monotone. -/
theorem count_grows (domains : List Domain) (names : List String) {A B : List Act}
    (growth : ∀ act ∈ A, act ∈ B) (uniqueA : NodupAddr A) (uniqueB : NodupAddr B) :
    FinSet.card (FinSet.mk (selected domains names A)) ≤ FinSet.card (FinSet.mk (selected domains names B)) := by
  have leftUnique : (selected domains names A).Nodup := (uniqueA.nodup.filter _).filter _
  have rightUnique : (selected domains names B).Nodup := (uniqueB.nodup.filter _).filter _
  rw [FinSet.card_mk_of_nodup leftUnique,FinSet.card_mk_of_nodup rightUnique]
  obtain ⟨chosen,perm,subset⟩ := List.subperm_of_subset leftUnique (selected_grows domains names growth)
  have lengths := perm.length_eq
  have bounded := subset.length_le
  omega

/-- A prior reached count survives a later healthy fault cut for multiple
initializer/roster domains, without an opener-ancestry or admission premise. -/
theorem count_success_at_cut (domains : List Domain) (names : List String) (A B : List Act)
    (growth : ∀ act ∈ A, act ∈ B) (uniqueA : NodupAddr A) (uniqueB : NodupAddr B)
    (freezeVerb : String) (freezer : Act) (first : Earliest (fun act => act ∈ B) freezeVerb B freezer)
    (healthy : freezeFault (fun act => act ∈ B) freezeVerb
      (StateAuthoredBindings.contributes domains B (.verbs names)) true none B = none)
    (bound : Nat) (reached : bound ≤ FinSet.card (FinSet.mk (selected domains names A))) :
    bound ≤ FinSet.card (FinSet.mk (selected domains names (causalCut (fun act => act ∈ B) B freezer))) := by
  rw [selected_cut domains names B freezeVerb freezer first healthy]
  exact Nat.le_trans reached (count_grows domains names growth uniqueA uniqueB)

end CBCL.StateDomainSupportLocality
