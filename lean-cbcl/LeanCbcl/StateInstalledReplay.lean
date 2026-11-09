import LeanCbcl.StateFiniteReplay
import LeanCbcl.StateResourceReplay
import LeanCbcl.StateInstalledResource

/-! Replay certificates follow installed guard factories into their generated
source plans. Arbitrary certified IR extensions still require an explicit law. -/
set_option autoImplicit false
namespace CBCL.StateInstalledReplay
open State StateLift StateLVar StateObservation StateObservationPlan StateInstalledCompiler
open StateInstalledTerm StateWitnessReplay StateResourceReplay

/-- The error path represented by one installed guard before attachment. -/
def guardPath : Guard → Path
  | .certified spec => .certified spec
  | .domain opener field => .domain opener field
  | .resource config decode => .resource config decode
  | .threshold spec => .threshold spec

/-- Actual guard attachment preserves its complete error channel. This exact
equation detects guard omission independently of the replay predicate. -/
theorem guard_errors {V : Type} (world : Act → Prop) (guard : Guard) (source : Source V) (A : List Act) :
    errors world (path (sourcePlan (guard.apply source))) A =
      unionError (errors world (guardPath guard) A) (errors world (path (sourcePlan source)) A) := by
  cases guard <;> rfl

/-- Only certified extension guards need an extra replay obligation. -/
def GuardCertified (A B : List Act) : Guard → Prop
  | .certified spec => Replays spec.read A B
  | _ => True

/-- Compiling a guard preserves the source's certified replay inventory. -/
theorem guard_certified {V : Type} (guard : Guard) (source : Source V) (A B : List Act)
    (checked : GuardCertified A B guard)
    (prior : CertifiedReplay A B (path (sourcePlan source))) :
    CertifiedReplay A B (path (sourcePlan (guard.apply source))) := by
  cases guard with
  | certified spec => exact ⟨checked,prior⟩
  | domain opener field | resource config decode | threshold spec => exact ⟨trivial,prior⟩

/-- Every generated term guard is retained in the emitted source plan. -/
theorem term_certified {V : Type} (term : Term V) (A B : List Act)
    (checked : ∀ guard ∈ term.guards, GuardCertified A B guard) :
    CertifiedReplay A B (path (sourcePlan (StateInstalledTerm.source term))) := by
  unfold StateInstalledTerm.source
  generalize term.guards = guards at checked ⊢
  induction guards with
  | nil => trivial
  | cons guard rest ih =>
    exact guard_certified guard _ A B (checked guard (by simp))
      (ih (fun next member => checked next (List.mem_cons_of_mem guard member)))

/-- A resolved domain's concrete guard supplies its own replay certificate. -/
theorem domain_guards_certified (domains : List StateInstalledDomains.Domain) (verbs : List String)
    (A B : List Act) : ∀ guard ∈ StateInstalledDomains.guards domains verbs, GuardCertified A B guard := by
  intro guard member
  obtain ⟨domain,declared,equal⟩ := List.mem_map.mp member
  subst guard
  exact StateFiniteReplay.domain_source_replays domain.source A B

/-- The installed finite source emits the concrete unconditional replay guard,
including the initializer and roster context added to its fault evidence. -/
theorem finite_source_certified (field : StateInstalledFinite.Field) (A B : List Act) :
    CertifiedReplay A B (path (sourcePlan (StateInstalledFinite.source field))) := by
  apply term_certified
  intro guard member
  have same : guard = .certified (StateInstalledFinite.errorSpec field) := by simpa [StateInstalledFinite.term] using member
  subst guard
  exact StateFiniteReplay.finite_error_replays field A B

/-- Whole finite source error paths replay after compiler guard construction. -/
theorem finite_source_replays (world : Act → Prop) (field : StateInstalledFinite.Field)
    {A B : List Act} (closed : CausallyClosed world A) :
    Replays (errors world (path (sourcePlan (StateInstalledFinite.source field)))) A B :=
  paths_replay world _ closed (finite_source_certified field A B)

/-- Domain-aware legacy term factories emit only built-in initializer guards
and the resolved, replayable domain guards. -/
theorem domain_term_certified (context : StateKernelSEC.Context)
    (domains : List StateInstalledDomains.Domain) (expression : StateKernel.Expr)
    (resourceVerbs : String → List String) (A B : List Act) :
    CertifiedReplay A B (path (sourcePlan (StateInstalledTerm.source
      (StateInstalledDomains.term context domains expression resourceVerbs)))) := by
  apply term_certified
  intro guard member
  dsimp only [StateInstalledDomains.term] at member
  rcases List.mem_append.mp member with initial | domain
  · cases expression <;> simp at initial
    subst guard
    trivial
  · exact domain_guards_certified domains _ A B guard domain

/-- Installed context source compilation retains its path-specific replay
certificate; opener-sensitive paths use the explicit causal-root contract. -/
theorem context_source_certified (world : Act → Prop) (profile : StateInstalledContext.Profile)
    (projection : List String) {A B : List Act} (valid : ∀ act ∈ A, world act)
    (closed : CausallyClosed world B)
    (rooted : StateContextReplay.RootedOpeners world (StateInstalledContext.evidenceInput profile)) :
    CertifiedReplay A B (path (sourcePlan (StateInstalledContext.source profile projection))) := by
  change Replays (StateInstalledContext.errorSpec profile projection).read A B ∧ True
  refine ⟨?_,trivial⟩
  unfold StateInstalledContext.errorSpec
  split
  · exact StateContextReplay.context_spec_replays_of_ancestry world _ _ valid closed rooted
  · intro e impossible accepted
    contradiction

/-- Concrete resource sources emit the built-in resource guard whose replay
law is discharged by the resource certificate grammar. -/
theorem resource_source_certified (profile : StateInstalledResource.Profile)
    (decode : Act → CheckpointEvidence.ResourceData) (A B : List Act) :
    CertifiedReplay A B (path (sourcePlan (StateInstalledResource.source profile decode))) := by
  exact ⟨trivial,trivial⟩

/-- Appending compiler-resolved domain guards preserves a term's certificates.
This is the update performed by authored bounded-resource binding. -/
theorem append_domain_guards_certified {V : Type} (term : Term V)
    (domains : List StateInstalledDomains.Domain) (verbs : List String) (A B : List Act)
    (checked : ∀ guard ∈ term.guards, GuardCertified A B guard) :
    CertifiedReplay A B (path (sourcePlan (StateInstalledTerm.source
      {term with guards := term.guards ++ StateInstalledDomains.guards domains verbs}))) := by
  apply term_certified
  intro guard member
  rcases List.mem_append.mp member with original | domain
  · exact checked guard original
  · exact domain_guards_certified domains verbs A B guard domain

/-- Primitive source certificates required by one installed rule. References
and derived operations inherit the certificates of earlier compiled plans. -/
def RuleCertified {V : Type} (A B : List Act) : StateInstalledCompiler.Rule V → Prop
  | .source source => CertifiedReplay A B (path (sourcePlan source))
  | _ => True

/-- Every successful installed-rule compilation preserves certified witness
replay through references, maps, products, thresholds and freezes. -/
theorem compiled_rule_certified {V : Type} (earlier : Plans V) (rule : StateInstalledCompiler.Rule V)
    (plan : Plan V) (A B : List Act)
    (prior : ∀ name source, earlier.lookup name = some source → CertifiedReplay A B (path source))
    (source : RuleCertified A B rule) (compiled : compileRule earlier rule = some plan) :
    CertifiedReplay A B (path plan) := by
  cases rule with
  | source leaf =>
    have same : sourcePlan leaf = plan := Option.some.inj compiled
    subst plan
    exact source
  | earlier name => exact prior name plan compiled
  | derived post name =>
    cases found : earlier.lookup name with
    | none => simp [compileRule,found] at compiled
    | some dependency =>
      have same : Plan.map post dependency = plan := by simpa [compileRule,found] using compiled
      subst plan
      exact prior name dependency found
  | pair combine left right =>
    cases hl : earlier.lookup left with
    | none => simp [compileRule,hl] at compiled
    | some l =>
      cases hr : earlier.lookup right with
      | none => simp [compileRule,hl,hr] at compiled
      | some r =>
        have same : Plan.map (fun (a,b) => combine a b) (.pair l r) = plan := by
          simpa [compileRule,hl,hr] using compiled
        subst plan
        exact ⟨prior left l hl,prior right r hr⟩
  | threshold alternatives test name =>
    cases found : earlier.lookup name with
    | none => simp [compileRule,found] at compiled
    | some dependency =>
      have same : Plan.thresholdOn alternatives test dependency = plan := by simpa [compileRule,found] using compiled
      subst plan
      exact prior name dependency found
  | thresholdRaw alternatives test state name =>
    cases found : earlier.lookup name with
    | none => simp [compileRule,found] at compiled
    | some dependency =>
      have same : Plan.thresholdRaw alternatives test state dependency = plan := by simpa [compileRule,found] using compiled
      subst plan
      exact prior name dependency found
  | thresholdLift spec embed name =>
    cases found : earlier.lookup name with
    | none => simp [compileRule,found] at compiled
    | some dependency =>
      have same : Plan.embed embed (.threshold spec dependency) = plan := by simpa [compileRule,found] using compiled
      subst plan
      exact ⟨trivial,prior name dependency found⟩
  | freeze spec name =>
    cases found : earlier.lookup name with
    | none => simp [compileRule,found] at compiled
    | some dependency =>
      have same : Plan.freeze spec dependency = plan := by simpa [compileRule,found] using compiled
      subst plan
      exact prior name dependency found

/-- Clause-wide freeze attachment preserves the compiled field's certified
primitive inventory; the freeze replay law handles its own witness pairs. -/
theorem compiled_field_certified {V : Type} (earlier : Plans V)
    (field : StateInstalledClause.Field V) (plan : Plan V) (A B : List Act)
    (prior : ∀ name source, earlier.lookup name = some source → CertifiedReplay A B (path source))
    (source : RuleCertified A B field.rule)
    (compiled : StateInstalledClause.compileField earlier field = some plan) :
    CertifiedReplay A B (path plan) := by
  cases found : compileRule earlier field.rule with
  | none => simp [StateInstalledClause.compileField,found] at compiled
  | some base =>
    have checked := compiled_rule_certified earlier field.rule base A B prior source found
    cases frozen : field.freeze with
    | none =>
      have same : base = plan := by simpa [StateInstalledClause.compileField,found,frozen] using compiled
      subst plan
      exact checked
    | some spec =>
      have same : Plan.freeze spec base = plan := by simpa [StateInstalledClause.compileField,found,frozen] using compiled
      subst plan
      exact checked

/-- Ordered installed clauses preserve replay certificates for every output,
including dependencies on previously compiled fields and their freezes. -/
theorem compiled_fields_certified {V : Type} (fields : List (String × StateInstalledClause.Field V))
    (A B : List Act) (sources : ∀ binding ∈ fields, RuleCertified A B binding.2.rule)
    (earlier result : Plans V)
    (prior : ∀ name source, earlier.lookup name = some source → CertifiedReplay A B (path source))
    (compiled : StateInstalledClause.compileFields earlier fields = some result) :
    ∀ binding ∈ result, CertifiedReplay A B (path binding.2) := by
  induction fields generalizing earlier result with
  | nil =>
    have empty : ([] : Plans V) = result := Option.some.inj compiled
    subst result
    simp
  | cons binding rest ih =>
    obtain ⟨name,field⟩ := binding
    cases head : StateInstalledClause.compileField earlier field with
    | none => simp [StateInstalledClause.compileFields,head] at compiled
    | some plan =>
      have checked := compiled_field_certified earlier field plan A B prior
        (sources (name,field) (by simp)) head
      have extended : ∀ query source, (((name,plan)::earlier).lookup query = some source) →
          CertifiedReplay A B (path source) := by
        intro query source found
        by_cases equal : query = name
        · subst query
          have same : plan = source := by simpa [List.lookup_cons] using found
          simpa [same] using checked
        · exact prior query source (by simpa [List.lookup_cons,beq_eq_false_iff_ne.mpr equal] using found)
      cases tail : StateInstalledClause.compileFields ((name,plan)::earlier) rest with
      | none => simp [StateInstalledClause.compileFields,head,tail] at compiled
      | some plans =>
        have same : (name,plan)::plans = result := by
          simpa [StateInstalledClause.compileFields,head,tail] using compiled
        subst result
        have remaining := ih (fun binding member => sources binding (List.mem_cons_of_mem (name,field) member))
          ((name,plan)::earlier) plans extended tail
        intro binding member
        rcases List.mem_cons.mp member with equal | later
        · subst binding
          exact checked
        · exact remaining binding later

end CBCL.StateInstalledReplay
