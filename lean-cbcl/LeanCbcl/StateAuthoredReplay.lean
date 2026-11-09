import LeanCbcl.StateInstalledReplay
import LeanCbcl.StateQuasiDeterminism
import LeanCbcl.StateAuthoredSourceProvenance

/-! Authored binding supplies the concrete source replay certificates consumed
by the installed compiler. Immutable context prerequisites remain explicit. -/
set_option autoImplicit false
namespace CBCL.StateAuthoredReplay
open State StateLift StateLVar StateObservation StateObservationPlan StateInstalledCompiler
open StateInstalledReplay StateResourceReplay StateAuthoredBindings StateInstalledLowering
open StateInstalledLegacy

/-- A definition's primitive source is certified; derived references inherit
certificates later through actual installed lookup and compilation. -/
def DefinitionCertified (A B : List Act) (definition : Definition Value) : Prop :=
  RuleCertified A B (lowerDefinition definition)

/-- Every ordinary native expression binds the resolved domain factories. -/
theorem primitive_certified (environment : Environment) (domains : List StateInstalledDomains.Domain)
    (expression : StateKernel.Expr) (rule : StateKernelClause.Rule) (A B : List Act) :
    DefinitionCertified A B (primitive environment domains expression rule) := by
  cases rule <;> exact domain_term_certified environment.context domains expression (resourceVerbs environment) A B

/-- The finite read policy retains the same concrete guarded term. -/
theorem finite_definition_certified (field : StateInstalledFinite.Field) (A B : List Act) :
    DefinitionCertified A B (StateFiniteRead.definition field) := finite_source_certified field A B

/-- Resource binding appends only certified resolved-domain guard factories. -/
theorem resource_definition_certified (resource : Resource) (domains : List StateInstalledDomains.Domain)
    (verbs : List String) (A B : List Act) :
    DefinitionCertified A B (.factored
      {StateInstalledResource.term resource.profile resource.decode with guards :=
        (StateInstalledResource.term resource.profile resource.decode).guards ++ StateInstalledDomains.guards domains verbs} none) := by
  apply append_domain_guards_certified
  intro guard member
  have same : guard = .resource resource.profile.config resource.decode := by
    simpa [StateInstalledResource.term] using member
  subst guard
  trivial

/-- Successfully recognized context paths retain their actual source factory. -/
theorem context_definition_certified (world : Act → Prop) (profile : StateInstalledContext.Profile)
    (projection : List String) (definition : Definition Value) {A B : List Act}
    (valid : ∀ act ∈ A, world act) (closed : CausallyClosed world B)
    (rooted : StateContextReplay.RootedOpeners world (StateInstalledContext.evidenceInput profile))
    (installed : StateInstalledContext.make profile projection = some definition) :
    DefinitionCertified A B definition := by
  unfold StateInstalledContext.make at installed
  split at installed
  · cases Option.some.inj installed
    exact context_source_certified world profile projection valid closed rooted
  · contradiction

/-- Every successful authored binding supplies its primitive source
certificate. No detached source-plan or fault-classifier premise is supplied. -/
theorem bind_certified (world : Act → Prop) (environment : Environment)
    (domains : List StateInstalledDomains.Domain) (tables : List (String × StateFiniteTable.Verified))
    (earlier : List (String × Binding)) (rule : StateAuthoredBindings.Rule) (binding : Binding)
    {A B : List Act} (valid : ∀ act ∈ A, world act) (closed : CausallyClosed world B)
    (rooted : StateContextReplay.RootedOpeners world (StateInstalledContext.evidenceInput environment.profile))
    (bound : StateAuthoredBindings.bind environment domains tables earlier rule = some binding) :
    DefinitionCertified A B binding.definition := by
  cases rule with
  | context projection =>
    cases installed : StateInstalledContext.make environment.profile projection with
    | none => simp [StateAuthoredBindings.bind,installed] at bound
    | some definition =>
      have same : (⟨.context projection,definition,contextFootprint environment projection⟩ : Binding) = binding := by
        simpa [StateAuthoredBindings.bind,installed] using bound
      subst binding
      exact context_definition_certified world environment.profile projection definition valid closed rooted installed
  | finite lattice declaration =>
    cases table : tables.lookup lattice with
    | none => simp [StateAuthoredBindings.bind,table] at bound
    | some verified =>
      cases field : StateInstalledFinite.make environment.schema verified domains declaration with
      | none => simp [StateAuthoredBindings.bind,table,field] at bound
      | some source =>
        have same : (⟨.finite lattice declaration,StateFiniteRead.definition source,.verbs [declaration.verb]⟩ : Binding) = binding := by
          simpa [StateAuthoredBindings.bind,table,field] using bound
        subst binding
        exact finite_definition_certified source A B
  | legacy rule =>
    cases rule
    case histogram reference =>
      simp only [StateAuthoredBindings.bind] at bound
      split at bound
      · contradiction
      · split at bound
        · cases Option.some.inj bound
          trivial
        · contradiction
    case sum reference =>
      simp only [StateAuthoredBindings.bind] at bound
      split at bound
      · contradiction
      · split at bound
        · contradiction
        · cases Option.some.inj bound
          trivial
    case boundedCounter name =>
      cases resource : environment.resources.lookup name with
      | none => simp [StateAuthoredBindings.bind,resource] at bound
      | some profile =>
        simp only [StateAuthoredBindings.bind,resource] at bound
        cases Option.some.inj bound
        exact resource_definition_certified profile domains (resourceVerbs environment name) A B
    all_goals
      simp only [StateAuthoredBindings.bind,StateKernelClause.compileRule,StateKernelClause.mapPlanOf] at bound
      cases Option.some.inj bound
      dsimp only
      apply primitive_certified

/-- A lowered declaration certifies its source or defers a threshold reference
to the installed compiler's earlier-plan invariant. -/
def DeclarationCertified (A B : List Act) : Declaration Value → Prop
  | .field _ definition => DefinitionCertified A B definition
  | .threshold .. => True

/-- Successful authored declaration lowering constructs certificates for all
emitted definitions, including fields interleaved with auxiliary entries. -/
theorem declarations_certified (world : Act → Prop) (environment : Environment)
    (domains : List StateInstalledDomains.Domain) (tables : List (String × StateFiniteTable.Verified))
    (entries : List Entry) (earlier : List (String × Binding))
    (output : List (Declaration Value)) (bindings : List (String × Binding))
    {A B : List Act} (valid : ∀ act ∈ A, world act) (closed : CausallyClosed world B)
    (rooted : StateContextReplay.RootedOpeners world (StateInstalledContext.evidenceInput environment.profile))
    (lowered : declarations environment domains tables earlier entries = some (output,bindings)) :
    ∀ declaration ∈ output, DeclarationCertified A B declaration := by
  induction entries generalizing earlier output bindings with
  | nil =>
    have same : ([],earlier) = (output,bindings) := Option.some.inj lowered
    have empty : output = [] := (congrArg Prod.fst same).symm
    simp [empty]
  | cons entry rest ih =>
    cases entry with
    | field name rule =>
      cases head : StateAuthoredBindings.bind environment domains tables earlier rule with
      | none => simp [declarations,head] at lowered
      | some binding =>
        cases tail : declarations environment domains tables ((name,binding)::earlier) rest with
        | none => simp [declarations,head,tail] at lowered
        | some result =>
          obtain ⟨more,last⟩ := result
          simp [declarations,head,tail] at lowered
          rcases lowered with ⟨rfl,rfl⟩
          have current := bind_certified world environment domains tables earlier rule binding valid closed rooted head
          have remaining := ih ((name,binding)::earlier) more last tail
          intro declaration member
          rcases List.mem_cons.mp member with equal | later
          · subst declaration
            exact current
          · exact remaining declaration later
    | threshold name source elements =>
      cases tail : declarations environment domains tables earlier rest with
      | none => simp [declarations,tail] at lowered
      | some result =>
        obtain ⟨more,last⟩ := result
        simp [declarations,tail] at lowered
        rcases lowered with ⟨rfl,rfl⟩
        have remaining := ih earlier more last tail
        intro declaration member
        rcases List.mem_cons.mp member with equal | later
        · subst declaration
          trivial
        · exact remaining declaration later
    | condition _ _ | domain _ | lattice _ | freeze _ _ _ =>
      exact ih earlier output bindings (by simpa [declarations] using lowered)

/-- Source-relative query dispatch introduces no new certified primitive. -/
theorem lower_rule_certified (earlier : Definitions Value) (declaration : Declaration Value)
    (rule : StateInstalledCompiler.Rule Value) (A B : List Act)
    (checked : DeclarationCertified A B declaration) (lowered : StateInstalledLowering.lowerRule earlier declaration = some rule) :
    RuleCertified A B rule := by
  cases declaration with
  | field name definition =>
    cases Option.some.inj lowered
    exact checked
  | threshold name reference elements =>
    cases found : earlier.lookup reference with
    | none => simp [StateInstalledLowering.lowerRule,found] at lowered
    | some definition =>
      cases definition with
      | native leaf policy =>
        cases policy with
        | none => simp [StateInstalledLowering.lowerRule,found] at lowered
        | some policy =>
          simp only [StateInstalledLowering.lowerRule,found] at lowered
          split at lowered
          · cases Option.some.inj lowered
            trivial
          · contradiction
      | factored term policy =>
        cases policy with
        | none => simp [StateInstalledLowering.lowerRule,found] at lowered
        | some policy =>
          simp only [StateInstalledLowering.lowerRule,found] at lowered
          split at lowered
          · cases Option.some.inj lowered
            trivial
          · contradiction
      | lattice field =>
        cases prepared : StateInstalledLattice.prepareQuery field elements with
        | none => simp [StateInstalledLowering.lowerRule,found,prepared] at lowered
        | some query =>
          have same : StateInstalledLattice.queryRule query reference = rule := by
            simpa [StateInstalledLowering.lowerRule,found,prepared] using lowered
          subst rule
          trivial
      | derived post source | pair combine left right => simp [StateInstalledLowering.lowerRule,found] at lowered

/-- Ordered source-relative lowering preserves certificates for every rule it
actually emits, including thresholds interleaved with ordinary fields. -/
theorem resolve_certified (declarations : List (Declaration Value)) (A B : List Act)
    (checked : ∀ declaration ∈ declarations, DeclarationCertified A B declaration)
    (earlier : Definitions Value) (result : List (String × StateInstalledCompiler.Rule Value))
    (resolved : StateInstalledLowering.resolve earlier declarations = some result) :
    ∀ binding ∈ result, RuleCertified A B binding.2 := by
  induction declarations generalizing earlier result with
  | nil =>
    have empty : ([] : List (String × StateInstalledCompiler.Rule Value)) = result := Option.some.inj resolved
    subst result
    simp
  | cons declaration rest ih =>
    cases head : StateInstalledLowering.lowerRule earlier declaration with
    | none => simp [StateInstalledLowering.resolve,head] at resolved
    | some rule =>
      cases tail : StateInstalledLowering.resolve (extend earlier declaration) rest with
      | none => simp [StateInstalledLowering.resolve,head,tail] at resolved
      | some rules =>
        have same : (declaration.name,rule)::rules = result := by
          simpa [StateInstalledLowering.resolve,head,tail] using resolved
        subst result
        have current := lower_rule_certified earlier declaration rule A B (checked declaration (by simp)) head
        have remaining := ih (fun declaration member => checked declaration (List.mem_cons_of_mem _ member))
          (extend earlier declaration) rules tail
        intro binding member
        rcases List.mem_cons.mp member with equal | later
        · subst binding
          exact current
        · exact remaining binding later

/-- Successful authored preparation constructs all source certificates before
history-dependent freezes are materialized. -/
theorem prepared_declarations_certified (world : Act → Prop) (environment : Environment)
    (entries : List Entry) (prepared : Prepared) {A B : List Act}
    (valid : ∀ act ∈ A, world act) (closed : CausallyClosed world B)
    (rooted : StateContextReplay.RootedOpeners world (StateInstalledContext.evidenceInput environment.profile))
    (installed : prepareStatic environment entries = some prepared) :
    ∀ declaration ∈ prepared.declarations, DeclarationCertified A B declaration := by
  obtain ⟨tables,bindings,_,_,lowered,_⟩ := StateAuthoredSourceProvenance.static_trace environment entries prepared installed
  exact declarations_certified world environment prepared.domains tables entries [] prepared.declarations bindings
    valid closed rooted lowered

/-- Every actual plan produced from an authored prepared clause has certified
replay guards. The theorem follows binding, lowering, freeze attachment and
ordered compilation; no source certificate is supplied by the caller. -/
theorem prepared_plans_certified (world : Act → Prop) (environment : Environment)
    (entries : List Entry) (prepared : Prepared) (history : List Act) (plans : Plans Value)
    {A B : List Act} (valid : ∀ act ∈ A, world act) (closed : CausallyClosed world B)
    (rooted : StateContextReplay.RootedOpeners world (StateInstalledContext.evidenceInput environment.profile))
    (installed : prepareStatic environment entries = some prepared)
    (compiled : StateInstalledLowering.compile (clauseAt prepared history) = some plans) :
    ∀ binding ∈ plans, CertifiedReplay A B (path binding.2) := by
  have declarationsChecked := prepared_declarations_certified world environment entries prepared valid closed rooted installed
  unfold StateInstalledLowering.compile at compiled
  split at compiled
  · cases resolved : StateInstalledLowering.resolve [] prepared.declarations with
    | none => simp [clauseAt,resolved] at compiled
    | some rules =>
      have rulesChecked := resolve_certified prepared.declarations A B declarationsChecked [] rules resolved
      have attached : ∀ binding ∈ StateInstalledClause.attach (materialize prepared.domains history prepared.freezes) rules,
          RuleCertified A B binding.2.rule := by
        intro binding member
        obtain ⟨⟨name,rule⟩,inside,equal⟩ := List.mem_map.mp member
        subst binding
        exact rulesChecked (name,rule) inside
      apply compiled_fields_certified _ A B attached [] plans
      · intro name source impossible
        simp at impossible
      · simpa [clauseAt,resolved] using compiled
  · contradiction

/-- Successful authored compilation certifies every emitted plan directly
from the authored entries and concrete factory executions. -/
theorem compile_certified (world : Act → Prop) (environment : Environment) (entries : List Entry)
    (history : List Act) (plans : Plans Value) {A B : List Act}
    (valid : ∀ act ∈ A, world act) (closed : CausallyClosed world B)
    (rooted : StateContextReplay.RootedOpeners world (StateInstalledContext.evidenceInput environment.profile))
    (compiled : StateAuthoredBindings.compile environment entries history = some plans) :
    ∀ binding ∈ plans, CertifiedReplay A B (path binding.2) := by
  cases installed : prepareStatic environment entries with
  | none => simp [StateAuthoredBindings.compile,prepare,installed] at compiled
  | some prepared =>
    apply prepared_plans_certified world environment entries prepared history plans valid closed rooted installed
    simpa [StateAuthoredBindings.compile,prepare,installed,clauseAt] using compiled

/-- An actual authored plan reproduces its fault from the reported acts. The
plan remains the same compiled object; later history-dependent recompilation
requires its separate contributor-transport theorem. -/
theorem authored_plan_fault_replays (world : Act → Prop) (environment : Environment)
    (entries : List Entry) (plans : Plans Value) (binding : String × Plan Value)
    {A B : List Act} {e : Evidence} (valid : ∀ act ∈ A, world act)
    (sourceClosed : CausallyClosed world A) (receiverClosed : CausallyClosed world B)
    (rooted : StateContextReplay.RootedOpeners world (StateInstalledContext.evidenceInput environment.profile))
    (compiled : StateAuthoredBindings.compile environment entries A = some plans) (present : binding ∈ plans)
    (fault : observe world binding.2 A = .fault e) (accepted : StateWitnessReplay.Accepts A e B) :
    ∃ enlarged, observe world binding.2 B = .fault enlarged ∧ ∀ id ∈ e, id ∈ enlarged := by
  have checked := compile_certified world environment entries A plans valid receiverClosed rooted compiled binding present
  exact StateQuasiDeterminism.fault_of_accepting_witness world binding.2 sourceClosed
    (primitive_replay _ A B checked) accepted fault

end CBCL.StateAuthoredReplay
