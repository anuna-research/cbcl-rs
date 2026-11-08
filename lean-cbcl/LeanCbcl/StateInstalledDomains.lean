import LeanCbcl.StateInstalledContext

/-! Resolved initializer and sealed-context roster domains. Allowed membership
is retained under union of observed sources, as native freeze witnesses require;
independent source faults prevent a conflicting roster from becoming a success.
The same selectors can feed ordinary native posts and finite contribution rows. -/
set_option autoImplicit false
namespace CBCL.StateInstalledDomains
open State StateLift StateLVar StateObservation StateInstalledCompiler

/-- A resolved initializer-list or sealed-role-roster domain source. -/
inductive DomainSource where
  | initial (opener field : String)
  | roster (profile : StateInstalledContext.Profile) (role : String)

/-- The allowed values contributed by one accepted initializer or sealed root. -/
def contribution (source : DomainSource) (act : Act) : FinSet Val :=
  match source with
  | .initial opener field =>
    if act.verb == opener then match act.get field with
      | some (.list values) => FinSet.mk (values.map Scalar.toVal)
      | _ => ⊥
    else ⊥
  | .roster profile role =>
    if act.preds.isEmpty then match StateInstalledContext.cast profile act.addr with
      | some bindings => match bindings.find? (fun binding => binding.role == role) with
          | some binding => FinSet.mk (binding.accounts.map Val.str)
          | none => ⊥
      | none => ⊥
    else ⊥

/-- Union retained domain source contributions over accepted history. -/
def allowed (source : DomainSource) (A : List Act) : FinSet Val := lift (contribution source) A

/-- The actual initializer/context fault checker associated with this domain source. -/
def errorSpec : DomainSource → ErrorSpec
  | .initial opener field => {
      read := domainError opener field
      equiv := fun same => by simp [domainError,initialCarrier_invariant same]
      grow := fun growth => errors_persist (fun _ => False) (.domain opener field)
        (StateContextEvidence.vacuous_closed _) growth }
  | .roster profile _ => StateContextEvidence.spec (StateInstalledContext.evidenceInput profile) false

/-- A resolved verb, keyword, and domain source used by data selection. -/
structure Domain where
  /-- The source performative selected by this declaration. -/
  verb : String
  /-- The message keyword read by this declaration. -/
  key : String
  /-- The authored source field name or the resolved domain source. -/
  source : DomainSource

/-- Test domain membership for the targeted verb, leaving other verbs eligible. -/
def eligible (domain : Domain) (A : List Act) (act : Act) : Bool :=
  if act.verb == domain.verb then match act.get domain.key with
    | none => false
    | some value => FinSet.contains value (allowed domain.source A)
  else true

/-- Select acts satisfying every applicable domain against retained accepted evidence. -/
def select (domains : List Domain) (A : List Act) : List Act :=
  A.filter (fun act => domains.all (fun domain => eligible domain A act))

theorem allowed_setEq (source : DomainSource) {A B : List Act} (same : SetEq A B) : allowed source A = allowed source B :=
  lift_setEq (contribution source) same

theorem allowed_grows (source : DomainSource) {A B : List Act} (growth : ∀ act ∈ A, act ∈ B)
    (value : Val) (member : value ∈ allowed source A) : value ∈ allowed source B := by
  obtain ⟨act,accepted,contributes⟩ := (mem_lift (contribution source)).mp member
  exact (mem_lift (contribution source)).mpr ⟨act,growth act accepted,contributes⟩

theorem eligible_setEq (domain : Domain) {A B : List Act} (same : SetEq A B) (act : Act) :
    eligible domain A act = eligible domain B act := by
  simp only [eligible,allowed_setEq domain.source same]

theorem eligible_grows (domain : Domain) {A B : List Act} (growth : ∀ act ∈ A, act ∈ B)
    (act : Act) (before : eligible domain A act = true) : eligible domain B act = true := by
  by_cases relevant : act.verb = domain.verb
  · cases field : act.get domain.key with
    | none => simp [eligible,relevant,field] at before
    | some value =>
      have member : value ∈ allowed domain.source A := by simpa [eligible,relevant,field,FinSet.contains_eq_true] using before
      simpa [eligible,relevant,field,FinSet.contains_eq_true] using allowed_grows domain.source growth value member
  · simp [eligible,beq_eq_false_iff_ne.mpr relevant]

theorem selected_setEq (domains : List Domain) {A B : List Act} (same : SetEq A B) : SetEq (select domains A) (select domains B) := by
  intro act
  have predicates : (fun domain => eligible domain A act) = (fun domain => eligible domain B act) :=
    funext (fun domain => eligible_setEq domain same act)
  simp only [select,List.mem_filter,same act,predicates]

theorem selected_grows (domains : List Domain) {A B : List Act} (growth : ∀ act ∈ A, act ∈ B) :
    ∀ act ∈ select domains A, act ∈ select domains B := by
  intro act member
  obtain ⟨accepted,selected⟩ := List.mem_filter.mp member
  apply List.mem_filter.mpr
  refine ⟨growth act accepted,?_⟩
  exact List.all_eq_true.mpr (fun domain inside => eligible_grows domain growth act ((List.all_eq_true.mp selected) domain inside))

/-- Guards are attached only for domains relevant to this field's native
selection verbs; their checkers retain initializer/context evidence. -/
def guards (domains : List Domain) (verbs : List String) : List StateInstalledTerm.Guard :=
  (domains.filter (fun domain => verbs.contains domain.verb)).map (fun domain => .certified (errorSpec domain.source))

/-- Domain-aware native closures keep raw metadata for initial/progress while
application data operations see the same resolved selected history. -/
def rawExpression : StateKernel.Expr → Bool
  | .initial .. | .progress _ | .bounded _ => true
  | _ => false

/-- Run a native data expression over selected acts while retaining raw causal metadata. -/
noncomputable def evaluate (context : StateKernelSEC.Context) (domains : List Domain)
    (expression : StateKernel.Expr) (carrier : FinSet Act) : StateKernel.Observation :=
  let A := StateInstalledLegacy.history carrier
  let input := context.input A
  let eligible := if rawExpression expression then A else select domains A
  StateKernel.evaluate {input with acts := eligible} [] expression

/-- Factor a domain-aware native expression through the retained-history carrier. -/
noncomputable def term (context : StateKernelSEC.Context) (domains : List Domain) (expression : StateKernel.Expr)
    (resourceVerbs : String → List String) : StateInstalledTerm.Term StateInstalledLegacy.Value := {
  Carrier := FinSet Act
  state := id
  project := fun carrier => .kernel (evaluate context domains expression carrier)
  guards := (match expression with | .initial opener field => [.domain opener field] | _ => []) ++
    guards domains (expressionVerbs resourceVerbs expression)
  algebra := inferInstance
  state_bottom := rfl
  state_merge := fun _ _ => rfl }

/-- Installation metadata used to recognize a raw domain declaration. Domains
above are resolved IR; callers lowering authored clauses use makeDomain. -/
inductive FieldType where
  | string | number | nonnegative | boolean | list | other
  deriving DecidableEq

/-- Recognized installed verb and field-type metadata used for domain validation. -/
structure Schema where
  /-- The declared performative names. -/
  verbs : List String
  /-- The recognized field types indexed by performative and keyword. -/
  types : List ((String × String) × FieldType)

/-- The closed source forms permitted by authored domain resolution. -/
inductive FieldSource where
  | initial (verb field : String)
  | context (path : List String)
  | other

/-- An authored domain before validating its verb, key type, and source. -/
structure Declaration where
  /-- The source performative selected by this declaration. -/
  verb : String
  /-- The message keyword read by this declaration. -/
  key : String
  /-- The authored source field name or the resolved domain source. -/
  source : String

/-- Validate a domain declaration against the full installed field environment and schema. -/
def makeDomain (profile : StateInstalledContext.Profile) (schema : Schema)
    (fields : List (String × FieldSource)) (declaration : Declaration) : Option Domain := do
  let opener ← profile.definition.opener
  if !schema.verbs.contains declaration.verb || declaration.verb == opener ||
      schema.types.lookup (declaration.verb,declaration.key) != some .string then none else do
    match ← fields.lookup declaration.source with
    | .initial verb field =>
      if verb == opener && schema.types.lookup (verb,field) == some .list then
        some ⟨declaration.verb,declaration.key,.initial verb field⟩ else none
    | .context path => match path with
      | ["thread","roles",role] =>
        if StateInstalledContext.validPath profile.definition path then
          some ⟨declaration.verb,declaration.key,.roster profile role⟩ else none
      | _ => none
    | .other => none

/-- Sealed roster references cannot bypass the closed path recognizer. -/
theorem roster_source_recognized (profile : StateInstalledContext.Profile) (schema : Schema)
    (fields : List (String × FieldSource)) (declaration : Declaration) (role : String)
    (source : fields.lookup declaration.source = some (.context ["thread","roles",role]))
    (unknown : StateInstalledContext.validPath profile.definition ["thread","roles",role] = false) :
    makeDomain profile schema fields declaration = none := by
  cases opener : profile.definition.opener <;> simp [makeDomain,opener,source,unknown]

end CBCL.StateInstalledDomains
