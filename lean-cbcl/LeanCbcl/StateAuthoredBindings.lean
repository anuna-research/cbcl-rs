import LeanCbcl.StateInstalledRecognition
import LeanCbcl.StateFiniteRead
import LeanCbcl.StateInstalledResource

/-! Concrete authored-rule binding over recognized installed metadata. The
inventory includes every legacy head, context paths, finite lifts, domains,
threshold declarations and global freezes. Observation-indexed contributor
sets are built once from the full accepted history and reused at nested cuts.
Literal wire/shape extraction remains the explicit typed metadata boundary. -/
set_option autoImplicit false
namespace CBCL.StateAuthoredBindings
open State StateLift StateLVar StateObservation StateObservationPlan StateInstalledCompiler
open StateInstalledLegacy

/-- A concrete resource configuration with its immutable typed act decoder. -/
structure Resource where
  /-- The checked native resource configuration. -/
  profile : StateInstalledResource.Profile
  /-- Immutable typed resource metadata extraction from an accepted act. -/
  decode : Act → CheckpointEvidence.ResourceData

/-- The authored source inventory; ordinary aliases are normalized before it. -/
inductive Rule where
  | legacy (rule : StateKernelClause.Rule)
  | context (path : List String)
  | finite (lattice : String) (declaration : StateInstalledFinite.Declaration)

/-- Additional state entries retain their actual authored arguments. -/
inductive Entry where
  | field (name : String) (rule : Rule)
  | threshold (name source : String) (elements : List Value)
  | domain (declaration : StateInstalledDomains.Declaration)
  | lattice (declaration : StateFiniteTable.Definition)
  | freeze (field verb : String) (fault : Bool)

/-- Immutable installed metadata shared by every concrete source factory. -/
structure Environment where
  /-- Fixed protocol, clock, signer-rank and causal evidence interpretation. -/
  context : StateKernelSEC.Context
  /-- Recognized dialect and per-address sealed-thread metadata. -/
  profile : StateInstalledContext.Profile
  /-- Recognized performative names and message field types. -/
  schema : StateInstalledDomains.Schema
  /-- Mandatory nonnegative writer shapes used by sum threshold admission. -/
  shapes : List WriterShape
  /-- Concrete resource profiles indexed by installed configuration name. -/
  resources : List (String × Resource)
  /-- Recognized sender roles indexed by performative name. -/
  fromRoles : List (String × String)

/-- Static native freeze dependency footprint, before selecting a history. -/
inductive Footprint where
  | all
  | rawVerbs (names : List String)
  | verbs (names : List String)

/-- Each lowered source retains its raw declaration and freeze dependency set. -/
structure Binding where
  /-- The original authored source form retained for dependency validation. -/
  rule : Rule
  /-- The concrete source term and its source-relative query policy. -/
  definition : StateInstalledLowering.Definition Value
  /-- Raw or domain-selected source verbs governing freeze witnesses. -/
  footprint : Footprint

/-- State names use the concrete parser's bounded lowercase ASCII grammar. -/
def nameCheck (name : String) : Bool :=
  let lower := fun c : Char => decide ('a'.toNat ≤ c.toNat ∧ c.toNat ≤ 'z'.toNat)
  match name.toList with
  | [] => false
  | first :: _ => lower first && decide (name.length ≤ 48) && name.toList.all (fun c =>
      lower c || decide ('0'.toNat ≤ c.toNat ∧ c.toNat ≤ '9'.toNat) || c == '-')

/-- Fields, thresholds and lattices share the native installed name namespace. -/
def declaredNames (entries : List Entry) : List String :=
  entries.filterMap (fun entry => match entry with
    | .field name _ | .threshold name _ _ => some name
    | .lattice declaration => some declaration.name
    | _ => none)

/-- Executable source namespace and rendered-field bound checks. -/
def metadataCheck (environment : Environment) (entries : List Entry) : Bool :=
  let names := declaredNames entries
  let fields := entries.filter (fun entry => match entry with | .field .. | .threshold .. => true | _ => false)
  names.all nameCheck && decide names.Nodup && !fields.isEmpty &&
    decide (fields.length ≤ environment.profile.definition.bounds.maxFields)

/-- Extract raw field metadata over the whole clause, before domain resolution. -/
def rawFields (entries : List Entry) : List (String × Rule) :=
  entries.filterMap (fun entry => match entry with | .field name rule => some (name,rule) | _ => none)

/-- Domain sources are initializer fields or closed context paths. -/
def domainFields (entries : List Entry) : List (String × StateInstalledDomains.FieldSource) :=
  (rawFields entries).map (fun (name,rule) => (name,match rule with
    | .legacy (.initial verb key) => .initial verb key
    | .context path => .context path
    | _ => .other))

/-- Resource dependency verbs come from the same concrete installed profile. -/
def resourceVerbs (environment : Environment) (name : String) : List String :=
  match environment.resources.lookup name with
  | none => []
  | some resource => resource.profile.config.initialVerb :: StateResourcePreflight.operationNames resource.profile.config

/-- Resolve every domain from full-clause metadata, including later sources. -/
def domains (environment : Environment) (entries : List Entry) : Option (List StateInstalledDomains.Domain) :=
  let declarations := entries.filterMap (fun entry => match entry with | .domain declaration => some declaration | _ => none)
  let resourceOperations := (rawFields entries).flatMap (fun (_,rule) => match rule with
    | .legacy (.boundedCounter name) => resourceVerbs environment name
    | _ => [])
  if declarations.any (fun declaration => resourceOperations.contains declaration.verb ||
      ["escrow-prev","escrow-deps","escrow-nonce"].contains declaration.key) then none else
  declarations.mapM (StateInstalledDomains.makeDomain environment.profile environment.schema (domainFields entries))

/-- Validate every authored lattice, including declarations not used by a lift. -/
def tables (environment : Environment) (entries : List Entry) : Option (List (String × StateFiniteTable.Verified)) :=
  (entries.filterMap (fun entry => match entry with | .lattice declaration => some declaration | _ => none)).mapM
    (fun declaration => (StateFiniteTable.compile environment.profile.definition.bounds.maxList declaration).map
      (fun verified => (declaration.name,verified)))

/-- Earlier original legacy rules are retained for aggregate source checks. -/
def legacyFields (earlier : List (String × Binding)) : List (String × StateKernelClause.Rule) :=
  earlier.filterMap (fun (name,binding) => match binding.rule with
    | .legacy rule => some (name,rule) | _ => none)

/-- Native freeze footprints follow earlier aggregate sources without aliases. -/
def legacyFootprint (environment : Environment) (earlier : List (String × Binding)) : StateKernelClause.Rule → Footprint
  | .initial verb _ | .existsRule verb | .count verb | .events verb _ | .setUnion verb _
  | .values verb _ | .valuesPerKey verb _ _ none | .lwwRegister verb _ _ | .lwwPerSigner verb _ _
  | .lwwMap verb _ _ _ none => .verbs [verb]
  | .valuesPerKey verb _ _ (some delete) | .lwwMap verb _ _ _ (some delete) => .verbs [verb,delete]
  | .observedSet add remove _ | .counter add remove _ => .verbs [add,remove]
  | .histogram source | .sum source => ((earlier.lookup source).map Binding.footprint).getD (.verbs [])
  | .progress verb => .rawVerbs [verb]
  | .boundedCounter name => .rawVerbs (resourceVerbs environment name)

/-- Whole context/observation freezes depend on every accepted act; sealed
thread opener projections depend on the configured opener verb only. -/
def contextFootprint (environment : Environment) (path : List String) : Footprint :=
  if path.isEmpty || path.head? == some "observation" then .all else
  if path == ["thread"] || path == ["thread","opener"] then
    .verbs environment.profile.definition.opener.toList else .verbs []

/-- Native data primitives use selected history; closure progress keeps raw history. -/
noncomputable def primitive (environment : Environment) (resolvedDomains : List StateInstalledDomains.Domain)
    (expression : StateKernel.Expr) (rule : StateKernelClause.Rule) : StateInstalledLowering.Definition Value :=
  let term := StateInstalledDomains.term environment.context resolvedDomains expression (resourceVerbs environment)
  match rule with
  | .progress _ => .native (StateInstalledTerm.source term) (queryPolicy environment.shapes rule)
  | _ => .factored term ((queryPolicy environment.shapes rule).map (fun policy =>
      ⟨(fun query state => policy.test query (term.project state)),policy.check⟩))

/-- Lower each concrete source through its closed factory; no caller-supplied
source display, threshold test or fault classifier is accepted here. -/
noncomputable def bind (environment : Environment) (resolvedDomains : List StateInstalledDomains.Domain)
    (resolvedTables : List (String × StateFiniteTable.Verified)) (earlier : List (String × Binding)) : Rule → Option Binding
  | .context path => match StateInstalledContext.make environment.profile path with
      | none => none
      | some definition => some ⟨.context path,definition,contextFootprint environment path⟩
  | .finite lattice declaration => match resolvedTables.lookup lattice with
      | none => none
      | some table => (StateInstalledFinite.make environment.schema table resolvedDomains declaration).map
          (fun field => ⟨.finite lattice declaration,StateFiniteRead.definition field,.verbs [declaration.verb]⟩)
  | .legacy rule =>
      let footprint := legacyFootprint environment earlier rule
      match rule with
      | .histogram source => match (legacyFields earlier).lookup source with
          | none => none
          | some prior => if StateKernelClause.histogramAllowed prior then
              some ⟨.legacy rule,.derived histogramPost source,footprint⟩ else none
      | .sum source => match (legacyFields earlier).lookup source with
          | none => none
          | some prior => match StateKernelClause.mapPlanOf prior with
              | none => none
              | some _ => some ⟨.legacy rule,.derived sumPost source,footprint⟩
      | .boundedCounter name => match environment.resources.lookup name with
          | none => none
          | some resource =>
            let term := StateInstalledResource.term resource.profile resource.decode
            let guarded := { term with guards := term.guards ++ StateInstalledDomains.guards resolvedDomains (resourceVerbs environment name) }
            some ⟨.legacy rule,.factored guarded none,footprint⟩
      | _ => match StateKernelClause.compileRule [] rule with
          | none => none
          | some expression => some ⟨.legacy rule,primitive environment resolvedDomains expression rule,footprint⟩

/-- Lower ordered fields and thresholds while retaining source metadata.
Domains, lattices and freezes have already been collected from the whole clause. -/
noncomputable def declarations (environment : Environment) (resolvedDomains : List StateInstalledDomains.Domain)
    (resolvedTables : List (String × StateFiniteTable.Verified)) (earlier : List (String × Binding)) :
    List Entry → Option (List (StateInstalledLowering.Declaration Value) × List (String × Binding))
  | [] => some ([],earlier)
  | .field name rule :: rest => do
      let binding ← bind environment resolvedDomains resolvedTables earlier rule
      let (tail,bindings) ← declarations environment resolvedDomains resolvedTables ((name,binding)::earlier) rest
      some (.field name binding.definition::tail,bindings)
  | .threshold name source elements :: rest => do
      let (tail,bindings) ← declarations environment resolvedDomains resolvedTables earlier rest
      some (.threshold name source elements::tail,bindings)
  | _ :: rest => declarations environment resolvedDomains resolvedTables earlier rest

/-- Retained native contributors are selected from the full observation once. -/
def contributes (resolvedDomains : List StateInstalledDomains.Domain) (history : List Act) (footprint : Footprint) : Act → Prop :=
  match footprint with
  | .all => fun act => act.addr ∈ history.map Act.addr
  | .rawVerbs names => fun act => ∃ writer ∈ history, writer.verb ∈ names ∧ writer.addr = act.addr
  | .verbs names => fun act => ∃ writer ∈ StateInstalledDomains.select resolvedDomains history,
      writer.verb ∈ names ∧ writer.addr = act.addr

/-- History-independent freeze metadata resolved from actual source fields. -/
structure FreezeTemplate where
  /-- The source field decorated by this freeze. -/
  field : String
  /-- The accepted performative that selects the causal cut. -/
  verb : String
  /-- Raw or domain-selected source dependency verbs. -/
  footprint : Footprint
  /-- Whether excluded writes fault instead of being superseded. -/
  policy : Bool

/-- Resolve global freeze targets and sender-role requirements once. Threshold
outputs are not source bindings and cannot be decorated as native fields. -/
def freezeTemplates (environment : Environment) (bindings : List (String × Binding)) (entries : List Entry) :
    Option (List FreezeTemplate) :=
  (entries.filterMap (fun entry => match entry with
    | .freeze field verb policy => some (field,verb,policy) | _ => none)).mapM
    (fun (field,verb,policy) => match bindings.lookup field with
      | none => none
      | some binding => do
        let senderRole ← environment.fromRoles.lookup verb
        if senderRole.isEmpty || !environment.schema.verbs.contains verb then none else
        some ⟨field,verb,binding.footprint,policy⟩)

/-- The only observation-dependent phase fixes retained contributors from the
full accepted history; the same predicates are reused at every nested cut. -/
def materialize (resolvedDomains : List StateInstalledDomains.Domain) (history : List Act)
    (templates : List FreezeTemplate) : List (String × FreezeSpec) :=
  templates.map (fun template => (template.field,
    ⟨template.verb,contributes resolvedDomains history template.footprint,template.policy⟩))

/-- Native freeze decorations for recognized whole-clause source metadata. -/
def freezes (environment : Environment) (resolvedDomains : List StateInstalledDomains.Domain)
    (history : List Act) (bindings : List (String × Binding)) (entries : List Entry) : Option (List (String × FreezeSpec)) :=
  (freezeTemplates environment bindings entries).map (materialize resolvedDomains history)

/-- Concrete source lowering before full-observation freeze specialization. -/
structure Prepared where
  /-- Ordered concrete source declarations and source-relative thresholds. -/
  declarations : List (StateInstalledLowering.Declaration Value)
  /-- Validated raw domain selectors shared by all source factories. -/
  domains : List StateInstalledDomains.Domain
  /-- Resolved global freeze targets, verbs and source footprints. -/
  freezes : List FreezeTemplate

/-- Lower concrete authored entries before source-relative installation validation. -/
noncomputable def lowerStatic (environment : Environment) (entries : List Entry) : Option Prepared :=
  if !metadataCheck environment entries then none else
  match domains environment entries with
  | none => none
  | some resolvedDomains => match tables environment entries with
      | none => none
      | some resolvedTables => match declarations environment resolvedDomains resolvedTables [] entries with
          | none => none
          | some (lowered,bindings) => match freezeTemplates environment bindings entries with
              | none => none
              | some resolvedFreezes => some ⟨lowered,resolvedDomains,resolvedFreezes⟩

/-- Materialize the statically lowered clause at one observation. -/
def clauseAt (prepared : Prepared) (history : List Act) : StateInstalledLowering.Clause Value :=
  ⟨prepared.declarations,materialize prepared.domains history prepared.freezes⟩

/-- Freeze policies are independent of observation-specific contributor sets. -/
theorem stable_source_history (resolvedDomains : List StateInstalledDomains.Domain)
    (templates : List FreezeTemplate) (A B : List Act) (name : String) :
    StateInstalledLowering.stableSource (materialize resolvedDomains A templates) name =
      StateInstalledLowering.stableSource (materialize resolvedDomains B templates) name := by
  induction templates with
  | nil => rfl
  | cons template rest ih =>
    by_cases same : name = template.field
    · subst name; simp [StateInstalledLowering.stableSource,materialize]
    · simpa [StateInstalledLowering.stableSource,materialize,List.lookup,beq_eq_false_iff_ne.mpr same] using ih

/-- Complete metadata validation can run once, before observation specialization. -/
theorem metadata_history (prepared : Prepared) (A B : List Act) :
    StateInstalledLowering.ValidMetadata (clauseAt prepared A) ↔ StateInstalledLowering.ValidMetadata (clauseAt prepared B) := by
  have names : (materialize prepared.domains A prepared.freezes).map Prod.fst =
      (materialize prepared.domains B prepared.freezes).map Prod.fst := by
    simp [materialize,List.map_map,Function.comp_def]
  have stable : StateInstalledLowering.stableDeclarations (materialize prepared.domains A prepared.freezes) prepared.declarations =
      StateInstalledLowering.stableDeclarations (materialize prepared.domains B prepared.freezes) prepared.declarations := by
    unfold StateInstalledLowering.stableDeclarations
    apply congrArg (fun predicate => prepared.declarations.all predicate)
    funext declaration
    cases declaration with
    | field _ _ => rfl
    | threshold _ source _ => exact stable_source_history prepared.domains prepared.freezes A B source
  simp only [clauseAt,StateInstalledLowering.ValidMetadata]
  rw [names,stable]

/-- Check policy admission, backward references and all freeze/name metadata
without constructing or executing any observation plan. -/
noncomputable def preparedCheck (prepared : Prepared) : Bool :=
  decide (StateInstalledLowering.ValidMetadata (clauseAt prepared [])) &&
    StateInstalledRecognition.check [] [] prepared.declarations

/-- Complete history-independent validation of modeled authored metadata,
source policies and backward references; native parser/R7 extraction is separate. -/
noncomputable def prepareStatic (environment : Environment) (entries : List Entry) : Option Prepared :=
  (lowerStatic environment entries).filter preparedCheck

/-- Successful static installation supplies every compiler premise at every history. -/
theorem static_preparation_sound (environment : Environment) (entries : List Entry) (prepared : Prepared)
    (accepted : prepareStatic environment entries = some prepared) (history : List Act) :
    StateInstalledLowering.ValidMetadata (clauseAt prepared history) ∧
      StateInstalledLowering.WellFormed [] [] prepared.declarations := by
  cases lowered : lowerStatic environment entries with
  | none => simp [prepareStatic,lowered] at accepted
  | some raw =>
    by_cases checked : preparedCheck raw = true
    · have same : raw = prepared := by simpa [prepareStatic,lowered,Option.filter,checked] using accepted
      subst prepared
      have parts : StateInstalledLowering.ValidMetadata (clauseAt raw []) ∧
          StateInstalledRecognition.check [] [] raw.declarations = true := by
        simpa only [preparedCheck,Bool.and_eq_true,decide_eq_true_eq] using checked
      exact ⟨(metadata_history raw [] history).mp parts.1,(StateInstalledRecognition.check_iff _ _ _).mp parts.2⟩
    · simp [prepareStatic,lowered,Option.filter,checked] at accepted

/-- Prepare the full concrete source clause for one accepted observation. -/
noncomputable def prepare (environment : Environment) (entries : List Entry) (history : List Act) :
    Option (StateInstalledLowering.Clause Value) :=
  (prepareStatic environment entries).map (fun prepared =>
    ⟨prepared.declarations,materialize prepared.domains history prepared.freezes⟩)

/-- Compile the actual concrete authored source bindings for this observation. -/
noncomputable def compile (environment : Environment) (entries : List Entry) (history : List Act) : Option (Plans Value) :=
  (prepare environment entries history).bind StateInstalledLowering.compile

/-- Independent history-indexed native reader composition for the same sources. -/
noncomputable def interpret (world : Act → Prop) (environment : Environment) (entries : List Entry)
    (history : List Act) : Option (Readers Value) :=
  (prepare environment entries history).bind (StateInstalledLowering.interpret world)

/-- The whole concrete source family feeds the installed-rule/plan refinement,
including backward thresholds, derived sources and global freeze decorations. -/
theorem authored_binding_refinement (world : Act → Prop) (environment : Environment) (entries : List Entry)
    (history : List Act) : FieldsCorrespond world (compile environment entries history) (interpret world environment entries history) := by
  cases prepared : prepare environment entries history with
  | none => simp [compile,interpret,prepared,FieldsCorrespond]
  | some clause =>
    simpa [compile,interpret,prepared] using StateInstalledLowering.native_installed_compiler_refinement world clause

/-- Successful authored preparation compiles without assumed metadata or
reference well-formedness; installation has constructed those obligations. -/
theorem prepared_compiler_complete (environment : Environment) (entries : List Entry) (history : List Act)
    (clause : StateInstalledLowering.Clause Value) (prepared : prepare environment entries history = some clause) :
    ∃ plans, compile environment entries history = some plans := by
  cases installed : prepareStatic environment entries with
  | none => simp [prepare,installed] at prepared
  | some metadata =>
    have same : clauseAt metadata history = clause := by simpa [prepare,installed,clauseAt] using prepared
    obtain ⟨valid,wellFormed⟩ := static_preparation_sound environment entries metadata installed history
    rw [same] at valid
    have references : StateInstalledLowering.WellFormed [] [] clause.declarations := by simpa [← same,clauseAt] using wellFormed
    obtain ⟨plans,compiled⟩ := StateInstalledLowering.native_installed_compiler_complete clause valid references
    exact ⟨plans,by simpa [compile,prepared] using compiled⟩

/-- Authored preparation and compilation accept exactly the same clauses. -/
theorem preparation_compilation_iff (environment : Environment) (entries : List Entry) (history : List Act) :
    (prepare environment entries history).isSome = (compile environment entries history).isSome := by
  cases prepared : prepare environment entries history with
  | none => simp [compile,prepared]
  | some clause =>
    obtain ⟨plans,compiled⟩ := prepared_compiler_complete environment entries history clause prepared
    simp [compiled]

/-- Strengthening static preparation preserves every result of the earlier
partial-lowering pipeline, including rejection; no compilable clause is lost. -/
theorem preparation_preserves_compilation (environment : Environment) (entries : List Entry) (history : List Act) :
    compile environment entries history = (lowerStatic environment entries).bind
      (fun prepared => StateInstalledLowering.compile (clauseAt prepared history)) := by
  cases lowered : lowerStatic environment entries with
  | none => simp [compile,prepare,prepareStatic,lowered]
  | some raw =>
    by_cases checked : preparedCheck raw = true
    · simp [compile,prepare,prepareStatic,lowered,Option.filter,checked,clauseAt]
    · have rejected : StateInstalledLowering.compile (clauseAt raw history) = none := by
        cases compiled : StateInstalledLowering.compile (clauseAt raw history) with
        | none => rfl
        | some plans =>
          have valid := (StateInstalledRecognition.compile_iff (clauseAt raw history)).mp (by simp [compiled])
          have staticValid := (metadata_history raw history []).mp valid.1
          have accepted : preparedCheck raw = true := by
            simp only [preparedCheck,Bool.and_eq_true,decide_eq_true_eq]
            exact ⟨staticValid,valid.2⟩
          exact False.elim (checked accepted)
      simp [compile,prepare,prepareStatic,lowered,Option.filter,checked,rejected]

/-- Fixed contributor metadata respects full-observation set equality. -/
theorem contributes_setEq (resolvedDomains : List StateInstalledDomains.Domain) {A B : List Act}
    (same : SetEq A B) (footprint : Footprint) :
    contributes resolvedDomains A footprint = contributes resolvedDomains B footprint := by
  funext act
  apply propext
  cases footprint with
  | all =>
    simp only [contributes,List.mem_map]
    constructor
    · rintro ⟨writer,member,address⟩; exact ⟨writer,(same writer).mp member,address⟩
    · rintro ⟨writer,member,address⟩; exact ⟨writer,(same writer).mpr member,address⟩
  | rawVerbs names =>
    have membership : ∀ act, act ∈ A ↔ act ∈ B := same
    simp only [contributes,membership]
  | verbs names =>
    have selected := StateInstalledDomains.selected_setEq resolvedDomains same
    have membership : ∀ act, act ∈ StateInstalledDomains.select resolvedDomains A ↔
      act ∈ StateInstalledDomains.select resolvedDomains B := selected
    simp only [contributes,membership]

/-- Native retained contributor sets can only gain witnesses with accepted history. -/
theorem contributes_grows (resolvedDomains : List StateInstalledDomains.Domain) {A B : List Act}
    (growth : ∀ act ∈ A, act ∈ B) (footprint : Footprint) :
    ∀ act, contributes resolvedDomains A footprint act → contributes resolvedDomains B footprint act := by
  intro act member
  cases footprint with
  | all =>
    obtain ⟨writer,inside,address⟩ := List.mem_map.mp member
    exact List.mem_map.mpr ⟨writer,growth writer inside,address⟩
  | rawVerbs names =>
    obtain ⟨writer,inside,verb,address⟩ := member
    exact ⟨writer,growth writer inside,verb,address⟩
  | verbs names =>
    obtain ⟨writer,inside,verb,address⟩ := member
    exact ⟨writer,StateInstalledDomains.selected_grows resolvedDomains growth writer inside,verb,address⟩

/-- Equal accepted sets generate exactly equal global freeze decorations. -/
theorem freezes_setEq (environment : Environment) (resolvedDomains : List StateInstalledDomains.Domain)
    (bindings : List (String × Binding)) (entries : List Entry) {A B : List Act} (same : SetEq A B) :
    freezes environment resolvedDomains A bindings entries = freezes environment resolvedDomains B bindings entries := by
  cases template : freezeTemplates environment bindings entries <;>
    simp [freezes,template,materialize,contributes_setEq resolvedDomains same]

/-- History-indexed preparation preserves all metadata on equal accepted sets. -/
theorem prepare_setEq (environment : Environment) (entries : List Entry) {A B : List Act} (same : SetEq A B) :
    prepare environment entries A = prepare environment entries B := by
  simp only [prepare,materialize,contributes_setEq _ same]

/-- Observation-indexed compilation is invariant under order and duplicates. -/
theorem compile_setEq (environment : Environment) (entries : List Entry) {A B : List Act} (same : SetEq A B) :
    compile environment entries A = compile environment entries B := by
  rw [compile,compile,prepare_setEq environment entries same]

/-- Equal accepted histories yield the same native readers and extensionally
equal whole-clause observations, including regenerated freeze metadata. -/
theorem authored_observations_setEq (world : Act → Prop) (environment : Environment) (entries : List Entry)
    {A B : List Act} (uniqueA : NodupAddr A) (uniqueB : NodupAddr B) (same : SetEq A B)
    (closedA : CausallyClosed world A) (closedB : CausallyClosed world B)
    (plans : Plans Value) (compiled : compile environment entries A = some plans) :
    ∃ readers, interpret world environment entries A = some readers ∧
      interpret world environment entries B = some readers ∧
      readers.map (fun (name,reader) => (name,reader A)) = readers.map (fun (name,reader) => (name,reader B)) := by
  cases prepared : prepare environment entries A with
  | none => simp [compile,prepared] at compiled
  | some clause =>
    have compiledClause : StateInstalledLowering.compile clause = some plans := by simpa [compile,prepared] using compiled
    obtain ⟨readers,interpreted,equal⟩ := StateInstalledLowering.native_installed_observations_setEq world clause plans
      compiledClause uniqueA uniqueB same closedA closedB
    have preparedB : prepare environment entries B = some clause := (prepare_setEq environment entries same).symm.trans prepared
    exact ⟨readers,by simp [interpret,prepared,interpreted],by simp [interpret,preparedB,interpreted],equal⟩

end CBCL.StateAuthoredBindings
