import LeanCbcl.StateOutputConvergence

/-! Successful emitted thresholds return installed alternatives. Singleton
policies agree independently of source presentation and raw scope. -/
set_option autoImplicit false
namespace CBCL.StateOutputThresholdAgreement
open State StateObservationPlan StateOutputCompiler
open StateAuthoredBindings StateInstalledLowering StateInstalledLegacy

/-- Closure dispatch can only return a supplied alternative. -/
theorem closure_reached_member {V : Type} (alternatives : List V) (test : V → V → Bool)
    (value : StateReaderValues.Result V) (result : V)
    (reached : Query.run (.closure alternatives test) [] value = .data (.reached result)) :
    result ∈ alternatives := by
  unfold Query.run StateRuleRefinement.nativeClosureThreshold at reached
  cases current : StateReaderValues.unfrozen value with
  | fault evidence => simp [current] at reached
  | data datum =>
    simp only [current] at reached
    cases payload : datum.payload with
    | none => simp [payload] at reached
    | some raw =>
      cases found : alternatives.find? (fun q => test q raw) with
      | none => simp [payload,found] at reached
      | some selected =>
        have same : selected = result := by simpa [payload,found] using reached
        subst selected
        exact List.mem_of_find?_eq_some found

/-- Raw dispatch can only return a supplied alternative, including at a cut. -/
theorem raw_reached_member {V C : Type} (alternatives : List V) (test : V → C → Bool)
    (state : StateLift.FinSet Act → C) (history : List Act)
    (value : StateReaderValues.Result V) (result : V)
    (reached : Query.run (.raw alternatives test state) history value = .data (.reached result)) :
    result ∈ alternatives := by
  cases value with
  | fault evidence => simp [Query.run,StateInstalledCompiler.nativeRawThreshold] at reached
  | data datum =>
    cases found : alternatives.find? (fun q => test q (state (StateLVar.rawHistory history))) with
    | none => simp [Query.run,StateInstalledCompiler.nativeRawThreshold,found] at reached
    | some selected =>
      have same : selected = result := by
        simpa [Query.run,StateInstalledCompiler.nativeRawThreshold,found] using reached
      subst selected
      exact List.mem_of_find?_eq_some found

/-- The native installation check admits exactly one alternative. -/
theorem read_check_singleton (allowed : StateInstalledLegacy.Element → Bool)
    (elements : List StateInstalledLegacy.Value)
    (checked : StateInstalledLegacy.readCheck allowed elements = true) :
    ∃ element, elements = [.element element] ∧ allowed element = true := by
  cases elements with
  | nil => simp [StateInstalledLegacy.readCheck] at checked
  | cons value rest =>
    cases rest with
    | cons _ _ => simp [StateInstalledLegacy.readCheck] at checked
    | nil =>
      cases value <;> simp_all [StateInstalledLegacy.readCheck]

/-- Alternatives retained by ordinary emitted query strategies. Generic finite
extension code has its own carrier and is deliberately outside this projection. -/
def alternatives {V : Type} : Query V → Option (List V)
  | .closure elements _ | .raw elements _ _ => some elements
  | .finite _ _ => none

/-- Ordinary strategy projection recovers every successful result's membership. -/
theorem reached_member {V : Type} (query : Query V) (elements : List V)
    (history : List Act) (value : StateReaderValues.Result V) (result : V)
    (shape : alternatives query = some elements)
    (reached : query.run history value = .data (.reached result)) : result ∈ elements := by
  cases query with
  | closure queries test =>
    have same : queries = elements := Option.some.inj shape
    subst queries
    exact closure_reached_member elements test value result reached
  | raw queries test state =>
    have same : queries = elements := Option.some.inj shape
    subst queries
    exact raw_reached_member elements test state history value result reached
  | finite spec embed => simp [alternatives] at shape

/-- Actual ordinary query compilation retains exactly the authored alternatives. -/
theorem compiled_alternatives {V : Type} (definition : StateInstalledLowering.Definition V)
    (elements : List V) (query : Query V)
    (plain : StateAuthoredOutputReplay.PlainDefinition definition)
    (compiled : compileQuery elements definition = some query) :
    alternatives query = some elements := by
  cases definition with
  | native source policy =>
    cases policy with
    | none => simp [compileQuery] at compiled
    | some policy =>
      cases check : policy.check elements <;> simp [compileQuery,check] at compiled
      subst query
      rfl
  | factored term policy =>
    cases policy with
    | none => simp [compileQuery] at compiled
    | some policy =>
      cases check : policy.check elements <;> simp [compileQuery,check] at compiled
      subst query
      rfl
  | lattice field => simp [StateAuthoredOutputReplay.PlainDefinition] at plain
  | derived source post => simp [compileQuery] at compiled
  | pair left right post => simp [compileQuery] at compiled

/-- Independently compiled singleton queries cannot return different successful
answers, even when their source values and source-owned raw cuts differ. -/
theorem compiled_singleton_success_agreement {V : Type}
    (leftDefinition rightDefinition : StateInstalledLowering.Definition V)
    (element leftResult rightResult : V) (leftQuery rightQuery : Query V)
    (leftPlain : StateAuthoredOutputReplay.PlainDefinition leftDefinition)
    (rightPlain : StateAuthoredOutputReplay.PlainDefinition rightDefinition)
    (leftCompiled : compileQuery [element] leftDefinition = some leftQuery)
    (rightCompiled : compileQuery [element] rightDefinition = some rightQuery)
    (leftHistory rightHistory : List Act)
    (leftValue rightValue : StateReaderValues.Result V)
    (leftReached : leftQuery.run leftHistory leftValue = .data (.reached leftResult))
    (rightReached : rightQuery.run rightHistory rightValue = .data (.reached rightResult)) :
    leftResult = rightResult := by
  have left := reached_member leftQuery [element] leftHistory leftValue leftResult
    (compiled_alternatives leftDefinition [element] leftQuery leftPlain leftCompiled) leftReached
  have right := reached_member rightQuery [element] rightHistory rightValue rightResult
    (compiled_alternatives rightDefinition [element] rightQuery rightPlain rightCompiled) rightReached
  have first : leftResult = element := by simpa using left
  have second : rightResult = element := by simpa using right
  exact first.trans second.symm

/-- Every successfully compiled legacy primitive threshold has one alternative;
this follows from the installed factory, independently of a displayed value. -/
theorem primitive_singleton (environment : StateAuthoredBindings.Environment)
    (domains : List StateInstalledDomains.Domain) (expression : StateKernel.Expr)
    (rule : StateKernelClause.Rule) (elements : List StateInstalledLegacy.Value)
    (query : Query StateInstalledLegacy.Value)
    (compiled : compileQuery elements (StateAuthoredBindings.primitive environment domains expression rule) = some query) :
    ∃ element, elements = [.element element] := by
  cases rule <;>
    simp [StateAuthoredBindings.primitive,StateInstalledLegacy.queryPolicy,compileQuery] at compiled
  all_goals exact (read_check_singleton _ _ compiled.1).imp (fun _ proof => proof.1)

/-- A policy whose successful installation admits only one authored element. -/
def SingletonPolicy (definition : StateInstalledLowering.Definition StateInstalledLegacy.Value) : Prop :=
  ∀ elements query, compileQuery elements definition = some query →
    ∃ element, elements = [.element element]

/-- Context threshold installation is restricted to a singleton roster query. -/
theorem context_singleton (profile : StateInstalledContext.Profile) (projection : List String)
    (definition : StateInstalledLowering.Definition StateInstalledLegacy.Value)
    (installed : StateInstalledContext.make profile projection = some definition) :
    SingletonPolicy definition := by
  unfold StateInstalledContext.make at installed
  split at installed
  · cases Option.some.inj installed
    intro elements query compiled
    cases policy : StateInstalledContext.queryPolicy projection with
    | none => simp [compileQuery,policy] at compiled
    | some strategy =>
      obtain ⟨role,rfl⟩ := StateInstalledContext.roster_query_only projection strategy policy
      simp [compileQuery,StateInstalledContext.queryPolicy] at compiled
      exact (read_check_singleton _ _ compiled.1).imp (fun _ proof => proof.1)
  · contradiction

/-- The authored binder emits singleton policies or a concrete verified finite
field. This is a complete classification of source-rule heads, not a premise
supplied by the caller of an agreement theorem. -/
theorem bind_query_classification (environment : StateAuthoredBindings.Environment)
    (domains : List StateInstalledDomains.Domain)
    (tables : List (String × StateFiniteTable.Verified))
    (earlier : List (String × StateAuthoredBindings.Binding))
    (rule : StateAuthoredBindings.Rule) (binding : StateAuthoredBindings.Binding)
    (bound : StateAuthoredBindings.bind environment domains tables earlier rule = some binding) :
    SingletonPolicy binding.definition ∨
      ∃ field, binding.definition = StateFiniteRead.definition field := by
  cases rule with
  | context projection =>
    cases installed : StateInstalledContext.make environment.profile projection with
    | none => simp [StateAuthoredBindings.bind,installed] at bound
    | some definition =>
      have same : (⟨.context projection,definition,StateAuthoredBindings.contextFootprint environment projection⟩ : StateAuthoredBindings.Binding) = binding := by
        simpa [StateAuthoredBindings.bind,installed] using bound
      subst binding
      exact Or.inl (context_singleton environment.profile projection definition installed)
  | finite lattice declaration =>
    cases table : tables.lookup lattice with
    | none => simp [StateAuthoredBindings.bind,table] at bound
    | some verified =>
      cases field : StateInstalledFinite.make environment.schema verified domains declaration with
      | none => simp [StateAuthoredBindings.bind,table,field] at bound
      | some source =>
        have same : (⟨.finite lattice declaration,StateFiniteRead.definition source,.verbs [declaration.verb]⟩ : StateAuthoredBindings.Binding) = binding := by
          simpa [StateAuthoredBindings.bind,table,field] using bound
        subst binding
        exact Or.inr ⟨source,rfl⟩
  | legacy rule =>
    apply Or.inl
    cases rule
    case histogram reference =>
      simp only [StateAuthoredBindings.bind] at bound
      split at bound
      · contradiction
      · split at bound
        · cases Option.some.inj bound
          intro elements query compiled
          simp [compileQuery] at compiled
        · contradiction
    case sum reference =>
      simp only [StateAuthoredBindings.bind] at bound
      split at bound
      · contradiction
      · split at bound
        · contradiction
        · cases Option.some.inj bound
          intro elements query compiled
          simp [compileQuery] at compiled
    case boundedCounter name =>
      cases resource : environment.resources.lookup name with
      | none => simp [StateAuthoredBindings.bind,resource] at bound
      | some profile =>
        simp only [StateAuthoredBindings.bind,resource] at bound
        cases Option.some.inj bound
        intro elements query compiled
        simp [compileQuery] at compiled
    all_goals
      simp only [StateAuthoredBindings.bind,StateKernelClause.compileRule,StateKernelClause.mapPlanOf] at bound
      cases Option.some.inj bound
      intro elements query compiled
      dsimp only at compiled
      exact primitive_singleton environment domains _ _ elements query compiled

/-- The closed authored policy inventory: singleton or verified finite field. -/
def ClassifiedDefinition (definition : StateInstalledLowering.Definition StateInstalledLegacy.Value) : Prop :=
  StateAuthoredOutputReplay.PlainDefinition definition ∧
    (SingletonPolicy definition ∨ ∃ field, definition = StateFiniteRead.definition field)

/-- Field declarations retain the source-owned policy classification. -/
def ClassifiedDeclaration : StateInstalledLowering.Declaration StateInstalledLegacy.Value → Prop
  | .field _ definition => ClassifiedDefinition definition
  | .threshold .. => True

theorem declarations_classified (environment : Environment) (domains : List StateInstalledDomains.Domain)
    (tables : List (String × StateFiniteTable.Verified)) (entries : List Entry)
    (earlier : List (String × Binding)) (output : List (Declaration Value)) (bindings : List (String × Binding))
    (lowered : declarations environment domains tables earlier entries = some (output,bindings)) :
    ∀ declaration ∈ output, ClassifiedDeclaration declaration := by
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
          have current : ClassifiedDefinition binding.definition :=
            ⟨StateAuthoredOutputReplay.bind_plain environment domains tables earlier rule binding head,
             bind_query_classification environment domains tables earlier rule binding head⟩
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
    | domain _ | lattice _ | freeze _ _ _ =>
      exact ih earlier output bindings (by simpa [declarations] using lowered)

/-- Static preparation supplies the actual plain-query declaration inventory. -/
theorem prepared_declarations_classified (environment : Environment) (entries : List Entry) (prepared : Prepared)
    (installed : prepareStatic environment entries = some prepared) :
    ∀ declaration ∈ prepared.declarations, ClassifiedDeclaration declaration := by
  obtain ⟨tables,bindings,_,_,lowered,_⟩ := StateAuthoredSourceProvenance.static_trace environment entries prepared installed
  exact declarations_classified environment prepared.domains tables entries [] prepared.declarations bindings lowered

/-- Every definition visible to a threshold keeps the authored policy inventory. -/
def ClassifiedDefinitions (definitions : Definitions StateInstalledLegacy.Value) : Prop :=
  ∀ name definition, definitions.lookup name = some definition → ClassifiedDefinition definition

/-- Extending the ordered metadata dictionary preserves its query inventory. -/
theorem extend_classified (definitions : Definitions StateInstalledLegacy.Value) (declaration : Declaration StateInstalledLegacy.Value)
    (prior : ClassifiedDefinitions definitions) (checked : ClassifiedDeclaration declaration) :
    ClassifiedDefinitions (extend definitions declaration) := by
  intro query source found
  cases declaration with
  | field name definition =>
    simp only [extend,List.lookup_cons] at found
    split at found
    · cases Option.some.inj found
      exact checked
    · exact prior query source found
  | threshold name sourceName elements => exact prior query source found

/-- Emitted query strategies retain either singleton alternatives or the exact
concrete finite factory whose incompatibility theorem governs them. -/
def ClassifiedQuery (query : Query StateInstalledLegacy.Value) : Prop :=
  (∃ element, alternatives query = some [.element element]) ∨
    ∃ field elements, compileQuery elements (StateFiniteRead.definition field) = some query

/-- Source classification survives successful query compilation. -/
theorem compile_query_classified (elements : List StateInstalledLegacy.Value)
    (definition : StateInstalledLowering.Definition StateInstalledLegacy.Value)
    (query : Query StateInstalledLegacy.Value) (checked : ClassifiedDefinition definition)
    (compiled : compileQuery elements definition = some query) : ClassifiedQuery query := by
  obtain ⟨plain,checked⟩ := checked
  rcases checked with singleton | ⟨field,rfl⟩
  · obtain ⟨element,rfl⟩ := singleton elements query compiled
    apply Or.inl
    exact ⟨element,compiled_alternatives definition _ query plain compiled⟩
  · exact Or.inr ⟨field,elements,compiled⟩

/-- Ordinary fields impose no threshold classification obligation. -/
def ClassifiedOutput : Output StateInstalledLegacy.Value → Prop
  | .field .. => True
  | .threshold _ _ query _ => ClassifiedQuery query

/-- Compiling one output preserves its source-owned policy classification. -/
theorem compile_one_classified (plans : StateInstalledCompiler.Plans StateInstalledLegacy.Value) (definitions : Definitions StateInstalledLegacy.Value)
    (declaration : Declaration StateInstalledLegacy.Value) (output : Output StateInstalledLegacy.Value) (prior : ClassifiedDefinitions definitions)
    (compiled : compileOne plans definitions declaration = some output) : ClassifiedOutput output := by
  cases declaration with
  | field name definition =>
    cases found : plans.lookup name with
    | none => simp [compileOne,found] at compiled
    | some source =>
      have same : Output.field name source = output := by simpa [compileOne,found] using compiled
      subst output
      trivial
  | threshold name sourceName elements =>
    cases plan : plans.lookup sourceName with
    | none => simp [compileOne,plan] at compiled
    | some source =>
      cases found : definitions.lookup sourceName with
      | none => simp [compileOne,plan,found] at compiled
      | some definition =>
        cases query : compileQuery elements definition with
        | none => simp [compileOne,plan,found,query] at compiled
        | some strategy =>
          have same : Output.threshold name sourceName strategy source = output := by
            simpa [compileOne,plan,found,query] using compiled
          subst output
          exact compile_query_classified elements definition strategy (prior sourceName definition found) query

/-- Ordered output compilation retains the authored strategy inventory while
extending source metadata at each declaration. -/
theorem compile_declarations_classified (declarations : List (Declaration StateInstalledLegacy.Value))
    (checked : ∀ declaration ∈ declarations, ClassifiedDeclaration declaration)
    (plans : StateInstalledCompiler.Plans StateInstalledLegacy.Value) (definitions : Definitions StateInstalledLegacy.Value) (outputs : List (Output StateInstalledLegacy.Value))
    (prior : ClassifiedDefinitions definitions) (compiled : compileDeclarations plans definitions declarations = some outputs) :
    ∀ output ∈ outputs, ClassifiedOutput output := by
  induction declarations generalizing definitions outputs with
  | nil =>
    have empty : ([] : List (Output StateInstalledLegacy.Value)) = outputs := Option.some.inj compiled
    subst outputs
    simp
  | cons declaration rest ih =>
    cases head : compileOne plans definitions declaration with
    | none => simp [compileDeclarations,head] at compiled
    | some output =>
      cases tail : compileDeclarations plans (extend definitions declaration) rest with
      | none => simp [compileDeclarations,head,tail] at compiled
      | some more =>
        have same : output::more = outputs := by simpa [compileDeclarations,head,tail] using compiled
        subst outputs
        have current := compile_one_classified plans definitions declaration output prior head
        have remaining := ih (fun declaration member => checked declaration (List.mem_cons_of_mem _ member))
          (extend definitions declaration) more (extend_classified definitions declaration prior (checked declaration (by simp))) tail
        intro next member
        rcases List.mem_cons.mp member with equal | later
        · subst next
          exact current
        · exact remaining next later

/-- Every instruction in an actual successful authored output compilation has
the proved singleton-or-finite inventory; callers supply no classification. -/
theorem compile_authored_classified (environment : Environment) (entries : List Entry) (whole : List Act)
    (observation : CompiledObservation) (compiled : compileAuthored environment entries whole = some observation) :
    ∀ output ∈ observation.program.outputs, ClassifiedOutput output := by
  cases installed : prepareStatic environment entries with
  | none => simp [compileAuthored,StateAuthoredBindings.prepare,installed] at compiled
  | some prepared =>
    have preparedWhole : StateAuthoredBindings.prepare environment entries whole = some (clauseAt prepared whole) := by
      simp [StateAuthoredBindings.prepare,installed,clauseAt]
    cases plans : StateInstalledLowering.compile (clauseAt prepared whole) with
    | none => simp [compileAuthored,preparedWhole,compileClause,plans] at compiled
    | some sources =>
      simp [compileAuthored,preparedWhole,compileClause,plans] at compiled
      dsimp only [clauseAt] at compiled
      cases code : compileDeclarations sources [] prepared.declarations with
      | none => simp [code] at compiled
      | some outputs =>
        have same : (⟨whole,⟨materialize prepared.domains whole prepared.freezes,outputs⟩⟩ : CompiledObservation) = observation := by
          simpa [code] using compiled
        subst observation
        exact compile_declarations_classified prepared.declarations (prepared_declarations_classified environment entries prepared installed)
          sources [] outputs (by intro name definition impossible; simp at impossible) code


end CBCL.StateOutputThresholdAgreement
