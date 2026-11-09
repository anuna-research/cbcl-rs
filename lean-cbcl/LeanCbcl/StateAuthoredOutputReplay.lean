import LeanCbcl.StateOutputWitnessReplay

/-! The actual authored binding inventory emits native/factored query policies;
generic installed lattice-query adapters are not authored source definitions. -/
set_option autoImplicit false
namespace CBCL.StateAuthoredOutputReplay
open State StateLift StateLVar StateObservation StateObservationPlan StateOutputCompiler StateOutputWitnessReplay
open StateAuthoredBindings StateInstalledLowering StateInstalledLegacy

/-- Authored definitions exclude the independent generic lattice-query adapter. -/
def PlainDefinition {V : Type} : Definition V → Prop
  | .lattice _ => False
  | _ => True

/-- Every native expression is represented by a native or factored definition. -/
theorem primitive_plain (environment : Environment) (domains : List StateInstalledDomains.Domain)
    (expression : StateKernel.Expr) (rule : StateKernelClause.Rule) :
    PlainDefinition (primitive environment domains expression rule) := by
  cases rule <;> trivial

/-- Context recognition emits the native policy constructor. -/
theorem context_definition_plain (profile : StateInstalledContext.Profile) (projection : List String)
    (definition : Definition Value) (installed : StateInstalledContext.make profile projection = some definition) :
    PlainDefinition definition := by
  unfold StateInstalledContext.make at installed
  split at installed
  · cases Option.some.inj installed
    trivial
  · contradiction

/-- The successful authored binder emits no generic lattice-query definition,
including its finite-lift case, which retains a factored source-owned policy. -/
theorem bind_plain (environment : Environment) (domains : List StateInstalledDomains.Domain)
    (tables : List (String × StateFiniteTable.Verified)) (earlier : List (String × Binding))
    (rule : StateAuthoredBindings.Rule) (binding : Binding)
    (bound : StateAuthoredBindings.bind environment domains tables earlier rule = some binding) :
    PlainDefinition binding.definition := by
  cases rule with
  | context projection =>
    cases installed : StateInstalledContext.make environment.profile projection with
    | none => simp [StateAuthoredBindings.bind,installed] at bound
    | some definition =>
      have same : (⟨.context projection,definition,contextFootprint environment projection⟩ : Binding) = binding := by
        simpa [StateAuthoredBindings.bind,installed] using bound
      subst binding
      exact context_definition_plain environment.profile projection definition installed
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
        trivial
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
        trivial
    all_goals
      simp only [StateAuthoredBindings.bind,StateKernelClause.compileRule,StateKernelClause.mapPlanOf] at bound
      cases Option.some.inj bound
      dsimp only
      apply primitive_plain

/-- A declaration's source metadata excludes generic lattice-query dispatch. -/
def PlainDeclaration {V : Type} : Declaration V → Prop
  | .field _ definition => PlainDefinition definition
  | .threshold .. => True

/-- Actual declaration lowering preserves the authored query inventory. -/
theorem declarations_plain (environment : Environment) (domains : List StateInstalledDomains.Domain)
    (tables : List (String × StateFiniteTable.Verified)) (entries : List Entry)
    (earlier : List (String × Binding)) (output : List (Declaration Value)) (bindings : List (String × Binding))
    (lowered : declarations environment domains tables earlier entries = some (output,bindings)) :
    ∀ declaration ∈ output, PlainDeclaration declaration := by
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
          have current := bind_plain environment domains tables earlier rule binding head
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

/-- Static preparation supplies the actual plain-query declaration inventory. -/
theorem prepared_declarations_plain (environment : Environment) (entries : List Entry) (prepared : Prepared)
    (installed : prepareStatic environment entries = some prepared) :
    ∀ declaration ∈ prepared.declarations, PlainDeclaration declaration := by
  obtain ⟨tables,bindings,_,_,lowered,_⟩ := StateAuthoredSourceProvenance.static_trace environment entries prepared installed
  exact declarations_plain environment prepared.domains tables entries [] prepared.declarations bindings lowered

/-- Every definition visible to a threshold keeps the authored policy inventory. -/
def PlainDefinitions {V : Type} (definitions : Definitions V) : Prop :=
  ∀ name definition, definitions.lookup name = some definition → PlainDefinition definition

/-- Extending the ordered metadata dictionary preserves its query inventory. -/
theorem extend_plain {V : Type} (definitions : Definitions V) (declaration : Declaration V)
    (prior : PlainDefinitions definitions) (checked : PlainDeclaration declaration) :
    PlainDefinitions (extend definitions declaration) := by
  intro query source found
  cases declaration with
  | field name definition =>
    simp only [extend,List.lookup_cons] at found
    split at found
    · cases Option.some.inj found
      exact checked
    · exact prior query source found
  | threshold name sourceName elements => exact prior query source found

/-- Actual source-owned policy compilation emits only closure/raw adapters
for authored definitions, rather than assuming this about arbitrary IR. -/
theorem compile_query_plain {V : Type} (elements : List V) (definition : Definition V) (query : Query V)
    (plain : PlainDefinition definition) (compiled : compileQuery elements definition = some query) : PlainQuery query := by
  cases definition with
  | native source policy =>
    cases policy with
    | none => simp [compileQuery] at compiled
    | some policy =>
      simp only [compileQuery] at compiled
      split at compiled
      · cases Option.some.inj compiled
        trivial
      · contradiction
  | factored term policy =>
    cases policy with
    | none => simp [compileQuery] at compiled
    | some policy =>
      simp only [compileQuery] at compiled
      split at compiled
      · cases Option.some.inj compiled
        trivial
      · contradiction
  | lattice field => contradiction
  | derived post source | pair combine left right => simp [compileQuery] at compiled

/-- Every successfully emitted instruction uses the source-owned query strategy. -/
theorem compile_one_plain {V : Type} (plans : StateInstalledCompiler.Plans V) (definitions : Definitions V)
    (declaration : Declaration V) (output : Output V) (prior : PlainDefinitions definitions)
    (compiled : compileOne plans definitions declaration = some output) : PlainOutput output := by
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
          exact compile_query_plain elements definition strategy (prior sourceName definition found) query

/-- Ordered output compilation retains the authored strategy inventory while
extending source metadata at each declaration. -/
theorem compile_declarations_plain {V : Type} (declarations : List (Declaration V))
    (checked : ∀ declaration ∈ declarations, PlainDeclaration declaration)
    (plans : StateInstalledCompiler.Plans V) (definitions : Definitions V) (outputs : List (Output V))
    (prior : PlainDefinitions definitions) (compiled : compileDeclarations plans definitions declarations = some outputs) :
    ∀ output ∈ outputs, PlainOutput output := by
  induction declarations generalizing definitions outputs with
  | nil =>
    have empty : ([] : List (Output V)) = outputs := Option.some.inj compiled
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
        have current := compile_one_plain plans definitions declaration output prior head
        have remaining := ih (fun declaration member => checked declaration (List.mem_cons_of_mem _ member))
          (extend definitions declaration) more (extend_plain definitions declaration prior (checked declaration (by simp))) tail
        intro next member
        rcases List.mem_cons.mp member with equal | later
        · subst next
          exact current
        · exact remaining next later

/-- Every instruction in an actual successful authored output compilation has
the proved plain-query inventory; callers supply no strategy classification. -/
theorem compile_authored_plain (environment : Environment) (entries : List Entry) (whole : List Act)
    (observation : CompiledObservation) (compiled : compileAuthored environment entries whole = some observation) :
    ∀ output ∈ observation.program.outputs, PlainOutput output := by
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
        exact compile_declarations_plain prepared.declarations (prepared_declarations_plain environment entries prepared installed)
          sources [] outputs (by intro name definition impossible; simp at impossible) code

/-- Paired output instructions keep their name and related complete sources. -/
def OutputRelated {V : Type} (domains : List StateInstalledDomains.Domain) (A B : List Act)
    (left right : Output V) : Prop :=
  outputName left = outputName right ∧
    StateReplayPaths.Related domains A B (path (outputSource left)) (path (outputSource right))

/-- Optional output compilation preserves rejection and successful source pairing. -/
inductive OutputMatch {V : Type} (domains : List StateInstalledDomains.Domain) (A B : List Act) :
    Option (Output V) → Option (Output V) → Prop where
  | none : OutputMatch domains A B none none
  | some {left right} : OutputRelated domains A B left right → OutputMatch domains A B (some left) (some right)

/-- Aligned named path lists preserve each actual dictionary lookup. -/
theorem related_lookup (domains : List StateInstalledDomains.Domain) (A B : List Act)
    (left right : List (String × Path))
    (related : List.Forall₂ (fun a b => a.1 = b.1 ∧ StateReplayPaths.Related domains A B a.2 b.2) left right) :
    StateReplayPaths.Environments domains A B left right := by
  induction related with
  | nil => intro name; exact .none
  | @cons a b left right head tail ih =>
    intro name
    obtain ⟨leftName,leftPath⟩ := a
    obtain ⟨rightName,rightPath⟩ := b
    have names : leftName = rightName := head.1
    subst rightName
    by_cases same : name = leftName
    · subst name
      simpa [List.lookup] using StateReplayPaths.Match.some head.2
    · simpa [List.lookup,beq_eq_false_iff_ne.mpr same] using ih name

/-- Output compilation pairs exactly the source plans selected by name. Both
sides use the same validated source-owned query metadata. -/
theorem compile_one_related {V : Type} (domains : List StateInstalledDomains.Domain) (A B : List Act)
    (left right : StateInstalledCompiler.Plans V) (definitions : Definitions V) (declaration : Declaration V)
    (related : StateReplayPaths.Environments domains A B (StateCompiledFreezeGrowth.paths left) (StateCompiledFreezeGrowth.paths right)) :
    OutputMatch domains A B (compileOne left definitions declaration) (compileOne right definitions declaration) := by
  cases declaration with
  | field name definition =>
    have paired := related name
    rw [StateCompiledFreezeGrowth.lookup_paths,StateCompiledFreezeGrowth.lookup_paths] at paired
    cases la : left.lookup name <;> cases rb : right.lookup name <;>
      simp only [la,rb,Option.map_none,Option.map_some] at paired
    all_goals cases paired
    · simp [compileOne,la,rb]
      exact .none
    · simp [compileOne,la,rb]
      exact .some ⟨rfl,by assumption⟩
  | threshold name source elements =>
    have paired := related source
    rw [StateCompiledFreezeGrowth.lookup_paths,StateCompiledFreezeGrowth.lookup_paths] at paired
    cases la : left.lookup source <;> cases rb : right.lookup source <;>
      simp only [la,rb,Option.map_none,Option.map_some] at paired
    all_goals cases paired
    · simp [compileOne,la,rb]
      exact .none
    · cases found : definitions.lookup source with
      | none =>
        simp [compileOne,la,rb,found]
        exact .none
      | some definition =>
        cases query : compileQuery elements definition with
        | none =>
          simp [compileOne,la,rb,found,query]
          exact .none
        | some strategy =>
          simp [compileOne,la,rb,found,query]
          exact .some ⟨rfl,by assumption⟩

/-- Ordered output compilation preserves instruction names and paired source
plans while extending the same declaration metadata on both sides. -/
theorem compile_declarations_related {V : Type} (domains : List StateInstalledDomains.Domain) (A B : List Act)
    (declarations : List (Declaration V)) (definitions : Definitions V)
    (left right : StateInstalledCompiler.Plans V) (leftCode rightCode : List (Output V))
    (related : StateReplayPaths.Environments domains A B (StateCompiledFreezeGrowth.paths left) (StateCompiledFreezeGrowth.paths right))
    (leftCompiled : compileDeclarations left definitions declarations = some leftCode)
    (rightCompiled : compileDeclarations right definitions declarations = some rightCode) :
    List.Forall₂ (OutputRelated domains A B) leftCode rightCode := by
  induction declarations generalizing definitions leftCode rightCode with
  | nil =>
    have first : ([] : List (Output V)) = leftCode := Option.some.inj leftCompiled
    have second : ([] : List (Output V)) = rightCode := Option.some.inj rightCompiled
    subst leftCode
    subst rightCode
    exact .nil
  | cons declaration rest ih =>
    have head := compile_one_related domains A B left right definitions declaration related
    generalize la : compileOne left definitions declaration = leftOutput at head
    generalize rb : compileOne right definitions declaration = rightOutput at head
    cases head with
    | none => simp [compileDeclarations,la] at leftCompiled
    | @some first second paired =>
      cases lt : compileDeclarations left (extend definitions declaration) rest with
      | none => simp [compileDeclarations,la,lt] at leftCompiled
      | some moreLeft =>
        cases rt : compileDeclarations right (extend definitions declaration) rest with
        | none => simp [compileDeclarations,rb,rt] at rightCompiled
        | some moreRight =>
          have firstEq : first::moreLeft = leftCode := by simpa [compileDeclarations,la,lt] using leftCompiled
          have secondEq : second::moreRight = rightCode := by simpa [compileDeclarations,rb,rt] using rightCompiled
          subst leftCode
          subst rightCode
          exact .cons paired (ih (extend definitions declaration) moreLeft moreRight lt rt)

/-- Successful authored output compilation exposes its actual source-plan and
instruction compiler executions, with the captured history retained exactly. -/
theorem compile_authored_parts (environment : Environment) (entries : List Entry) (whole : List Act)
    (observation : CompiledObservation) (compiled : compileAuthored environment entries whole = some observation) :
    ∃ prepared sources code, prepareStatic environment entries = some prepared ∧
      StateAuthoredBindings.compile environment entries whole = some sources ∧
      compileDeclarations sources [] prepared.declarations = some code ∧
      observation.history = whole ∧ observation.program = ⟨materialize prepared.domains whole prepared.freezes,code⟩ := by
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
        refine ⟨prepared,sources,outputs,rfl,?_,code,rfl,rfl⟩
        simpa [StateAuthoredBindings.compile,preparedWhole] using plans

/-- Actual authored output programs retain paired source paths across fresh
history-dependent recompilation; no instruction pairing is assumed. -/
theorem authored_outputs_related (world : Act → Prop) (environment : Environment) (entries : List Entry)
    (A B : List Act) (valid : ∀ act ∈ A, world act) (closed : CausallyClosed world B)
    (rooted : StateContextReplay.RootedOpeners world (StateInstalledContext.evidenceInput environment.profile))
    (left right : CompiledObservation)
    (leftCompiled : compileAuthored environment entries A = some left)
    (rightCompiled : compileAuthored environment entries B = some right) :
    ∃ prepared, prepareStatic environment entries = some prepared ∧
      List.Forall₂ (OutputRelated prepared.domains A B) left.program.outputs right.program.outputs := by
  obtain ⟨prepared,first,firstCode,installed,firstCompiled,firstInstructions,firstHistory,firstProgram⟩ :=
    compile_authored_parts environment entries A left leftCompiled
  obtain ⟨other,second,secondCode,otherInstalled,secondCompiled,secondInstructions,secondHistory,secondProgram⟩ :=
    compile_authored_parts environment entries B right rightCompiled
  have same : prepared = other := Option.some.inj (installed.symm.trans otherInstalled)
  subst other
  have paths := StateReplayPaths.authored_paths_related world environment entries prepared installed A B valid closed rooted
    first second firstCompiled secondCompiled
  have paired := compile_declarations_related prepared.domains A B prepared.declarations [] first second firstCode secondCode
    (related_lookup prepared.domains A B _ _ paths) firstInstructions secondInstructions
  exact ⟨prepared,installed,by simpa [firstProgram,secondProgram] using paired⟩

/-- Paired emitted instructions replay a named fault from reported witness
acts, using exact local-world and source-owned query bridges. -/
theorem related_output_fault (world : Act → Prop) (domains : List StateInstalledDomains.Domain)
    (A B : List Act) (unique : NodupAddr A) (validA : ∀ act ∈ A, world act) (validB : ∀ act ∈ B, world act)
    (closedA : CausallyClosed world A) (closedB : CausallyClosed world B)
    (left right : Output Value) (paired : OutputRelated domains A B left right) (plain : PlainOutput left)
    (first second : List (String × FreezeSpec)) (name : String) (e : Evidence)
    (fault : left.observe A first = (name,.fault e)) (accepted : StateWitnessReplay.Accepts A e B) :
    ∃ enlarged, right.observe B second = (name,.fault enlarged) ∧ ∀ id ∈ e, id ∈ enlarged := by
  have correctName : (left.observe A first).1 = outputName left := by cases left <;> rfl
  have nameEqual : outputName left = name := correctName.symm.trans (congrArg Prod.fst fault)
  have sourceFault := (output_fault_iff world A validA closedA left plain first e).mp (by simpa [nameEqual] using fault)
  have original := (observation_fault_iff world (outputSource left) A e).mp sourceFault
  obtain ⟨enlarged,current,contains⟩ := StateReplayPaths.related_replays world domains A B unique closedA closedB paired.2
    e original accepted
  have sourceCurrent := (observation_fault_iff world (outputSource right) B enlarged).mpr current
  obtain ⟨emittedEvidence,emitted,retained⟩ := output_preserves_source_fault right B second enlarged
    ((source_value_fault_iff world B validB closedB (outputSource right) enlarged).mpr sourceCurrent)
  have targetName : outputName right = name := paired.1.symm.trans nameEqual
  exact ⟨emittedEvidence,by simpa [targetName] using emitted,fun id member => retained id (contains id member)⟩

/-- Complete ordered output vectors preserve every named fault and previous
identity when the receiving program uses its freshly compiled source plans. -/
theorem code_fault_replays (world : Act → Prop) (domains : List StateInstalledDomains.Domain)
    (A B : List Act) (unique : NodupAddr A) (validA : ∀ act ∈ A, world act) (validB : ∀ act ∈ B, world act)
    (closedA : CausallyClosed world A) (closedB : CausallyClosed world B)
    (left right : List (Output Value)) (paired : List.Forall₂ (OutputRelated domains A B) left right)
    (plain : ∀ output ∈ left, PlainOutput output) (first second : List (String × FreezeSpec))
    (name : String) (e : Evidence) (fault : (name,.fault e) ∈ left.map (Output.observe A first))
    (accepted : StateWitnessReplay.Accepts A e B) :
    ∃ enlarged, (name,.fault enlarged) ∈ right.map (Output.observe B second) ∧ ∀ id ∈ e, id ∈ enlarged := by
  induction paired with
  | nil => simp at fault
  | @cons leftOutput rightOutput left right head tail ih =>
    change (name,.fault e) ∈ leftOutput.observe A first :: left.map (Output.observe A first) at fault
    rcases List.mem_cons.mp fault with current | later
    · obtain ⟨enlarged,emitted,contains⟩ := related_output_fault world domains A B unique validA validB closedA closedB
        leftOutput rightOutput head (plain leftOutput (by simp)) first second name e current.symm accepted
      exact ⟨enlarged,List.mem_cons.mpr (Or.inl emitted.symm),contains⟩
    · obtain ⟨enlarged,emitted,contains⟩ := ih (fun output inside => plain output (List.mem_cons_of_mem leftOutput inside)) later
      exact ⟨enlarged,List.mem_cons_of_mem _ emitted,contains⟩

/-- Actual emitted authored observations replay faults with containing evidence
across complete receiver recompilation. Neither a plain-query assumption nor a
caller-supplied source-plan pairing remains. -/
theorem authored_output_fault_replays (world : Act → Prop) (environment : Environment) (entries : List Entry)
    (A B : List Act) (unique : NodupAddr A) (validA : ∀ act ∈ A, world act) (validB : ∀ act ∈ B, world act)
    (closedA : CausallyClosed world A) (closedB : CausallyClosed world B)
    (rooted : StateContextReplay.RootedOpeners world (StateInstalledContext.evidenceInput environment.profile))
    (left right : CompiledObservation)
    (leftCompiled : compileAuthored environment entries A = some left)
    (rightCompiled : compileAuthored environment entries B = some right)
    (name : String) (e : Evidence) (fault : (name,.fault e) ∈ left.observe)
    (accepted : StateWitnessReplay.Accepts A e B) :
    ∃ enlarged, (name,.fault enlarged) ∈ right.observe ∧ ∀ id ∈ e, id ∈ enlarged := by
  obtain ⟨prepared,_,paired⟩ := authored_outputs_related world environment entries A B validA closedB rooted
    left right leftCompiled rightCompiled
  obtain ⟨_,_,_,_,_,_,firstHistory,_⟩ := compile_authored_parts environment entries A left leftCompiled
  obtain ⟨_,_,_,_,_,_,secondHistory,_⟩ := compile_authored_parts environment entries B right rightCompiled
  have sourceFault : (name,.fault e) ∈ left.program.outputs.map (Output.observe A left.program.freezes) := by
    simpa [CompiledObservation.observe,Program.observe,firstHistory] using fault
  obtain ⟨enlarged,emitted,contains⟩ := code_fault_replays world prepared.domains A B unique validA validB closedA closedB
    left.program.outputs right.program.outputs paired (compile_authored_plain environment entries A left leftCompiled)
    left.program.freezes right.program.freezes name e sourceFault accepted
  exact ⟨enlarged,by simpa [CompiledObservation.observe,Program.observe,secondHistory] using emitted,contains⟩

/-- Actual emitted authored faults report only accepted act identities. -/
theorem authored_output_evidence_supported (world : Act → Prop) (environment : Environment) (entries : List Entry)
    (A : List Act) (valid : ∀ act ∈ A, world act) (closed : CausallyClosed world A)
    (observation : CompiledObservation) (compiled : compileAuthored environment entries A = some observation)
    (name : String) (e : Evidence) (fault : (name,.fault e) ∈ observation.observe) :
    StateEvidenceSupport.Supported A e := by
  obtain ⟨_,_,_,_,_,_,history,_⟩ := compile_authored_parts environment entries A observation compiled
  have member : (name,.fault e) ∈ observation.program.outputs.map (Output.observe A observation.program.freezes) := by
    simpa [CompiledObservation.observe,Program.observe,history] using fault
  obtain ⟨output,inside,emitted⟩ := List.mem_map.mp member
  have correctName : (output.observe A observation.program.freezes).1 = outputName output := by cases output <;> rfl
  have nameEqual : outputName output = name := correctName.symm.trans (congrArg Prod.fst emitted)
  have sourceFault := (output_fault_iff world A valid closed output
    (compile_authored_plain environment entries A observation compiled output inside) observation.program.freezes e).mp
      (by simpa [nameEqual] using emitted)
  exact StateEvidenceSupport.observation_supported world (outputSource output) A e sourceFault

/-- Authored output code can be recompiled at a ranked content-consistent
receiver history, using the already proved complete output/cache compiler. -/
theorem authored_output_recompiles (environment : Environment) (entries : List Entry) (A B : List Act)
    (left : CompiledObservation) (compiled : compileAuthored environment entries A = some left)
    (ranked : StateExecutableFreeze.Ranked B) (consistent : ∀ a ∈ B, ∀ b ∈ B, a.addr = b.addr → a = b) :
    ∃ right, compileAuthored environment entries B = some right := by
  obtain ⟨prepared,_,_,installed,_,_,_,_⟩ := compile_authored_parts environment entries A left compiled
  have receiver : StateAuthoredBindings.prepare environment entries B = some (clauseAt prepared B) := by
    simp [StateAuthoredBindings.prepare,installed,clauseAt]
  obtain ⟨right,_,compiledRight,_⟩ := authored_compiler_refinement environment entries B (clauseAt prepared B) receiver ranked consistent
  exact ⟨right,compiledRight⟩

open StateKernelDelivery AdmissionStratification StateRefinement

/-- Explicit causal dependency coverage and replica closure derive the rank
used by the actual output compiler; semantic addresses need not order edges. -/
theorem replica_ranked {adm : Admission} {auth : Act → Prop} {H : ValidHistory adm}
    (replica : Replica adm auth H) (admission : PredecessorAdmission adm H.contains)
    (causal : StateContextReplay.CausalDependencies H) (n : Nat) :
    StateExecutableFreeze.Ranked (replica.run n).accepted := by
  have closed := replica_causal_closed replica admission n
  have unique := (reachable_wellFormed (behavior_reachable replica.behavior n)).accepted_unique
  refine ⟨H.rank,?_⟩
  intro child inside parent present edge
  have childValid := accepted_valid replica n child inside
  obtain ⟨dependency,member,identity⟩ := causal child childValid parent.addr edge
  have dependencyValid := H.closed child childValid dependency member
  have dependencyAccepted := closed child inside dependency dependencyValid (by simpa [identity] using edge)
  have same := unique.eq_of_addr dependencyAccepted present identity
  rw [← same]
  exact H.lower child childValid dependency member

/-- A finite exact list of reported actual witness acts suffices for eventual
same-named faults in every freshly compiled emitted receiver output vector.
All earlier evidence is retained; no whole-source-history delivery is used. -/
theorem eventual_authored_output_witness_fault {adm : Admission} {auth : Act → Prop} {H : ValidHistory adm}
    (left right : Replica adm auth H) (admission : PredecessorAdmission adm H.contains)
    (causal : StateContextReplay.CausalDependencies H) (environment : Environment) (entries : List Entry)
    (atTime : Nat) (observation : CompiledObservation)
    (compiled : compileAuthored environment entries (left.run atTime).accepted = some observation)
    (name : String) (e : Evidence) (fault : (name,.fault e) ∈ observation.observe) :
    ∃ witness : List Act,
      (∀ act, act ∈ witness ↔ act ∈ (left.run atTime).accepted ∧ act.addr ∈ e) ∧
      (∀ id, id ∈ witness.map Act.addr ↔ id ∈ e) ∧
      ∃ time, ∀ n, time ≤ n → ∃ current enlarged,
        compileAuthored environment entries (right.run n).accepted = some current ∧
        (name,.fault enlarged) ∈ current.observe ∧ ∀ id ∈ e, id ∈ enlarged := by
  classical
  let A := (left.run atTime).accepted
  have validA := accepted_valid left atTime
  have closedA := replica_causal_closed left admission atTime
  have uniqueA := (reachable_wellFormed (behavior_reachable left.behavior atTime)).accepted_unique
  have support := authored_output_evidence_supported H.contains environment entries A validA closedA observation compiled name e fault
  let witness := A.filter (fun act => decide (act.addr ∈ e))
  have exactWitness : ∀ act, act ∈ witness ↔ act ∈ A ∧ act.addr ∈ e := by intro act; simp [witness]
  have exactIds : ∀ id, id ∈ witness.map Act.addr ↔ id ∈ e := by
    intro id
    constructor
    · intro member
      obtain ⟨act,inside,identity⟩ := List.mem_map.mp member
      simpa [identity] using ((exactWitness act).mp inside).2
    · intro member
      obtain ⟨act,inside,identity⟩ := List.mem_map.mp (support id member)
      exact List.mem_map.mpr ⟨act,(exactWitness act).mpr ⟨inside,by simpa [identity] using member⟩,identity⟩
  obtain ⟨time,delivered⟩ := witness_dissemination left right witness atTime
    (fun act inside => ((exactWitness act).mp inside).1)
  have rooted := StateContextReplay.rooted_openers_of_dependencies H causal (StateInstalledContext.evidenceInput environment.profile)
  refine ⟨witness,exactWitness,exactIds,time,fun n later => ?_⟩
  have uniqueB := (reachable_wellFormed (behavior_reachable right.behavior n)).accepted_unique
  obtain ⟨current,currentCompiled⟩ := authored_output_recompiles environment entries A (right.run n).accepted observation compiled
    (replica_ranked right admission causal n) (fun a ma b mb same => uniqueB.eq_of_addr ma mb same)
  have accepted : StateWitnessReplay.Accepts A e (right.run n).accepted := by
    intro act inside named
    exact delivered n later act ((exactWitness act).mpr ⟨inside,named⟩)
  obtain ⟨enlarged,emitted,contains⟩ := authored_output_fault_replays H.contains environment entries A (right.run n).accepted
    uniqueA validA (accepted_valid right n) closedA (replica_causal_closed right admission n) rooted
    observation current compiled currentCompiled name e fault accepted
  exact ⟨current,enlarged,currentCompiled,emitted,contains⟩

end CBCL.StateAuthoredOutputReplay
