import LeanCbcl.StateInstalledLowering
import LeanCbcl.StateKernelSEC

/-! Concrete legacy-rule bindings for the installed semantic IR. Native rule
heads and post operations are fixed by the declaration constructors. Snapshot
carriers use a duplicate-free representative only to erase enumeration order;
the value bridge below compares it with the actual accepted history. -/
namespace CBCL.StateInstalledLegacy
open State StateLift StateLVar StateObservation StateObservationPlan StateInstalledCompiler
open StateKernel StateKernelSEC StateKernelSemantics StateKernelAggregates

/-- Choose a duplicate-free list representing the retained accepted-act set. -/
noncomputable def history (carrier : FinSet Act) : List Act := FinSet.dedup (Classical.choose (Quotient.exists_rep carrier))

theorem history_member (carrier : FinSet Act) (a : Act) : a ∈ history carrier ↔ a ∈ carrier := by
  rw [history,FinSet.mem_dedup]
  have representative : FinSet.mk (Classical.choose (Quotient.exists_rep carrier)) = carrier := Classical.choose_spec (Quotient.exists_rep carrier)
  exact FinSet.mem_mk.symm.trans (Iff.of_eq (congrArg (fun carrier => a ∈ carrier) representative))

theorem history_setEq (A : List Act) : SetEq (history (rawHistory A)) A := by
  intro a
  rw [history_member,rawHistory_eq,FinSet.mem_mk]

theorem unique_of_consistent {A : List Act} (unique : A.Nodup)
    (consistent : ∀ a ∈ A, ∀ b ∈ A, a.addr = b.addr → a = b) : NodupAddr A := by
  induction A with
  | nil => exact List.nodup_nil
  | cons a rest ih =>
    obtain ⟨absent,tail⟩ := List.nodup_cons.mp unique
    apply List.nodup_cons.mpr
    constructor
    · intro member
      obtain ⟨b,inside,equal⟩ := List.mem_map.mp member
      have same := consistent a (by simp) b (by simp [inside]) equal.symm
      exact absent (same ▸ inside)
    · exact ih tail (fun a ha b hb => consistent a (by simp [ha]) b (by simp [hb]))

theorem history_unique {A : List Act} (unique : NodupAddr A) : NodupAddr (history (rawHistory A)) := by
  apply unique_of_consistent (FinSet.nodup_dedup _)
  intro a ha b hb equal
  exact unique.eq_of_addr ((history_setEq A a).mp ha) ((history_setEq A b).mp hb) equal

/-- The closed author-facing threshold element forms. -/
inductive Element where
  | scalar (value : Val)
  | count (bound : Nat)
  | member (value : Val)
  | sum (bound : Int)
  | progress (bound : Nat)
  deriving DecidableEq

/-- The common payload type for primitive and composed installed observations. -/
inductive Value where
  | kernel (value : StateKernel.Observation)
  | pair (left right : Value)
  | nativeResource (read : StateResourceValidated.Read)
  | element (query : Element)
  | object (fields : List (String × Value))
  | list (values : List Value)

/-- The two derived native operations consume observed source maps. -/
def sumPost : Value → Value
  | .kernel (.map m) => .kernel (.integer (mapSum m))
  | _ => .kernel (.cell .absent)

/-- Project an observed value collection to its histogram. -/
def histogramPost : Value → Value
  | .kernel (.map m) => .kernel (.histogram (histogramKeys m) (histogram m))
  | _ => .kernel (.cell .absent)

/-- Render the legacy evaluator on a canonical retained history. -/
noncomputable def snapshotSource (context : Context) (domains : List Domain) (expression : StateKernel.Expr) : Source Value :=
  .snapshot (fun carrier => .kernel (evaluate (context.input (history carrier)) domains expression))

/-- All ordinary native expression constructors have an accepted-history
value bridge, including progress and current/HLC selections. -/
theorem snapshot_value_refinement (context : Context) (domains : List Domain) (expression : StateKernel.Expr)
    (A : List Act) (unique : NodupAddr A) :
    ∃ value, sourceRead (snapshotSource context domains expression) A = .data (.snapshot (.kernel value)) ∧
      StateKernelSEC.Equivalent value (evaluate (context.input A) domains expression) := by
  refine ⟨_,rfl,?_⟩
  exact strong_convergence context domains expression (history_unique unique) unique (history_setEq A)

/-- Only scalar members are admitted by the native value carriers. -/
def scalar : Val → Bool
  | .list _ => false
  | _ => true

/-- Test whether a closed threshold element is reached by the native value. -/
def readTest : Value → Value → Bool
  | .element (.scalar (.bool true)),.kernel (.boolean value) => value
  | .element (.count required),.kernel (.integer value) => decide ((required : Int) ≤ value)
  | .element (.sum required),.kernel (.map entries) => decide (required ≤ mapSum entries)
  | .element (.progress required),.kernel (.integer value) => decide ((required : Int) ≤ value)
  | .element (.member member),.kernel (.values has) => has member
  | .element (.member member),.kernel (.map entries) =>
      entries.keys.any (fun key => cellScalar (entries.read key) == some member)
  | _,_ => false

/-- The non-finite native carriers have no incompatible pair of distinct
alternatives; their legal installed thresholds are singletons. -/
def readCheck (allowed : Element → Bool) : List Value → Bool
  | [.element element] => allowed element
  | _ => false

/-- Recognized writer-shape metadata retained by installation. Shape parsing
and admission's enforcement of these constraints are separate typed boundaries. -/
structure WriterShape where
  /-- The contributing verb name. -/
  verb : String
  /-- The contributing field name. -/
  field : String
  /-- Whether the writer requires this field. -/
  required : Bool
  /-- Whether the writer restricts the field to nonnegative numbers. -/
  nonnegative : Bool

/-- Check that the contributing writer requires a nonnegative numeric field. -/
def mandatoryNonnegative (shapes : List WriterShape) (verb field : String) : Bool :=
  shapes.any (fun shape => shape.verb == verb && shape.field == field && shape.required && shape.nonnegative)

/-- Check whether an element is admitted by the source's threshold policy. -/
def allowed (shapes : List WriterShape) (rule : StateKernelClause.Rule) : Element → Bool
  | .scalar (.bool true) => match rule with | .existsRule _ => true | _ => false
  | .count n => match rule with | .count _ => decide (n < 2^63) | _ => false
  | .progress n => match rule with | .progress _ => decide (n < 2^63) | _ => false
  | .sum bound => decide (-(2^63) ≤ bound ∧ bound < 2^63) && (match rule with
      | .events verb field => mandatoryNonnegative shapes verb field | _ => false)
  | .member member => scalar member && (match rule with
      | .setUnion .. | .events .. => true | _ => false)
  | _ => false

/-- Construct the closed threshold policy for a legacy primitive. -/
def queryPolicy (shapes : List WriterShape) (rule : StateKernelClause.Rule) : Option (StateInstalledLowering.NativeRead Value) :=
  match rule with
  | .existsRule _ | .count _ | .progress _ | .setUnion .. | .events .. =>
      some ⟨readTest,readCheck (allowed shapes rule)⟩
  | _ => none

/-- Initializer dependencies are retained as explicit guard nodes, even though
the native snapshot closure already knows its data-domain selectors. -/
def guardSources (sources : List (String × String)) (source : Source Value) : Source Value :=
  sources.foldr (fun (opener,field) tail => .guardDomain opener field tail) source

/-- Decorate a legacy source with its initializer fault guards. -/
noncomputable def kernelSource (context : Context) (domains : List Domain) (expression : StateKernel.Expr) : Source Value :=
  guardSources (initializerSources (fun _ => []) domains expression) (snapshotSource context domains expression)

theorem guardSources_clear (sources : List (String × String)) (source : Source Value) (A : List Act)
    (clear : ∀ dependency ∈ sources, domainError dependency.1 dependency.2 A = none) :
    sourceRead (guardSources sources source) A = sourceRead source A := by
  induction sources with
  | nil => rfl
  | cons dependency rest ih =>
    have head := clear dependency (by simp)
    have tail := ih (fun source member => clear source (by simp [member]))
    change nativeGuard (domainError dependency.1 dependency.2 A) (sourceRead (guardSources rest source) A) = _
    rw [head,tail]
    cases sourceRead source A <;> rfl

theorem kernel_source_value_refinement (context : Context) (domains : List Domain) (expression : StateKernel.Expr)
    (A : List Act) (unique : NodupAddr A)
    (clear : ∀ dependency ∈ initializerSources (fun _ => []) domains expression,
      domainError dependency.1 dependency.2 A = none) :
    ∃ value, sourceRead (kernelSource context domains expression) A = .data (.snapshot (.kernel value)) ∧
      StateKernelSEC.Equivalent value (evaluate (context.input A) domains expression) := by
  rw [kernelSource,guardSources_clear _ _ A clear]
  exact snapshot_value_refinement context domains expression A unique

/-- Factor a legacy primitive through the retained-history lattice. -/
noncomputable def kernelTerm (context : Context) (domains : List Domain) (expression : StateKernel.Expr) :
    StateInstalledTerm.Term Value := {
  Carrier := FinSet Act
  state := id
  project := fun carrier => .kernel (evaluate (context.input (history carrier)) domains expression)
  guards := (initializerSources (fun _ => []) domains expression).map (fun (opener,field) =>
    StateInstalledTerm.Guard.domain opener field)
  algebra := inferInstance
  state_bottom := rfl
  state_merge := fun _ _ => rfl }

theorem kernelTerm_source (context : Context) (domains : List Domain) (expression : StateKernel.Expr) :
    StateInstalledTerm.source (kernelTerm context domains expression) = kernelSource context domains expression := by
  simp [StateInstalledTerm.source,kernelTerm,kernelSource,guardSources,List.foldr_map,Function.comp_def,
    StateInstalledTerm.Guard.apply,snapshotSource]

/-- Test queries against the same retained raw history as the source. -/
noncomputable def rawQueryPolicy (context : Context) (domains : List Domain) (expression : StateKernel.Expr)
    (shapes : List WriterShape) (rule : StateKernelClause.Rule) :
    Option (StateInstalledTerm.Policy Value (FinSet Act)) :=
  (queryPolicy shapes rule).map (fun policy =>
    ⟨(fun query state => policy.test query ((kernelTerm context domains expression).project state)),policy.check⟩)

/-- Lower a legacy primitive with its source-specific query policy. -/
noncomputable def primitiveDefinition (context : Context) (domains : List Domain) (expression : StateKernel.Expr)
    (rule : StateKernelClause.Rule) (shapes : List WriterShape) : StateInstalledLowering.Definition Value :=
  match rule with
  | .progress _ => .native (StateInstalledTerm.source (kernelTerm context domains expression)) (queryPolicy shapes rule)
  | _ => .factored (kernelTerm context domains expression) (rawQueryPolicy context domains expression shapes rule)

/-- Literal legacy-head lowering. Derived heads use observed earlier values;
resource definitions use the separately verified native resource leaf binding.
All other native closures are generated from the fixed expression compiler. -/
noncomputable def lowerRule (context : Context) (domains : List Domain)
    (resources : String → Option (Source Value)) (earlier : List (String × StateKernelClause.Rule))
    (rule : StateKernelClause.Rule) (shapes : List WriterShape := []) : Option (StateInstalledLowering.Definition Value) :=
  match rule with
  | .histogram reference => match earlier.lookup reference with
      | none => none
      | some source => if StateKernelClause.histogramAllowed source then
          some (.derived histogramPost reference) else none
  | .sum reference => match earlier.lookup reference with
      | none => none
      | some source => match StateKernelClause.mapPlanOf source with
          | some _ => some (.derived sumPost reference)
          | none => none
  | .boundedCounter name => match resources name with
      | none => none
      | some source => some (.native source none)
  | _ => match StateKernelClause.compileRule [] rule with
      | none => none
      | some expression => some (primitiveDefinition context domains expression rule shapes)

/-- The successful primitive lowering's closure has the independently proved
accepted-history meaning of its concrete compiled legacy expression. -/
theorem primitive_native_binding (context : Context) (domains : List Domain)
    (resources : String → Option (Source Value)) (earlier : List (String × StateKernelClause.Rule))
    (rule : StateKernelClause.Rule) (expression : StateKernel.Expr) (shapes : List WriterShape)
    (primitive : StateKernelClause.compileRule [] rule = some expression)
    (notResource : ∀ name, rule ≠ .boundedCounter name)
    (notHistogram : ∀ name, rule ≠ .histogram name) (notSum : ∀ name, rule ≠ .sum name) :
    lowerRule context domains resources earlier rule shapes =
      some (primitiveDefinition context domains expression rule shapes) := by
  cases rule <;> simp_all [lowerRule]

/-- Every well-formed legacy head lowers; resource availability is checked by
the installed registry rather than invented by the observation compiler. -/
theorem lower_rule_complete (context : Context) (domains : List Domain)
    (resources : String → Option (Source Value)) (earlier : List (String × StateKernelClause.Rule))
    (rule : StateKernelClause.Rule) (shapes : List WriterShape)
    (wellFormed : StateKernelClause.WellFormedRule earlier rule)
    (resourceAvailable : ∀ name, rule = .boundedCounter name → ∃ source, resources name = some source) :
    ∃ definition, lowerRule context domains resources earlier rule shapes = some definition := by
  by_cases histogram : ∃ name, rule = .histogram name
  · obtain ⟨name,rfl⟩ := histogram
    obtain ⟨source,found,accepted⟩ := wellFormed
    exact ⟨.derived histogramPost name,by simp [lowerRule,found,(StateKernelClause.histogram_allowed_correct source).mpr accepted]⟩
  by_cases sum : ∃ name, rule = .sum name
  · obtain ⟨name,rfl⟩ := sum
    obtain ⟨source,found,accepted⟩ := wellFormed
    obtain ⟨plan,compiled⟩ := StateKernelClause.map_plan_complete accepted
    exact ⟨.derived sumPost name,by simp [lowerRule,found,compiled]⟩
  by_cases resource : ∃ name, rule = .boundedCounter name
  · obtain ⟨name,equal⟩ := resource
    obtain ⟨source,found⟩ := resourceAvailable name equal
    subst rule
    exact ⟨.native source none,by simp [lowerRule,found]⟩
  have notHistogram : ∀ name, rule ≠ .histogram name := fun name equal => histogram ⟨name,equal⟩
  have notSum : ∀ name, rule ≠ .sum name := fun name equal => sum ⟨name,equal⟩
  have notResource : ∀ name, rule ≠ .boundedCounter name := fun name equal => resource ⟨name,equal⟩
  have primitiveFormed : StateKernelClause.WellFormedRule [] rule := by
    cases rule <;> simp_all [StateKernelClause.WellFormedRule]
  obtain ⟨expression,compiled⟩ := StateKernelClause.compile_rule_complete [] rule primitiveFormed
  exact ⟨primitiveDefinition context domains expression rule shapes,
    primitive_native_binding context domains resources earlier rule expression shapes compiled notResource notHistogram notSum⟩

/-- Concrete ordered vocabulary lowering, before source-relative threshold and
freeze compilation. Backward reference checks use original declarations. -/
noncomputable def lowerFields (context : Context) (domains : List Domain)
    (resources : String → Option (Source Value)) (shapes : List WriterShape)
    (earlier : List (String × StateKernelClause.Rule)) : List (String × StateKernelClause.Rule) →
      Option (List (StateInstalledLowering.Declaration Value))
  | [] => some []
  | (name,rule)::rest => do
      let definition ← lowerRule context domains resources earlier rule shapes
      let tail ← lowerFields context domains resources shapes (earlier ++ [(name,rule)]) rest
      return .field name definition :: tail

theorem lower_fields_complete (context : Context) (domains : List Domain)
    (resources : String → Option (Source Value)) (shapes : List WriterShape)
    {earlier fields : List (String × StateKernelClause.Rule)}
    (wellFormed : StateKernelClause.WellFormedFields earlier fields)
    (resourceAvailable : ∀ fieldName name, (fieldName,StateKernelClause.Rule.boundedCounter name) ∈ fields →
      ∃ source, resources name = some source) :
    ∃ lowered, lowerFields context domains resources shapes earlier fields = some lowered := by
  induction wellFormed with
  | nil => exact ⟨[],rfl⟩
  | cons earlier name rule rest head tail ih =>
    obtain ⟨definition,compiled⟩ := lower_rule_complete context domains resources earlier rule shapes head
      (fun resource equal => resourceAvailable name resource (by simp [equal]))
    obtain ⟨lowered,more⟩ := ih (fun fieldName resource member => resourceAvailable fieldName resource (List.mem_cons_of_mem _ member))
    exact ⟨.field name definition::lowered,by simp [lowerFields,compiled,more]⟩

/-- Derived totals retain the independently specified finite-map sum meaning,
including when their source payload was frozen at a historical cut. -/
theorem derived_frozen_sum_sound (world : Act → Prop) (source : Plan Value) (A : List Act)
    (freezer : Nat) (m : StateKernelQueries.FiniteMap) (excluded : FinSet Act)
    (unique : m.keys.Nodup)
    (frozen : data world source A = .frozen freezer (.kernel (.map m)) excluded) :
    ∃ value, data world (.map sumPost source) A = .snapshot (.kernel (.integer value)) ∧ SumMeaning m value := by
  exact ⟨mapSum m,derived_frozen_payload world source sumPost A freezer _ excluded frozen,map_sum_correct m unique⟩

theorem derived_frozen_histogram_sound (world : Act → Prop) (source : Plan Value) (A : List Act)
    (freezer : Nat) (m : StateKernelQueries.FiniteMap) (excluded : FinSet Act)
    (unique : m.keys.Nodup)
    (frozen : data world source A = .frozen freezer (.kernel (.map m)) excluded) :
    ∃ keys counts, data world (.map histogramPost source) A = .snapshot (.kernel (.histogram keys counts)) ∧
      HistogramMeaning m counts keys := by
  exact ⟨histogramKeys m,histogram m,
    derived_frozen_payload world source histogramPost A freezer _ excluded frozen,histogram_correct m unique⟩

/-- The names referenced by this installed declaration. -/
def references : StateKernelClause.Rule → List String
  | .histogram reference | .sum reference => [reference]
  | _ => []

theorem lookup_name_member {α : Type u} {entries : List (String × α)} {name : String} {value : α}
    (found : entries.lookup name = some value) : name ∈ entries.map Prod.fst := by
  obtain ⟨left,right,rfl,_⟩ := List.lookup_eq_some_iff.mp found
  simp

theorem original_references_scoped (earlier : List (String × StateKernelClause.Rule))
    (rule : StateKernelClause.Rule) (wellFormed : StateKernelClause.WellFormedRule earlier rule) :
    ∀ reference ∈ references rule, reference ∈ earlier.map Prod.fst := by
  cases rule <;> simp only [references,List.not_mem_nil,false_implies,forall_const]
  all_goals
    obtain ⟨source,found,_⟩ := wellFormed
    intro name member
    have equal := List.mem_singleton.mp member
    subst name
    exact lookup_name_member found

/-- Literal lowering preserves exactly the backward dependencies specified by
the original legacy heads. -/
theorem lower_rule_references (context : Context) (domains : List Domain)
    (resources : String → Option (Source Value)) (earlier : List (String × StateKernelClause.Rule))
    (rule : StateKernelClause.Rule) (shapes : List WriterShape) (definition : StateInstalledLowering.Definition Value)
    (compiled : lowerRule context domains resources earlier rule shapes = some definition) (name : String) :
    StateInstalledLowering.references (.field name definition) = references rule := by
  cases rule with
  | histogram reference =>
    cases found : earlier.lookup reference with
    | none => simp [lowerRule,found] at compiled
    | some source =>
      cases check : StateKernelClause.histogramAllowed source <;> simp [lowerRule,found,check] at compiled
      subst definition
      rfl
  | sum reference =>
    cases found : earlier.lookup reference with
    | none => simp [lowerRule,found] at compiled
    | some source =>
      cases plan : StateKernelClause.mapPlanOf source <;> simp [lowerRule,found,plan] at compiled
      subst definition
      rfl
  | boundedCounter resource =>
    cases found : resources resource <;> simp [lowerRule,found] at compiled
    subst definition
    rfl
  | _ =>
    simp [lowerRule,StateKernelClause.compileRule,StateKernelClause.mapPlanOf] at compiled
    subst definition
    rfl

/-- Well-formed legacy references give independently well-formed installed
semantic declarations, irrespective of the internal name enumeration order. -/
theorem lower_fields_wellFormed (context : Context) (domains : List Domain)
    (resources : String → Option (Source Value)) (shapes : List WriterShape)
    {earlier fields : List (String × StateKernelClause.Rule)}
    (wellFormed : StateKernelClause.WellFormedFields earlier fields)
    (definitions : StateInstalledLowering.Definitions Value) (names : List String)
    (namesMatch : ∀ name, name ∈ names ↔ name ∈ earlier.map Prod.fst)
    (lowered : List (StateInstalledLowering.Declaration Value))
    (compiled : lowerFields context domains resources shapes earlier fields = some lowered) :
    StateInstalledLowering.WellFormed definitions names lowered := by
  induction wellFormed generalizing definitions names lowered with
  | nil =>
    simp [lowerFields] at compiled
    subst lowered
    exact .nil _ _
  | cons earlier name rule rest head tail ih =>
    cases definitionFound : lowerRule context domains resources earlier rule shapes with
    | none => simp [lowerFields,definitionFound] at compiled
    | some definition =>
      cases restFound : lowerFields context domains resources shapes (earlier++[(name,rule)]) rest with
      | none => simp [lowerFields,definitionFound,restFound] at compiled
      | some more =>
        simp [lowerFields,definitionFound,restFound] at compiled
        subst lowered
        refine .cons _ _ _ _ (.field _ _) ?_ ?_
        · rw [lower_rule_references context domains resources earlier rule shapes definition definitionFound name]
          intro reference member
          exact (namesMatch reference).mpr (original_references_scoped earlier rule head reference member)
        · apply ih _ _ ?_ more restFound
          intro reference
          simp [namesMatch reference,or_comm,StateInstalledLowering.Declaration.name]

/-- Compile the concrete legacy vocabulary through the proved installed IR. -/
noncomputable def compile (context : Context) (domains : List Domain)
    (resources : String → Option (Source Value)) (shapes : List WriterShape)
    (fields : List (String × StateKernelClause.Rule)) (freezes : List (String × FreezeSpec)) : Option (Plans Value) := do
  let declarations ← lowerFields context domains resources shapes [] fields
  StateInstalledLowering.compile ⟨declarations,freezes⟩

/-- Concrete source-head lowering feeds the complete installed semantic
compiler theorem. Native primitive value meaning and frozen map aggregate
meaning are supplied by the bridges above, rather than arbitrary callbacks. -/
theorem concrete_installed_refinement (world : Act → Prop) (context : Context) (domains : List Domain)
    (resources : String → Option (Source Value)) (shapes : List WriterShape)
    (fields : List (String × StateKernelClause.Rule)) (freezes : List (String × FreezeSpec))
    (declarations : List (StateInstalledLowering.Declaration Value))
    (lowered : lowerFields context domains resources shapes [] fields = some declarations) :
    FieldsCorrespond world (compile context domains resources shapes fields freezes)
      (StateInstalledLowering.interpret world ⟨declarations,freezes⟩) := by
  simpa [compile,lowered] using
    StateInstalledLowering.native_installed_compiler_refinement world ⟨declarations,freezes⟩

theorem lower_fields_metadata (context : Context) (domains : List Domain)
    (resources : String → Option (Source Value)) (shapes : List WriterShape)
    (earlier fields : List (String × StateKernelClause.Rule))
    (declarations : List (StateInstalledLowering.Declaration Value))
    (compiled : lowerFields context domains resources shapes earlier fields = some declarations)
    (freezes : List (String × FreezeSpec)) :
    declarations.map StateInstalledLowering.Declaration.name = fields.map Prod.fst ∧
      StateInstalledLowering.stableDeclarations freezes declarations = true := by
  induction fields generalizing earlier declarations with
  | nil =>
    simp [lowerFields] at compiled
    subst declarations
    exact ⟨rfl,rfl⟩
  | cons binding rest ih =>
    obtain ⟨name,rule⟩ := binding
    cases found : lowerRule context domains resources earlier rule shapes with
    | none => simp [lowerFields,found] at compiled
    | some definition =>
      cases tail : lowerFields context domains resources shapes (earlier++[(name,rule)]) rest with
      | none => simp [lowerFields,found,tail] at compiled
      | some more =>
        simp [lowerFields,found,tail] at compiled
        subst declarations
        obtain ⟨names,stable⟩ := ih _ _ tail
        exact ⟨congrArg (List.cons name) names,by simpa [StateInstalledLowering.stableDeclarations] using stable⟩

/-- All well-formed legacy clauses with recognized resources and valid global
freeze targets compile through the concrete bindings and the installed IR. -/
theorem concrete_installed_complete (context : Context) (domains : List Domain)
    (resources : String → Option (Source Value)) (shapes : List WriterShape)
    (fields : List (String × StateKernelClause.Rule)) (freezes : List (String × FreezeSpec))
    (wellFormed : StateKernelClause.WellFormedFields [] fields)
    (resourceAvailable : ∀ fieldName name, (fieldName,StateKernelClause.Rule.boundedCounter name) ∈ fields →
      ∃ source, resources name = some source)
    (uniqueFields : (fields.map Prod.fst).Nodup) (uniqueFreezes : (freezes.map Prod.fst).Nodup)
    (targets : ∀ name ∈ freezes.map Prod.fst, name ∈ fields.map Prod.fst) :
    ∃ plans, compile context domains resources shapes fields freezes = some plans := by
  obtain ⟨declarations,lowered⟩ := lower_fields_complete context domains resources shapes wellFormed resourceAvailable
  have scopes := lower_fields_wellFormed context domains resources shapes wellFormed [] [] (by simp) declarations lowered
  obtain ⟨names,stable⟩ := lower_fields_metadata context domains resources shapes [] fields declarations lowered freezes
  have metadata : StateInstalledLowering.ValidMetadata ⟨declarations,freezes⟩ := by
    exact ⟨by simpa [names] using uniqueFields,uniqueFreezes,by simpa [names] using targets,stable⟩
  obtain ⟨plans,compiled⟩ := StateInstalledLowering.native_installed_compiler_complete ⟨declarations,freezes⟩ metadata scopes
  exact ⟨plans,by simpa [compile,lowered] using compiled⟩

end CBCL.StateInstalledLegacy
