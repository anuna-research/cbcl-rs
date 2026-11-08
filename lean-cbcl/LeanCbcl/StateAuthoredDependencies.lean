import LeanCbcl.StateScopePool
import LeanCbcl.StateAuthoredCompletion
import LeanCbcl.StateReaderIndices

/-! Complete extraction of native derived-field dependencies from concrete
source declarations. Ordinary/context/finite sources have no field dependency;
histogram and sum retain exactly the authored source through installation. -/
set_option autoImplicit false
namespace CBCL.StateAuthoredDependencies
open StateAuthoredBindings StateInstalledCompiler StateInstalledLowering StateReaderIndices

/-- The exact dependency inventory used by native field evaluation. -/
def dependency : StateAuthoredBindings.Rule → Option String
  | .legacy (.histogram source) | .legacy (.sum source) => some source
  | _ => none

/-- Native field lookup reads original source metadata, never a supplied list
of dependencies or an observation-derived selector. -/
def lookupDependency (entries : List Entry) (name : String) : Option String :=
  ((rawFields entries).lookup name).bind dependency

/-- Primitive source factories introduce no cross-field read. -/
theorem primitive_references (environment : Environment) (resolvedDomains : List StateInstalledDomains.Domain)
    (expression : StateKernel.Expr) (rule : StateKernelClause.Rule) :
    references (lowerDefinition (primitive environment resolvedDomains expression rule)) = [] := by
  cases rule <;> rfl

/-- Every successful concrete source binding preserves all and only its native
field dependencies; ordinary sources cannot conceal extra IR references. -/
theorem bind_references (environment : Environment) (resolvedDomains : List StateInstalledDomains.Domain)
    (resolvedTables : List (String × StateFiniteTable.Verified)) (earlier : List (String × Binding))
    (rule : StateAuthoredBindings.Rule) (binding : Binding)
    (bound : StateAuthoredBindings.bind environment resolvedDomains resolvedTables earlier rule = some binding) :
    references (lowerDefinition binding.definition) = (dependency rule).toList := by
  cases rule with
  | context path =>
    cases checked : StateInstalledContext.validPath environment.profile.definition path with
    | false => simp [StateAuthoredBindings.bind,StateInstalledContext.make,checked] at bound
    | true => simp [StateAuthoredBindings.bind,StateInstalledContext.make,checked] at bound; subst binding; rfl
  | finite lattice declaration =>
    cases found : resolvedTables.lookup lattice with
    | none => simp [StateAuthoredBindings.bind,found] at bound
    | some table =>
      cases made : StateInstalledFinite.make environment.schema table resolvedDomains declaration with
      | none => simp [StateAuthoredBindings.bind,found,made] at bound
      | some field => simp [StateAuthoredBindings.bind,found,made] at bound; subst binding; rfl
  | legacy rule =>
    cases rule <;> simp only [StateAuthoredBindings.bind] at bound
    all_goals repeat' first | split at bound | simp only [Option.none_ne_some] at bound
    all_goals first
      | contradiction
      | (simp only [Option.some.injEq] at bound; subst binding; first | rfl | exact primitive_references _ _ _ _)

/-- Ordered declaration lowering retains the exact dependency inventory of
every original field, including fields after thresholds or auxiliary entries. -/
theorem declaration_dependencies (environment : Environment) (resolvedDomains : List StateInstalledDomains.Domain)
    (resolvedTables : List (String × StateFiniteTable.Verified)) (entries : List Entry)
    (earlier : List (String × Binding)) (loweredFields : List (Declaration StateInstalledLegacy.Value))
    (bindings : List (String × Binding))
    (lowered : declarations environment resolvedDomains resolvedTables earlier entries = some (loweredFields,bindings)) :
    ∀ name rule, (name,rule) ∈ rawFields entries → ∃ definition,
      .field name definition ∈ loweredFields ∧ references (lowerDefinition definition) = (dependency rule).toList := by
  induction entries generalizing earlier loweredFields bindings with
  | nil => intro name rule impossible; simp [rawFields] at impossible
  | cons entry rest ih =>
    cases entry with
    | field fieldName fieldRule =>
      cases head : StateAuthoredBindings.bind environment resolvedDomains resolvedTables earlier fieldRule with
      | none => simp [declarations,head] at lowered
      | some binding =>
        cases tail : declarations environment resolvedDomains resolvedTables ((fieldName,binding)::earlier) rest with
        | none => simp [declarations,head,tail] at lowered
        | some output =>
          obtain ⟨more,last⟩ := output
          simp [declarations,head,tail] at lowered
          rcases lowered with ⟨rfl,rfl⟩
          intro name rule member
          have selected : (name,rule) = (fieldName,fieldRule) ∨ (name,rule) ∈ rawFields rest := by
            simpa [rawFields] using member
          rcases selected with same | inside
          · cases same
            exact ⟨binding.definition,by simp,bind_references environment resolvedDomains resolvedTables earlier fieldRule binding head⟩
          · obtain ⟨definition,present,exactDeps⟩ := ih ((fieldName,binding)::earlier) more last tail name rule inside
            exact ⟨definition,by simp [present],exactDeps⟩
    | threshold thresholdName source elements =>
      cases tail : declarations environment resolvedDomains resolvedTables earlier rest with
      | none => simp [declarations,tail] at lowered
      | some output =>
        obtain ⟨more,last⟩ := output
        simp [declarations,tail] at lowered
        rcases lowered with ⟨rfl,rfl⟩
        intro name rule member
        obtain ⟨definition,present,exactDeps⟩ := ih earlier more last tail name rule (by simpa [rawFields] using member)
        exact ⟨definition,by simp [present],exactDeps⟩
    | domain _ | lattice _ | freeze _ _ _ =>
      exact ih earlier loweredFields bindings (by simpa [declarations] using lowered)

/-- Source-relative resolution preserves every concrete field definition and
its references; threshold lowering cannot replace or erase a source field. -/
theorem resolve_field {V : Type} (definitions : Definitions V) (declarations : List (Declaration V))
    (fields : List (String × StateInstalledCompiler.Rule V))
    (resolved : resolve definitions declarations = some fields) (name : String) (definition : Definition V)
    (present : .field name definition ∈ declarations) :
    (name,lowerDefinition definition) ∈ fields := by
  induction declarations generalizing definitions fields with
  | nil => simp at present
  | cons declaration rest ih =>
    cases head : lowerRule definitions declaration with
    | none => simp [resolve,head] at resolved
    | some rule =>
      cases tail : resolve (extend definitions declaration) rest with
      | none => simp [resolve,head,tail] at resolved
      | some more =>
        simp [resolve,head,tail] at resolved
        subst fields
        rcases List.mem_cons.mp present with same | inside
        · subst declaration
          simp [lowerRule] at head
          subst rule
          simp [Declaration.name]
        · exact List.mem_cons_of_mem _ (ih _ more tail inside)

/-- Full-clause static lowering retains every original dependency, including
when domains, lattice declarations and freeze metadata are present. -/
theorem static_dependencies (environment : Environment) (entries : List Entry) (prepared : Prepared)
    (lowered : lowerStatic environment entries = some prepared) :
    ∀ name rule, (name,rule) ∈ rawFields entries → ∃ definition,
      .field name definition ∈ prepared.declarations ∧ references (lowerDefinition definition) = (dependency rule).toList := by
  by_cases checked : metadataCheck environment entries = true
  · cases domainResult : domains environment entries with
    | none => simp [lowerStatic,checked,domainResult] at lowered
    | some resolvedDomains =>
      cases tableResult : tables environment entries with
      | none => simp [lowerStatic,checked,domainResult,tableResult] at lowered
      | some resolvedTables =>
        cases declResult : declarations environment resolvedDomains resolvedTables [] entries with
        | none => simp [lowerStatic,checked,domainResult,tableResult,declResult] at lowered
        | some result =>
          obtain ⟨loweredFields,bindings⟩ := result
          cases freezeResult : freezeTemplates environment bindings entries with
          | none => simp [lowerStatic,checked,domainResult,tableResult,declResult,freezeResult] at lowered
          | some templates =>
            simp [lowerStatic,checked,domainResult,tableResult,declResult,freezeResult] at lowered
            subst prepared
            exact declaration_dependencies environment resolvedDomains resolvedTables entries [] loweredFields bindings declResult
  · simp [lowerStatic,checked] at lowered

/-- Successful authored preparation exposes exact original dependencies at the
observation-specialized clause, without an extraction-correctness premise. -/
theorem prepared_dependencies (environment : Environment) (entries : List Entry) (history : List State.Act)
    (clause : Clause StateInstalledLegacy.Value) (prepared : prepare environment entries history = some clause) :
    ∀ name rule, (name,rule) ∈ rawFields entries → ∃ definition,
      .field name definition ∈ clause.declarations ∧ references (lowerDefinition definition) = (dependency rule).toList := by
  cases installed : prepareStatic environment entries with
  | none => simp [prepare,installed] at prepared
  | some metadata =>
    have same : clauseAt metadata history = clause := by simpa [prepare,installed,clauseAt] using prepared
    cases lowered : lowerStatic environment entries with
    | none => simp [prepareStatic,lowered] at installed
    | some raw =>
      have equal : raw = metadata := by
        by_cases checked : preparedCheck raw = true
        · simpa [prepareStatic,lowered,Option.filter,checked] using installed
        · simp [prepareStatic,lowered,Option.filter,checked] at installed
      subst metadata
      rw [← same]
      exact static_dependencies environment entries raw lowered

/-- A selected raw native dependency survives source-relative resolution as an
actual installed IR reference. This constructs the earlier extraction premise. -/
theorem extracted_reference (environment : Environment) (entries : List Entry) (history : List State.Act)
    (clause : Clause StateInstalledLegacy.Value) (prepared : prepare environment entries history = some clause)
    (fields : List (String × StateInstalledCompiler.Rule StateInstalledLegacy.Value))
    (resolved : resolve [] clause.declarations = some fields) (name source : String)
    (selected : lookupDependency entries name = some source) :
    ∃ rule, (name,rule) ∈ fields ∧ source ∈ references rule := by
  cases found : (rawFields entries).lookup name with
  | none => simp [lookupDependency,found] at selected
  | some raw =>
    have dep : dependency raw = some source := by simpa [lookupDependency,found] using selected
    obtain ⟨priorFields,laterFields,equal,_⟩ := List.lookup_eq_some_iff.mp found
    have present : (name,raw) ∈ rawFields entries := by simp [equal]
    obtain ⟨definition,declared,exactDeps⟩ := prepared_dependencies environment entries history clause prepared name raw present
    refine ⟨lowerDefinition definition,resolve_field [] clause.declarations fields resolved name definition declared,?_⟩
    rw [exactDeps,dep]
    simp

/-- Source-relative resolution preserves the ordered field namespace exactly. -/
theorem resolve_names {V : Type} (definitions : Definitions V) (declarations : List (Declaration V))
    (fields : List (String × StateInstalledCompiler.Rule V)) (resolved : resolve definitions declarations = some fields) :
    fields.map Prod.fst = declarations.map Declaration.name := by
  induction declarations generalizing definitions fields with
  | nil => simp [resolve] at resolved; subst fields; rfl
  | cons declaration rest ih =>
    cases head : lowerRule definitions declaration with
    | none => simp [resolve,head] at resolved
    | some rule =>
      cases tail : resolve (extend definitions declaration) rest with
      | none => simp [resolve,head,tail] at resolved
      | some more =>
        simp [resolve,head,tail] at resolved
        subst fields
        simp only [List.map_cons,ih _ more tail]

/-- A successful source-relative compiler constructs the exact installed field
clause whose validation supplies cache ordering; no detached clause is assumed. -/
theorem lowered_compiled_clause {V : Type} (clause : Clause V) (plans : Plans V)
    (compiled : StateInstalledLowering.compile clause = some plans) :
    ∃ fields, resolve [] clause.declarations = some fields ∧
      StateInstalledClause.compile ⟨fields,clause.freezes⟩ = some plans := by
  unfold StateInstalledLowering.compile at compiled
  split at compiled
  · rename_i metadata
    cases resolved : resolve [] clause.declarations with
    | none => simp [resolved] at compiled
    | some fields =>
      have names := resolve_names [] clause.declarations fields resolved
      have fieldMetadata : StateInstalledClause.ValidMetadata ⟨fields,clause.freezes⟩ := by
        exact ⟨by simpa [names] using metadata.1,metadata.2.1,by simpa [names] using metadata.2.2.1⟩
      refine ⟨fields,rfl,?_⟩
      simpa [StateInstalledClause.compile,fieldMetadata,resolved] using compiled
  · contradiction

/-- Operational dependencies are constructed directly from the original
recognized declarations; callers supply only typed value/fault/wrapper leaves. -/
def operations {V : Type} (entries : List Entry) (leaves : StateMemoizedReader.Operations V) : StateMemoizedReader.Operations V :=
  { leaves with dependency := lookupDependency entries }

/-- Successful concrete authored preparation constructs compilation, exact
native dependency extraction, numeric ranks and empty-cache execution together.
Only native leaf operations and cut/scope interpretation remain supplied. -/
theorem prepared_native_cache {V : Type} (environment : Environment) (entries : List Entry) (history : List State.Act)
    (clause : Clause StateInstalledLegacy.Value) (prepared : prepare environment entries history = some clause)
    (leaves : StateMemoizedReader.Operations V) (keys : List StateMemoizedReader.Key) :
    ∃ plans fields, StateAuthoredBindings.compile environment entries history = some plans ∧
      resolve [] clause.declarations = some fields ∧
      let ops := operations entries leaves
      let rank := StateMemoizedReader.requestRank (fields.map Prod.fst).idxOf ops.cut
      ∃ ranked : ∀ key, (ops.body key).Below rank (rank key),
        ∃ after, StateMemoizedReader.reads ops.body rank keys [] =
          some (keys.map (StateMemoizedReader.reference ops.body rank ranked),after) ∧
          StateMemoizedReader.Valid (StateMemoizedReader.reference ops.body rank ranked) after := by
  obtain ⟨plans,compiled⟩ := prepared_compiler_complete environment entries history clause prepared
  have lowered : StateInstalledLowering.compile clause = some plans := by
    simpa [StateAuthoredBindings.compile,prepared] using compiled
  obtain ⟨fields,resolved,fieldCompiled⟩ := lowered_compiled_clause clause plans lowered
  let ops := operations entries leaves
  have extracted : ∀ name source, ops.dependency name = some source →
      ∃ rule, (name,rule) ∈ fields ∧ source ∈ references rule := by
    exact extracted_reference environment entries history clause prepared fields resolved
  have ordering := compiled_dependency_ordering ⟨fields,clause.freezes⟩ plans fieldCompiled ops extracted
  let ranked := StateMemoizedReader.body_ranked ops (fields.map Prod.fst).idxOf ordering
  exact ⟨plans,fields,compiled,resolved,ranked,
    StateMemoizedReader.native_reads_refinement ops (fields.map Prod.fst).idxOf ordering keys⟩

/-- Concrete authored preparation now constructs dependency, active-plan and
cut-index inputs of the memoized reader from source entries and full history. -/
theorem prepared_scoped_cache {V : Type} (environment : Environment) (entries : List Entry) (history : List State.Act)
    (clause : Clause StateInstalledLegacy.Value) (prepared : prepare environment entries history = some clause)
    (leaves : StateMemoizedReader.Operations V) (keys : List StateMemoizedReader.Key)
    (ranked : StateExecutableFreeze.Ranked history)
    (consistent : ∀ a ∈ history, ∀ b ∈ history, a.addr = b.addr → a = b) :
    StateScopePool.ScopeSound history clause.freezes ∧
    (∃ plans fields, StateAuthoredBindings.compile environment entries history = some plans ∧
      resolve [] clause.declarations = some fields ∧
      let ops := operations entries (StateScopePool.readerOperations history clause.freezes leaves)
      let rank := StateMemoizedReader.requestRank (fields.map Prod.fst).idxOf ops.cut
      ∃ ranked : ∀ key, (ops.body key).Below rank (rank key),
        ∃ after, StateMemoizedReader.reads ops.body rank keys [] =
          some (keys.map (StateMemoizedReader.reference ops.body rank ranked),after) ∧
          StateMemoizedReader.Valid (StateMemoizedReader.reference ops.body rank ranked) after) :=
  ⟨StateScopePool.normalized_scopes_sound history ranked consistent clause.freezes,
    prepared_native_cache environment entries history clause prepared
      (StateScopePool.readerOperations history clause.freezes leaves) keys⟩

end CBCL.StateAuthoredDependencies
