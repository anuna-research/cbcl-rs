import LeanCbcl.StateReaderValues

/-! Request-domain closure for the concrete scoped cache reader. Successful
preparation makes dependencies original source fields, and constructed freeze
indices always name allocated scope data. -/
set_option autoImplicit false
namespace CBCL.StateReaderReachability
universe u
open State StateLift StateObservation StateObservationPlan StateInstalledCompiler StateInstalledLowering
open StateAuthoredBindings StateAuthoredDependencies StateMemoizedReader

/-- A successful native aggregate binding uses an earlier original field. -/
theorem bind_dependency_known (environment : Environment) (resolvedDomains : List StateInstalledDomains.Domain)
    (resolvedTables : List (String × StateFiniteTable.Verified)) (earlier : List (String × Binding))
    (rule : StateAuthoredBindings.Rule) (binding : Binding)
    (bound : StateAuthoredBindings.bind environment resolvedDomains resolvedTables earlier rule = some binding)
    (source : String) (selected : dependency rule = some source) : source ∈ earlier.map Prod.fst := by
  cases rule with
  | context _ | finite _ _ => simp [dependency] at selected
  | legacy raw =>
    cases raw <;> simp [dependency] at selected
    all_goals subst source
    all_goals rename_i source
    all_goals
      cases found : (legacyFields earlier).lookup source with
      | none => simp [StateAuthoredBindings.bind,found] at bound
      | some prior =>
        obtain ⟨before,after,equal,_⟩ := List.lookup_eq_some_iff.mp found
        have member : (source,prior) ∈ legacyFields earlier := by simp [equal]
        obtain ⟨⟨name,value⟩,inside,matched⟩ := List.mem_filterMap.mp member
        cases original : value.rule with
        | context _ | finite _ _ => simp [original] at matched
        | legacy legacy =>
          simp [original] at matched
          rcases matched with ⟨rfl,_⟩
          exact List.mem_map.mpr ⟨_,inside,rfl⟩

/-- Every lowered field dependency comes from earlier original bindings or an
original field in this source-entry suffix; threshold outputs never enter it. -/
theorem declarations_known (environment : Environment) (resolvedDomains : List StateInstalledDomains.Domain)
    (resolvedTables : List (String × StateFiniteTable.Verified)) (entries : List Entry)
    (earlier : List (String × Binding)) (loweredFields : List (Declaration StateInstalledLegacy.Value))
    (bindings : List (String × Binding))
    (lowered : declarations environment resolvedDomains resolvedTables earlier entries = some (loweredFields,bindings)) :
    ∀ name rule, (name,rule) ∈ rawFields entries → ∀ source, dependency rule = some source →
      source ∈ earlier.map Prod.fst ∨ source ∈ (rawFields entries).map Prod.fst := by
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
          intro name rule member source selected
          have chosen : (name,rule) = (fieldName,fieldRule) ∨ (name,rule) ∈ rawFields rest := by simpa [rawFields] using member
          rcases chosen with same | inside
          · cases same
            exact .inl (bind_dependency_known environment resolvedDomains resolvedTables earlier fieldRule binding head source selected)
          · rcases ih ((fieldName,binding)::earlier) more last tail name rule inside source selected with prior | localField
            · rcases List.mem_cons.mp prior with same | earlierField
              · exact .inr (by simp [rawFields,same])
              · exact .inl earlierField
            · exact .inr (by simpa [rawFields] using List.mem_cons_of_mem fieldName localField)
    | threshold thresholdName source elements =>
      cases tail : declarations environment resolvedDomains resolvedTables earlier rest with
      | none => simp [declarations,tail] at lowered
      | some output =>
        obtain ⟨more,last⟩ := output
        simp [declarations,tail] at lowered
        rcases lowered with ⟨rfl,rfl⟩
        simpa [rawFields] using ih earlier more last tail
    | domain _ | lattice _ | freeze _ _ _ =>
      simpa [rawFields] using ih earlier loweredFields bindings (by simpa [declarations] using lowered)

/-- Successful static lowering admits dependencies only from original source
fields; auxiliary declarations and threshold outputs do not become sources. -/
theorem static_known (environment : Environment) (entries : List Entry) (prepared : Prepared)
    (lowered : lowerStatic environment entries = some prepared) :
    ∀ name rule, (name,rule) ∈ rawFields entries → ∀ source, dependency rule = some source →
      source ∈ (rawFields entries).map Prod.fst := by
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
          | some _ =>
            intro name rule member source selected
            simpa using declarations_known environment resolvedDomains resolvedTables entries [] loweredFields bindings
              declResult name rule member source selected
  · simp [lowerStatic,checked] at lowered

/-- Actual preparation supplies dependency-domain closure without an assumed
relation between reader field names and IR names. -/
theorem prepared_known (environment : Environment) (entries : List Entry) (history : List Act)
    (clause : Clause StateInstalledLegacy.Value) (prepared : prepare environment entries history = some clause)
    (name source : String) (selected : lookupDependency entries name = some source) :
    source ∈ (rawFields entries).map Prod.fst := by
  cases installed : prepareStatic environment entries with
  | none => simp [prepare,installed] at prepared
  | some _ =>
    cases lowered : lowerStatic environment entries with
    | none => simp [prepareStatic,lowered] at installed
    | some raw =>
      cases found : (rawFields entries).lookup name with
      | none => simp [lookupDependency,found] at selected
      | some rule =>
        obtain ⟨before,after,equal,_⟩ := List.lookup_eq_some_iff.mp found
        exact static_known environment entries raw lowered name rule (by simp [equal]) source
          (by simpa [lookupDependency,found] using selected)

/-- A request names an original source and a concrete allocated history scope. -/
def Admitted (entries : List Entry) (whole : List Act) (freezes : List (String × FreezeSpec)) (key : Key) : Prop :=
  key.2 ∈ (rawFields entries).map Prod.fst ∧
    ∃ history, (StateScopePool.scopeAllocation whole freezes).2.scopes[key.1]? = some history

/-- Every possible continuation request stays in the admitted domain. -/
def Within {V : Type} (allowed : Key → Prop) : Body V → Prop
  | .done _ => True
  | .request key next => allowed key ∧ ∀ value, Within allowed (next value)

/-- Constructed cut callbacks return only allocated scope indices. -/
theorem cut_allocated {V : Type} (entries : List Entry) (whole : List Act)
    (fields : List (String × StateInstalledCompiler.Rule V)) (freezes : List (String × FreezeSpec))
    (ranked : StateExecutableFreeze.Ranked whole)
    (consistent : ∀ a ∈ whole, ∀ b ∈ whole, a.addr = b.addr → a = b) (name : String) (index : Nat)
    (selected : (StateReaderValues.operations entries whole fields freezes).cut name = some index) :
    ∃ history, (StateScopePool.scopeAllocation whole freezes).2.scopes[index]? = some history := by
  let roots := (StateScopePool.selectedRoots (StateScopePool.normalize whole) freezes).map (fun (field,freezer) => (field,freezer.addr))
  let pool := (StateScopePool.scopeAllocation whole freezes).2
  change StateScopePool.cutScope roots pool name = some index at selected
  cases root : roots.lookup name with
  | none => simp [StateScopePool.cutScope,root] at selected
  | some address =>
    have cached : pool.indices.lookup address = some index := by simpa [StateScopePool.cutScope,root] using selected
    exact ⟨StateScopePool.cutAt (StateScopePool.normalize whole) address,
      (StateScopePool.normalized_scopes_sound whole ranked consistent freezes).1.2 address index cached⟩

/-- Native finishing can request only its own known field at an allocated cut. -/
theorem finish_within {V : Type} (entries : List Entry) (whole : List Act)
    (fields : List (String × StateInstalledCompiler.Rule V)) (freezes : List (String × FreezeSpec))
    (ranked : StateExecutableFreeze.Ranked whole)
    (consistent : ∀ a ∈ whole, ∀ b ∈ whole, a.addr = b.addr → a = b)
    (key : Key) (admitted : Admitted entries whole freezes key) (normal : StateReaderValues.Result V) :
    Within (Admitted entries whole freezes) ((StateReaderValues.operations entries whole fields freezes).finish key normal) := by
  unfold Operations.finish
  split
  · trivial
  · split
    · split
      · trivial
      · rename_i index selected
        split
        · trivial
        · exact ⟨⟨admitted.1,cut_allocated entries whole fields freezes ranked consistent key.2 index selected⟩,fun _ => trivial⟩
    · trivial

/-- Every branch of every admitted concrete field body preserves known field
names and allocated scopes, independently of dependency values. -/
theorem body_within (environment : Environment) (entries : List Entry) (whole : List Act)
    (clause : Clause StateInstalledLegacy.Value) (prepared : prepare environment entries whole = some clause)
    (fields : List (String × StateInstalledCompiler.Rule StateInstalledLegacy.Value))
    (ranked : StateExecutableFreeze.Ranked whole)
    (consistent : ∀ a ∈ whole, ∀ b ∈ whole, a.addr = b.addr → a = b)
    (key : Key) (admitted : Admitted entries whole clause.freezes key) :
    Within (Admitted entries whole clause.freezes)
      ((StateReaderValues.operations entries whole fields clause.freezes).body key) := by
  unfold Operations.body
  split
  · exact finish_within entries whole fields clause.freezes ranked consistent key admitted _
  · rename_i source selected
    have original : lookupDependency entries key.2 = some source := selected
    exact ⟨⟨prepared_known environment entries whole clause prepared key.2 source original,admitted.2⟩,
      fun _ => finish_within entries whole fields clause.freezes ranked consistent key admitted _⟩

/-- Cache provenance records the admitted identity of every stored request. -/
def CacheWithin {V : Type} (allowed : Key → Prop) (cache : Cache V) : Prop :=
  ∀ key value, (key,value) ∈ cache → allowed key

/-- Dependency execution preserves provenance for all branches of a body. -/
theorem run_within {V : Type} (allowed : Key → Prop)
    (read : Key → Cache V → Option (V × Cache V)) (body : Body V) (within : Within allowed body)
    (requests : ∀ key, allowed key → ∀ cache value after, CacheWithin allowed cache →
      read key cache = some (value,after) → CacheWithin allowed after) :
    ∀ cache value after, CacheWithin allowed cache → body.run read cache = some (value,after) →
      CacheWithin allowed after := by
  induction body with
  | done current =>
    intro cache value after valid ran
    simp [Body.run] at ran
    obtain ⟨rfl,rfl⟩ := ran
    exact valid
  | request key next ih =>
    intro cache value after valid ran
    cases called : read key cache with
    | none => simp [Body.run,called] at ran
    | some output =>
      obtain ⟨current,middle⟩ := output
      have middleValid := requests key within.1 cache current middle valid called
      have continued : (next current).run read middle = some (value,after) := by simpa [Body.run,called] using ran
      exact ih current (within.2 current) middle value after middleValid continued

/-- Every completed memoized read from admitted inputs retains only admitted
cache entries, starting from any cache whose provenance is already established. -/
theorem read_within {V : Type} (allowed : Key → Prop) (body : Key → Body V)
    (within : ∀ key, allowed key → Within allowed (body key)) :
    ∀ fuel key cache value after, allowed key → CacheWithin allowed cache →
      read body fuel key cache = some (value,after) → CacheWithin allowed after := by
  intro fuel
  induction fuel with
  | zero =>
    intro key cache value after admitted valid ran
    cases found : cache.lookup key with
    | none => simp [StateMemoizedReader.read,found] at ran
    | some current =>
      simp [StateMemoizedReader.read,found] at ran
      obtain ⟨rfl,rfl⟩ := ran
      exact valid
  | succ fuel ih =>
    intro key cache value after admitted valid ran
    cases found : cache.lookup key with
    | some current =>
      simp [StateMemoizedReader.read,found] at ran
      obtain ⟨rfl,rfl⟩ := ran
      exact valid
    | none =>
      cases executed : (body key).run (read body fuel) cache with
      | none => simp [StateMemoizedReader.read,found,executed] at ran
      | some output =>
        obtain ⟨current,middle⟩ := output
        have middleValid := run_within allowed (read body fuel) (body key) (within key admitted)
          (fun key allowed cache value after valid ran => ih key cache value after allowed valid ran)
          cache current middle valid executed
        simp [StateMemoizedReader.read,found,executed] at ran
        obtain ⟨rfl,rfl⟩ := ran
        intro other value member
        rcases List.mem_cons.mp member with same | inside
        · cases same; exact admitted
        · exact middleValid other value inside

/-- A batch of top-level source requests preserves cache provenance. -/
theorem reads_within {V : Type} (allowed : Key → Prop) (body : Key → Body V) (rank : Key → Nat)
    (within : ∀ key, allowed key → Within allowed (body key)) (keys : List Key)
    (admitted : ∀ key ∈ keys, allowed key) :
    ∀ cache values after, CacheWithin allowed cache → reads body rank keys cache = some (values,after) →
      CacheWithin allowed after := by
  induction keys with
  | nil =>
    intro cache values after valid ran
    simp [reads] at ran
    obtain ⟨rfl,rfl⟩ := ran
    exact valid
  | cons key rest ih =>
    intro cache values after valid ran
    cases head : read body (rank key+1) key cache with
    | none => simp [reads,head] at ran
    | some result =>
      obtain ⟨value,middle⟩ := result
      have middleValid := read_within allowed body within _ key cache value middle (admitted key (by simp)) valid head
      cases tail : reads body rank rest middle with
      | none => simp [reads,head,tail] at ran
      | some result =>
        obtain ⟨more,final⟩ := result
        simp [reads,head,tail] at ran
        obtain ⟨rfl,rfl⟩ := ran
        exact ih (fun key member => admitted key (by simp [member])) middle more final middleValid tail

/-- Original source fields at scope zero are admitted by construction. -/
theorem initial_admitted (entries : List Entry) (whole : List Act) (freezes : List (String × FreezeSpec))
    (ranked : StateExecutableFreeze.Ranked whole)
    (consistent : ∀ a ∈ whole, ∀ b ∈ whole, a.addr = b.addr → a = b)
    (name : String) (known : name ∈ (rawFields entries).map Prod.fst) : Admitted entries whole freezes (0,name) :=
  ⟨known,StateScopePool.normalize whole,(StateScopePool.normalized_scopes_sound whole ranked consistent freezes).1.1⟩

/-- An admitted request reads actual allocated data rather than the empty-history
helper fallback. -/
theorem admitted_scope (entries : List Entry) (whole : List Act) (freezes : List (String × FreezeSpec))
    (key : Key) (admitted : Admitted entries whole freezes key) :
    ∃ history, (StateScopePool.scopeAllocation whole freezes).2.scopes[key.1]? = some history ∧
      StateReaderValues.scope whole freezes key = history := by
  obtain ⟨history,present⟩ := admitted.2
  exact ⟨history,present,by simp [StateReaderValues.scope,present]⟩

/-- Unique installed field names make original member lookup exact. -/
theorem lookup_original {V : Type u} (fields : List (String × V)) (unique : (fields.map Prod.fst).Nodup)
    (name : String) (rule : V) (present : (name,rule) ∈ fields) : fields.lookup name = some rule := by
  induction fields with
  | nil => simp at present
  | cons binding rest ih =>
    obtain ⟨head,value⟩ := binding
    obtain ⟨fresh,tailUnique⟩ := List.nodup_cons.mp unique
    rcases List.mem_cons.mp present with same | inside
    · cases same; simp
    · have different : name ≠ head := by
        intro same
        subst name
        exact fresh (List.mem_map.mpr ⟨(head,rule),inside,rfl⟩)
      simpa [List.lookup,beq_eq_false_iff_ne.mpr different] using ih tailUnique inside

/-- Preparation and source-relative resolution exclude unsupported field forms
at every admitted source name, not merely at an existential list member. -/
theorem admitted_rule (environment : Environment) (entries : List Entry) (whole : List Act)
    (clause : Clause StateInstalledLegacy.Value) (prepared : prepare environment entries whole = some clause)
    (fields : List (String × StateInstalledCompiler.Rule StateInstalledLegacy.Value))
    (resolved : resolve [] clause.declarations = some fields) (key : Key)
    (admitted : Admitted entries whole clause.freezes key) :
    ∃ rule, fields.lookup key.2 = some rule ∧ StateReaderValues.supported rule := by
  obtain ⟨plans,compiled⟩ := prepared_compiler_complete environment entries whole clause prepared
  have lowered : StateInstalledLowering.compile clause = some plans := by simpa [StateAuthoredBindings.compile,prepared] using compiled
  have names := StateAuthoredDependencies.resolve_names [] clause.declarations fields resolved
  have unique : (fields.map Prod.fst).Nodup := by
    rw [names]
    exact (StateInstalledRecognition.compile_sound clause plans lowered).1.1
  obtain ⟨⟨name,raw⟩,member,equal⟩ := List.mem_map.mp admitted.1
  dsimp only at equal
  subst name
  obtain ⟨rule,present,supported⟩ := StateReaderValues.prepared_supported environment entries whole clause prepared fields resolved key.2 raw member
  exact ⟨rule,lookup_original fields unique key.2 rule present,supported⟩

/-- Source and threshold inventory, erasing values but preserving read targets. -/
def entryShape : Entry → Option (String × Option String)
  | .field name _ => some (name,none)
  | .threshold name source _ => some (name,some source)
  | _ => none

/-- The same inventory after concrete source lowering. -/
def declarationShape {V : Type} : Declaration V → String × Option String
  | .field name _ => (name,none)
  | .threshold name source _ => (name,some source)

/-- Concrete lowering preserves source versus threshold entry kinds and names. -/
theorem declaration_shapes (environment : Environment) (resolvedDomains : List StateInstalledDomains.Domain)
    (resolvedTables : List (String × StateFiniteTable.Verified)) (entries : List Entry)
    (earlier : List (String × Binding)) (loweredFields : List (Declaration StateInstalledLegacy.Value))
    (bindings : List (String × Binding))
    (lowered : declarations environment resolvedDomains resolvedTables earlier entries = some (loweredFields,bindings)) :
    loweredFields.map declarationShape = entries.filterMap entryShape := by
  induction entries generalizing earlier loweredFields bindings with
  | nil => simp [declarations] at lowered; obtain ⟨rfl,rfl⟩ := lowered; rfl
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
          simpa [entryShape,declarationShape] using congrArg (fun shapes => (fieldName,none)::shapes)
            (ih ((fieldName,binding)::earlier) more last tail)
    | threshold thresholdName source elements =>
      cases tail : declarations environment resolvedDomains resolvedTables earlier rest with
      | none => simp [declarations,tail] at lowered
      | some output =>
        obtain ⟨more,last⟩ := output
        simp [declarations,tail] at lowered
        rcases lowered with ⟨rfl,rfl⟩
        simpa [entryShape,declarationShape] using congrArg (fun shapes => (thresholdName,some source)::shapes) (ih earlier more last tail)
    | domain _ | lattice _ | freeze _ _ _ =>
      simpa [entryShape] using ih earlier loweredFields bindings (by simpa [declarations] using lowered)

/-- Successful static lowering exposes the source-lowering execution used by
inventory proofs, not merely its already validated semantic declarations. -/
theorem lowering_witness (environment : Environment) (entries : List Entry) (prepared : Prepared)
    (lowered : lowerStatic environment entries = some prepared) :
    ∃ domains tables bindings, declarations environment domains tables [] entries = some (prepared.declarations,bindings) := by
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
          | some _ =>
            simp [lowerStatic,checked,domainResult,tableResult,declResult,freezeResult] at lowered
            subst prepared
            exact ⟨resolvedDomains,resolvedTables,bindings,declResult⟩
  · simp [lowerStatic,checked] at lowered

/-- Preparation preserves the original source/threshold read inventory exactly. -/
theorem prepared_shapes (environment : Environment) (entries : List Entry) (whole : List Act)
    (clause : Clause StateInstalledLegacy.Value) (prepared : prepare environment entries whole = some clause) :
    clause.declarations.map declarationShape = entries.filterMap entryShape := by
  cases installed : prepareStatic environment entries with
  | none => simp [prepare,installed] at prepared
  | some metadata =>
    have same : clauseAt metadata whole = clause := by simpa [prepare,installed,clauseAt] using prepared
    cases lowered : lowerStatic environment entries with
    | none => simp [prepareStatic,lowered] at installed
    | some raw =>
      have equal : raw = metadata := by
        by_cases checked : preparedCheck raw = true
        · simpa [prepareStatic,lowered,Option.filter,checked] using installed
        · simp [prepareStatic,lowered,Option.filter,checked] at installed
      subst metadata
      rw [← same]
      obtain ⟨domains,tables,bindings,declared⟩ := lowering_witness environment entries raw lowered
      exact declaration_shapes environment domains tables entries [] raw.declarations bindings declared

/-- A lowered threshold's source metadata comes only from source declarations,
never a previously rendered threshold output. -/
theorem resolved_threshold_source {V : Type} (definitions : Definitions V) (declarations : List (Declaration V))
    (fields : List (String × StateInstalledCompiler.Rule V)) (resolved : resolve definitions declarations = some fields)
    (name source : String) (elements : List V) (present : .threshold name source elements ∈ declarations) :
    source ∈ definitions.map Prod.fst ∨ ∃ definition, .field source definition ∈ declarations := by
  induction declarations generalizing definitions fields with
  | nil => simp at present
  | cons declaration rest ih =>
    cases head : lowerRule definitions declaration with
    | none => simp [resolve,head] at resolved
    | some rule =>
      cases tail : resolve (extend definitions declaration) rest with
      | none => simp [resolve,head,tail] at resolved
      | some more =>
        rcases List.mem_cons.mp present with same | inside
        · subst declaration
          cases found : definitions.lookup source with
          | none => simp [lowerRule,found] at head
          | some definition =>
            obtain ⟨before,after,equal,_⟩ := List.lookup_eq_some_iff.mp found
            exact .inl (by simp [equal])
        · rcases ih (extend definitions declaration) more tail inside with prior | ⟨definition,field⟩
          · cases declaration with
            | field fieldName definition =>
              rcases List.mem_cons.mp prior with same | earlierSource
              · dsimp only at same
                subst fieldName
                exact .inr ⟨definition,by simp⟩
              · exact .inl earlierSource
            | threshold _ _ _ => exact .inl prior
          · exact .inr ⟨definition,List.mem_cons_of_mem _ field⟩

/-- Every threshold source named by an admitted original entry is itself an
original source field. This covers the native fold's threshold field requests. -/
theorem prepared_threshold_known (environment : Environment) (entries : List Entry) (whole : List Act)
    (clause : Clause StateInstalledLegacy.Value) (prepared : prepare environment entries whole = some clause)
    (name source : String) (elements : List StateInstalledLegacy.Value)
    (present : .threshold name source elements ∈ entries) : source ∈ (rawFields entries).map Prod.fst := by
  obtain ⟨plans,compiled⟩ := prepared_compiler_complete environment entries whole clause prepared
  have lowered : StateInstalledLowering.compile clause = some plans := by simpa [StateAuthoredBindings.compile,prepared] using compiled
  obtain ⟨fields,resolved,_⟩ := StateAuthoredDependencies.lowered_compiled_clause clause plans lowered
  have shapes := prepared_shapes environment entries whole clause prepared
  have inventory : (name,some source) ∈ clause.declarations.map declarationShape := by
    rw [shapes]
    exact List.mem_filterMap.mpr ⟨.threshold name source elements,present,rfl⟩
  obtain ⟨declaration,declared,equal⟩ := List.mem_map.mp inventory
  cases declaration with
  | field _ _ => simp [declarationShape] at equal
  | threshold foundName foundSource queries =>
    simp [declarationShape] at equal
    obtain ⟨sameName,sameSource⟩ := equal
    subst foundName
    subst foundSource
    obtain ⟨definition,sourceField⟩ : ∃ definition, .field source definition ∈ clause.declarations := by
      simpa using resolved_threshold_source [] clause.declarations fields resolved name source queries declared
    have original : (source,none) ∈ entries.filterMap entryShape := by
      rw [← shapes]
      exact List.mem_map.mpr ⟨.field source definition,sourceField,rfl⟩
    obtain ⟨entry,inEntries,shape⟩ := List.mem_filterMap.mp original
    cases entry with
    | field fieldName raw =>
      simp [entryShape] at shape
      subst fieldName
      exact List.mem_map.mpr ⟨(source,raw),List.mem_filterMap.mpr ⟨.field source raw,inEntries,rfl⟩,rfl⟩
    | threshold _ _ _ | domain _ | lattice _ | freeze _ _ _ => simp [entryShape] at shape

/-- The exact top-level field requests made by native fold: source fields and
threshold sources, preserving entry order and shared-cache reuse. -/
def initialKeys (entries : List Entry) : List Key := entries.filterMap (fun entry => match entry with
  | .field name _ => some (0,name)
  | .threshold _ source _ => some (0,source)
  | _ => none)

/-- Every native top-level request is admitted by actual successful preparation. -/
theorem initial_keys_admitted (environment : Environment) (entries : List Entry) (whole : List Act)
    (clause : Clause StateInstalledLegacy.Value) (prepared : prepare environment entries whole = some clause)
    (ranked : StateExecutableFreeze.Ranked whole)
    (consistent : ∀ a ∈ whole, ∀ b ∈ whole, a.addr = b.addr → a = b) :
    ∀ key ∈ initialKeys entries, Admitted entries whole clause.freezes key := by
  intro key included
  obtain ⟨entry,member,selected⟩ := List.mem_filterMap.mp included
  cases entry with
  | field name rule =>
    have same : (0,name) = key := by simpa using selected
    subst key
    apply initial_admitted entries whole clause.freezes ranked consistent name
    exact List.mem_map.mpr ⟨(name,rule),List.mem_filterMap.mpr ⟨.field name rule,member,rfl⟩,rfl⟩
  | threshold name source elements =>
    have same : (0,source) = key := by simpa using selected
    subst key
    exact initial_admitted entries whole clause.freezes ranked consistent source
      (prepared_threshold_known environment entries whole clause prepared name source elements member)
  | domain _ | lattice _ | freeze _ _ _ => simp at selected

/-- Complete native request-domain theorem: preparation constructs the actual
initial request list, every branch stays in admitted source/scopes, and the
completed shared cache contains no unsupported or invalid-scope entry. -/
theorem prepared_reachable_cache (environment : Environment) (entries : List Entry) (whole : List Act)
    (clause : Clause StateInstalledLegacy.Value) (prepared : prepare environment entries whole = some clause)
    (ranked : StateExecutableFreeze.Ranked whole)
    (consistent : ∀ a ∈ whole, ∀ b ∈ whole, a.addr = b.addr → a = b) :
    ∃ plans fields, StateAuthoredBindings.compile environment entries whole = some plans ∧
      resolve [] clause.declarations = some fields ∧ StateScopePool.ScopeSound whole clause.freezes ∧
      let ops := StateReaderValues.operations entries whole fields clause.freezes
      let rank := requestRank (fields.map Prod.fst).idxOf ops.cut
      ∃ ranked : ∀ key, (ops.body key).Below rank (rank key), ∃ after,
        reads ops.body rank (initialKeys entries) [] = some ((initialKeys entries).map (reference ops.body rank ranked),after) ∧
        Valid (reference ops.body rank ranked) after ∧ CacheWithin (Admitted entries whole clause.freezes) after ∧
        (∀ key value, (key,value) ∈ after → ∃ rule history, fields.lookup key.2 = some rule ∧
          StateReaderValues.supported rule ∧
          (StateScopePool.scopeAllocation whole clause.freezes).2.scopes[key.1]? = some history) := by
  obtain ⟨plans,fields,compiled,resolved,sound,requestRanked,after,ran,valid⟩ :=
    StateReaderValues.prepared_fixed_cache environment entries whole clause prepared (initialKeys entries) ranked consistent
  let ops := StateReaderValues.operations entries whole fields clause.freezes
  have provenance := reads_within (Admitted entries whole clause.freezes) ops.body
    (requestRank (fields.map Prod.fst).idxOf ops.cut)
    (fun key admitted => body_within environment entries whole clause prepared fields ranked consistent key admitted)
    (initialKeys entries) (initial_keys_admitted environment entries whole clause prepared ranked consistent)
    [] ((initialKeys entries).map (reference ops.body _ requestRanked)) after
    (fun _ _ impossible => by simp at impossible) ran
  refine ⟨plans,fields,compiled,resolved,sound,requestRanked,after,ran,valid,provenance,?_⟩
  intro key value member
  have admitted := provenance key value member
  obtain ⟨rule,found,supported⟩ := admitted_rule environment entries whole clause prepared fields resolved key admitted
  obtain ⟨history,present⟩ := admitted.2
  exact ⟨rule,history,found,supported,present⟩

/-- Body meanings need agreement only at admitted lower requests; no equation
is required for unknown fields or unallocated scope indices. -/
theorem meaning_congr {V : Type} (allowed : Key → Prop) (rank : Key → Nat) (bound : Nat) (body : Body V)
    (below : body.Below rank bound) (within : Within allowed body) (left right : Key → V)
    (agree : ∀ key, rank key < bound → allowed key → left key = right key) :
    body.meaning left = body.meaning right := by
  induction body with
  | done _ => rfl
  | request key next ih =>
    simp only [Body.meaning,agree key below.1 within.1]
    exact ih (right key) (below.2 _) (within.2 _)

/-- The final recursive refinement may be proved exclusively on the admitted
request domain. A well-founded induction avoids requiring reference equations
outside that domain or inventing semantics for invalid native requests. -/
theorem reference_on_domain {V : Type} (allowed : Key → Prop) (body : Key → Body V) (rank : Key → Nat)
    (ranked : ∀ key, (body key).Below rank (rank key))
    (within : ∀ key, allowed key → Within allowed (body key)) (meaning : Key → V)
    (equation : ∀ key, allowed key → (body key).meaning meaning = meaning key) :
    ∀ key, allowed key → reference body rank ranked key = meaning key := by
  intro key
  apply (measure rank).wf.induction key
  intro key ih admitted
  calc
    reference body rank ranked key = (body key).meaning (reference body rank ranked) :=
      (reference_equation body rank ranked key).symm
    _ = (body key).meaning meaning := meaning_congr allowed rank (rank key) (body key)
      (ranked key) (within key admitted) _ meaning (fun dependency smaller known => ih dependency smaller known)
    _ = meaning key := equation key admitted

end CBCL.StateReaderReachability
