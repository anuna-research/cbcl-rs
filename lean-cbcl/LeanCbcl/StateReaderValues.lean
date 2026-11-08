import LeanCbcl.StateAuthoredDependencies

/-! Fixed value/fault/presentation leaves for the scoped cache machine. Native
source reads and derived operations come from the installed concrete compiler;
no caller supplies a normal-value callback, fault classifier or wrapper. The
final equation to the complete scoped plan reader remains a separate theorem. -/
set_option autoImplicit false
namespace CBCL.StateReaderValues
open State StateLift StateLVar StateObservation StateObservationPlan StateRuleRefinement StateInstalledCompiler

/-- Cached results retain the complete semantic observation, including faults. -/
abbrev Result (V : Type) := StateObservationPlan.Observation V

/-- Native dependency unwrapping strips only a frozen observation's wrapper. -/
def unfrozen {V : Type} : Result V → Result V
  | .data (.frozen _ value _) => .data (.snapshot value)
  | result => result

/-- Derived native operations see exactly the same payload after unwrapping. -/
theorem derived_unfrozen {V W : Type} (post : V → W) (result : Result V) :
    nativeDerived post (unfrozen result) = nativeDerived post result := by
  cases result with
  | fault _ => rfl
  | data current => cases current <;> rfl

/-- The error-first scoped observation used by the independent native plan. -/
noncomputable def scopedObserve {V : Type} (world : Act → Prop) (whole : List Act)
    (plan : Plan V) (scope : List Act) : Result V :=
  match StateNativeReader.error world whole plan scope with
  | some evidence => .fault evidence
  | none => .data (StateNativeReader.value world whole plan scope)

/-- Primitive installed sources have no hidden freeze dependency, so their
scoped error pass equals the original source guard interpretation. -/
theorem source_error {V : Type} (world : Act → Prop) (whole : List Act) (source : Source V) (scope : List Act) :
    StateNativeReader.error world whole (sourcePlan source) scope = errors world (path (sourcePlan source)) scope := by
  induction source with
  | snapshot _ | read _ _ | context _ _ | domain _ _ _ _ _ => rfl
  | guardCertified _ _ ih | resource _ _ _ ih | guardDomain _ _ _ ih | guardThreshold _ _ ih =>
    simp only [sourcePlan,StateNativeReader.error,path,errors,ih]

/-- Primitive source values read the actual supplied scope, independently of
the full observation used by other fields' global freeze plans. -/
theorem source_value {V : Type} (world : Act → Prop) (whole : List Act) (source : Source V) (scope : List Act) :
    StateNativeReader.value world whole (sourcePlan source) scope = data world (sourcePlan source) scope := by
  induction source with
  | snapshot _ | read _ _ | context _ _ | domain _ _ _ _ _ => rfl
  | guardCertified _ _ ih | resource _ _ _ ih | guardDomain _ _ _ ih | guardThreshold _ _ ih =>
    exact ih

/-- Fixed native source evaluation equals the compiled source's complete
scoped observation, including every primitive terminal error. -/
theorem source_scoped_refinement {V : Type} (world : Act → Prop) (whole : List Act) (source : Source V) (scope : List Act) :
    scopedObserve world whole (sourcePlan source) scope = sourceRead source scope := by
  rw [← source_refinement world source scope]
  simp only [scopedObserve,source_error,source_value,StateObservationPlan.observe]
  rfl

/-- The native derived adapter consumes the completed scoped dependency value
and preserves its faults exactly as the compiled map plan does. -/
theorem derived_scoped_refinement {V W : Type} (world : Act → Prop) (whole scope : List Act)
    (post : V → W) (source : Plan V) :
    scopedObserve world whole (.map post source) scope =
      nativeDerived post (unfrozen (scopedObserve world whole source scope)) := by
  rw [derived_unfrozen]
  cases found : StateNativeReader.error world whole source scope <;>
    simp [scopedObserve,StateNativeReader.error,StateNativeReader.value,nativeDerived,found]

/-- Combine normal and precomputed freeze faults before requesting any cut. -/
def combinedFault {V : Type} (own : Error) (normal : Result V) : Option (Result V) :=
  (unionError (sourceError normal) own).map StateObservationPlan.Observation.fault

/-- Fault construction preserves both independent evidence sets. -/
theorem combined_two_faults {V : Type} (normal own : Evidence) :
    combinedFault (V := V) (some own) (.fault normal) = some (.fault (normal ∪ own)) := rfl

/-- With no freeze fault, ordinary errors remain terminal and unchanged. -/
theorem combined_no_freeze {V : Type} (normal : Result V) :
    combinedFault none normal = match normal with | .fault evidence => some (.fault evidence) | .data _ => none := by
  cases normal <;> rfl

/-- Fixed frozen presentation consumes only the source payload; a terminal
source fault is retained and a semantically absent payload stays pending. -/
def frozen {V : Type} (root : Nat) (excluded : FinSet Act) : Result V → Result V
  | .fault evidence => .fault evidence
  | .data current => match current.payload with
      | none => .data .pending
      | some value => .data (.frozen root value excluded)

/-- Derived reads of frozen presentation retain the same underlying value. -/
theorem derived_frozen {V W : Type} (post : V → W) (root : Nat) (excluded : FinSet Act) (result : Result V) :
    nativeDerived post (frozen root excluded result) = nativeDerived post result := by
  cases result with
  | fault _ => rfl
  | data current => cases current <;> rfl

/-- Rewrapping a historical result replaces metadata without altering payloads. -/
theorem frozen_unfrozen {V : Type} (root : Nat) (excluded : FinSet Act) (result : Result V) :
    frozen root excluded (unfrozen result) = frozen root excluded result := by
  cases result with
  | fault _ => rfl
  | data current => cases current <;> rfl

/-- A recursive same-field cut read can carry its own frozen wrapper; the
outer scope replaces that wrapper and preserves the cut's underlying payload. -/
theorem frozen_nested {V : Type} (outer inner : Nat) (outerExcluded innerExcluded : FinSet Act) (result : Result V) :
    frozen outer outerExcluded (frozen inner innerExcluded result) = frozen outer outerExcluded result := by
  cases result with
  | fault _ => rfl
  | data current => cases current <;> rfl

/-- Scoped source error extraction is exactly the native reader's error pass. -/
theorem scoped_error {V : Type} (world : Act → Prop) (whole scope : List Act) (plan : Plan V) :
    sourceError (scopedObserve world whole plan scope) = StateNativeReader.error world whole plan scope := by
  cases found : StateNativeReader.error world whole plan scope <;> simp [scopedObserve,sourceError,found]

/-- Combining local source errors and global freeze errors is precisely the
compiled native freeze node's complete fault pass, including both witnesses. -/
theorem freeze_error_refinement {V : Type} (world : Act → Prop) (whole scope : List Act)
    (spec : FreezeSpec) (source : Plan V) :
    combinedFault (freezeFault world spec.verb spec.contributes spec.policy none whole)
      (scopedObserve world whole source scope) =
      (StateNativeReader.error world whole (.freeze spec source) scope).map StateObservationPlan.Observation.fault := by
  simp only [combinedFault,scoped_error,StateNativeReader.error]

/-- On a clear historical source, fixed presentation is exactly the native
compiled frozen data adapter, including missing semantic payloads. -/
theorem frozen_data_refinement {V : Type} (world : Act → Prop) (whole scope : List Act)
    (source : Plan V) (root : Nat) (excluded : FinSet Act)
    (clear : StateNativeReader.error world whole source scope = none) :
    frozen root excluded (scopedObserve world whole source scope) =
      .data (frozenData (.frozen root (StateNativeReader.value world whole source scope) excluded)) := by
  simp only [scopedObserve,clear,frozen,frozenData]
  cases (StateNativeReader.value world whole source scope).payload <;> rfl

/-- Clear scoped native errors stay clear in smaller closed scopes even
though nested freezes continue using their full-history global fault plans. -/
theorem scoped_clear {V : Type} (world : Act → Prop) (whole parent smaller : List Act) (plan : Plan V)
    (closed : CausallyClosed world smaller) (inside : ∀ act ∈ smaller, act ∈ parent)
    (clear : StateNativeReader.error world whole plan parent = none) :
    StateNativeReader.error world whole plan smaller = none := by
  induction plan with
  | snapshot _ | read _ _ => rfl
  | context decode | contextAs decode _ =>
    exact StateFreezeScopes.source_clear_in_scope world (.context decode) closed inside clear
  | domain _ _ opener field _ =>
    exact StateFreezeScopes.source_clear_in_scope world (.domain opener field) closed inside clear
  | guardCertified spec source ih =>
    have parts := (StateNativeReader.union_clear _ _).mp clear
    have own := StateFreezeScopes.source_clear_in_scope world (.certified spec) closed inside parts.1
    simp only [errors] at own
    simp only [StateNativeReader.error,own,ih parts.2,unionError]
  | guardThreshold spec source ih | threshold spec source ih =>
    have parts := (StateNativeReader.union_clear _ _).mp clear
    have own := StateFreezeScopes.source_clear_in_scope world (.threshold spec) closed inside parts.1
    simp only [errors] at own
    simp only [StateNativeReader.error,own,ih parts.2,unionError]
  | guardDomain opener field source ih =>
    have parts := (StateNativeReader.union_clear _ _).mp clear
    have own := StateFreezeScopes.source_clear_in_scope world (.domain opener field) closed inside parts.1
    simp only [errors] at own
    simp only [StateNativeReader.error,own,ih parts.2,unionError]
  | resource config decode source ih =>
    have parts := (StateNativeReader.union_clear _ _).mp clear
    have own := StateFreezeScopes.source_clear_in_scope world (.resource config decode) closed inside parts.1
    simp only [errors] at own
    simp only [StateNativeReader.error,own,ih parts.2,unionError]
  | embed _ source ih | map _ source ih | thresholdRaw _ _ _ source ih | thresholdOn _ _ source ih => exact ih clear
  | pair left right ihLeft ihRight =>
    have parts := (StateNativeReader.union_clear _ _).mp clear
    simp only [StateNativeReader.error,ihLeft parts.1,ihRight parts.2,unionError]
  | freeze spec source ih =>
    have parts := (StateNativeReader.union_clear _ _).mp clear
    simp only [StateNativeReader.error,ih parts.1,parts.2,unionError]

/-- A clear source cannot acquire a hidden error when the native reader
redirects into an accepted freezer's globally precomputed causal cut. -/
theorem cut_clear {V : Type} (world : Act → Prop) (whole parent : List Act) (source : Plan V)
    (wholeClosed : CausallyClosed world whole) (parentClosed : CausallyClosed world parent)
    (inside : ∀ act ∈ parent, act ∈ whole) (root : Act) (present : root ∈ parent)
    (clear : StateNativeReader.error world whole source parent = none) :
    StateNativeReader.error world whole source (causalCut world whole root) = none := by
  apply scoped_clear world whole parent (causalCut world whole root) source
    (StateFreezeScopes.causal_cut_closed wholeClosed root) _ clear
  intro act member
  have same := StateFreezeScopes.global_cut_in_scope wholeClosed parentClosed inside present
  exact (List.mem_filter.mp ((same act).mp member)).1

/-- Independent cached freeze adapter over completed scoped source reads.
Fault unions are resolved before the selected historical data is presented. -/
noncomputable def cachedFreezeRead {V : Type} (world : Act → Prop) (whole : List Act) (spec : FreezeSpec)
    (source : List Act → Result V) (scope : List Act) : Result V :=
  match unionError (sourceError (source scope))
      (freezeFault world spec.verb spec.contributes spec.policy none whole) with
  | some evidence => .fault evidence
  | none => presentFreeze (StateFreezeScopes.cachedFreeze world spec (fun cut => sourceData (source cut)) whole scope)

/-- The complete cached freeze adapter, with source errors and value wrappers,
agrees with the compiled native reader at every closed contained scope. -/
theorem cached_freeze_scoped {V : Type} (world : Act → Prop) (whole scope : List Act)
    (spec : FreezeSpec) (source : Plan V) (wholeClosed : CausallyClosed world whole)
    (scopeClosed : CausallyClosed world scope) (inside : ∀ act ∈ scope, act ∈ whole) :
    scopedObserve world whole (.freeze spec source) scope =
      cachedFreezeRead world whole spec (scopedObserve world whole source) scope := by
  classical
  cases raw : StateNativeReader.error world whole source scope with
  | some evidence =>
    cases own : freezeFault world spec.verb spec.contributes spec.policy none whole <;>
      simp [scopedObserve,StateNativeReader.error,cachedFreezeRead,sourceError,raw,own,unionError]
  | none =>
    cases own : freezeFault world spec.verb spec.contributes spec.policy none whole with
    | some evidence => simp [scopedObserve,StateNativeReader.error,cachedFreezeRead,sourceError,raw,own,unionError]
    | none =>
      have noConflict : ¬∃ a b, FreezeConflict world spec.verb spec.contributes spec.policy whole a b := by
        rintro ⟨a,b,bad⟩
        exact (StateNativeReader.freeze_clear world spec none whole).mp own |>.2 a b bad
      simp only [scopedObserve,StateNativeReader.error,raw,own,unionError,StateNativeReader.value,
        cachedFreezeRead,sourceError]
      simp only [StateFreezeScopes.cachedFreeze,if_neg noConflict]
      cases selected : whole.find? (fun act => decide (Earliest world spec.verb whole act)) with
      | none => simp [sourceData,presentFreeze,frozenData,raw]
      | some root =>
        by_cases present : root ∈ scope
        · have historicalClear := cut_clear world whole scope source wholeClosed scopeClosed inside root present raw
          simp [present,sourceData,presentFreeze,frozenData,historicalClear]
        · simp [present,sourceData,presentFreeze,frozenData,raw]

/-- Resolve scope data through the same constructed pool used by cache keys. -/
def scope (whole : List Act) (freezes : List (String × FreezeSpec)) (key : StateMemoizedReader.Key) : List Act :=
  ((StateScopePool.scopeAllocation whole freezes).2.scopes[key.1]?).getD []

/-- Read an original installed field source or its native aggregate operation.
Other IR forms are threshold/output entries, outside known source field reads. -/
noncomputable def normal {V : Type} (whole : List Act) (freezes : List (String × FreezeSpec))
    (fields : List (String × Rule V)) (key : StateMemoizedReader.Key) (dependency : Option (Result V)) : Result V :=
  match fields.lookup key.2 with
  | some (.source source) => sourceRead source (scope whole freezes key)
  | some (.derived post _) => nativeDerived post (dependency.getD (.data .pending))
  | _ => .data .pending

/-- Own freeze errors use the full normalized observation and the installed
contribution/policy metadata, never an observation-derived error callback. -/
noncomputable def ownFault (whole : List Act) (freezes : List (String × FreezeSpec)) (name : String) : Error :=
  match freezes.lookup name with
  | none => none
  | some spec =>
    let canonical := StateScopePool.normalize whole
    freezeFault (fun act => act ∈ canonical) spec.verb spec.contributes spec.policy none canonical

/-- Freeze presentation uses the constructed scope, selected accepted freezer,
and scoped contributor exclusions from the installed metadata. -/
noncomputable def presentation {V : Type} (whole : List Act) (freezes : List (String × FreezeSpec))
    (key : StateMemoizedReader.Key) (result : Result V) : Result V := by
  classical
  exact match freezes.lookup key.2 with
  | none => result
  | some spec =>
    let canonical := StateScopePool.normalize whole
    match StateScopePool.uniqueRoot canonical spec.verb with
    | none => result
    | some root => frozen root.addr (FinSet.mk ((scope whole freezes key).filter
        (fun act => decide (spec.contributes act ∧ ¬Ancestor (fun a => a ∈ canonical) act root)))) result

/-- All cache-machine leaves are constructed from original declarations,
resolved installed rules and the concrete full-history scope pool. -/
noncomputable def operations {V : Type} (entries : List StateAuthoredBindings.Entry) (whole : List Act)
    (fields : List (String × Rule V)) (freezes : List (String × FreezeSpec)) : StateMemoizedReader.Operations (Result V) :=
  let roots := (StateScopePool.selectedRoots (StateScopePool.normalize whole) freezes).map (fun (name,freezer) => (name,freezer.addr))
  let pool := (StateScopePool.scopeAllocation whole freezes).2
  { dependency := StateAuthoredDependencies.lookupDependency entries
    cut := StateScopePool.cutScope roots pool
    active := StateScopePool.active roots pool
    unfrozen := unfrozen
    normal := normal whole freezes fields
    fault := fun key value => combinedFault (ownFault whole freezes key.2) value
    frozen := presentation whole freezes }

/-- Reapplying prepared metadata construction leaves the fixed operations
unchanged; dependency/cut/active inputs are not detached supplied callbacks. -/
theorem operations_fixed {V : Type} (entries : List StateAuthoredBindings.Entry) (whole : List Act)
    (fields : List (String × Rule V)) (freezes : List (String × FreezeSpec)) :
    StateAuthoredDependencies.operations entries (StateScopePool.readerOperations whole freezes
      (operations entries whole fields freezes)) = operations entries whole fields freezes := rfl

/-- A fixed primitive normal leaf reads the constructed scope and agrees with
the compiled source, with no native-value or error callback assumption. -/
theorem normal_source {V : Type} (whole : List Act) (freezes : List (String × FreezeSpec))
    (fields : List (String × Rule V)) (key : StateMemoizedReader.Key) (source : Source V)
    (found : fields.lookup key.2 = some (.source source)) (dependency : Option (Result V)) (world : Act → Prop) :
    normal whole freezes fields key dependency =
      scopedObserve world (StateScopePool.normalize whole) (sourcePlan source) (scope whole freezes key) := by
  simp only [normal,found]
  exact (source_scoped_refinement world _ source _).symm

/-- Fixed derived normal leaves consume the actual scoped dependency payload. -/
theorem normal_derived {V : Type} (whole : List Act) (freezes : List (String × FreezeSpec))
    (fields : List (String × Rule V)) (key : StateMemoizedReader.Key) (post : V → V) (name : String)
    (found : fields.lookup key.2 = some (.derived post name)) (source : Plan V) (world : Act → Prop) :
    normal whole freezes fields key (some (unfrozen (scopedObserve world (StateScopePool.normalize whole) source
      (scope whole freezes key)))) =
      scopedObserve world (StateScopePool.normalize whole) (.map post source) (scope whole freezes key) := by
  simp only [normal,found,Option.getD_some]
  exact (derived_scoped_refinement world _ _ post source).symm

/-- Concrete source definitions with at most one reference are exactly within
the native reader's primitive/derived field inventory. -/
def supported {V : Type} : Rule V → Prop
  | .source _ | .derived _ _ => True
  | _ => False

/-- Lowering a concrete definition cannot hide a pair behind a one-source
native dependency inventory. -/
theorem supported_definition {V : Type} (definition : StateInstalledLowering.Definition V)
    (bound : (references (StateInstalledLowering.lowerDefinition definition)).length ≤ 1) :
    supported (StateInstalledLowering.lowerDefinition definition) := by
  cases definition <;> simp [StateInstalledLowering.lowerDefinition,references,supported] at bound ⊢

/-- Every original field retained by preparation has a supported compiled
normal leaf; threshold/output IR forms cannot replace it. -/
theorem prepared_supported (environment : StateAuthoredBindings.Environment) (entries : List StateAuthoredBindings.Entry)
    (history : List Act) (clause : StateInstalledLowering.Clause StateInstalledLegacy.Value)
    (prepared : StateAuthoredBindings.prepare environment entries history = some clause)
    (fields : List (String × Rule StateInstalledLegacy.Value))
    (resolved : StateInstalledLowering.resolve [] clause.declarations = some fields)
    (name : String) (raw : StateAuthoredBindings.Rule) (present : (name,raw) ∈ StateAuthoredBindings.rawFields entries) :
    ∃ rule, (name,rule) ∈ fields ∧ supported rule := by
  obtain ⟨definition,declared,exactDeps⟩ := StateAuthoredDependencies.prepared_dependencies
    environment entries history clause prepared name raw present
  refine ⟨StateInstalledLowering.lowerDefinition definition,
    StateAuthoredDependencies.resolve_field [] clause.declarations fields resolved name definition declared,
    supported_definition definition ?_⟩
  rw [exactDeps]
  cases StateAuthoredDependencies.dependency raw <;> simp

/-- Authored preparation now constructs scope and cache execution with fixed
source/fault/presentation operations. The remaining refinement is the recursive
whole-reader equation, not a caller-supplied leaf classifier. -/
theorem prepared_fixed_cache (environment : StateAuthoredBindings.Environment) (entries : List StateAuthoredBindings.Entry)
    (history : List Act) (clause : StateInstalledLowering.Clause StateInstalledLegacy.Value)
    (prepared : StateAuthoredBindings.prepare environment entries history = some clause)
    (keys : List StateMemoizedReader.Key) (ranked : StateExecutableFreeze.Ranked history)
    (consistent : ∀ a ∈ history, ∀ b ∈ history, a.addr = b.addr → a = b) :
    ∃ plans fields, StateAuthoredBindings.compile environment entries history = some plans ∧
      StateInstalledLowering.resolve [] clause.declarations = some fields ∧
      StateScopePool.ScopeSound history clause.freezes ∧
      let ops := operations entries history fields clause.freezes
      let rank := StateMemoizedReader.requestRank (fields.map Prod.fst).idxOf ops.cut
      ∃ ranked : ∀ key, (ops.body key).Below rank (rank key),
        ∃ after, StateMemoizedReader.reads ops.body rank keys [] =
          some (keys.map (StateMemoizedReader.reference ops.body rank ranked),after) ∧
          StateMemoizedReader.Valid (StateMemoizedReader.reference ops.body rank ranked) after := by
  obtain ⟨plans,compiled⟩ := StateAuthoredBindings.prepared_compiler_complete environment entries history clause prepared
  have lowered : StateInstalledLowering.compile clause = some plans := by
    simpa [StateAuthoredBindings.compile,prepared] using compiled
  obtain ⟨fields,resolved,fieldCompiled⟩ := StateAuthoredDependencies.lowered_compiled_clause clause plans lowered
  let ops := operations entries history fields clause.freezes
  have extracted : ∀ name source, ops.dependency name = some source →
      ∃ rule, (name,rule) ∈ fields ∧ source ∈ references rule :=
    StateAuthoredDependencies.extracted_reference environment entries history clause prepared fields resolved
  have ordering := StateReaderIndices.compiled_dependency_ordering ⟨fields,clause.freezes⟩ plans fieldCompiled ops extracted
  exact ⟨plans,fields,compiled,resolved,StateScopePool.normalized_scopes_sound history ranked consistent clause.freezes,
    StateMemoizedReader.body_ranked ops (fields.map Prod.fst).idxOf ordering,
    StateMemoizedReader.native_reads_refinement ops (fields.map Prod.fst).idxOf ordering keys⟩

end CBCL.StateReaderValues
