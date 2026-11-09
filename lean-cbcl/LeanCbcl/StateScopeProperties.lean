import LeanCbcl.StateCompiledFieldEquations

/-! Semantic provenance and freeze metadata for every allocated native scope.
The resulting closure/subset facts justify nested historical reads rather than
assuming valid scope indices alone imply valid causal subhistories. -/
set_option autoImplicit false
namespace CBCL.StateScopeProperties
open State StateLift StateLVar StateObservation StateObservationPlan StateScopePool

/-- Interning preserves a property of all scope values if the new cut has it. -/
theorem intern_property {V : Type} (property : V → Prop) (cut : Nat → V) (pool : Pool V) (root : Nat)
    (old : ∀ value ∈ pool.scopes, property value) (new : property (cut root)) :
    ∀ value ∈ (intern cut pool root).2.scopes, property value := by
  cases found : pool.indices.lookup root with
  | some _ => simpa [intern,found] using old
  | none =>
    intro value member
    have selected : value ∈ pool.scopes ∨ value = cut root := by simpa [intern,found] using member
    rcases selected with present | rfl
    · exact old value present
    · exact new

/-- Batched cut allocation preserves every semantic property supplied by the
initial full-history scope and each accepted requested cut. -/
theorem allocate_property {V : Type} (property : V → Prop) (cut : Nat → V) (requests : List (String × Nat))
    (pool : Pool V) (old : ∀ value ∈ pool.scopes, property value)
    (new : ∀ request ∈ requests, property (cut request.2)) :
    ∀ value ∈ (allocate cut requests pool).2.scopes, property value := by
  induction requests generalizing pool with
  | nil => exact old
  | cons request rest ih =>
    obtain ⟨name,root⟩ := request
    cases step : intern cut pool root with
    | mk index after =>
      have values := intern_property property cut pool root old (new (name,root) (by simp))
      simp only [step] at values
      simpa only [allocate,step] using ih after values (fun request member => new request (by simp [member]))

/-- Every allocated scope is full normalized history or an exact cut of an
accepted freezer. No unindexed arbitrary history can occur in the vector. -/
theorem scope_origin (whole : List Act) (freezes : List (String × FreezeSpec))
    (ranked : StateExecutableFreeze.Ranked whole)
    (consistent : ∀ a ∈ whole, ∀ b ∈ whole, a.addr = b.addr → a = b)
    (index : Nat) (history : List Act) (present : (scopeAllocation whole freezes).2.scopes[index]? = some history) :
    history = normalize whole ∨ ∃ root ∈ normalize whole,
      history = causalCut (fun act => act ∈ normalize whole) (normalize whole) root := by
  let canonical := normalize whole
  let property := fun history => history = canonical ∨ ∃ root ∈ canonical,
    history = causalCut (fun act => act ∈ canonical) canonical root
  have old : ∀ value ∈ (initial canonical).scopes, property value := by
    intro value member
    have same : value = canonical := by simpa [initial] using member
    exact .inl same
  have new : ∀ request ∈ (selectedRoots canonical freezes).map (fun (name,freezer) => (name,freezer.addr)),
      property (cutAt canonical request.2) := by
    intro request member
    obtain ⟨⟨name,freezer⟩,selected,equal⟩ := List.mem_map.mp member
    subst request
    have accepted := selectedRoots_accepted canonical freezes (name,freezer) selected
    exact .inr ⟨freezer,accepted,cutAt_refinement canonical (normalize_ranked whole ranked)
      (normalize_unique whole consistent) freezer accepted⟩
  have all := allocate_property property (cutAt canonical) _ (initial canonical) old new
  exact all history (List.mem_of_getElem? present)

/-- Every actual allocated history is closed, contained in full history and
address-unique. These facts are constructed for all scope indices at once. -/
theorem scope_properties (whole : List Act) (freezes : List (String × FreezeSpec))
    (ranked : StateExecutableFreeze.Ranked whole)
    (consistent : ∀ a ∈ whole, ∀ b ∈ whole, a.addr = b.addr → a = b)
    (index : Nat) (history : List Act) (present : (scopeAllocation whole freezes).2.scopes[index]? = some history) :
    CausallyClosed (fun act => act ∈ normalize whole) history ∧
      (∀ act ∈ history, act ∈ normalize whole) ∧ NodupAddr history := by
  have closed : CausallyClosed (fun act => act ∈ normalize whole) (normalize whole) := by
    intro child inside parent valid edge
    exact valid
  rcases scope_origin whole freezes ranked consistent index history present with same | ⟨root,accepted,same⟩
  · subst history
    exact ⟨closed,fun _ member => member,normalize_unique whole consistent⟩
  · subst history
    exact ⟨StateFreezeScopes.causal_cut_closed closed root,
      fun _ member => (List.mem_filter.mp member).1,(normalize_unique whole consistent).filter _⟩

/-- Root selection preserves each freeze declaration's exact field lookup,
including the absent-root case, under the compiler's unique freeze namespace. -/
theorem root_lookup (whole : List Act) (freezes : List (String × FreezeSpec)) (unique : (freezes.map Prod.fst).Nodup)
    (name : String) :
    ((selectedRoots whole freezes).map (fun (field,freezer) => (field,freezer.addr))).lookup name =
      (freezes.lookup name).bind (fun spec => (uniqueRoot whole spec.verb).map Act.addr) := by
  induction freezes with
  | nil => rfl
  | cons binding rest ih =>
    obtain ⟨field,spec⟩ := binding
    obtain ⟨fresh,tailUnique⟩ := List.nodup_cons.mp unique
    by_cases same : name = field
    · subst name
      cases selected : uniqueRoot whole spec.verb with
      | some root => simp [selectedRoots,selected]
      | none =>
        have absent : rest.lookup field = none := by
          apply List.lookup_eq_none_iff.mpr
          intro binding member
          have different : field ≠ binding.1 := by
            intro equal
            exact fresh (List.mem_map.mpr ⟨binding,member,equal.symm⟩)
          simpa using different
        simp only [selectedRoots,List.filterMap_cons,selected,Option.map_none,
          List.lookup_cons_self,Option.bind_some]
        exact StateCompiledFieldEquations.missing_freeze_root whole rest field absent
    · cases selected : uniqueRoot whole spec.verb <;>
        simpa [selectedRoots,selected,List.lookup,beq_eq_false_iff_ne.mpr same] using ih tailUnique

/-- A clear global freeze has the same unique selected root in executable pool
metadata and the compiled native reader's declarative earliest-freezer search. -/
theorem root_find (whole : List Act) (ranked : StateExecutableFreeze.Ranked whole) (unique : NodupAddr whole)
    (spec : FreezeSpec) (clear : ∀ a b, ¬FreezeConflict (fun act => act ∈ whole) spec.verb spec.contributes spec.policy whole a b) :
    uniqueRoot whole spec.verb =
      (by classical exact whole.find? (fun root => decide (Earliest (fun act => act ∈ whole) spec.verb whole root))) := by
  classical
  cases found : whole.find? (fun root => decide (Earliest (fun act => act ∈ whole) spec.verb whole root)) with
  | none =>
    cases selected : uniqueRoot whole spec.verb with
    | none => rfl
    | some root =>
      have first := uniqueRoot_earliest whole ranked spec.verb root selected
      have rejected := List.find?_eq_none.mp found root first.1
      exact False.elim (rejected (decide_eq_true first))
  | some root =>
    have first : Earliest (fun act => act ∈ whole) spec.verb whole root :=
      of_decide_eq_true (List.find?_some (p := fun root => decide (Earliest (fun act => act ∈ whole) spec.verb whole root)) found)
    apply uniqueRoot_complete whole ranked root spec.verb first
    intro other earlier
    by_cases same : other.addr = root.addr
    · exact unique.eq_of_addr earlier.1 first.1 same
    · exact False.elim (clear other root (.concurrent earlier first same))

/-- Successful installed compilation constructs the freeze namespace used by
exact root lookup; callers do not supply a fresh-name assumption separately. -/
theorem compiled_freezes_unique {V : Type} (clause : StateInstalledClause.Clause V) (plans : StateInstalledCompiler.Plans V)
    (compiled : StateInstalledClause.compile clause = some plans) : (clause.freezes.map Prod.fst).Nodup := by
  unfold StateInstalledClause.compile at compiled
  split at compiled
  · rename_i metadata; exact metadata.2.1
  · contradiction

/-- Every admitted scope is a closed, unique causal subhistory of the same full
observation, so nested native freeze refinement hypotheses are available. -/
theorem admitted_properties (entries : List StateAuthoredBindings.Entry) (whole : List Act)
    (freezes : List (String × FreezeSpec)) (ranked : StateExecutableFreeze.Ranked whole)
    (consistent : ∀ a ∈ whole, ∀ b ∈ whole, a.addr = b.addr → a = b)
    (key : StateMemoizedReader.Key) (admitted : StateReaderReachability.Admitted entries whole freezes key) :
    CausallyClosed (fun act => act ∈ normalize whole) (StateReaderValues.scope whole freezes key) ∧
      (∀ act ∈ StateReaderValues.scope whole freezes key, act ∈ normalize whole) ∧
      NodupAddr (StateReaderValues.scope whole freezes key) := by
  obtain ⟨history,present,same⟩ := StateReaderReachability.admitted_scope entries whole freezes key admitted
  rw [same]
  exact scope_properties whole freezes ranked consistent key.1 history present

/-- Fixed scoped exclusion metadata used by both semantic freeze presentation
and the native cache wrapper. -/
noncomputable def exclusions (whole : List Act) (freezes : List (String × FreezeSpec)) (key : StateMemoizedReader.Key)
    (spec : FreezeSpec) (root : Act) : FinSet Act := by
  classical
  exact FinSet.mk ((StateReaderValues.scope whole freezes key).filter
    (fun act => decide (spec.contributes act ∧ ¬Ancestor (fun a => a ∈ normalize whole) act root)))

/-- An unselected global freezer cannot create a cut, active flag or wrapper
in the fixed reader, even when another field has an allocated freeze scope. -/
theorem absent_root_metadata {V : Type} (entries : List StateAuthoredBindings.Entry) (whole : List Act)
    (fields : List (String × StateInstalledCompiler.Rule V)) (freezes : List (String × FreezeSpec))
    (unique : (freezes.map Prod.fst).Nodup) (key : StateMemoizedReader.Key) (spec : FreezeSpec)
    (declared : freezes.lookup key.2 = some spec) (absent : uniqueRoot (normalize whole) spec.verb = none) :
    let ops := StateReaderValues.operations entries whole fields freezes
    ops.cut key.2 = none ∧ ops.active key = false ∧ ∀ value, ops.frozen key value = value := by
  have missing : ((selectedRoots (normalize whole) freezes).map (fun (field,root) => (field,root.addr))).lookup key.2 = none := by
    rw [root_lookup (normalize whole) freezes unique key.2,declared]
    simp [absent]
  simp [StateReaderValues.operations,cutScope,active,missing,StateReaderValues.presentation,declared,absent]

/-- Selected root metadata retrieves the precise allocated cut; active status
is semantic root membership, and presentation uses the exact scoped exclusions. -/
theorem selected_root_metadata {V : Type} (entries : List StateAuthoredBindings.Entry) (whole : List Act)
    (fields : List (String × StateInstalledCompiler.Rule V)) (freezes : List (String × FreezeSpec))
    (ranked : StateExecutableFreeze.Ranked whole)
    (consistent : ∀ a ∈ whole, ∀ b ∈ whole, a.addr = b.addr → a = b)
    (unique : (freezes.map Prod.fst).Nodup) (key : StateMemoizedReader.Key)
    (admitted : StateReaderReachability.Admitted entries whole freezes key) (spec : FreezeSpec)
    (declared : freezes.lookup key.2 = some spec) (root : Act)
    (selected : uniqueRoot (normalize whole) spec.verb = some root) :
    let ops := StateReaderValues.operations entries whole fields freezes
    ∃ index, ops.cut key.2 = some index ∧
      StateReaderValues.scope whole freezes (index,key.2) =
        causalCut (fun act => act ∈ normalize whole) (normalize whole) root ∧
      (ops.active key = true ↔ root ∈ StateReaderValues.scope whole freezes key) ∧
      (∀ value, ops.frozen key value = StateReaderValues.frozen root.addr (exclusions whole freezes key spec root) value) := by
  classical
  let roots := (selectedRoots (normalize whole) freezes).map (fun (field,root) => (field,root.addr))
  let pool := (scopeAllocation whole freezes).2
  have rootLookup : roots.lookup key.2 = some root.addr := by
    rw [root_lookup (normalize whole) freezes unique key.2,declared]
    simp [selected]
  obtain ⟨before,after,equal,_⟩ := List.lookup_eq_some_iff.mp declared
  have specMember : (key.2,spec) ∈ freezes := by simp [equal]
  have request : (key.2,root) ∈ selectedRoots (normalize whole) freezes :=
    List.mem_filterMap.mpr ⟨(key.2,spec),specMember,by simp [selected]⟩
  obtain ⟨index,_,cached,cut⟩ := (normalized_scopes_sound whole ranked consistent freezes).2 key.2 root request
  refine ⟨index,?_,?_,?_,?_⟩
  · change (roots.lookup key.2).bind (fun address => pool.indices.lookup address) = some index
    rw [rootLookup]
    exact cached
  · simp only [StateReaderValues.scope,cut,Option.getD_some]
  · obtain ⟨history,present,same⟩ := StateReaderReachability.admitted_scope entries whole freezes key admitted
    change active roots pool key = true ↔ root ∈ StateReaderValues.scope whole freezes key
    rw [active_iff roots pool key root.addr history rootLookup present,same]
    constructor
    · rintro ⟨act,member,address⟩
      have inside := (scope_properties whole freezes ranked consistent key.1 history present).2.1 act member
      have accepted := (uniqueRoot_accepted (normalize whole) spec.verb root selected).1
      have equal := (normalize_unique whole consistent).eq_of_addr inside accepted address
      exact equal ▸ member
    · intro member; exact ⟨root,member,rfl⟩
  · intro value
    simp only [StateReaderValues.operations,StateReaderValues.presentation,declared,selected,exclusions]


end CBCL.StateScopeProperties

