import LeanCbcl.StateFreezeScopes

/-! Functional native scoped-reader semantics. Source error checks run in the
current scope, while each freeze's conflict/cut plan is fixed from full history.
This functional model is independent of recursive local freeze selection;
correspondence to mutable Rust cache entries is a separate obligation. Leaf extraction remains the
same explicit typed boundary as the concrete source factories. -/
set_option autoImplicit false
namespace CBCL.StateNativeReader
open State StateLift StateLVar StateObservation StateObservationPlan StateFreezeScopes

/-- A freeze error is the union of its source error and its own conflict plan. -/
theorem freeze_error_union (world : Act → Prop) (spec : FreezeSpec) (raw : Error) (A : List Act) :
    freezeFault world spec.verb spec.contributes spec.policy raw A =
      unionError raw (freezeFault world spec.verb spec.contributes spec.policy none A) := by
  classical
  have leftEmpty (e : Evidence) : (∅ : Evidence) ∪ e = e := by
    funext address
    apply propext
    change (False ∨ e address) ↔ e address
    simp
  have rightEmpty (e : Evidence) : e ∪ (∅ : Evidence) = e := by
    funext address
    apply propext
    change (e address ∨ False) ↔ e address
    simp
  by_cases conflict : ∃ a b, FreezeConflict world spec.verb spec.contributes spec.policy A a b
  · cases raw <;> simp [freezeFault,conflict,unionError,leftEmpty]
  · have empty : freezeEvidence world spec.verb spec.contributes spec.policy A = ∅ := by
      funext address
      apply propext
      constructor
      · rintro ⟨a,b,bad,_⟩; exact conflict ⟨a,b,bad⟩
      · intro impossible; exact False.elim impossible
    cases raw <;> simp [freezeFault,conflict,empty,unionError,rightEmpty]

/-- Scoped native error pass: source guards use the current scope, whereas
freeze conflicts always use their globally precomputed full-history plan. -/
noncomputable def error (world : Act → Prop) (whole : List Act) : {V : Type} → Plan V → List Act → Error
  | _, .snapshot _, _ => none
  | _, .read _ _, _ => none
  | _, .guardCertified spec source, scope => unionError (spec.read scope) (error world whole source scope)
  | _, .context decode, scope => contextError (StateContext.read decode scope)
  | _, .contextAs decode _, scope => contextError (StateContext.read decode scope)
  | _, .guardThreshold spec source, scope => unionError (thresholdError spec scope) (error world whole source scope)
  | _, .domain _ _ opener field _, scope => domainError opener field scope
  | _, .embed _ source, scope => error world whole source scope
  | _, .map _ source, scope => error world whole source scope
  | _, .pair left right, scope => unionError (error world whole left scope) (error world whole right scope)
  | _, .guardDomain opener field source, scope => unionError (domainError opener field scope) (error world whole source scope)
  | _, .resource config decode source, scope => unionError (StateResource.faultRead config decode scope) (error world whole source scope)
  | _, .threshold spec source, scope => unionError (thresholdError spec scope) (error world whole source scope)
  | _, .thresholdRaw _ _ _ source, scope => error world whole source scope
  | _, .thresholdOn _ _ source, scope => error world whole source scope
  | _, .freeze spec source, scope => unionError (error world whole source scope)
      (freezeFault world spec.verb spec.contributes spec.policy none whole)

/-- Scoped native value pass. Cached global cuts are reused at every freeze;
source dependencies are evaluated in that selected scope, not at full history. -/
noncomputable def value (world : Act → Prop) (whole : List Act) : {V : Type} → Plan V → List Act → Data V
  | _, .snapshot display, scope => .snapshot (display (rawHistory scope))
  | _, .read contextual read, scope => optionalData contextual (read (rawHistory scope))
  | _, .guardCertified _ source, scope => value world whole source scope
  | _, .context decode, scope => match StateContext.read decode scope with
      | .pending | .fault _ => .pending
      | .value v => .context v
  | _, .contextAs decode embed, scope => match StateContext.read decode scope with
      | .pending | .fault _ => .pending
      | .value v => .context (embed v)
  | _, .guardThreshold _ source, scope => value world whole source scope
  | _, .domain verb key opener field display, scope => .snapshot (display (FinSet.mk (initialDomain verb key opener field scope)))
  | _, .embed f source, scope => embedData f (value world whole source scope)
  | _, .map f source, scope => mapData f (value world whole source scope)
  | _, .pair left right, scope => pairData (value world whole left scope) (value world whole right scope)
  | _, .guardDomain _ _ source, scope => value world whole source scope
  | _, .resource _ _ source, scope => value world whole source scope
  | _, .threshold spec source, scope =>
      letI := spec.algebra
      match thresholdRead spec.alternatives (lift spec.contribution scope)
          (error world whole source scope).isSome (rawHistory scope) with
      | .pending | .fault _ => .pending
      | .reached q => .reached q
  | _, .thresholdRaw alternatives test state _, scope =>
      match alternatives.find? (fun query => test query (state (rawHistory scope))) with
      | none => .pending
      | some query => .reached query
  | _, .thresholdOn alternatives test source, scope => match (value world whole source scope).payload with
      | none => .pending
      | some current => match alternatives.find? (fun query => test query current) with
          | none => .pending
          | some query => .reached query
  | _, .freeze spec source, scope => frozenData (cachedFreeze world spec (fun cut => value world whole source cut) whole scope)

/-- The native full observation checks its composed error pass before exposing
snapshot, contextual, reached or frozen data. -/
noncomputable def observe (world : Act → Prop) {V : Type} (plan : Plan V) (whole : List Act) : Observation V :=
  match error world whole plan whole with
  | some evidence => .fault evidence
  | none => .data (value world whole plan whole)

/-- Faulting and nonfaulting full-history headers agree exactly for all plans.
This is an error-pass theorem, not a clear-history conditional. -/
theorem full_error_refinement (world : Act → Prop) {V : Type} (plan : Plan V) (A : List Act) :
    error world A plan A = errors world (path plan) A := by
  induction plan with
  | snapshot _ | read _ _ | context _ | contextAs _ _ | domain _ _ _ _ _ => rfl
  | guardCertified spec source ih | guardThreshold spec source ih | guardDomain opener field source ih
  | resource config decode source ih | threshold spec source ih =>
    simp only [error,path,errors,ih]
  | embed f source ih | map f source ih | thresholdRaw alternatives test state source ih
  | thresholdOn alternatives test source ih => exact ih
  | pair left right ihLeft ihRight => simp only [error,path,errors,ihLeft,ihRight]
  | freeze spec source ih =>
    simp only [error,path,errors,ih]
    exact (freeze_error_union world spec _ A).symm

/-- Independent source errors are both clear exactly when their union is clear. -/
theorem union_clear (left right : Error) : unionError left right = none ↔ left = none ∧ right = none := by
  cases left <;> cases right <;> simp [unionError]

/-- Freeze clarity discharges both raw source faults and all concrete freeze witnesses. -/
theorem freeze_clear (world : Act → Prop) (spec : FreezeSpec) (raw : Error) (A : List Act) :
    freezeFault world spec.verb spec.contributes spec.policy raw A = none ↔
      raw = none ∧ ∀ a b, ¬FreezeConflict world spec.verb spec.contributes spec.policy A a b := by
  classical
  cases raw <;> simp [freezeFault]

/-- A globally clear source stays clear under the native scoped error pass,
including globally planned freeze conflicts that are outside the smaller cut. -/
theorem scoped_error_clear (world : Act → Prop) {V : Type} (plan : Plan V) (whole scope : List Act)
    (scopeClosed : CausallyClosed world scope) (inside : ∀ act ∈ scope, act ∈ whole)
    (clear : errors world (path plan) whole = none) : error world whole plan scope = none := by
  induction plan with
  | snapshot _ | read _ _ | context _ | contextAs _ _ | domain _ _ _ _ _ =>
    exact source_clear_in_scope world _ scopeClosed inside clear
  | guardCertified spec source ih | guardThreshold spec source ih | guardDomain opener field source ih
  | resource config decode source ih | threshold spec source ih =>
    have globalParts := (union_clear _ _).mp clear
    have localClear := source_clear_in_scope world _ scopeClosed inside clear
    have localParts := (union_clear _ _).mp localClear
    have own := localParts.1
    simp only [errors] at own
    simp only [error,ih globalParts.2,own,unionError]
  | embed f source ih | map f source ih | thresholdRaw alternatives test state source ih
  | thresholdOn alternatives test source ih => exact ih clear
  | pair left right ihLeft ihRight =>
    have parts := (union_clear _ _).mp clear
    simp only [error,ihLeft parts.1,ihRight parts.2,unionError]
  | freeze spec source ih =>
    have parts := (freeze_clear world spec _ whole).mp clear
    have own : freezeFault world spec.verb spec.contributes spec.policy none whole = none :=
      (freeze_clear world spec none whole).mpr ⟨rfl,parts.2⟩
    simp only [error,ih parts.1,own,unionError]

/-- Cached freeze evaluation calls only the current scope and accepted global
freezer cuts; equal reads at those scopes suffice for identical cached results. -/
theorem cached_congr {V : Type} (world : Act → Prop) (spec : FreezeSpec)
    (first second : List Act → V) (whole scope : List Act)
    (current : first scope = second scope)
    (cuts : ∀ freezer ∈ whole, first (causalCut world whole freezer) = second (causalCut world whole freezer)) :
    cachedFreeze world spec first whole scope = cachedFreeze world spec second whole scope := by
  classical
  unfold cachedFreeze
  split
  · rfl
  · cases selected : whole.find? (fun f => decide (Earliest world spec.verb whole f)) with
    | none => simp [current]
    | some freezer => simp [current,cuts freezer (List.mem_of_find?_eq_some selected)]

/-- The independent cached native value pass agrees at every closed sub-scope
of a clear full observation, with all nested freeze dependencies included. -/
theorem scoped_value_refinement (world : Act → Prop) {V : Type} (plan : Plan V) (whole scope : List Act)
    (globalClosed : CausallyClosed world whole) (uniqueWhole : NodupAddr whole)
    (scopeClosed : CausallyClosed world scope) (uniqueScope : NodupAddr scope)
    (inside : ∀ act ∈ scope, act ∈ whole) (clear : errors world (path plan) whole = none) :
    value world whole plan scope = data world plan scope := by
  induction plan generalizing scope with
  | snapshot _ | read _ _ | context _ | contextAs _ _ | domain _ _ _ _ _ => rfl
  | guardCertified spec source ih | guardThreshold spec source ih | guardDomain opener field source ih
  | resource config decode source ih =>
    have parts := (union_clear _ _).mp clear
    exact ih scope scopeClosed uniqueScope inside parts.2
  | embed f source ih =>
    simp only [value,data,ih scope scopeClosed uniqueScope inside clear]
  | map f source ih =>
    simp only [value,data,ih scope scopeClosed uniqueScope inside clear]
  | pair left right ihLeft ihRight =>
    have parts := (union_clear _ _).mp clear
    simp only [value,data,ihLeft scope scopeClosed uniqueScope inside parts.1,
      ihRight scope scopeClosed uniqueScope inside parts.2]
  | threshold spec source _ =>
    have parts := (union_clear _ _).mp clear
    have nativeClear := scoped_error_clear world source whole scope scopeClosed inside parts.2
    have originalClear := source_clear_in_scope world (path source) scopeClosed inside parts.2
    simp only [value,data,nativeClear,originalClear]
    rfl
  | thresholdRaw alternatives test state source _ => rfl
  | thresholdOn alternatives test source ih =>
    simp only [value,data,ih scope scopeClosed uniqueScope inside clear]
    rfl
  | freeze spec source ih =>
    have parts := (freeze_clear world spec _ whole).mp clear
    have current := ih scope scopeClosed uniqueScope inside parts.1
    have cuts : ∀ freezer ∈ whole, value world whole source (causalCut world whole freezer) =
        data world source (causalCut world whole freezer) := by
      intro freezer member
      apply ih (causalCut world whole freezer) (causal_cut_closed globalClosed freezer) (uniqueWhole.filter _)
      · intro act accepted; exact (List.mem_filter.mp accepted).1
      · exact parts.1
    change frozenData (cachedFreeze world spec (fun cut => value world whole source cut) whole scope) = _
    rw [cached_congr world spec _ _ whole scope current cuts]
    exact cached_plan_data_refinement world spec source whole scope globalClosed scopeClosed inside uniqueWhole uniqueScope parts.1 parts.2

/-- The complete cached native scoped reader equals the observation plan on
accepted closed unique histories, including every faulting observation. -/
theorem native_reader_refinement (world : Act → Prop) {V : Type} (plan : Plan V) (A : List Act)
    (closed : CausallyClosed world A) (unique : NodupAddr A) :
    observe world plan A = StateObservationPlan.observe world plan A := by
  unfold observe StateObservationPlan.observe
  rw [full_error_refinement]
  cases clear : errors world (path plan) A with
  | some evidence => rfl
  | none =>
    rw [scoped_value_refinement world plan A A closed unique closed unique (fun _ member => member) clear]

end CBCL.StateNativeReader
