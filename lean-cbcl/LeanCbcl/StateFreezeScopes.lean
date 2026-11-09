import LeanCbcl.StateFreezeGrowth

/-! Native global freeze plans and nested causal scopes. The native reader
computes each freezer and its cut once from the full accepted history. These
lemmas justify reusing that global plan inside a closed nested scope. -/
set_option autoImplicit false
namespace CBCL.StateFreezeScopes
open State StateLift StateLVar StateObservation

/-- Every causal cut of an accepted causally closed history is itself closed. -/
theorem causal_cut_closed {world : Act → Prop} {A : List Act} (closed : CausallyClosed world A) (freezer : Act) :
    CausallyClosed world (causalCut world A freezer) := by
  classical
  intro child member parent valid edge
  obtain ⟨accepted,path⟩ := List.mem_filter.mp member
  have ancestry : Ancestor world child freezer := of_decide_eq_true path
  apply List.mem_filter.mpr
  exact ⟨closed child accepted parent valid edge,decide_eq_true (Ancestor.step valid edge ancestry)⟩

/-- A closed scope sees exactly the global earliest freezers that it contains. -/
theorem earliest_scope {world : Act → Prop} {verb : String} {whole scope : List Act}
    (closed : CausallyClosed world scope) (inside : ∀ act ∈ scope, act ∈ whole) (freezer : Act) :
    Earliest world verb scope freezer ↔ freezer ∈ scope ∧ Earliest world verb whole freezer := by
  constructor
  · intro first
    exact ⟨first.1,earliest_transfer closed first (inside freezer first.1)⟩
  · rintro ⟨member,first⟩
    exact ⟨member,first.2.1,fun earlier accepted selected path => first.2.2 earlier (inside earlier accepted) selected path⟩

/-- Any scoped freeze conflict is already a full-observation conflict. Native
freezer faults cannot be concealed by evaluating a dependency at a smaller cut. -/
theorem scoped_conflict_global {world : Act → Prop} {verb : String} {contributes : Act → Prop}
    {policy : Bool} {whole scope : List Act} {a b : Act}
    (closed : CausallyClosed world scope) (inside : ∀ act ∈ scope, act ∈ whole)
    (conflict : FreezeConflict world verb contributes policy scope a b) :
    FreezeConflict world verb contributes policy whole a b := by
  have accepted := freeze_witness_accepted conflict
  exact freeze_witness_transfer closed conflict (inside a accepted.1) (inside b accepted.2)

/-- The global freezer's precomputed cut equals the local cut in every closed
scope containing that freezer. Equality is semantic set equality, not list order. -/
theorem global_cut_in_scope {world : Act → Prop} {whole scope : List Act} {freezer : Act}
    (globalClosed : CausallyClosed world whole) (scopeClosed : CausallyClosed world scope)
    (inside : ∀ act ∈ scope, act ∈ whole) (member : freezer ∈ scope) :
    SetEq (causalCut world whole freezer) (causalCut world scope freezer) :=
  causalCut_agreement globalClosed scopeClosed (inside freezer member) member

/-- If a global selected freezer is absent, a closed scope cannot contain a
different earliest freezer when the full history has no concurrent-freezer fault. -/
theorem absent_global_freezer_no_scoped_freezer {world : Act → Prop} {verb : String}
    {whole scope : List Act} {freezer : Act} (scopeClosed : CausallyClosed world scope)
    (inside : ∀ act ∈ scope, act ∈ whole) (unique : NodupAddr whole)
    (first : Earliest world verb whole freezer) (absent : freezer ∉ scope)
    (noConcurrent : ∀ a b, ¬FreezeConflict world verb (fun _ => False) false whole a b) :
    ∀ localFreezer, ¬Earliest world verb scope localFreezer := by
  intro localFreezer localFirst
  have globalFirst := ((earliest_scope scopeClosed inside localFreezer).mp localFirst).2
  have equalAddress : freezer.addr = localFreezer.addr := by
    by_cases same : freezer.addr = localFreezer.addr
    · exact same
    · exact False.elim (noConcurrent freezer localFreezer (.concurrent first globalFirst same))
  have same := unique.eq_of_addr first.1 globalFirst.1 equalAddress
  exact absent (same ▸ localFirst.1)

/-- Exclusion metadata inside a scope is precisely the global late-contributor
predicate restricted to that scope, independent of the cached cut's enumeration. -/
theorem excluded_restriction {world : Act → Prop} {whole scope : List Act} (inside : ∀ act ∈ scope, act ∈ whole)
    (contributes : Act → Prop) (freezer : Act) (act : Act) :
    (act ∈ scope ∧ contributes act ∧ ¬Ancestor world act freezer) ↔
      act ∈ scope ∧ act ∈ whole ∧ contributes act ∧ ¬Ancestor world act freezer := by
  constructor
  · rintro ⟨member,contribution,outside⟩
    exact ⟨member,inside act member,contribution,outside⟩
  · rintro ⟨member,_,contribution,outside⟩
    exact ⟨member,contribution,outside⟩

/-- The global unique earliest freezer is reused exactly when a closed scope
contains it; a scoped find cannot discover another hidden earlier freezer. -/
theorem selected_freezer_scope {world : Act → Prop} {verb : String} {contributes : Act → Prop} {policy : Bool}
    {whole scope : List Act} (scopeClosed : CausallyClosed world scope)
    (inside : ∀ act ∈ scope, act ∈ whole) (unique : NodupAddr whole)
    (clear : ∀ a b, ¬FreezeConflict world verb contributes policy whole a b) :
    (by classical exact scope.find? (fun f => decide (Earliest world verb scope f))) =
      (by classical exact (whole.find? (fun f => decide (Earliest world verb whole f))).filter (fun f => decide (f ∈ scope))) := by
  classical
  cases global : whole.find? (fun f => decide (Earliest world verb whole f)) with
  | none =>
    cases localFound : scope.find? (fun f => decide (Earliest world verb scope f)) with
    | none => rfl
    | some localFreezer =>
      have first := of_decide_eq_true (List.find?_some (p := fun f => decide (Earliest world verb scope f)) localFound)
      have globalFirst := ((earliest_scope scopeClosed inside localFreezer).mp first).2
      have rejected := List.find?_eq_none.mp global localFreezer globalFirst.1
      exact False.elim (rejected (by simpa using globalFirst))
  | some freezer =>
    have first : Earliest world verb whole freezer := of_decide_eq_true (List.find?_some (p := fun f => decide (Earliest world verb whole f)) global)
    by_cases member : freezer ∈ scope
    · have localFirst : Earliest world verb scope freezer := (earliest_scope scopeClosed inside freezer).mpr ⟨member,first⟩
      cases localFound : scope.find? (fun f => decide (Earliest world verb scope f)) with
      | none =>
        have rejected := List.find?_eq_none.mp localFound freezer member
        exact False.elim (rejected (by simpa using localFirst))
      | some localFreezer =>
        have foundFirst : Earliest world verb scope localFreezer := of_decide_eq_true (List.find?_some (p := fun f => decide (Earliest world verb scope f)) localFound)
        have globalFirst := ((earliest_scope scopeClosed inside localFreezer).mp foundFirst).2
        have equalAddress : freezer.addr = localFreezer.addr := by
          by_cases same : freezer.addr = localFreezer.addr
          · exact same
          · exact False.elim (clear freezer localFreezer (.concurrent first globalFirst same))
        have same := unique.eq_of_addr first.1 globalFirst.1 equalAddress
        subst localFreezer
        simp [Option.filter,member]
    · cases localFound : scope.find? (fun f => decide (Earliest world verb scope f)) with
      | none => simp [Option.filter,member]
      | some localFreezer =>
        have localFirst : Earliest world verb scope localFreezer := of_decide_eq_true (List.find?_some (p := fun f => decide (Earliest world verb scope f)) localFound)
        have globalFirst := ((earliest_scope scopeClosed inside localFreezer).mp localFirst).2
        have equalAddress : freezer.addr = localFreezer.addr := by
          by_cases same : freezer.addr = localFreezer.addr
          · exact same
          · exact False.elim (clear freezer localFreezer (.concurrent first globalFirst same))
        have same := unique.eq_of_addr first.1 globalFirst.1 equalAddress
        exact False.elim (member (same ▸ localFirst.1))

/-- Native global-plan data read: reuse the precomputed full-history cut only
when its freezer belongs to this scope, and restrict exclusion metadata locally.
Raw source faults are handled by the enclosing compositional error channel. -/
noncomputable def cachedFreeze {V : Type} (world : Act → Prop) (spec : FreezeSpec)
    (evaluate : List Act → V) (whole scope : List Act) : FreezeRead V := by
  classical
  exact if ∃ a b, FreezeConflict world spec.verb spec.contributes spec.policy whole a b then
      .fault (freezeEvidence world spec.verb spec.contributes spec.policy whole)
    else match whole.find? (fun f => decide (Earliest world spec.verb whole f)) with
      | none => .snapshot (evaluate scope)
      | some freezer => if freezer ∈ scope then
          .frozen freezer.addr (evaluate (causalCut world whole freezer))
            (FinSet.mk (scope.filter (fun act => decide (spec.contributes act ∧ ¬Ancestor world act freezer))))
        else .snapshot (evaluate scope)

/-- On clear global history, cached native cuts and recursive local cuts give
exactly equal scoped data. This lemma applies at every nested freeze dependency. -/
theorem cached_freeze_refinement {V : Type} (world : Act → Prop) (spec : FreezeSpec)
    (evaluate : List Act → V) (whole scope : List Act)
    (globalClosed : CausallyClosed world whole) (scopeClosed : CausallyClosed world scope)
    (inside : ∀ act ∈ scope, act ∈ whole) (uniqueWhole : NodupAddr whole) (uniqueScope : NodupAddr scope)
    (clear : ∀ a b, ¬FreezeConflict world spec.verb spec.contributes spec.policy whole a b)
    (invariant : ∀ X Y, NodupAddr X → NodupAddr Y → SetEq X Y → evaluate X = evaluate Y) :
    cachedFreeze world spec evaluate whole scope =
      freezeRead world spec.verb spec.contributes spec.policy none evaluate scope := by
  classical
  have noGlobal : ¬∃ a b, FreezeConflict world spec.verb spec.contributes spec.policy whole a b := by
    rintro ⟨a,b,bad⟩; exact clear a b bad
  have noScoped : ¬∃ a b, FreezeConflict world spec.verb spec.contributes spec.policy scope a b := by
    rintro ⟨a,b,bad⟩
    exact clear a b (scoped_conflict_global scopeClosed inside bad)
  have selection := selected_freezer_scope scopeClosed inside uniqueWhole clear
  simp only [cachedFreeze,if_neg noGlobal,freezeRead,Option.isSome_none,Bool.false_eq_true,false_or,if_neg noScoped]
  rw [selection]
  cases selected : whole.find? (fun f => decide (Earliest world spec.verb whole f)) with
  | none => rfl
  | some freezer =>
    by_cases member : freezer ∈ scope
    · simp only [member,ite_true,Option.filter,decide_true]
      have equal : evaluate (causalCut world whole freezer) = evaluate (causalCut world scope freezer) := by
        apply invariant
        · exact uniqueWhole.filter _
        · exact uniqueScope.filter _
        · exact global_cut_in_scope globalClosed scopeClosed inside member
      rw [equal]
    · simp [Option.filter,member]

/-- A clear global source path is clear in every accepted closed sub-scope. -/
theorem source_clear_in_scope (world : Act → Prop) (source : Path) {whole scope : List Act}
    (scopeClosed : CausallyClosed world scope) (inside : ∀ act ∈ scope, act ∈ whole)
    (clear : errors world source whole = none) : errors world source scope = none := by
  cases localError : errors world source scope with
  | none => rfl
  | some evidence =>
    obtain ⟨later,current,_⟩ := errors_persist world source scopeClosed inside evidence localError
    simp [clear] at current

/-- Native cached freeze payloads agree with the actual compositional plan at
closed nested cuts when the full observation has no source or freeze fault. -/
theorem cached_plan_data_refinement {V : Type} (world : Act → Prop) (spec : FreezeSpec)
    (source : StateObservationPlan.Plan V) (whole scope : List Act)
    (globalClosed : CausallyClosed world whole) (scopeClosed : CausallyClosed world scope)
    (inside : ∀ act ∈ scope, act ∈ whole) (uniqueWhole : NodupAddr whole) (uniqueScope : NodupAddr scope)
    (noSourceFault : errors world (StateObservationPlan.path source) whole = none)
    (noFreezeFault : ∀ a b, ¬FreezeConflict world spec.verb spec.contributes spec.policy whole a b) :
    StateObservationPlan.frozenData (cachedFreeze world spec (StateObservationPlan.data world source) whole scope) =
      StateObservationPlan.data world (.freeze spec source) scope := by
  have clear := source_clear_in_scope world (StateObservationPlan.path source) scopeClosed inside noSourceFault
  rw [cached_freeze_refinement world spec _ whole scope globalClosed scopeClosed inside uniqueWhole uniqueScope noFreezeFault
    (fun X Y ux uy same => StateObservationPlan.data_setEq world source ux uy same)]
  simp only [StateObservationPlan.data,clear]

end CBCL.StateFreezeScopes
