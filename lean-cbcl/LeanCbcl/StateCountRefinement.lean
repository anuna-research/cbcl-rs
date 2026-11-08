import LeanCbcl.StateRuleRefinement

/-! Installed domain/count threshold: actual filtered source, actual lower-bound
query, and stable success or attributable fault. This is a concrete installed
source instance, not a monotonicity assumption on arbitrary predicates. -/
namespace CBCL.StateCountRefinement
open State StateLift StateLVar StateObservation StateObservationPlan StateRuleRefinement

theorem initial_absorbs {A B : List Act} (growth : ∀ a ∈ A, a ∈ B) (opener field : String) :
    initialCarrier opener field A ⊔ initialCarrier opener field B = initialCarrier opener field B :=
  lift_join_of_forall _ (fun a ha => join_lift_of_mem _ (List.mem_filter.mpr
    ⟨growth a (List.mem_filter.mp ha).1,(List.mem_filter.mp ha).2⟩))

/-- An immutable domain cannot lose an eligible act unless its opener faults. -/
theorem selected_grows {A B : List Act} (growth : ∀ a ∈ A, a ∈ B)
    (verb key opener field : String) (clear : domainError opener field B = none) :
    ∀ a ∈ initialDomain verb key opener field A, a ∈ initialDomain verb key opener field B := by
  have absorbs := initial_absorbs growth opener field
  change Sole.join (initialCarrier opener field A) (initialCarrier opener field B) =
    initialCarrier opener field B at absorbs
  cases old : initialCarrier opener field A with
  | bot =>
    intro a selected
    cases value : a.get key <;>
      simp [initialDomain,initialAllowed,old,Sole.display,inDomain,value] at selected
  | top oldEvidence =>
    cases new : initialCarrier opener field B <;> simp [old,new,Sole.join] at absorbs
    case top e => simp [domainError,new] at clear
  | one address value =>
    cases new : initialCarrier opener field B with
    | bot => simp [old,new,Sole.join] at absorbs
    | top e => simp [domainError,new] at clear
    | one other payload =>
      have same : address = other ∧ value = payload := by
        by_cases different : address = other ∧ value = payload
        · exact different
        · simp [old,new,Sole.join,different] at absorbs
      have allowed : initialAllowed opener field A = initialAllowed opener field B := by
        simp [initialAllowed,old,new,same.1,same.2]
      intro a selected
      have member := List.mem_filter.mp selected
      have act := List.mem_filter.mp member.1
      apply List.mem_filter.mpr
      exact ⟨List.mem_filter.mpr ⟨growth a act.1,act.2⟩,by simpa [allowed] using member.2⟩

theorem selected_unique {A : List Act} (unique : NodupAddr A) (verb key opener field : String) :
    (initialDomain verb key opener field A).Nodup :=
  List.Pairwise.of_map Act.addr (fun _ _ different same => different (congrArg Act.addr same))
    ((unique.acts verb).filter _)

theorem count_display_refinement {A : List Act} (unique : NodupAddr A)
    (verb key opener field : String) :
    FinSet.card (FinSet.mk (initialDomain verb key opener field A)) =
      FinSet.card (lift address (initialDomain verb key opener field A)) := by
  rw [FinSet.card_mk_of_nodup (selected_unique unique verb key opener field)]
  have selected : NodupAddr (initialDomain verb key opener field A) := (unique.acts verb).filter _
  exact size_eq_lift selected

theorem count_grows {A B : List Act} (growth : ∀ a ∈ A, a ∈ B)
    (ua : NodupAddr A) (ub : NodupAddr B) (verb key opener field : String)
    (clear : domainError opener field B = none) :
    FinSet.card (FinSet.mk (initialDomain verb key opener field A)) ≤
      FinSet.card (FinSet.mk (initialDomain verb key opener field B)) := by
  rw [FinSet.card_mk_of_nodup (selected_unique ua verb key opener field),
    FinSet.card_mk_of_nodup (selected_unique ub verb key opener field)]
  obtain ⟨chosen,perm,sub⟩ := List.subperm_of_subset (selected_unique ua verb key opener field)
    (selected_grows growth verb key opener field clear)
  have lengths := perm.length_eq
  have bounded := sub.length_le
  omega

def compileCountThreshold (verb key opener field : String) (bound : Nat) : Plan Nat :=
  compileClosureThreshold [bound] (fun required observed : Nat => decide (required ≤ observed))
    (.domain verb key opener field FinSet.card)

theorem count_reached_iff (world : Act → Prop) (verb key opener field : String) (bound : Nat)
    (A : List Act) :
    observe world (compileCountThreshold verb key opener field bound) A = .data (.reached bound) ↔
      domainError opener field A = none ∧
      bound ≤ FinSet.card (FinSet.mk (initialDomain verb key opener field A)) := by
  cases error : domainError opener field A with
  | some e => simp [compileCountThreshold,compileClosureThreshold,observe,path,data,errors,error]
  | none =>
    by_cases reached : bound ≤ FinSet.card (FinSet.mk (initialDomain verb key opener field A)) <;>
      simp [compileCountThreshold,compileClosureThreshold,observe,path,data,Data.payload,errors,error,reached]

/-- This installed threshold instance cannot retract a successful answer. -/
theorem installed_count_threshold_stable (world : Act → Prop) (verb key opener field : String)
    (bound : Nat) {A B : List Act} (growth : ∀ a ∈ A, a ∈ B)
    (ua : NodupAddr A) (ub : NodupAddr B)
    (success : observe world (compileCountThreshold verb key opener field bound) A = .data (.reached bound)) :
    observe world (compileCountThreshold verb key opener field bound) B = .data (.reached bound) ∨
      ∃ e, observe world (compileCountThreshold verb key opener field bound) B = .fault e := by
  have old := (count_reached_iff world verb key opener field bound A).mp success
  cases fault : domainError opener field B with
  | some e =>
    right
    exact ⟨e,by simp [compileCountThreshold,compileClosureThreshold,observe,path,errors,fault]⟩
  | none =>
    left
    exact (count_reached_iff world verb key opener field bound B).mpr
      ⟨fault,Nat.le_trans old.2 (count_grows growth ua ub verb key opener field fault)⟩

end CBCL.StateCountRefinement
