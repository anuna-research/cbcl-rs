import LeanCbcl.StateFrozenCompilation

/-! Successful frozen values across actual recompiled source structures. -/
set_option autoImplicit false
namespace CBCL.StateFrozenSuccess
open State StateLift StateLVar StateObservation StateObservationPlan StateFrozenPayload

/-- Primitive installed source leaves cannot manufacture a frozen status. -/
theorem source_not_frozen {V : Type} (world : Act → Prop) (source : StateInstalledCompiler.Source V)
    (A : List Act) (address : Nat) (value : V) (excluded : FinSet Act) :
    data world (StateInstalledCompiler.sourcePlan source) A ≠ .frozen address value excluded := by
  induction source with
  | snapshot display | domain _ _ _ _ display => simp [StateInstalledCompiler.sourcePlan,data]
  | read contextual read =>
    cases current : read (rawHistory A) <;> cases contextual <;>
      simp [StateInstalledCompiler.sourcePlan,data,current,optionalData]
  | context decode embed =>
    cases current : StateContext.read decode A <;> simp [StateInstalledCompiler.sourcePlan,data,current]
  | guardCertified _ _ ih | resource _ _ _ ih | guardDomain _ _ _ ih | guardThreshold _ _ ih => exact ih

/-- An embedded frozen result recovers the actual source's frozen result. -/
theorem embed_frozen_inverse {V W : Type} (f : V → W) (datum : Data V)
    (address : Nat) (value : W) (excluded : FinSet Act)
    (frozen : embedData f datum = .frozen address value excluded) :
    ∃ original, datum = .frozen address original excluded ∧ f original = value := by
  cases datum <;> simp only [embedData] at frozen
  all_goals cases frozen
  exact ⟨_,rfl,rfl⟩

/-- A frozen wrapper retains the selected address and the exact source payload. -/
theorem frozen_inverse {V : Type} (address : Nat) (datum : Data V) (excluded : FinSet Act)
    (selected : Nat) (value : V) (reported : FinSet Act)
    (frozen : frozenData (.frozen address datum excluded) = .frozen selected value reported) :
    address = selected ∧ datum.payload = some value := by
  cases current : datum.payload with
  | none => simp [frozenData,current] at frozen
  | some original =>
    have parts : address = selected ∧ original = value ∧ excluded = reported := by
      simpa [frozenData,current] using frozen
    exact ⟨parts.1,by simpa [parts.2.1] using current⟩

/-- Clear complete freeze evaluation exposes the selected cut and preserves its
current exclusion metadata without treating that metadata as the frozen value. -/
theorem freeze_data_clear {V : Type} (world : Act → Prop) (spec : FreezeSpec) (source : Plan V) (A : List Act)
    (clear : errors world (path (.freeze spec source)) A = none) :
    data world (.freeze spec source) A =
      (by classical exact match A.find? (fun act => decide (Earliest world spec.verb A act)) with
        | none => data world source A
        | some root => frozenData (.frozen root.addr (data world source (causalCut world A root))
            (FinSet.mk (A.filter (fun act => decide (spec.contributes act ∧ ¬Ancestor world act root)))))) := by
  classical
  have parts := (StateNativeReader.freeze_clear world spec _ A).mp clear
  have healthy : ¬∃ a b, FreezeConflict world spec.verb spec.contributes spec.policy A a b := by
    rintro ⟨a,b,bad⟩
    exact parts.2 a b bad
  simp only [data,freezeRead,parts.1,Option.isSome_none,Bool.false_eq_true,false_or,if_neg healthy]
  cases A.find? (fun act => decide (Earliest world spec.verb A act)) <;> rfl

/-- Healthy related source plans returning the same accepted freezer agree on
underlying values. The returned exclusion sets may differ independently. -/
theorem related_frozen_agreement {V : Type} (world : Act → Prop) {left right : Plan V}
    (related : Related left right) (A B : List Act) (freezer : Act)
    (uniqueA : NodupAddr A) (uniqueB : NodupAddr B)
    (closedA : CausallyClosed world A) (closedB : CausallyClosed world B)
    (presentA : freezer ∈ A) (presentB : freezer ∈ B)
    (clearLeft : errors world (path left) A = none) (clearRight : errors world (path right) B = none)
    (leftValue rightValue : V) (leftExcluded rightExcluded : FinSet Act)
    (leftFrozen : data world left A = .frozen freezer.addr leftValue leftExcluded)
    (rightFrozen : data world right B = .frozen freezer.addr rightValue rightExcluded) : leftValue = rightValue := by
  classical
  induction related generalizing A B leftExcluded rightExcluded with
  | source leaf => exact False.elim (source_not_frozen world leaf A _ _ _ leftFrozen)
  | embed f related ih =>
    obtain ⟨lv,lread,leq⟩ := embed_frozen_inverse f _ _ _ _ leftFrozen
    obtain ⟨rv,rread,req⟩ := embed_frozen_inverse f _ _ _ _ rightFrozen
    have same := ih A B uniqueA uniqueB closedA closedB presentA presentB clearLeft clearRight
      lv rv leftExcluded rightExcluded lread rread
    exact leq.symm.trans ((congrArg f same).trans req)
  | map f related ih =>
    simp only [data,mapData] at leftFrozen
    split at leftFrozen <;> contradiction
  | pair lr rr il ir =>
    simp only [data,pairData] at leftFrozen
    split at leftFrozen <;> contradiction
  | threshold spec related ih =>
    letI := spec.algebra
    simp only [data] at leftFrozen
    split at leftFrozen <;> contradiction
  | thresholdRaw alternatives test state related ih =>
    simp only [data] at leftFrozen
    split at leftFrozen <;> contradiction
  | thresholdOn alternatives test related ih =>
    simp only [data] at leftFrozen
    split at leftFrozen <;> try contradiction
    split at leftFrozen <;> contradiction
  | freeze verb policy lc rc related ih =>
    have rawLeft := ((StateNativeReader.freeze_clear world _ _ A).mp clearLeft).1
    have rawRight := ((StateNativeReader.freeze_clear world _ _ B).mp clearRight).1
    rw [freeze_data_clear world _ _ A clearLeft] at leftFrozen
    rw [freeze_data_clear world _ _ B clearRight] at rightFrozen
    dsimp only at leftFrozen rightFrozen
    cases selectedA : A.find? (fun act => decide (Earliest world verb A act)) with
    | none =>
      simp only [selectedA] at leftFrozen
      cases selectedB : B.find? (fun act => decide (Earliest world verb B act)) with
      | none =>
        simp only [selectedB] at rightFrozen
        exact ih A B uniqueA uniqueB closedA closedB presentA presentB rawLeft rawRight
          leftValue rightValue leftExcluded rightExcluded leftFrozen rightFrozen
      | some rootB =>
        simp only [selectedB] at rightFrozen
        have selected : Earliest world verb B rootB := of_decide_eq_true (List.find?_some (p := fun act => decide (Earliest world verb B act)) selectedB)
        have parts := frozen_inverse _ _ _ _ _ _ rightFrozen
        have rootEq : rootB = freezer := uniqueB.eq_of_addr selected.1 presentB parts.1
        subst rootB
        have earliestA := earliest_transfer closedB selected presentA
        have absent := List.find?_eq_none.mp selectedA freezer presentA
        exact False.elim (absent (by simpa using earliestA))
    | some rootA =>
      simp only [selectedA] at leftFrozen
      have selected : Earliest world verb A rootA := of_decide_eq_true (List.find?_some (p := fun act => decide (Earliest world verb A act)) selectedA)
      have leftParts := frozen_inverse _ _ _ _ _ _ leftFrozen
      have rootEq : rootA = freezer := uniqueA.eq_of_addr selected.1 presentA leftParts.1
      subst rootA
      cases selectedB : B.find? (fun act => decide (Earliest world verb B act)) with
      | none =>
        have earliestB := earliest_transfer closedA selected presentB
        have absent := List.find?_eq_none.mp selectedB freezer presentB
        exact False.elim (absent (by simpa using earliestB))
      | some rootB =>
        simp only [selectedB] at rightFrozen
        have selectedRight : Earliest world verb B rootB := of_decide_eq_true (List.find?_some (p := fun act => decide (Earliest world verb B act)) selectedB)
        have rightParts := frozen_inverse _ _ _ _ _ _ rightFrozen
        have rootEq : rootB = freezer := uniqueB.eq_of_addr selectedRight.1 presentB rightParts.1
        subst rootB
        have same := same_freezer_source_payload world related A B freezer uniqueA uniqueB closedA closedB
          presentA presentB rawLeft rawRight
        rw [leftParts.2,rightParts.2] at same
        exact Option.some.inj same

end CBCL.StateFrozenSuccess
