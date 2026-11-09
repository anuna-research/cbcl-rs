import LeanCbcl.StateAuthoredThresholdOrigin

/-! Payload agreement under regenerated freeze contribution predicates. The
relation retains concrete source computations and query code; only attributable
freeze exclusions may differ. Healthy observations retain the same payload. -/
set_option autoImplicit false
namespace CBCL.StateFrozenPayload
open State StateLift StateLVar StateObservation StateObservationPlan

/-- Matching compiled value structure with independently regenerated freeze
contributor predicates. Every computation and selected-freezer verb is retained. -/
inductive Related : {V : Type} → Plan V → Plan V → Prop where
  | source {V : Type} (leaf : StateInstalledCompiler.Source V) :
      Related (StateInstalledCompiler.sourcePlan leaf) (StateInstalledCompiler.sourcePlan leaf)
  | embed {V W : Type} (f : V → W) {left right : Plan V} :
      Related left right → Related (.embed f left) (.embed f right)
  | map {V W : Type} (f : V → W) {left right : Plan V} :
      Related left right → Related (.map f left) (.map f right)
  | pair {V W : Type} {a b : Plan V} {c d : Plan W} :
      Related a b → Related c d → Related (.pair a c) (.pair b d)
  | threshold {V : Type} (spec : ThresholdSpec) {left right : Plan V} :
      Related left right → Related (.threshold spec left) (.threshold spec right)
  | thresholdRaw {V C Q : Type} (alternatives : List Q) (test : Q → C → Bool)
      (state : FinSet Act → C) {left right : Plan V} : Related left right →
      Related (.thresholdRaw alternatives test state left) (.thresholdRaw alternatives test state right)
  | thresholdOn {V Q : Type} (alternatives : List Q) (test : Q → V → Bool) {left right : Plan V} :
      Related left right → Related (.thresholdOn alternatives test left) (.thresholdOn alternatives test right)
  | freeze {V : Type} (verb : String) (policy : Bool) (leftContribution rightContribution : Act → Prop)
      {left right : Plan V} : Related left right →
      Related (.freeze ⟨verb,leftContribution,policy⟩ left) (.freeze ⟨verb,rightContribution,policy⟩ right)

/-- Representation embeddings retain exactly the embedded payload. -/
theorem embed_payload {V W : Type} (f : V → W) (datum : Data V) :
    (embedData f datum).payload = datum.payload.map f := by cases datum <;> rfl

/-- A fresh frozen wrapper does not change its source's underlying payload. -/
theorem frozen_payload {V : Type} (address : Nat) (datum : Data V) (excluded : FinSet Act) :
    (frozenData (.frozen address datum excluded)).payload = datum.payload := by cases datum <;> rfl

/-- A healthy freeze's payload uses only its selected causal cut. Contributor
predicates affect fault and exclusion channels, which remain separate. -/
theorem freeze_payload_clear {V : Type} (world : Act → Prop) (spec : FreezeSpec) (source : Plan V) (A : List Act)
    (clear : errors world (path (.freeze spec source)) A = none) :
    (data world (.freeze spec source) A).payload =
      (by classical exact match A.find? (fun act => decide (Earliest world spec.verb A act)) with
        | none => (data world source A).payload
        | some root => (data world source (causalCut world A root)).payload) := by
  classical
  have parts := (StateNativeReader.freeze_clear world spec _ A).mp clear
  have healthy : ¬∃ a b, FreezeConflict world spec.verb spec.contributes spec.policy A a b := by
    rintro ⟨a,b,bad⟩
    exact parts.2 a b bad
  simp only [data,freezeRead,parts.1,Option.isSome_none,Bool.false_eq_true,false_or,if_neg healthy]
  cases selected : A.find? (fun act => decide (Earliest world spec.verb A act)) with
  | none => rfl
  | some root => exact frozen_payload root.addr _ _

/-- On the same closed causal scope, healthy recompiled structures agree on
payload despite independently regenerated freeze contribution predicates. -/
theorem related_payload {V : Type} (world : Act → Prop) {left right : Plan V}
    (related : Related left right) (A : List Act) (closed : CausallyClosed world A)
    (clearLeft : errors world (path left) A = none)
    (clearRight : errors world (path right) A = none) :
    (data world left A).payload = (data world right A).payload := by
  classical
  induction related generalizing A with
  | source leaf => rfl
  | embed f related ih =>
    simp only [data,embed_payload,ih A closed clearLeft clearRight]
  | map f related ih =>
    simp only [data,mapData,ih A closed clearLeft clearRight]
  | pair leftRelated rightRelated ihLeft ihRight =>
    have leftParts := (StateNativeReader.union_clear _ _).mp clearLeft
    have rightParts := (StateNativeReader.union_clear _ _).mp clearRight
    simp only [data,pairData,ihLeft A closed leftParts.1 rightParts.1,ihRight A closed leftParts.2 rightParts.2]
  | threshold spec related ih =>
    have leftParts := (StateNativeReader.union_clear _ _).mp clearLeft
    have rightParts := (StateNativeReader.union_clear _ _).mp clearRight
    simp only [data,leftParts.2,rightParts.2]
  | thresholdRaw alternatives test state related ih => rfl
  | thresholdOn alternatives test related ih =>
    simp only [data,ih A closed clearLeft clearRight]
  | freeze verb policy leftContribution rightContribution related ih =>
    rw [freeze_payload_clear world _ _ A clearLeft,freeze_payload_clear world _ _ A clearRight]
    cases selected : A.find? (fun act => decide (Earliest world verb A act)) with
    | none =>
      exact ih A closed ((StateNativeReader.freeze_clear world _ _ A).mp clearLeft).1
        ((StateNativeReader.freeze_clear world _ _ A).mp clearRight).1
    | some root =>
      have cutClosed := StateFreezeScopes.causal_cut_closed closed root
      have inside : ∀ act ∈ causalCut world A root, act ∈ A := by
        intro act member
        exact (List.mem_filter.mp member).1
      exact ih _ cutClosed
        (StateFreezeScopes.source_clear_in_scope world _ cutClosed inside ((StateNativeReader.freeze_clear world _ _ A).mp clearLeft).1)
        (StateFreezeScopes.source_clear_in_scope world _ cutClosed inside ((StateNativeReader.freeze_clear world _ _ A).mp clearRight).1)

/-- Equal closed accepted scopes preserve healthy payload agreement across
freshly specialized plan structures, including reordered delivery. -/
theorem related_payload_setEq {V : Type} (world : Act → Prop) {left right : Plan V}
    (related : Related left right) (A B : List Act) (same : SetEq A B)
    (uniqueA : NodupAddr A) (uniqueB : NodupAddr B) (closedA : CausallyClosed world A)
    (clearLeft : errors world (path left) A = none)
    (clearRight : errors world (path right) B = none) :
    (data world left A).payload = (data world right B).payload := by
  have rightAtA : errors world (path right) A = none := by
    rw [errors_setEq world (path right) same]
    exact clearRight
  rw [related_payload world related A closedA clearLeft rightAtA,
    data_setEq world right uniqueA uniqueB same]

/-- The same accepted freezer gives the same underlying source payload across
related freshly specialized plans. Excluded-contribution metadata need not agree. -/
theorem same_freezer_source_payload {V : Type} (world : Act → Prop) {left right : Plan V}
    (related : Related left right) (A B : List Act) (freezer : Act)
    (uniqueA : NodupAddr A) (uniqueB : NodupAddr B)
    (closedA : CausallyClosed world A) (closedB : CausallyClosed world B)
    (presentA : freezer ∈ A) (presentB : freezer ∈ B)
    (clearLeft : errors world (path left) A = none)
    (clearRight : errors world (path right) B = none) :
    (data world left (causalCut world A freezer)).payload =
      (data world right (causalCut world B freezer)).payload := by
  classical
  have cutA := StateFreezeScopes.causal_cut_closed closedA freezer
  have cutB := StateFreezeScopes.causal_cut_closed closedB freezer
  have insideA : ∀ act ∈ causalCut world A freezer, act ∈ A := fun _ member => (List.mem_filter.mp member).1
  have insideB : ∀ act ∈ causalCut world B freezer, act ∈ B := fun _ member => (List.mem_filter.mp member).1
  exact related_payload_setEq world related _ _ (causalCut_agreement closedA closedB presentA presentB)
    (uniqueA.filter _) (uniqueB.filter _) cutA
    (StateFreezeScopes.source_clear_in_scope world _ cutA insideA clearLeft)
    (StateFreezeScopes.source_clear_in_scope world _ cutB insideB clearRight)

end CBCL.StateFrozenPayload
