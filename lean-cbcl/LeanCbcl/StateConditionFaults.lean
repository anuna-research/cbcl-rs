import LeanCbcl.StateConditionCompiler

/-! Condition faults are the union of their real compiled source dependencies.
Plain authored queries add no independent top, while arbitrary query adapters
still preserve existing evidence. The dependency plan's normal value is used
only as the identity of its fault-path product, never as a condition result. -/
set_option autoImplicit false
namespace CBCL.StateConditionFaults
open State StateLift StateLVar StateObservation StateObservationPlan StateInstalledCompiler
open StateOutputCompiler StateOutputWitnessReplay StateCondition StateConditionCompiler

/-- Dependency products retain every leaf's source error path. -/
noncomputable def product {V : Type} (truth : V) (sources : List (Plan V)) : Plan V :=
  sources.foldr (fun source rest => .map (fun _ => truth) (.pair source rest)) (.snapshot (fun _ => truth))

/-- The complete source dependency graph retained by a compiled condition. -/
noncomputable def dependencies {V : Type} (truth : V) : Code V → Plan V :=
  Code.fold (fun _ _ source => source) (fun _ sources => product truth sources)

/-- Every leaf in an authored condition uses a source-owned raw or closure query. -/
noncomputable def Plain {V : Type} : Code V → Prop :=
  Code.fold (fun _ query _ => PlainQuery query) (fun _ children => ∀ value ∈ children, value)

/-- A normalized source value has exactly its plan's complete error channel. -/
theorem source_evidence {V : Type} (whole : List Act) (source : Plan V) :
    evidence (sourceValue whole source) =
      errors (fun act => act ∈ StateScopePool.normalize whole) (path source) (StateScopePool.normalize whole) := by
  unfold sourceValue observe
  cases errors (fun act => act ∈ StateScopePool.normalize whole) (path source) (StateScopePool.normalize whole) <;> rfl

/-- Pairing and mapping dependency values preserves the exact evidence union. -/
theorem product_evidence {V : Type} (truth : V) (whole : List Act) (sources : List (Plan V)) :
    evidence (sourceValue whole (product truth sources)) =
      (sources.map (fun source => evidence (sourceValue whole source))).foldr unionError none := by
  induction sources with
  | nil => rfl
  | cons source rest ih =>
    simp only [product,List.foldr_cons,List.map_cons]
    rw [source_evidence]
    simp only [path,errors]
    rw [← source_evidence,← source_evidence]
    exact congrArg (unionError (evidence (sourceValue whole source))) ih

/-- Every query preserves preexisting source evidence, including an empty fault. -/
theorem query_grows {V : Type} (query : Query V) (raw : List Act) (value : Observation V) :
    Grows (evidence value) (evidence (query.run raw value)) := by
  intro ids fault
  cases value with
  | data current => simp [evidence] at fault
  | fault original =>
    have same : original = ids := Option.some.inj fault
    subst original
    exact ⟨ids,by rw [query_preserves_fault]; rfl,fun _ member => member⟩

/-- Source-owned plain query dispatch preserves the exact complete error channel. -/
theorem query_evidence {V : Type} (query : Query V) (plain : PlainQuery query)
    (raw : List Act) (value : Observation V) : evidence (query.run raw value) = evidence value := by
  cases value with
  | fault ids => rw [query_preserves_fault]
  | data current =>
    cases result : query.run raw (.data current) with
    | data _ => rfl
    | fault ids =>
      have impossible := (plain_query_fault_iff query plain raw (.data current) ids).mp result
      contradiction

/-- Plain compiled conditions preserve exactly their complete dependency fault,
including every leaf and explicitly empty terminal evidence. -/
theorem dependencies_evidence {V : Type} (truth : V) (whole : List Act)
    (freezes : List (String × FreezeSpec)) (code : Code V) (plain : Plain code) :
    evidence (code.observe whole freezes) = evidence (sourceValue whole (dependencies truth code)) := by
  let P := fun code : Code V => Plain code →
    evidence (code.observe whole freezes) = evidence (sourceValue whole (dependencies truth code))
  apply Code.rec (motive_1 := P) (motive_2 := fun children => ∀ child ∈ children, P child) ?_ ?_ ?_ ?_ code plain
  · intro field query source admitted
    change PlainQuery query at admitted
    simp only [Code.observe,boolean_evidence,dependencies,Code.fold_read]
    exact query_evidence query admitted _ _
  · intro children ih admitted
    have childPlain : ∀ child ∈ children, Plain child := by
      intro child member
      have all : ∀ value ∈ children.map Plain, value := by simpa only [Plain,Code.fold_all] using admitted
      exact all _ (List.mem_map.mpr ⟨child,member,rfl⟩)
    simp only [Code.observe,combine_evidence,dependencies,Code.fold_all,product_evidence,List.map_map,Function.comp_def]
    apply congrArg (fun values : List Error => values.foldr unionError none)
    apply List.map_congr_left
    intro child member
    exact ih child member (childPlain child member)
  · intro child impossible
    simp at impossible
  · intro head tail headProof tailProof child member
    rcases List.mem_cons.mp member with equal | member
    · simpa only [equal] using headProof
    · exact tailProof child member

/-- Optional evidence equality records the exact terminal observation. -/
theorem evidence_fault_iff {V : Type} (value : Observation V) (ids : Evidence) :
    evidence value = some ids ↔ value = .fault ids := by
  cases value <;> simp [evidence]

/-- Rendering a condition Boolean never changes its error channel. -/
theorem truth_evidence {V : Type} (truth : V) (value : Observation Bool) :
    evidence (truthResult truth value) = evidence value := by
  cases value with
  | fault ids => rfl
  | data current => cases current <;> rfl

/-- A plain compiled condition faults exactly when its full dependency graph does. -/
theorem plain_fault_iff {V : Type} (truth : V) (whole : List Act)
    (freezes : List (String × FreezeSpec)) (code : Code V) (plain : Plain code) (ids : Evidence) :
    truthResult truth (code.observe whole freezes) = .fault ids ↔
      sourceValue whole (dependencies truth code) = .fault ids := by
  rw [← evidence_fault_iff,truth_evidence,dependencies_evidence truth whole freezes code plain,evidence_fault_iff]

/-- Evidence inclusion composes through an ordered union fold. -/
theorem fold_grows (left right : List Error) (growth : List.Forall₂ Grows left right) :
    Grows (left.foldr unionError none) (right.foldr unionError none) := by
  induction growth with
  | nil => intro ids impossible; cases impossible
  | cons head tail ih => exact unionError_grows head ih

/-- Every dependency fault survives compiled condition observation even when a
non-authored query adapter adds further independent fault evidence. -/
theorem dependencies_grow {V : Type} (truth : V) (whole : List Act)
    (freezes : List (String × FreezeSpec)) (code : Code V) :
    Grows (evidence (sourceValue whole (dependencies truth code))) (evidence (code.observe whole freezes)) := by
  let P := fun code : Code V =>
    Grows (evidence (sourceValue whole (dependencies truth code))) (evidence (code.observe whole freezes))
  apply Code.rec (motive_1 := P) (motive_2 := fun children => ∀ child ∈ children, P child) ?_ ?_ ?_ ?_ code
  · intro field query source
    dsimp only [P]
    simp only [Code.observe,boolean_evidence,dependencies,Code.fold_read]
    exact query_grows query _ _
  · intro children ih
    dsimp only [P]
    simp only [Code.observe,combine_evidence,dependencies,Code.fold_all,product_evidence,List.map_map,Function.comp_def]
    apply fold_grows
    induction children with
    | nil => exact .nil
    | cons head tail tailIH =>
      apply List.Forall₂.cons
      · exact ih head (by simp)
      · exact tailIH (fun child member => ih child (List.mem_cons_of_mem head member))
  · intro child impossible
    simp at impossible
  · intro head tail headProof tailProof child member
    rcases List.mem_cons.mp member with equal | member
    · simpa only [equal] using headProof
    · exact tailProof child member

/-- Any existing source witness is contained in the emitted condition fault. -/
theorem preserves_fault {V : Type} (truth : V) (whole : List Act)
    (freezes : List (String × FreezeSpec)) (code : Code V) (ids : Evidence)
    (fault : sourceValue whole (dependencies truth code) = .fault ids) :
    ∃ enlarged, truthResult truth (code.observe whole freezes) = .fault enlarged ∧ ∀ id ∈ ids, id ∈ enlarged := by
  have growth := dependencies_grow truth whole freezes code
  obtain ⟨enlarged,current,contains⟩ := growth ids (by rw [fault]; rfl)
  refine ⟨enlarged,?_,contains⟩
  apply (evidence_fault_iff _ enlarged).mp
  rw [truth_evidence]
  exact current

end CBCL.StateConditionFaults
