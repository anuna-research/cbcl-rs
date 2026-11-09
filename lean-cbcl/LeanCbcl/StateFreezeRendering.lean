import LeanCbcl.StateAddressPool
import LeanCbcl.StateFaultRendering

/-! Exact frozen-wrapper presentation from executable freeze observations.
The native wrapper sorts superseded addresses without deduplicating them;
finite accepted-scope identity uniqueness supplies that invariant explicitly. -/
set_option autoImplicit false
namespace CBCL.StateFreezeRendering
open State StateLift StateLVar StateExecutableFreeze

/-- Concrete native frozen object, retaining the stored value representation. -/
def layout (freezer : String) (value : StateJsonValue.Value) (excluded : List String) : StateJsonValue.Value :=
  .map [(.str "frozen",.str freezer),(.str "superseded",.list (excluded.map StateJsonValue.Value.str)),(.str "value",value)]

/-- Canonical finite-set exclusion names, independent of quotient representative. -/
def exclusions (address : Nat → String) (excluded : FinSet Act) : List String :=
  Quotient.lift (s := listSetoid Act)
    (fun acts => StateFaultRendering.canonical (acts.map (fun act => address act.addr)))
    (fun A B same => by
      apply StateFaultRendering.canonical_setEq
      intro name
      simp only [List.mem_map]
      constructor
      · rintro ⟨act,inside,equal⟩
        exact ⟨act,(same act).mp inside,equal⟩
      · rintro ⟨act,inside,equal⟩
        exact ⟨act,(same act).mpr inside,equal⟩) excluded

/-- Finite exclusion presentation agrees with an actual enumerable witness. -/
theorem exclusions_mk (address : Nat → String) (excluded : List Act) :
    exclusions address (FinSet.mk excluded) = StateFaultRendering.canonical (excluded.map (fun act => address act.addr)) := rfl

/-- Semantic frozen presentation fixes the root, payload and exclusion set. -/
def semantic (address : Nat → String) (freezer : Nat) (value : StateJsonValue.Value) (excluded : FinSet Act) : StateJsonValue.Value :=
  layout (address freezer) value (exclusions address excluded)

/-- On unique address inputs, the operational pool sort is exact canonical
order without adding a dedup operation absent from native frozen rendering. -/
theorem sort_unique (addresses : Array String) (unique : addresses.toList.Nodup) :
    StateAddressPool.sortPool addresses = some (StateFaultRendering.canonical addresses.toList) := by
  rw [StateAddressPool.sortPool_refinement]
  apply congrArg some
  have permutation := StateAddressRadix.radix_permutation (fun index => addresses[index]!) (List.range addresses.size)
  have ordered := StateAddressRadix.radix_digit_order (fun index => addresses[index]!) (List.range addresses.size)
  rw [StateAddressPool.source_enumeration] at permutation ordered
  have same := StateAddressDigits.sorted_result_refinement addresses.toList _ permutation ordered
  rw [FinSet.dedup_of_nodup (permutation.nodup_iff.mpr unique)] at same
  exact same

/-- Operational native wrapper: sort excluded addresses, then emit fixed fields.
There is deliberately no adjacent deduplication after this sort. -/
def emitFrozen (address : Nat → String) (freezer : Nat) (value : StateJsonValue.Value) (excluded : List Act) : Option String :=
  (StateAddressPool.sortPool (excluded.map (fun act => address act.addr)).toArray).map
    (fun names => StateJsonValue.emit (layout (address freezer) value names) "")

/-- Actual unique excluded identities make operational frozen emission equal
semantic canonical presentation, including complete value bytes. -/
theorem emit_refinement (address : Nat → String) (freezer : Nat) (value : StateJsonValue.Value) (excluded : List Act)
    (unique : (excluded.map (fun act => address act.addr)).Nodup) :
    emitFrozen address freezer value excluded = some (StateJsonValue.render (semantic address freezer value (FinSet.mk excluded))) := by
  unfold emitFrozen
  rw [sort_unique _ (by simpa using unique)]
  simp only [Option.map_some,StateJsonValue.empty_buffer,semantic,exclusions_mk]

/-- Executable frozen exclusions are a sublist of the actual accepted scope. -/
theorem frozen_sublist {V : Type} (A : List Act) (verb : String) (contributes : Act → Bool) (policy : Bool)
    (raw : Option (List Nat)) (evaluate : List Act → V) (freezer : Nat) (value : V) (excluded : List Act)
    (observed : StateExecutableFreeze.read A verb contributes policy raw evaluate = .frozen freezer value excluded) : List.Sublist excluded A := by
  unfold StateExecutableFreeze.read at observed
  split at observed
  · contradiction
  · cases selected : A.find? (earliest A verb) with
    | none => simp [selected] at observed
    | some root =>
      simp only [selected] at observed
      have equal := Read.frozen.inj observed
      rw [← equal.2.2]
      exact List.filter_sublist

/-- Complete semantic freeze refinement constructs the actual finite frozen
metadata instead of accepting a caller-selected exclusion enumeration. -/
theorem frozen_enumerated (A : List Act) (ranked : Ranked A) (verb : String) (contributes : Act → Bool)
    (policy : Bool) (raw : Option (List Nat)) (evaluate : List Act → StateJsonValue.Value)
    (freezer : Nat) (value : StateJsonValue.Value) (excluded : FinSet Act)
    (observed : StateLVar.freezeRead (fun act => act ∈ A) verb (fun act => contributes act = true) policy
      (raw.map (fun ids => fun id => id ∈ ids)) evaluate A = .frozen freezer value excluded) :
    ∃ listed, read A verb contributes policy raw evaluate = .frozen freezer value listed ∧ FinSet.mk listed = excluded := by
  have refined := read_refinement A ranked verb contributes policy raw evaluate
  rw [observed] at refined
  cases computed : read A verb contributes policy raw evaluate with
  | snapshot current => simp [computed,Read.semantic] at refined
  | fault evidence => simp [computed,Read.semantic] at refined
  | frozen root current listed =>
    rw [computed] at refined
    have same := FreezeRead.frozen.inj refined
    rcases same with ⟨rfl,rfl,same⟩
    exact ⟨listed,rfl,same⟩

/-- Complete frozen observation to exact native JSON, deriving the exclusion
list and its uniqueness from the actual finite source scope. Address projection
is fixed explicitly; this is not a full native AST/admission extraction theorem. -/
theorem frozen_serialized (A : List Act) (ranked : Ranked A) (address : Nat → String)
    (unique : (A.map (fun act => address act.addr)).Nodup) (verb : String) (contributes : Act → Bool)
    (policy : Bool) (raw : Option (List Nat)) (evaluate : List Act → StateJsonValue.Value)
    (freezer : Nat) (value : StateJsonValue.Value) (excluded : FinSet Act)
    (observed : StateLVar.freezeRead (fun act => act ∈ A) verb (fun act => contributes act = true) policy
      (raw.map (fun ids => fun id => id ∈ ids)) evaluate A = .frozen freezer value excluded) :
    ∃ listed, read A verb contributes policy raw evaluate = .frozen freezer value listed ∧
      emitFrozen address freezer value listed = some (StateJsonValue.render (semantic address freezer value excluded)) := by
  obtain ⟨listed,computed,same⟩ := frozen_enumerated A ranked verb contributes policy raw evaluate freezer value excluded observed
  have subset := frozen_sublist A verb contributes policy raw evaluate freezer value listed computed
  have listedUnique : (listed.map (fun act => address act.addr)).Nodup := unique.sublist (subset.map _)
  refine ⟨listed,computed,?_⟩
  rw [emit_refinement address freezer value listed listedUnique,same]

end CBCL.StateFreezeRendering
