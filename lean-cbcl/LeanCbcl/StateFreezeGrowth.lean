import LeanCbcl.StateAuthoredBindings

/-! Observation-indexed freeze contributors. Domain source delivery can grow
which acts contribute, so fixed-predicate freeze persistence alone is not the
native theorem. These proofs transfer the same actual witnesses while both the
accepted history and its retained contributor predicate grow. -/
set_option autoImplicit false
namespace CBCL.StateFreezeGrowth
open State StateLift StateLVar StateObservation StateObservationPlan

/-- Increasing contributors preserve every concurrent or late-write witness. -/
theorem conflict_transfer {world : Act → Prop} {verb : String} {left right : Act → Prop}
    {policy : Bool} {A B : List Act} {a b : Act}
    (closed : CausallyClosed world A) (growth : ∀ act ∈ A, act ∈ B)
    (contributors : ∀ act, left act → right act)
    (conflict : FreezeConflict world verb left policy A a b) :
    FreezeConflict world verb right policy B a b := by
  cases conflict with
  | concurrent first second different =>
    exact .concurrent (earliest_persists closed growth first) (earliest_persists closed growth second) different
  | late first member contribution outside policy =>
    exact .late (earliest_persists closed growth first) (growth _ member) (contributors _ contribution) outside policy

/-- Every earlier witness address remains attributable with the new selector. -/
theorem evidence_grows {world : Act → Prop} {verb : String} {left right : Act → Prop}
    {policy : Bool} {A B : List Act} (closed : CausallyClosed world A)
    (growth : ∀ act ∈ A, act ∈ B) (contributors : ∀ act, left act → right act) :
    ∀ address ∈ freezeEvidence world verb left policy A,
      address ∈ freezeEvidence world verb right policy B := by
  rintro address ⟨a,b,conflict,which⟩
  exact ⟨a,b,conflict_transfer closed growth contributors conflict,which⟩

/-- Native freeze error growth allows both raw fault evidence and the
observation-indexed retained contributor set to grow. -/
theorem fault_grows {world : Act → Prop} {verb : String} {left right : Act → Prop}
    {policy : Bool} {A B : List Act} (closed : CausallyClosed world A)
    (growth : ∀ act ∈ A, act ∈ B) (contributors : ∀ act, left act → right act)
    {rawA rawB : Error} (rawGrowth : Grows rawA rawB) :
    Grows (freezeFault world verb left policy rawA A) (freezeFault world verb right policy rawB B) := by
  classical
  intro evidence fault
  unfold freezeFault at fault ⊢
  split at fault
  · rename_i reason
    have equal : rawA.getD ∅ ∪ freezeEvidence world verb left policy A = evidence := Option.some.inj fault
    subst evidence
    have persists : rawB.isSome ∨ ∃ a b, FreezeConflict world verb right policy B a b := by
      rcases reason with raw | ⟨a,b,conflict⟩
      · cases rawA with
        | none => simp at raw
        | some initial =>
          obtain ⟨later,current,_⟩ := rawGrowth initial rfl
          exact Or.inl (by simp [current])
      · exact Or.inr ⟨a,b,conflict_transfer closed growth contributors conflict⟩
    simp only [if_pos persists]
    refine ⟨rawB.getD ∅ ∪ freezeEvidence world verb right policy B,rfl,?_⟩
    intro address member
    rcases member with raw | witness
    · cases rawA with
      | none => exact False.elim raw
      | some initial =>
        obtain ⟨later,current,includes⟩ := rawGrowth initial rfl
        exact Or.inl (by simpa [current] using includes address raw)
    · exact Or.inr (evidence_grows closed growth contributors address witness)
  · contradiction

/-- Structural error-path relation for compiling the same sources under a
larger full-observation contributor set. Source checks are unchanged. -/
inductive Related : Path → Path → Prop where
  | same (path : Path) : Related path path
  | join {a b c d : Path} : Related a c → Related b d → Related (.join a b) (.join c d)
  | freeze {a b : Path} (verb : String) (left right : Act → Prop) (policy : Bool) :
      (∀ act, left act → right act) → Related a b →
      Related (.freeze verb left policy a) (.freeze verb right policy b)

/-- Every dependency path preserves its previous fault witnesses even when
compilation regenerates the native freeze contributor predicates. -/
theorem related_errors_grow (world : Act → Prop) {left right : Path} (related : Related left right)
    {A B : List Act} (closed : CausallyClosed world A) (growth : ∀ act ∈ A, act ∈ B) :
    Grows (errors world left A) (errors world right B) := by
  induction related with
  | same path => exact errors_persist world path closed growth
  | join _ _ ihLeft ihRight => exact unionError_grows ihLeft ihRight
  | freeze verb left right policy contributors _ ih => exact fault_grows closed growth contributors ih

/-- Actual initializer/roster-domain freeze selectors discharge the growth
premise; callers do not supply an unproved selector persistence oracle. -/
theorem authored_freeze_grows (world : Act → Prop) (verb : String) (policy : Bool)
    (domains : List StateInstalledDomains.Domain) (footprint : StateAuthoredBindings.Footprint)
    {A B : List Act} (closed : CausallyClosed world A) (growth : ∀ act ∈ A, act ∈ B)
    {rawA rawB : Error} (rawGrowth : Grows rawA rawB) :
    Grows (freezeFault world verb (StateAuthoredBindings.contributes domains A footprint) policy rawA A)
      (freezeFault world verb (StateAuthoredBindings.contributes domains B footprint) policy rawB B) :=
  fault_grows closed growth (StateAuthoredBindings.contributes_grows domains growth footprint) rawGrowth

end CBCL.StateFreezeGrowth
