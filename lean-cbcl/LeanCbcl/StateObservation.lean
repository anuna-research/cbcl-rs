import LeanCbcl.StateResource

/-! Fault and value composition over the raw accepted-set carrier. A pure display
is a kernel term interpretation, not a replica-local host callback. Fields and
derived dependencies compile to this closed fault-path algebra. -/
namespace CBCL.StateObservation
open State StateLift StateLVar
/-- A set of act addresses witnessing a terminal fault. -/
abbrev Evidence := Lattice.Set Nat
/-- An optional terminal fault witness. -/
abbrev Error := Option Evidence

/-- Combine independent fault channels by unioning their evidence. -/
def unionError : Error → Error → Error
  | none, b => b
  | a, none => a
  | some a, some b => some (a ∪ b)

/-- Evidence inclusion from an earlier fault observation to a later one. -/
def Grows (a b : Error) : Prop :=
  ∀ e, a = some e → ∃ f, b = some f ∧ ∀ id ∈ e, id ∈ f

theorem unionError_grows {a b c d : Error} (ac : Grows a c) (bd : Grows b d) :
    Grows (unionError a b) (unionError c d) := by
  intro e h
  cases a with
  | none =>
    obtain ⟨f,hf,includes⟩ := bd e h
    cases c with
    | none => exact ⟨f,hf,includes⟩
    | some g => exact ⟨g ∪ f,by simp [unionError,hf],fun id hi => Or.inr (includes id hi)⟩
  | some x =>
    obtain ⟨f,hf,includes⟩ := ac x rfl
    cases b with
    | none =>
      have equal : x = e := Option.some.inj h
      subst e
      cases d with
      | none => exact ⟨f,by simp [unionError,hf],includes⟩
      | some g => exact ⟨f ∪ g,by simp [unionError,hf],fun id hi => Or.inl (includes id hi)⟩
    | some y =>
      obtain ⟨g,hg,includesY⟩ := bd y rfl
      have equal : x ∪ y = e := Option.some.inj h
      subst e
      exact ⟨f ∪ g,by simp [unionError,hf,hg],fun id hi => hi.elim
        (fun hx => Or.inl (includes id hx)) (fun hy => Or.inr (includesY id hy))⟩

/-- The addresses of the accepted acts in a history. -/
def acceptedEvidence (A : List Act) : Evidence := fun id => ∃ a ∈ A, a.addr = id

/-- A carrier, contribution function, and incompatible threshold alternatives. -/
structure ThresholdSpec where
  /-- The lattice carrier used by this source. -/
  Carrier : Type
  /-- The join and bottom operations, with their lattice laws. -/
  algebra : BoundedJoinSemilattice Carrier
  /-- The lattice element contributed by one accepted act. -/
  contribution : Act → Carrier
  /-- The installed alternatives of the threshold read. -/
  alternatives : List Carrier
  incompatible : letI := algebra; Incompatible (fun q => q ∈ alternatives)

/-- Fault evidence when the accumulated threshold carrier reaches top. -/
noncomputable def thresholdError (s : ThresholdSpec) (A : List Act) : Error := by
  classical
  letI := s.algebra
  exact if lift s.contribution A = ⊤ then some (acceptedEvidence A) else none

/-- The first installed threshold alternative reached by the carrier. -/
noncomputable def thresholdValue (s : ThresholdSpec) (A : List Act) : ThresholdRead s.Carrier :=
  letI := s.algebra
  thresholdRead s.alternatives (lift s.contribution A) false (rawHistory A)

/-- Fault evidence from conflicting context roots. -/
def contextError : StateContext.Read → Error
  | .fault e => some e
  | _ => none

/-- Fault evidence from conflicting initializer values. -/
def domainError (opener field : String) (A : List Act) : Error :=
  match initialCarrier opener field A with
  | .top e => some e
  | _ => none

/-- Fault evidence for conflicting freezes or forbidden late contributions. -/
noncomputable def freezeFault (world : Act → Prop) (verb : String)
    (contributes : Act → Prop) (policy : Bool) (raw : Error) (A : List Act) : Error := by
  classical
  exact if raw.isSome ∨ ∃ a b, FreezeConflict world verb contributes policy A a b
    then some (raw.getD ∅ ∪ freezeEvidence world verb contributes policy A) else none

/-- A native primitive can join the closed error-path algebra after its
executable checker has proved set extensionality and witness growth. Concrete
factories provide these proofs; no history classifier law is an axiom. -/
structure ErrorSpec where
  /-- Read data only when the compositional error channel is clear. -/
  read : List Act → Error
  equiv : ∀ {A B}, SetEq A B → read A = read B
  grow : ∀ {A B}, (∀ a ∈ A, a ∈ B) → Grows (read A) (read B)
  /-- Report only identities belonging to the accepted source history. -/
  support : ∀ {A e}, read A = some e → ∀ id ∈ e, id ∈ A.map Act.addr

/-- A compositional observation path with persistent error guards. -/
inductive Path where
  | clear
  | certified (spec : ErrorSpec)
  | context (decode : Act → Option Val)
  | domain (opener field : String)
  | resource (config : CheckpointEvidence.ResourceConfig) (decode : Act → CheckpointEvidence.ResourceData)
  | threshold (spec : ThresholdSpec)
  | join (left right : Path)
  | freeze (verb : String) (contributes : Act → Prop) (policy : Bool) (source : Path)

/-- Collect and union terminal fault evidence along an observation path. -/
noncomputable def errors (world : Act → Prop) : Path → List Act → Error
  | .clear, _ => none
  | .certified spec, A => spec.read A
  | .context decode, A => contextError (StateContext.read decode A)
  | .domain opener field, A => domainError opener field A
  | .resource config decode, A => StateResource.faultRead config decode A
  | .threshold spec, A => thresholdError spec A
  | .join left right, A => unionError (errors world left A) (errors world right A)
  | .freeze verb contributes policy source, A => freezeFault world verb contributes policy (errors world source A) A

/-- Derived fields join every dependency's error channel. Product construction
never arbitrates between simultaneous faults. -/
def dependencies (paths : List Path) : Path := paths.foldr Path.join .clear

theorem freezeEvidence_grows {world : Act → Prop} {A B : List Act}
    (closed : CausallyClosed world A) (growth : ∀ a ∈ A, a ∈ B)
    (verb : String) (contributes : Act → Prop) (policy : Bool) :
    ∀ id ∈ freezeEvidence world verb contributes policy A,
      id ∈ freezeEvidence world verb contributes policy B := by
  rintro id ⟨a,b,conflict,which⟩
  have accepted := freeze_witness_accepted conflict
  exact ⟨a,b,freeze_witness_transfer closed conflict (growth a accepted.1) (growth b accepted.2),which⟩

theorem freezeFault_grows {world : Act → Prop} {A B : List Act}
    (closed : CausallyClosed world A) (growth : ∀ a ∈ A, a ∈ B)
    (verb : String) (contributes : Act → Prop) (policy : Bool)
    {rawA rawB : Error} (rawGrowth : Grows rawA rawB) :
    Grows (freezeFault world verb contributes policy rawA A)
      (freezeFault world verb contributes policy rawB B) := by
  classical
  intro e fault
  unfold freezeFault at fault ⊢
  split at fault
  · rename_i reason
    have equal : rawA.getD ∅ ∪ freezeEvidence world verb contributes policy A = e := Option.some.inj fault
    subst e
    have either : rawB.isSome ∨ ∃ a b, FreezeConflict world verb contributes policy B a b := by
      rcases reason with raw | ⟨a,b,conflict⟩
      · cases rawA with
        | none => simp at raw
        | some old =>
          obtain ⟨f,h,_⟩ := rawGrowth old rfl
          exact Or.inl (by simp [h])
      · have accepted := freeze_witness_accepted conflict
        exact Or.inr ⟨a,b,freeze_witness_transfer closed conflict (growth a accepted.1) (growth b accepted.2)⟩
    simp only [if_pos either]
    refine ⟨rawB.getD ∅ ∪ freezeEvidence world verb contributes policy B,rfl,?_⟩
    intro id member
    rcases member with raw | witness
    · cases rawA with
      | none => exact False.elim raw
      | some old =>
        obtain ⟨f,h,includes⟩ := rawGrowth old rfl
        exact Or.inl (by simpa [h] using includes id raw)
    · exact Or.inr (freezeEvidence_grows closed growth verb contributes policy id witness)
  · contradiction

theorem errors_persist (world : Act → Prop) (path : Path) {A B : List Act}
    (closed : CausallyClosed world A) (growth : ∀ a ∈ A, a ∈ B) :
    Grows (errors world path A) (errors world path B) := by
  classical
  induction path with
  | clear => intro e h; contradiction
  | certified spec => exact spec.grow growth
  | context decode =>
    intro e fault
    have actual : StateContext.read decode A = .fault e := by
      cases h : StateContext.read decode A <;> simp [errors,contextError,h] at fault
      exact congrArg StateContext.Read.fault fault
    obtain ⟨f,h,includes⟩ := StateContext.read_fault_persists decode growth actual
    exact ⟨f,by simp [errors,h,contextError],includes⟩
  | resource config decode => exact fun e h => StateResource.faultRead_persists config decode growth h
  | domain opener field =>
    intro e h
    cases old : initialCarrier opener field A with
    | bot => simp [errors,domainError,old] at h
    | one _ _ => simp [errors,domainError,old] at h
    | top original =>
      have equal : original = e := by simpa [errors,domainError,old] using h
      subst e
      have absorbs : initialCarrier opener field A ⊔ initialCarrier opener field B = initialCarrier opener field B :=
        lift_join_of_forall _ (fun a ha => join_lift_of_mem _ (by
          have member := List.mem_filter.mp ha
          exact List.mem_filter.mpr ⟨growth a member.1, member.2⟩))
      have topEq : Sole.join (.top original) (initialCarrier opener field B) = initialCarrier opener field B := by
        simpa [old] using absorbs
      cases new : initialCarrier opener field B with
      | bot => simp [new,Sole.join] at topEq
      | one _ _ => simp [new,Sole.join] at topEq
      | top f =>
        refine ⟨f,by simp [errors,domainError,new],?_⟩
        have enlarged : original ∪ f = f := by simpa [new,Sole.join] using topEq
        intro id member
        rw [← enlarged]
        exact Or.inl member
  | threshold spec =>
    intro e h
    letI := spec.algebra
    change thresholdError spec A = some e at h
    change ∃ f, thresholdError spec B = some f ∧ _
    unfold thresholdError at h ⊢
    split at h
    · rename_i top
      have equal : acceptedEvidence A = e := Option.some.inj h
      subst e
      have absorbs : lift spec.contribution A ⊔ lift spec.contribution B = lift spec.contribution B :=
        lift_join_of_forall _ (fun a ha => join_lift_of_mem _ (growth a ha))
      have newTop : lift spec.contribution B = ⊤ := by rw [top,top_join] at absorbs; exact absorbs.symm
      refine ⟨acceptedEvidence B,by simp [newTop],?_⟩
      rintro id ⟨a,ha,equal⟩
      exact ⟨a,growth a ha,equal⟩
    · contradiction
  | join left right il ir => exact unionError_grows il ir
  | freeze verb contributes policy source ih => exact freezeFault_grows closed growth verb contributes policy ih

theorem acceptedEvidence_setEq {A B : List Act} (same : SetEq A B) :
    acceptedEvidence A = acceptedEvidence B := by
  funext id
  apply propext
  constructor
  · rintro ⟨a,ha,address⟩; exact ⟨a,(same a).mp ha,address⟩
  · rintro ⟨a,ha,address⟩; exact ⟨a,(same a).mpr ha,address⟩

theorem errors_setEq (world : Act → Prop) (path : Path) {A B : List Act} (same : SetEq A B) :
    errors world path A = errors world path B := by
  classical
  induction path with
  | clear => rfl
  | certified spec => exact spec.equiv same
  | context decode => simp only [errors,StateContext.read_setEq decode same]
  | resource config decode => exact StateResource.faultRead_setEq config decode same
  | domain opener field => simp only [errors,domainError,initialCarrier_invariant same]
  | threshold spec =>
    letI := spec.algebra
    simp only [errors,thresholdError,lift_setEq spec.contribution same,acceptedEvidence_setEq same]
  | join _ _ il ir => simp only [errors,il,ir]
  | freeze verb contributes policy source ih =>
    simp only [errors,freezeFault,ih,freezeConflict_setEq same,freezeEvidence_setEq same]

/-- The freeze verb, contributing-act predicate, and late-write policy. -/
structure FreezeSpec where
  /-- The contributing verb name. -/
  verb : String
  /-- Whether an accepted act contributes to the frozen source. -/
  contributes : Act → Prop
  /-- The installed handling of contributions after the freeze. -/
  policy : Bool

end CBCL.StateObservation
