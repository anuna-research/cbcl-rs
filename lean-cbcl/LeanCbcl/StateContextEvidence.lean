import LeanCbcl.StateEvidenceSupport

/-! Independent context fault witnesses survive diagnostic precedence. Root
sealing uses the kernel's typed root decoder; mixed-thread and opener-fork
checks retain their own accepted identities. The native normalizer is proved
equal to the union of these monotone witness channels. -/
set_option autoImplicit false

namespace CBCL.StateContextEvidence
open State StateLift StateLVar StateObservation

/-- Immutable root, thread, and opener metadata used by context fault checks. -/
structure Input where
  /-- The immutable root-context decoder. -/
  root : Act → Option Val
  /-- The thread identity extracted from the accepted message. -/
  thread : Act → Option String
  /-- The protocol opener verb, when the installed protocol defines one. -/
  opener : Option String

theorem vacuous_closed (A : List Act) : CausallyClosed (fun _ => False) A := by
  intro child member parent impossible edge
  contradiction

/-- Persistent error guard for incompatible or malformed root projections. -/
def rootSpec (input : Input) : ErrorSpec := {
  support := fun fault => StateEvidenceSupport.context_error_supported input.root _ _ fault
  read := fun A => contextError (StateContext.read input.root A)
  equiv := fun same => by rw [StateContext.read_setEq input.root same]
  grow := fun growth => errors_persist (fun _ => False) (.context input.root) (vacuous_closed _) growth }

/-- An accepted root and accepted act disagree on thread identity. -/
def Mixed (input : Input) (A : List Act) : Prop :=
  ∃ root ∈ A, root.preds = [] ∧ ∃ act ∈ A, input.thread act ≠ input.thread root

/-- Check accepted history for a thread-identity mismatch with an accepted root. -/
def mixedCheck (input : Input) (A : List Act) : Bool :=
  A.any (fun root => root.preds.isEmpty && A.any (fun act => input.thread act != input.thread root))

theorem mixedCheck_iff (input : Input) (A : List Act) : mixedCheck input A = true ↔ Mixed input A := by
  simp [mixedCheck,Mixed]

/-- Retain all accepted identities when a mixed-thread witness exists. -/
def mixedError (input : Input) (A : List Act) : Error :=
  if mixedCheck input A then some (acceptedEvidence A) else none

theorem mixed_setEq (input : Input) {A B : List Act} (same : SetEq A B) : mixedCheck input A = mixedCheck input B := by
  apply Bool.eq_iff_iff.mpr
  rw [mixedCheck_iff,mixedCheck_iff]
  constructor
  · rintro ⟨root,member,empty,act,inside,different⟩
    exact ⟨root,(same root).mp member,empty,act,(same act).mp inside,different⟩
  · rintro ⟨root,member,empty,act,inside,different⟩
    exact ⟨root,(same root).mpr member,empty,act,(same act).mpr inside,different⟩

/-- The mixed-thread error channel with proved extensionality and growth. -/
def mixedSpec (input : Input) : ErrorSpec := {
  support := by
    intro A e fault
    unfold mixedError at fault
    split at fault
    · have same := Option.some.inj fault
      subst e
      rintro id ⟨act,accepted,identity⟩
      exact List.mem_map.mpr ⟨act,accepted,identity⟩
    · contradiction
  read := mixedError input
  equiv := fun same => by simp [mixedError,mixed_setEq input same,acceptedEvidence_setEq same]
  grow := by
    intro A B growth evidence fault
    unfold mixedError at fault ⊢
    split at fault
    · rename_i old
      have mixed := (mixedCheck_iff input A).mp old
      obtain ⟨root,member,empty,act,inside,different⟩ := mixed
      have present : mixedCheck input B = true := (mixedCheck_iff input B).mpr
        ⟨root,growth root member,empty,act,growth act inside,different⟩
      have equal := Option.some.inj fault
      subst evidence
      refine ⟨acceptedEvidence B,by simp [present],?_⟩
      rintro address ⟨a,ha,identity⟩
      exact ⟨a,growth a ha,identity⟩
    · contradiction }

/-- Read terminal evidence from the sole-value lattice of contributions. -/
def soleError (contribution : Act → Sole) (A : List Act) : Error :=
  match lift contribution A with
  | .top evidence => some evidence
  | _ => none

theorem soleError_grows (contribution : Act → Sole) {A B : List Act} (growth : ∀ a ∈ A, a ∈ B) :
    Grows (soleError contribution A) (soleError contribution B) := by
  intro evidence fault
  have absorbs : lift contribution A ⊔ lift contribution B = lift contribution B :=
    lift_join_of_forall _ (fun a member => join_lift_of_mem _ (growth a member))
  cases old : lift contribution A with
  | bot => simp [soleError,old] at fault
  | one _ _ => simp [soleError,old] at fault
  | top original =>
    have equal : original = evidence := by simpa [soleError,old] using fault
    subst evidence
    have joined : Sole.join (.top original) (lift contribution B) = lift contribution B := by simpa [old] using absorbs
    cases current : lift contribution B with
    | bot => simp [current,Sole.join] at joined
    | one _ _ => simp [current,Sole.join] at joined
    | top enlarged =>
      refine ⟨enlarged,by simp [soleError,current],?_⟩
      have union : original ∪ enlarged = enlarged := by simpa [current,Sole.join] using joined
      intro address member
      rw [← union]
      exact Or.inl member

/-- Whether accepted history contains a predecessor-free root. -/
def hasRoot (A : List Act) : Bool := A.any (fun a => a.preds.isEmpty)

theorem hasRoot_iff (A : List Act) : hasRoot A = true ↔ ∃ root ∈ A, root.preds = [] := by simp [hasRoot]

/-- An opener contributes its identity to the sole-value lattice. -/
def openerContribution (input : Input) (a : Act) : Sole :=
  if input.opener == some a.verb then .one a.addr none else .bot

/-- Report opener-fork evidence only after a thread root is present. -/
def openerError (input : Input) (A : List Act) : Error :=
  if hasRoot A then soleError (openerContribution input) A else none

/-- Persistent error guard for competing accepted context openers. -/
def openerSpec (input : Input) : ErrorSpec := {
  support := by
    intro A e fault
    unfold openerError at fault
    split at fault
    · cases observed : lift (openerContribution input) A with
      | bot | one _ _ => simp [soleError,observed] at fault
      | top actual =>
        have same : actual = e := by simpa [soleError,observed] using fault
        subst e
        have supports := StateEvidenceSupport.sole_lift_supported (openerContribution input) (by
          intro act id
          unfold openerContribution
          split <;> simp [Sole.evidence]) A
        simpa only [observed,Sole.evidence] using supports
    · contradiction
  read := openerError input
  equiv := by
    intro A B same
    have roots : hasRoot A = hasRoot B := by
      apply Bool.eq_iff_iff.mpr
      simp only [hasRoot_iff]
      constructor
      · rintro ⟨root,member,empty⟩; exact ⟨root,(same root).mp member,empty⟩
      · rintro ⟨root,member,empty⟩; exact ⟨root,(same root).mpr member,empty⟩
    simp [openerError,roots,soleError,lift_setEq (openerContribution input) same]
  grow := by
    intro A B growth evidence fault
    unfold openerError at fault ⊢
    split at fault
    · rename_i present
      obtain ⟨root,member,empty⟩ := (hasRoot_iff A).mp present
      have roots : hasRoot B = true := (hasRoot_iff B).mpr ⟨root,growth root member,empty⟩
      simp only [roots,if_true]
      exact soleError_grows (openerContribution input) growth evidence fault
    · contradiction }

/-- Union independently proved error channels without changing their data. -/
def joinSpec (left right : ErrorSpec) : ErrorSpec := {
  support := fun fault => StateEvidenceSupport.union_error_supported _ _ _
    (fun _ h => left.support h) (fun _ h => right.support h) _ fault
  read := fun A => unionError (left.read A) (right.read A)
  equiv := fun same => by rw [left.equiv same,right.equiv same]
  grow := fun growth => unionError_grows (left.grow growth) (right.grow growth) }

/-- Combine root and mixed-thread checks with an optional opener-fork check. -/
def spec (input : Input) (observesOpener : Bool) : ErrorSpec :=
  if observesOpener then joinSpec (rootSpec input) (joinSpec (mixedSpec input) (openerSpec input))
  else joinSpec (rootSpec input) (mixedSpec input)

/-- Original diagnostic phase order: root, mixed-thread, then opener. -/
def firstError (root mixed opener : Error) : Error :=
  match root with
  | some evidence => some evidence
  | none => match mixed with
      | some evidence => some evidence
      | none => opener

/-- The native evidence-retention wrapper preserves independent witnesses
without changing the already selected fault's diagnostic reason. -/
def normalize (base mixed opener : Error) : Error :=
  match base with
  | none => none
  | some _ => unionError base (unionError mixed opener)

theorem normalization_eq_union (root mixed opener : Error) :
    normalize (firstError root mixed opener) mixed opener = unionError root (unionError mixed opener) := by
  cases root <;> cases mixed <;> cases opener <;> simp [normalize,firstError,unionError]
  all_goals
    funext address
    apply propext
    simp [Union.union,Lattice.Set.instUnion,Lattice.Set.union,or_assoc]

/-- Normalize the phase-ordered native diagnostic while retaining independent witness channels. -/
def nativeRead (input : Input) (observesOpener : Bool) (A : List Act) : Error :=
  let root := (rootSpec input).read A
  let mixed := mixedError input A
  let opener := if observesOpener then openerError input A else none
  normalize (firstError root mixed opener) mixed opener

theorem native_context_witness_refinement (input : Input) (observesOpener : Bool) (A : List Act) :
    nativeRead input observesOpener A = (spec input observesOpener).read A := by
  rw [nativeRead,normalization_eq_union]
  cases observesOpener <;> simp [spec,joinSpec,unionError,mixedSpec,openerSpec]
  cases mixedError input A <;> cases (rootSpec input).read A <;> rfl

theorem native_context_fault_persists (input : Input) (observesOpener : Bool)
    {A B : List Act} (growth : ∀ a ∈ A, a ∈ B) (evidence : Evidence)
    (fault : nativeRead input observesOpener A = some evidence) :
    ∃ enlarged, nativeRead input observesOpener B = some enlarged ∧ ∀ address ∈ evidence, address ∈ enlarged := by
  rw [native_context_witness_refinement] at fault
  rw [native_context_witness_refinement]
  exact (spec input observesOpener).grow growth evidence fault

/-- The native linear scan against its first root detects exactly the same
mixed-thread witness as the order-independent existential checker. -/
theorem mixedCheck_first_root (input : Input) (A : List Act) (root : Act)
    (accepted : root ∈ A) (empty : root.preds = []) :
    mixedCheck input A = A.any (fun act => input.thread act != input.thread root) := by
  apply Bool.eq_iff_iff.mpr
  have anyIff : A.any (fun act => input.thread act != input.thread root) = true ↔
      ∃ act ∈ A, input.thread act ≠ input.thread root := by simp
  rw [mixedCheck_iff,anyIff]
  constructor
  · rintro ⟨other,member,_,act,inside,different⟩
    by_cases mismatch : input.thread act = input.thread root
    · refine ⟨other,member,?_⟩
      intro same
      exact different (mismatch.trans same.symm)
    · exact ⟨act,inside,mismatch⟩
  · rintro ⟨act,inside,different⟩
    exact ⟨root,accepted,empty,act,inside,different⟩

end CBCL.StateContextEvidence
