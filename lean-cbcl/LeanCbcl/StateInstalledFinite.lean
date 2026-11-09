import LeanCbcl.StateFiniteProjection
import LeanCbcl.StateInstalledDomains

/-! Finite native sources retain raw accepted history. Domain eligibility grows
with retained initializer/roster evidence; error guards preserve the native
writer witnesses even when a domain fault takes diagnostic precedence. -/
set_option autoImplicit false
namespace CBCL.StateInstalledFinite
open State StateLift StateLVar StateObservation StateObservationPlan StateInstalledCompiler

/-- Installed finite source metadata shared by display, error, and raw reads. -/
structure Field where
  /-- The installed finite table with checked semilattice laws. -/
  table : StateFiniteTable.Verified
  /-- The source performative selected by this declaration. -/
  verb : String
  /-- The authored rows retained in declaration order. -/
  rows : List (StateFiniteProjection.Row table.table)
  /-- The resolved finite projection and its checked validation evidence. -/
  projection : Option (StateFiniteProjection.Verified table.table)
  /-- The resolved domain selectors affecting this source. -/
  domains : List StateInstalledDomains.Domain

/-- The exact all-matching-rows native contribution function. -/
def contribution (field : Field) := StateFiniteProjection.contribution field.table.table field.rows

/-- Domain-filtered source acts; the raw accepted set remains retained. -/
def selected (field : Field) (A : List Act) : List Act :=
  (StateInstalledDomains.select field.domains A).filter (fun act => act.verb == field.verb)

/-- Current finite carrier, independently of any freeze on its display. -/
def state (field : Field) (A : List Act) : Fin field.table.table.elements.length :=
  letI := StateFiniteTable.algebra field.table
  lift (contribution field) (selected field A)

/-- Addresses of non-bottom source writers in the supplied selection. -/
def writers (field : Field) (A : List Act) : Evidence := fun address =>
  ∃ act ∈ A, act.addr = address ∧ act.verb = field.verb ∧ contribution field act ≠ field.table.table.bottom

/-- Domain source faults relevant to this finite source's verb. -/
def domainSpec (field : Field) : ErrorSpec :=
  (field.domains.filter (fun domain => domain.verb == field.verb)).foldr
    (fun domain rest => StateContextEvidence.joinSpec (StateInstalledDomains.errorSpec domain.source) rest)
    { support := by intros A e fault; contradiction, read := fun _ => none, equiv := fun _ => rfl, grow := by intro A B growth e impossible; contradiction }

theorem selected_setEq (field : Field) {A B : List Act} (same : SetEq A B) :
    SetEq (selected field A) (selected field B) := by
  have selected := StateInstalledDomains.selected_setEq field.domains same
  intro act
  simp only [StateInstalledFinite.selected,List.mem_filter,selected act]

theorem selected_grows (field : Field) {A B : List Act} (growth : ∀ act ∈ A, act ∈ B) :
    ∀ act ∈ selected field A, act ∈ selected field B := by
  intro act member
  obtain ⟨eligible,verb⟩ := List.mem_filter.mp member
  exact List.mem_filter.mpr ⟨StateInstalledDomains.selected_grows field.domains growth act eligible,verb⟩

theorem selected_inside (field : Field) (A : List Act) : ∀ act ∈ selected field A, act ∈ A := by
  intro act member
  exact (List.mem_filter.mp (List.mem_filter.mp member).1).1

theorem state_setEq (field : Field) {A B : List Act} (same : SetEq A B) : state field A = state field B := by
  letI := StateFiniteTable.algebra field.table
  exact lift_setEq (contribution field) (selected_setEq field same)

theorem state_grows (field : Field) {A B : List Act} (growth : ∀ act ∈ A, act ∈ B) :
    letI := StateFiniteTable.algebra field.table
    Below (state field A) (state field B) := by
  letI := StateFiniteTable.algebra field.table
  exact lift_join_of_forall _ (fun act member => join_lift_of_mem _ (selected_grows field growth act member))

theorem writers_setEq (field : Field) {A B : List Act} (same : SetEq A B) : writers field A = writers field B := by
  funext address
  apply propext
  have membership : ∀ act, act ∈ A ↔ act ∈ B := same
  simp only [writers,membership]

theorem writers_grows (field : Field) {A B : List Act} (growth : ∀ act ∈ A, act ∈ B) :
    ∀ address ∈ writers field A, address ∈ writers field B := by
  rintro address ⟨act,member,identity,verb,nonbottom⟩
  exact ⟨act,growth act member,identity,verb,nonbottom⟩

/-- Applicable initializer and roster identities required to replay eligibility. -/
def domainEvidence (field : Field) (A : List Act) : Evidence := fun id =>
  ∃ domain ∈ field.domains, domain.verb = field.verb ∧ ∃ act ∈ A,
    StateInstalledDomains.supports domain.source act = true ∧ act.addr = id

/-- Domain support is monotone under receipt of accepted acts. -/
theorem domain_evidence_grows (field : Field) {A B : List Act} (growth : ∀ act ∈ A, act ∈ B) :
    ∀ id ∈ domainEvidence field A, id ∈ domainEvidence field B := by
  rintro id ⟨domain,declared,verb,act,inside,supports,identity⟩
  exact ⟨domain,declared,verb,act,growth act inside,supports,identity⟩

/-- Equal accepted sets give exactly equal domain support evidence. -/
theorem domain_evidence_setEq (field : Field) {A B : List Act} (same : SetEq A B) :
    domainEvidence field A = domainEvidence field B := by
  funext id
  exact propext ⟨domain_evidence_grows field (fun act member => (same act).mp member) id,
    domain_evidence_grows field (fun act member => (same act).mpr member) id⟩

/-- Domain witnesses name actual accepted supporting acts. -/
theorem domain_evidence_supported (field : Field) (A : List Act) :
    StateEvidenceSupport.Supported A (domainEvidence field A) := by
  rintro id ⟨domain,declared,verb,act,inside,supports,identity⟩
  exact List.mem_map.mpr ⟨act,inside,identity⟩

/-- Writer witnesses name actual accepted source acts. -/
theorem writers_supported (field : Field) (A : List Act) :
    StateEvidenceSupport.Supported A (writers field A) := by
  rintro id ⟨act,inside,identity,_,_⟩
  exact List.mem_map.mpr ⟨act,inside,identity⟩

/-- A domain fault retains raw writers and every applicable domain support. -/
def domainErrorSpec (field : Field) : ErrorSpec := {
  support := by
    intro A e fault
    cases old : (domainSpec field).read A with
    | none => simp [old] at fault
    | some initial =>
      have same : initial ∪ (writers field A ∪ domainEvidence field A) = e := by simpa [old] using fault
      subst e
      exact StateEvidenceSupport.union_supported ((domainSpec field).support old)
        (StateEvidenceSupport.union_supported (writers_supported field A) (domain_evidence_supported field A))
  read := fun A => match (domainSpec field).read A with
    | none => none
    | some evidence => some (evidence ∪ (writers field A ∪ domainEvidence field A))
  equiv := by
    intro A B same
    rw [(domainSpec field).equiv same,writers_setEq field same,domain_evidence_setEq field same]
  grow := by
    intro A B growth evidence fault
    cases old : (domainSpec field).read A with
    | none => simp [old] at fault
    | some initial =>
      have equal : initial ∪ (writers field A ∪ domainEvidence field A) = evidence := by simpa [old] using fault
      subst evidence
      obtain ⟨later,current,persist⟩ := (domainSpec field).grow growth initial old
      refine ⟨later ∪ (writers field B ∪ domainEvidence field B),by simp [current],?_⟩
      intro address member
      rcases member with old | writer | support
      · exact Or.inl (persist address old)
      · exact Or.inr (Or.inl (writers_grows field growth address writer))
      · exact Or.inr (Or.inr (domain_evidence_grows field growth address support)) }

/-- Finite top retains selected non-bottom writers and replay domain context. -/
def topErrorSpec (field : Field) : ErrorSpec := {
  support := by
    intro A e fault
    split at fault
    · have same := Option.some.inj fault
      subst e
      apply StateEvidenceSupport.union_supported
      · rintro id ⟨act,accepted,identity,_,_⟩
        exact List.mem_map.mpr ⟨act,selected_inside field A act accepted,identity⟩
      · exact domain_evidence_supported field A
    · contradiction
  read := fun A => if state field A = field.table.table.top then
    some (writers field (selected field A) ∪ domainEvidence field A) else none
  equiv := by
    intro A B same
    rw [state_setEq field same,writers_setEq field (selected_setEq field same),domain_evidence_setEq field same]
  grow := by
    intro A B growth evidence fault
    split at fault
    · rename_i conflict
      have equal : writers field (selected field A) ∪ domainEvidence field A = evidence := Option.some.inj fault
      subst evidence
      have conflictB : state field B = field.table.table.top := by
        letI := StateFiniteTable.algebra field.table
        have grows := state_grows field growth
        rw [conflict] at grows
        exact top_below grows
      refine ⟨writers field (selected field B) ∪ domainEvidence field B,by simp [conflictB],?_⟩
      intro id member
      exact member.elim (fun writer => Or.inl (writers_grows field (selected_grows field growth) id writer))
        (fun support => Or.inr (domain_evidence_grows field growth id support))
    · contradiction }

/-- Independent monotone witness channels compose before rendering. -/
def errorSpec (field : Field) : ErrorSpec :=
  StateContextEvidence.joinSpec (domainErrorSpec field) (topErrorSpec field)

/-- Native diagnostic precedence reports raw writers and support on domain failure. -/
def nativeError (field : Field) (A : List Act) : Error :=
  match (domainSpec field).read A with
  | some evidence => some (evidence ∪ (writers field A ∪ domainEvidence field A))
  | none => (topErrorSpec field).read A

/-- Adding top cannot change a domain fault's complete native witness set. -/
theorem native_error_refinement (field : Field) (A : List Act) : (errorSpec field).read A = nativeError field A := by
  unfold errorSpec StateContextEvidence.joinSpec nativeError domainErrorSpec
  cases domain : (domainSpec field).read A with
  | none => simp [domain,unionError]
  | some evidence =>
    simp only [domain]
    change unionError (some (evidence ∪ (writers field A ∪ domainEvidence field A)))
      (if state field A = field.table.table.top then some (writers field (selected field A) ∪ domainEvidence field A) else none) = _
    split
    · apply congrArg some
      funext address
      apply propext
      constructor
      · intro member
        rcases member with old | writer | support
        · exact old
        · exact Or.inr (Or.inl (writers_grows field (selected_inside field A) address writer))
        · exact Or.inr (Or.inr support)
      · exact Or.inl
    · rfl

/-- Render the checked projection, or the installed element name by default. -/
def display (field : Field) (element : Fin field.table.table.elements.length) : Val :=
  match field.projection with
  | none => .str field.table.table.elements[element]
  | some projection => StateFiniteProjection.value projection element

/-- Pure finite display on the canonical retained history. -/
noncomputable def snapshot (field : Field) (carrier : FinSet Act) : StateInstalledLegacy.Value :=
  .kernel (.cell (.value (display field (state field (StateInstalledLegacy.history carrier)))))

/-- The raw accepted carrier remains available to thresholds and freeze cuts. -/
noncomputable def term (field : Field) : StateInstalledTerm.Term StateInstalledLegacy.Value := {
  Carrier := FinSet Act
  state := id
  project := snapshot field
  guards := [.certified (errorSpec field)]
  algebra := inferInstance
  state_bottom := rfl
  state_merge := fun _ _ => rfl }

/-- Every finite source is a guarded history-backed kernel term. -/
noncomputable def source (field : Field) : Source StateInstalledLegacy.Value :=
  StateInstalledTerm.source (term field)

/-- Native finite source read, with diagnostic precedence and actual history. -/
noncomputable def nativeRead (field : Field) (A : List Act) : StateObservationPlan.Observation StateInstalledLegacy.Value :=
  match nativeError field A with
  | some evidence => .fault evidence
  | none => .data (.snapshot (.kernel (.cell (.value (display field (state field A))))))

/-- The closed finite factory agrees with its native reader on actual accepted
history, not only the chosen canonical list representative. -/
theorem concrete_finite_read_refinement (field : Field) (A : List Act) :
    sourceRead (source field) A = nativeRead field A := by
  have same : state field (StateInstalledLegacy.history (rawHistory A)) = state field A :=
    state_setEq field (StateInstalledLegacy.history_setEq A)
  change nativeGuard ((errorSpec field).read A) (.data (.snapshot (snapshot field (rawHistory A)))) = _
  rw [native_error_refinement]
  unfold nativeRead nativeGuard snapshot
  rw [same]
  cases nativeError field A <;> rfl

/-- Authored finite lift before contribution and projection name resolution. -/
structure Declaration where
  /-- The authored contributing performative. -/
  verb : String
  /-- Scalar comparison rows before target element resolution. -/
  rows : List StateFiniteProjection.Contribution
  /-- Optional authored scalar projection and stability declaration. -/
  projection : Option StateFiniteProjection.Declaration

/-- Resolve actual scalar contributions and checked projections. Verb/field
shape recognition is the same explicit installed-schema boundary as domains. -/
def make (schema : StateInstalledDomains.Schema) (table : StateFiniteTable.Verified)
    (domains : List StateInstalledDomains.Domain) (declaration : Declaration) : Option Field := do
  if !schema.verbs.contains declaration.verb || declaration.rows.isEmpty ||
      !declaration.rows.all (fun row => row.key != "replaces" &&
        (schema.types.lookup (declaration.verb,row.key)).isSome &&
        schema.types.lookup (declaration.verb,row.key) != some .other) then none else do
  let rows ← declaration.rows.mapM (StateFiniteProjection.resolveRow table.table)
  let projection ← match declaration.projection with
    | none => some none
    | some authored => (StateFiniteProjection.compile table.table authored).map some
  some ⟨table,declaration.verb,rows,projection,domains⟩

end CBCL.StateInstalledFinite
