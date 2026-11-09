import LeanCbcl.StateReplayPaths
import LeanCbcl.StateOutputCompiler
import LeanCbcl.StateConditionFaults

/-! Fault observations bridge the immutable replica world to the local,
normalized world used by emitted output instructions. -/
set_option autoImplicit false
namespace CBCL.StateOutputWitnessReplay
open State StateLift StateLVar StateObservation StateObservationPlan StateOutputCompiler

/-- A closed accepted history contains every global ancestor of an accepted
act, so restricting the world to that history preserves ancestry. -/
theorem ancestor_local_iff (world : Act → Prop) (A : List Act)
    (valid : ∀ act ∈ A, world act) (closed : CausallyClosed world A)
    {a f : Act} (present : f ∈ A) :
    Ancestor world a f ↔ Ancestor (fun act => act ∈ A) a f := by
  constructor
  · intro ancestry
    induction ancestry with
    | self _ => exact .self present
    | step earlier edge rest ih =>
      exact .step (ancestor_accepted closed (.step earlier edge rest) present) edge (ih present)
  · intro ancestry
    induction ancestry with
    | self member => exact .self (valid _ member)
    | step member edge rest ih => exact .step (valid _ member) edge (ih present)

/-- Earliest freezer selection agrees in the global and local closed worlds. -/
theorem earliest_local_iff (world : Act → Prop) (A : List Act)
    (valid : ∀ act ∈ A, world act) (closed : CausallyClosed world A) (verb : String) (freezer : Act) :
    Earliest world verb A freezer ↔ Earliest (fun act => act ∈ A) verb A freezer := by
  constructor
  · rintro ⟨present,matching,first⟩
    exact ⟨present,matching,fun earlier inside verb path => first earlier inside verb
      ((ancestor_local_iff world A valid closed present).mpr path)⟩
  · rintro ⟨present,matching,first⟩
    exact ⟨present,matching,fun earlier inside verb path => first earlier inside verb
      ((ancestor_local_iff world A valid closed present).mp path)⟩

/-- Both concurrent and late freeze conflicts preserve their actual pair when
the accepted history becomes the output interpreter's local world. -/
theorem conflict_local_iff (world : Act → Prop) (A : List Act)
    (valid : ∀ act ∈ A, world act) (closed : CausallyClosed world A)
    (verb : String) (contribution : Act → Prop) (policy : Bool) (a b : Act) :
    FreezeConflict world verb contribution policy A a b ↔
      FreezeConflict (fun act => act ∈ A) verb contribution policy A a b := by
  constructor
  · intro conflict
    cases conflict with
    | concurrent first second different =>
      exact .concurrent
        ((earliest_local_iff world A valid closed verb a).mp first)
        ((earliest_local_iff world A valid closed verb b).mp second) different
    | late first inside contributing outside faultPolicy =>
      exact .late ((earliest_local_iff world A valid closed verb a).mp first) inside contributing
        (fun path => outside ((ancestor_local_iff world A valid closed first.1).mpr path)) faultPolicy
  · intro conflict
    cases conflict with
    | concurrent first second different =>
      exact .concurrent
        ((earliest_local_iff world A valid closed verb a).mpr first)
        ((earliest_local_iff world A valid closed verb b).mpr second) different
    | late first inside contributing outside faultPolicy =>
      exact .late ((earliest_local_iff world A valid closed verb a).mpr first) inside contributing
        (fun path => outside ((ancestor_local_iff world A valid closed first.1).mp path)) faultPolicy

/-- Exact conflict evidence is independent of global versus local-world interpretation. -/
theorem evidence_local (world : Act → Prop) (A : List Act)
    (valid : ∀ act ∈ A, world act) (closed : CausallyClosed world A)
    (verb : String) (contribution : Act → Prop) (policy : Bool) :
    freezeEvidence world verb contribution policy A =
      freezeEvidence (fun act => act ∈ A) verb contribution policy A := by
  funext id
  apply propext
  constructor
  · rintro ⟨a,b,conflict,which⟩
    exact ⟨a,b,(conflict_local_iff world A valid closed verb contribution policy a b).mp conflict,which⟩
  · rintro ⟨a,b,conflict,which⟩
    exact ⟨a,b,(conflict_local_iff world A valid closed verb contribution policy a b).mpr conflict,which⟩

/-- Every complete dependency error path has the same fault and exact evidence
in the replica world and the output interpreter's local world. -/
theorem errors_local (world : Act → Prop) (A : List Act)
    (valid : ∀ act ∈ A, world act) (closed : CausallyClosed world A) (source : Path) :
    errors world source A = errors (fun act => act ∈ A) source A := by
  induction source with
  | clear | certified _ | context _ | domain _ _ | resource _ _ | threshold _ => rfl
  | join left right ihLeft ihRight => simp only [errors,ihLeft,ihRight]
  | freeze verb contribution policy source ih =>
    have conflicts : (∃ a b, FreezeConflict world verb contribution policy A a b) ↔
        ∃ a b, FreezeConflict (fun act => act ∈ A) verb contribution policy A a b := by
      constructor
      · rintro ⟨a,b,conflict⟩
        exact ⟨a,b,(conflict_local_iff world A valid closed verb contribution policy a b).mp conflict⟩
      · rintro ⟨a,b,conflict⟩
        exact ⟨a,b,(conflict_local_iff world A valid closed verb contribution policy a b).mpr conflict⟩
    simp only [errors]
    unfold freezeFault
    rw [ih,propext conflicts,evidence_local world A valid closed verb contribution policy]

/-- A plan fault is exactly its terminal error-channel observation. -/
theorem observation_fault_iff {V : Type} (world : Act → Prop) (source : Plan V) (A : List Act) (e : Evidence) :
    observe world source A = .fault e ↔ errors world (path source) A = some e := by
  cases observed : errors world (path source) A <;> simp [observe,observed]

/-- Output normalization preserves the global error observation. Causal closure
and valid-world membership are derived for the normalized accepted history. -/
theorem normalized_errors (world : Act → Prop) (A : List Act)
    (valid : ∀ act ∈ A, world act) (closed : CausallyClosed world A) (source : Path) :
    errors (fun act => act ∈ StateScopePool.normalize A) source (StateScopePool.normalize A) = errors world source A := by
  have same := StateScopePool.normalize_setEq A
  have normalizedValid : ∀ act ∈ StateScopePool.normalize A, world act :=
    fun act inside => valid act ((same act).mp inside)
  have normalizedClosed : CausallyClosed world (StateScopePool.normalize A) := by
    intro child inside parent parentValid edge
    exact (same parent).mpr (closed child ((same child).mp inside) parent parentValid edge)
  rw [← errors_local world _ normalizedValid normalizedClosed source]
  exact errors_setEq world source same

/-- The actual emitted source instruction faults exactly when the globally
interpreted compiled plan faults, with identical evidence. -/
theorem source_value_fault_iff {V : Type} (world : Act → Prop) (A : List Act)
    (valid : ∀ act ∈ A, world act) (closed : CausallyClosed world A) (source : Plan V) (e : Evidence) :
    sourceValue A source = .fault e ↔ observe world source A = .fault e := by
  rw [observation_fault_iff,sourceValue,observation_fault_iff,normalized_errors world A valid closed]

/-- The rendered name retained by either output instruction. -/
def outputName {V : Type} : Output V → String
  | .field name _ | .threshold name _ _ _ | .condition name _ _ => name

/-- The complete compiled source retained by either output instruction. -/
noncomputable def outputSource {V : Type} : Output V → Plan V
  | .field _ source | .threshold _ _ _ source => source
  | .condition _ truth code => StateConditionFaults.dependencies truth code

/-- An output's query strategy adds no independent top fault. -/
def PlainOutput {V : Type} : Output V → Prop
  | .field .. => True
  | .threshold _ _ query _ => PlainQuery query
  | .condition _ _ code => StateConditionFaults.Plain code

/-- Every instruction preserves completed source evidence; conjunctions may
add independent query witnesses but never erase the original fault. -/
theorem output_preserves_source_fault {V : Type} (output : Output V) (whole : List Act)
    (freezes : List (String × FreezeSpec)) (e : Evidence)
    (fault : sourceValue whole (outputSource output) = .fault e) :
    ∃ enlarged, output.observe whole freezes = (outputName output,.fault enlarged) ∧
      ∀ id ∈ e, id ∈ enlarged := by
  cases output with
  | field name source => exact ⟨e,congrArg (fun value => (name,value)) fault,fun _ member => member⟩
  | threshold name sourceName query source =>
    refine ⟨e,?_,fun _ member => member⟩
    change sourceValue whole source = .fault e at fault
    change (name,query.run _ (sourceValue whole source)) = _
    rw [fault,query_preserves_fault]
    rfl
  | condition name truth code =>
    obtain ⟨enlarged,current,contains⟩ := StateConditionFaults.preserves_fault truth whole freezes code e fault
    exact ⟨enlarged,congrArg (fun value => (name,value)) current,contains⟩

/-- For a plain emitted output, a fault is exactly the globally interpreted
source-plan fault. Local normalization and query scope introduce no new fault. -/
theorem output_fault_iff {V : Type} (world : Act → Prop) (A : List Act)
    (valid : ∀ act ∈ A, world act) (closed : CausallyClosed world A)
    (output : Output V) (plain : PlainOutput output) (freezes : List (String × FreezeSpec)) (e : Evidence) :
    output.observe A freezes = (outputName output,.fault e) ↔ observe world (outputSource output) A = .fault e := by
  cases output with
  | field name source =>
    simp only [Output.observe,outputName,outputSource,Prod.mk.injEq,true_and]
    exact source_value_fault_iff world A valid closed source e
  | threshold name sourceName query source =>
    simp only [Output.observe,outputName,outputSource,Prod.mk.injEq,true_and]
    rw [plain_query_fault_iff query plain]
    exact source_value_fault_iff world A valid closed source e
  | condition name truth code =>
    simp only [Output.observe,outputName,outputSource,Prod.mk.injEq,true_and]
    rw [StateConditionFaults.plain_fault_iff truth A freezes code plain e]
    exact source_value_fault_iff world A valid closed (StateConditionFaults.dependencies truth code) e

end CBCL.StateOutputWitnessReplay
