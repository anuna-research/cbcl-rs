import LeanCbcl.StateAuthoredOutputReplay

/-! Exact set invariance for corrected emitted output code, including raw
queries scoped to their source freezer, and finite-history replica convergence. -/
set_option autoImplicit false
namespace CBCL.StateOutputConvergence
open State StateLift StateLVar StateObservation StateObservationPlan StateOutputCompiler
open StateScopePool StateExecutableFreeze StateThresholdDispatch

/-- A single selected scope root is exactly the sole semantic earliest act. -/
theorem unique_root_iff (A : List Act) (ranked : Ranked A) (verb : String) (root : Act) :
    uniqueRoot A verb = some root ↔
      Earliest (fun act => act ∈ A) verb A root ∧
        ∀ other, Earliest (fun act => act ∈ A) verb A other → other = root := by
  constructor
  · intro selected
    have first := uniqueRoot_earliest A ranked verb root selected
    have singleton : FinSet.dedup (A.filter (earliest A verb)) = [root] := by
      cases found : FinSet.dedup (A.filter (earliest A verb)) with
      | nil => simp [uniqueRoot,found] at selected
      | cons head rest =>
        cases rest with
        | nil =>
          have same : head = root := by simpa [uniqueRoot,found] using selected
          simpa [same] using found
        | cons next more => simp [uniqueRoot,found] at selected
    refine ⟨first,?_⟩
    intro other otherFirst
    have inside := FinSet.mem_dedup.mpr (List.mem_filter.mpr
      ⟨otherFirst.1,(earliest_iff A ranked verb other).mpr otherFirst⟩)
    simpa [singleton] using inside
  · rintro ⟨first,only⟩
    exact uniqueRoot_complete A ranked root verb first only

/-- Equal act sets select the same unique root, including absent/concurrent cases. -/
theorem unique_root_setEq {A B : List Act} (rankedA : Ranked A) (rankedB : Ranked B)
    (same : SetEq A B) (verb : String) : uniqueRoot A verb = uniqueRoot B verb := by
  have transfer {X Y : List Act} (rx : Ranked X) (ry : Ranked Y) (eq : SetEq X Y) (root : Act)
      (selected : uniqueRoot X verb = some root) : uniqueRoot Y verb = some root := by
    have worldSame : (fun act => act ∈ X) = (fun act => act ∈ Y) := by
      funext act
      exact propext (eq act)
    have firsts : ∀ act, Earliest (fun node => node ∈ X) verb X act ↔
        Earliest (fun node => node ∈ Y) verb Y act := by
      intro act
      rw [worldSame]
      exact earliest_setEq eq act
    obtain ⟨first,only⟩ := (unique_root_iff X rx verb root).mp selected
    exact (unique_root_iff Y ry verb root).mpr ⟨(firsts root).mp first,
      fun other earliest => only other ((firsts other).mpr earliest)⟩
  cases left : uniqueRoot A verb with
  | none =>
    cases right : uniqueRoot B verb with
    | none => rfl
    | some root =>
      have contradiction := transfer rankedB rankedA (fun act => (same act).symm) root right
      rw [left] at contradiction
      contradiction
  | some root => exact (transfer rankedA rankedB same root left).symm

/-- Equal accepted sets yield equal source-freezer raw query scopes as sets. -/
theorem reference_scope_setEq {A B : List Act} (rankedA : Ranked A) (rankedB : Ranked B)
    (same : SetEq A B) (freezes : List (String × FreezeSpec)) (name : String) :
    SetEq (referenceScope A freezes name) (referenceScope B freezes name) := by
  have normalizedSame : SetEq (normalize A) (normalize B) := fun act =>
    ((normalize_setEq A act).trans (same act)).trans (normalize_setEq B act).symm
  cases declared : freezes.lookup name with
  | none => simpa [referenceScope,declared] using normalizedSame
  | some spec =>
    have selected := unique_root_setEq (normalize_ranked A rankedA) (normalize_ranked B rankedB) normalizedSame spec.verb
    cases root : uniqueRoot (normalize A) spec.verb with
    | none => simpa [referenceScope,declared,← selected,root] using normalizedSame
    | some freezer =>
      have worldSame : (fun act => act ∈ normalize A) = (fun act => act ∈ normalize B) := by
        funext act
        exact propext (normalizedSame act)
      simp only [referenceScope,declared,← selected,root]
      intro act
      simp only [causalCut,List.mem_filter,decide_eq_true_eq]
      rw [worldSame]
      exact and_congr (normalizedSame act) Iff.rfl

/-- Normalized source observations preserve all data, frozen exclusions and
fault evidence on equal accepted sets, including repeated delivery. -/
theorem source_value_setEq {V : Type} (source : Plan V) {A B : List Act}
    (consistentA : ∀ a ∈ A, ∀ b ∈ A, a.addr = b.addr → a = b)
    (consistentB : ∀ a ∈ B, ∀ b ∈ B, a.addr = b.addr → a = b) (same : SetEq A B) :
    sourceValue A source = sourceValue B source := by
  have normalizedSame : SetEq (normalize A) (normalize B) := fun act =>
    ((normalize_setEq A act).trans (same act)).trans (normalize_setEq B act).symm
  have worldSame : (fun act => act ∈ normalize A) = (fun act => act ∈ normalize B) := by
    funext act
    exact propext (normalizedSame act)
  unfold sourceValue
  rw [worldSame]
  exact observe_setEq _ source (normalize_unique A consistentA) (normalize_unique B consistentB) normalizedSame

/-- Every query strategy preserves exact source/result equality and accepted
raw-state set equality, including the generic checked finite adapter. -/
theorem query_run_setEq {V : Type} (query : Query V) {A B : List Act} (same : SetEq A B)
    (value : StateReaderValues.Result V) : query.run A value = query.run B value := by
  cases query with
  | closure alternatives test => rfl
  | raw alternatives test state => simp only [Query.run,rawHistory_setEq same]
  | finite spec embed =>
    letI := spec.algebra
    have thresholdSame : thresholdError spec A = thresholdError spec B :=
      errors_setEq (fun _ => True) (.threshold spec) same
    cases value with
    | fault _ => rfl
    | data current =>
      simp only [Query.run,StateInstalledCompiler.nativeLiftThreshold]
      rw [thresholdSame,lift_setEq spec.contribution same,rawHistory_setEq same]

/-- Corrected emitted instructions preserve exact observations on equal sets;
raw thresholds use equal source cuts rather than silently reading full history. -/
theorem output_observe_setEq {V : Type} (output : Output V) {A B : List Act}
    (rankedA : Ranked A) (rankedB : Ranked B)
    (consistentA : ∀ a ∈ A, ∀ b ∈ A, a.addr = b.addr → a = b)
    (consistentB : ∀ a ∈ B, ∀ b ∈ B, a.addr = b.addr → a = b)
    (same : SetEq A B) (freezes : List (String × FreezeSpec)) :
    output.observe A freezes = output.observe B freezes := by
  cases output with
  | field name source => exact congrArg (fun result => (name,result)) (source_value_setEq source consistentA consistentB same)
  | threshold name sourceName query source =>
    simp only [Output.observe]
    rw [source_value_setEq source consistentA consistentB same,
      query_run_setEq query (reference_scope_setEq rankedA rankedB same freezes sourceName)]

/-- The complete corrected emitted vector, not only its source plans or error
projection, is exactly invariant under accepted-set equality. -/
theorem program_observe_setEq {V : Type} (program : Program V) {A B : List Act}
    (rankedA : Ranked A) (rankedB : Ranked B)
    (consistentA : ∀ a ∈ A, ∀ b ∈ A, a.addr = b.addr → a = b)
    (consistentB : ∀ a ∈ B, ∀ b ∈ B, a.addr = b.addr → a = b) (same : SetEq A B) :
    program.observe A = program.observe B := by
  apply List.map_congr_left
  intro output member
  exact output_observe_setEq output rankedA rankedB consistentA consistentB same program.freezes

/-- Successful authored output compilation retains the same program at equal
accepted sets, and its complete captured observations agree exactly. -/
theorem authored_observations_setEq (environment : StateAuthoredBindings.Environment)
    (entries : List StateAuthoredBindings.Entry) {A B : List Act}
    (rankedA : Ranked A) (rankedB : Ranked B)
    (consistentA : ∀ a ∈ A, ∀ b ∈ A, a.addr = b.addr → a = b)
    (consistentB : ∀ a ∈ B, ∀ b ∈ B, a.addr = b.addr → a = b) (same : SetEq A B)
    (left right : CompiledObservation)
    (first : compileAuthored environment entries A = some left)
    (second : compileAuthored environment entries B = some right) : left.observe = right.observe := by
  have preparedSame := StateAuthoredBindings.prepare_setEq environment entries same
  cases prepared : StateAuthoredBindings.prepare environment entries A with
  | none => simp [compileAuthored,prepared] at first
  | some clause =>
    have preparedB : StateAuthoredBindings.prepare environment entries B = some clause := preparedSame.symm.trans prepared
    cases code : compileClause clause with
    | none => simp [compileAuthored,prepared,code] at first
    | some program =>
      have leftSame : (⟨A,program⟩ : CompiledObservation) = left := by simpa [compileAuthored,prepared,code] using first
      have rightSame : (⟨B,program⟩ : CompiledObservation) = right := by simpa [compileAuthored,preparedB,code] using second
      subst left
      subst right
      exact program_observe_setEq program rankedA rankedB consistentA consistentB same

/-- Successful static authored preparation constructs an emitted observation
at every ranked, content-consistent accepted history. -/
theorem prepared_output_exists (environment : StateAuthoredBindings.Environment)
    (entries : List StateAuthoredBindings.Entry) (prepared : StateAuthoredBindings.Prepared)
    (installed : StateAuthoredBindings.prepareStatic environment entries = some prepared) (A : List Act)
    (ranked : Ranked A) (consistent : ∀ a ∈ A, ∀ b ∈ A, a.addr = b.addr → a = b) :
    ∃ observation, compileAuthored environment entries A = some observation := by
  have ready : StateAuthoredBindings.prepare environment entries A = some (StateAuthoredBindings.clauseAt prepared A) := by
    simp [StateAuthoredBindings.prepare,installed,StateAuthoredBindings.clauseAt]
  obtain ⟨observation,_,compiled,_⟩ := authored_compiler_refinement environment entries A
    (StateAuthoredBindings.clauseAt prepared A) ready ranked consistent
  exact ⟨observation,compiled⟩

open StateKernelDelivery AdmissionStratification StateRefinement

/-- Fair replicas eventually agree exactly on the complete corrected emitted
vector for a finite valid history, including fault evidence and exclusions.
Compilation existence is derived from successful static installation. -/
theorem finite_history_output_convergence {adm : Admission} {auth : Act → Prop} {H : ValidHistory adm}
    (left right : Replica adm auth H) (admission : PredecessorAdmission adm H.contains)
    (causal : StateContextReplay.CausalDependencies H) (environment : StateAuthoredBindings.Environment)
    (entries : List StateAuthoredBindings.Entry) (prepared : StateAuthoredBindings.Prepared)
    (installed : StateAuthoredBindings.prepareStatic environment entries = some prepared)
    (history : List Act) (complete : ∀ act, H.contains act ↔ act ∈ history) :
    ∃ time, ∀ n m, time ≤ n → time ≤ m → ∃ first second,
      compileAuthored environment entries (left.run n).accepted = some first ∧
      compileAuthored environment entries (right.run m).accepted = some second ∧ first.observe = second.observe := by
  obtain ⟨tl,leftComplete⟩ := finite_history_stabilizes left history complete
  obtain ⟨tr,rightComplete⟩ := finite_history_stabilizes right history complete
  refine ⟨max tl tr,fun n m hn hm => ?_⟩
  have leftUnique := (reachable_wellFormed (behavior_reachable left.behavior n)).accepted_unique
  have rightUnique := (reachable_wellFormed (behavior_reachable right.behavior m)).accepted_unique
  have leftConsistent : ∀ a ∈ (left.run n).accepted, ∀ b ∈ (left.run n).accepted, a.addr = b.addr → a = b :=
    fun a ma b mb same => leftUnique.eq_of_addr ma mb same
  have rightConsistent : ∀ a ∈ (right.run m).accepted, ∀ b ∈ (right.run m).accepted, a.addr = b.addr → a = b :=
    fun a ma b mb same => rightUnique.eq_of_addr ma mb same
  have rankedA := StateAuthoredOutputReplay.replica_ranked left admission causal n
  have rankedB := StateAuthoredOutputReplay.replica_ranked right admission causal m
  obtain ⟨first,compiledA⟩ := prepared_output_exists environment entries prepared installed _ rankedA leftConsistent
  obtain ⟨second,compiledB⟩ := prepared_output_exists environment entries prepared installed _ rankedB rightConsistent
  have same : SetEq (left.run n).accepted (right.run m).accepted := fun act =>
    (leftComplete n (by omega) act).trans (rightComplete m (by omega) act).symm
  exact ⟨first,second,compiledA,compiledB,authored_observations_setEq environment entries rankedA rankedB
    leftConsistent rightConsistent same first second compiledA compiledB⟩

/-- A conflict-free vector has no terminal fault member. -/
def NoFault {V : Type} (values : List (String × StateReaderValues.Result V)) : Prop :=
  ∀ name e, (name,.fault e) ∉ values

/-- Extract each complete data observation, retaining reached/frozen/context
status and metadata rather than collapsing to a scalar snapshot. -/
def dataVector {V : Type} (values : List (String × StateReaderValues.Result V)) : List (String × Data V) :=
  values.filterMap (fun (name,result) => match result with | .data value => some (name,value) | .fault _ => none)

/-- In the no-top case, extracting data loses no observation or field name. -/
theorem data_vector_complete {V : Type} (values : List (String × StateReaderValues.Result V)) (clear : NoFault values) :
    (dataVector values).map (fun (name,value) => (name,Observation.data value)) = values := by
  induction values with
  | nil => rfl
  | cons binding rest ih =>
    obtain ⟨name,result⟩ := binding
    have restClear : NoFault rest := fun name e member => clear name e (List.mem_cons_of_mem _ member)
    cases result with
    | fault e => exact False.elim (clear name e (by simp))
    | data value =>
      change (name,Observation.data value) :: (dataVector rest).map (fun (name,value) => (name,Observation.data value)) = _
      rw [ih restClear]

/-- Conditional SEC is the no-top specialization of complete emitted-output
convergence, with a shared full data vector and no discarded fault members. -/
theorem conflict_free_output_SEC {adm : Admission} {auth : Act → Prop} {H : ValidHistory adm}
    (left right : Replica adm auth H) (admission : PredecessorAdmission adm H.contains)
    (causal : StateContextReplay.CausalDependencies H) (environment : StateAuthoredBindings.Environment)
    (entries : List StateAuthoredBindings.Entry) (prepared : StateAuthoredBindings.Prepared)
    (installed : StateAuthoredBindings.prepareStatic environment entries = some prepared)
    (history : List Act) (complete : ∀ act, H.contains act ↔ act ∈ history)
    (clear : ∀ n observation, compileAuthored environment entries (left.run n).accepted = some observation → NoFault observation.observe) :
    ∃ time, ∀ n m, time ≤ n → time ≤ m → ∃ (first second : CompiledObservation) (values : List (String × Data StateInstalledLegacy.Value)),
      compileAuthored environment entries (left.run n).accepted = some first ∧
      compileAuthored environment entries (right.run m).accepted = some second ∧
      first.observe = values.map (fun (name,value) => (name,Observation.data value)) ∧
      second.observe = values.map (fun (name,value) => (name,Observation.data value)) := by
  obtain ⟨time,converges⟩ := finite_history_output_convergence left right admission causal environment entries prepared installed history complete
  refine ⟨time,fun n m hn hm => ?_⟩
  obtain ⟨first,second,compiledA,compiledB,equal⟩ := converges n m hn hm
  have exactData := data_vector_complete first.observe (clear n first compiledA)
  exact ⟨first,second,dataVector first.observe,compiledA,compiledB,exactData.symm,equal.symm.trans exactData.symm⟩

end CBCL.StateOutputConvergence
