import LeanCbcl.StateEventMapTotal

/-! Sum query compilation uses the actual source-owned policy. Numeric growth
requires nonnegative accepted amounts; installation metadata alone is not proof
that accepted writers satisfy their shapes. -/
set_option autoImplicit false
namespace CBCL.StateNativeEventSum
open State StateLift StateLVar StateObservation StateObservationPlan StateInstalledCompiler
open StateInstalledLegacy StateInstalledDomains StateDomainSupportLocality StateOutputCompiler
open StateEventMapKernel

/-- Domain-aware numeric totals grow when every selected later contribution is
nonnegative. Distinct old addresses prevent repeated delivery from adding weight. -/
theorem sum_grows (domains : List Domain) (verb field : String) (A B : List Act)
    (unique : NodupAddr A) (growth : ∀ act ∈ A, act ∈ B)
    (nonnegative : ∀ act ∈ selected domains [verb] B, 0 ≤ amount field act) :
    sumField field (selected domains [verb] A) ≤ sumField field (selected domains [verb] B) := by
  have oldUnique := (unique.filter (fun act => domains.all (fun domain => eligible domain A act))).filter
    (fun act => [verb].contains act.verb)
  have subset := selected_grows domains [verb] growth
  obtain ⟨chosen,perm,sub⟩ := List.subperm_of_subset oldUnique.nodup subset
  have same : sumField field chosen = sumField field (selected domains [verb] A) :=
    perm.foldl_eq' (fun _ _ _ _ z => by simp only [Int.add_right_comm]) 0
  rw [← same]
  exact nonnegative_sum_sublist field sub nonnegative

/-- Actual emitted sum code reads the raw kernel carrier independently of the
source's displayed payload. Signed bound and writer-shape policy are checked. -/
theorem compiled_sum (environment : StateAuthoredBindings.Environment) (domains : List Domain) (verb field : String)
    (bound : Int) (bounded : -(2^63) ≤ bound ∧ bound < 2^63)
    (shaped : mandatoryNonnegative environment.shapes verb field = true) :
    ∃ code, compileQuery [.element (.sum bound)]
      (StateAuthoredBindings.primitive environment domains (.mapped (plan verb field)) (.events verb field)) = some code ∧
      ∀ (A : List Act), NodupAddr A → ∀ payload : Data Value, code.run A (.data payload) =
        if bound ≤ sumField field (selected domains [verb] A) then .data (.reached (.element (.sum bound))) else .data .pending := by
  let term := StateInstalledDomains.term environment.context domains (.mapped (plan verb field)) (StateAuthoredBindings.resourceVerbs environment)
  let test := fun query state => readTest query (term.project state)
  refine ⟨.raw [.element (.sum bound)] test term.state,?_,?_⟩
  · have bounded' : -9223372036854775808 ≤ bound ∧ bound < 9223372036854775808 := by simpa using bounded
    simp [compileQuery,StateAuthoredBindings.primitive,queryPolicy,readCheck,StateInstalledLegacy.allowed,bounded',shaped,term,test]
  · intro A unique payload
    have native : test (.element (.sum bound)) (rawHistory A) = decide (bound ≤ sumField field (selected domains [verb] A)) :=
      StateEventMapTotal.native_sum environment.context domains verb field bound A unique
    simp only [Query.run,term,StateInstalledDomains.term,id_eq,nativeRawThreshold,List.find?_cons,native]
    by_cases reached : bound ≤ sumField field (selected domains [verb] A) <;> simp [reached]

/-- The semantic raw dispatch scope is unique after normalization, including
no-freeze, absent-root and exact-cut outcomes. -/
theorem raw_unique (B : List Act) (freezes : List (String × FreezeSpec)) (name : String)
    (consistent : ∀ a ∈ B, ∀ b ∈ B, a.addr = b.addr → a = b) :
    NodupAddr (StateThresholdDispatch.referenceScope B freezes name) := by
  have unique := StateScopePool.normalize_unique B consistent
  unfold StateThresholdDispatch.referenceScope
  split
  · exact unique
  · split
    · exact unique
    · exact unique.filter _

/-- Earlier native sum success persists through every fault-freeze outcome,
provided accepted later writers actually have nonnegative amounts. This premise
is deliberately distinct from the source installation's shape metadata. -/
theorem sum_success_or_fault (environment : StateAuthoredBindings.Environment) (domains : List Domain)
    (verb field : String) (bound : Int) (bounded : -(2^63) ≤ bound ∧ bound < 2^63)
    (shaped : mandatoryNonnegative environment.shapes verb field = true) (A B : List Act)
    (unique : NodupAddr A) (growth : ∀ act ∈ A, act ∈ B)
    (nonnegative : ∀ act ∈ B, act.verb = verb → 0 ≤ amount field act)
    (reached : bound ≤ sumField field (selected domains [verb] A))
    (sourceName outputName : String) (declaration : Option String)
    (ranked : StateExecutableFreeze.Ranked (StateScopePool.normalize B))
    (consistent : ∀ a ∈ B, ∀ b ∈ B, a.addr = b.addr → a = b) :
    let bare := sourcePlan (StateInstalledTerm.source (StateInstalledDomains.term environment.context domains
      (.mapped (plan verb field)) (StateAuthoredBindings.resourceVerbs environment)))
    ∃ code, compileQuery [.element (.sum bound)]
      (StateAuthoredBindings.primitive environment domains (.mapped (plan verb field)) (.events verb field)) = some code ∧
      let output := (Output.threshold outputName sourceName code
        (StateNativeDataFreeze.decorate domains [verb] (StateScopePool.normalize B) declaration bare)).observe B
          (StateNativeDataFreeze.metadata domains [verb] (StateScopePool.normalize B) sourceName declaration)
      output = (outputName,.data (.reached (.element (.sum bound)))) ∨ ∃ evidence, output = (outputName,.fault evidence) := by
  intro bare
  obtain ⟨code,compiled,run⟩ := compiled_sum environment domains verb field bound bounded shaped
  refine ⟨code,compiled,?_⟩
  cases fault : errors (fun act => act ∈ StateScopePool.normalize B)
      (path (StateNativeDataFreeze.decorate domains [verb] (StateScopePool.normalize B) declaration bare)) (StateScopePool.normalize B) with
  | some evidence =>
    right; refine ⟨evidence,?_⟩
    simp only [Output.observe,sourceValue,observe,fault,StateNativeDataFreeze.query_fault]
  | none =>
    left
    have inside : ∀ act ∈ A, act ∈ StateScopePool.normalize B := fun act member =>
      (StateScopePool.normalize_setEq B act).mpr (growth act member)
    have positive : ∀ act ∈ selected domains [verb] (StateScopePool.normalize B), 0 ≤ amount field act := by
      intro act member
      obtain ⟨eligible,verbMatch⟩ := List.mem_filter.mp member
      exact nonnegative act ((StateScopePool.normalize_setEq B act).mp (List.mem_filter.mp eligible).1)
        (by simpa using verbMatch)
    have later := Int.le_trans reached (sum_grows domains verb field A (StateScopePool.normalize B) unique inside positive)
    let raw := StateThresholdDispatch.referenceScope B
      (StateNativeDataFreeze.metadata domains [verb] (StateScopePool.normalize B) sourceName declaration) sourceName
    have rawReached : bound ≤ sumField field (selected domains [verb] raw) := by
      rw [StateNativeDataFreeze.selected_scope domains [verb] B sourceName declaration bare ranked fault]
      exact later
    simp only [Output.observe,sourceValue,observe,fault]
    exact congrArg (outputName, ·) ((run raw (raw_unique B _ sourceName consistent) _).trans
      (by simp only [rawReached,if_true]))

end CBCL.StateNativeEventSum
