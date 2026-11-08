import LeanCbcl.StateNativeEventSum

/-! Event sums in actual authored compiled observations. Bound and shape-policy
admission, source provenance, emitted occurrence and freeze metadata are derived.
Nonnegative accepted amounts remain an explicit admission boundary. -/
set_option autoImplicit false
namespace CBCL.StateAuthoredEventSum
open State StateLift StateLVar StateObservation StateObservationPlan StateInstalledCompiler
open StateInstalledLegacy StateInstalledLowering StateAuthoredBindings StateOutputCompiler
open StateAuthoredDataProvenance StateAuthoredDataOutputs StateAuthoredDataPreservation

/-- Successful sum-query compilation derives its bound and mandatory shape policy. -/
theorem admitted_sum (environment : Environment) (domains : List StateInstalledDomains.Domain)
    (verb field : String) (bound : Int) (query : Query Value)
    (compiled : compileQuery [.element (.sum bound)] ((Head.events verb field).definition environment domains) = some query) :
    (-(2^63) ≤ bound ∧ bound < 2^63) ∧ mandatoryNonnegative environment.shapes verb field = true := by
  simp [compileQuery,Head.definition,Head.expression,Head.rule,primitive,queryPolicy,readCheck,StateInstalledLegacy.allowed] at compiled
  simpa using compiled.1

/-- Authored event sums reaches the complete actual compiled vector
from a prior native witness, or exposes the observed source's named fault. -/
theorem program_stability (environment : Environment) (entries : List Entry) (prepared : Prepared)
    (accepted : prepareStatic environment entries = some prepared) (name outputName verb field : String) (bound : Int)
    (present : (name,StateAuthoredBindings.Rule.legacy (.events verb field)) ∈ rawFields entries)
    (threshold : Entry.threshold outputName name [.element (.sum bound)] ∈ entries)
    (B : List Act) (nonnegative : ∀ act ∈ B, act.verb = verb → 0 ≤ amount field act) (ranked : StateExecutableFreeze.Ranked B)
    (consistent : ∀ a ∈ B, ∀ b ∈ B, a.addr = b.addr → a = b) :
    ∃ program, compileAuthored environment entries B = some program ∧
      ∀ A : List Act, NodupAddr A → (∀ act ∈ A, act ∈ B) →
        bound ≤ sumField field (StateDomainSupportLocality.selected prepared.domains [verb] A) →
        (outputName,.data (.reached (.element (.sum bound)))) ∈ program.observe ∨ ∃ evidence, (outputName,.fault evidence) ∈ program.observe := by
  obtain ⟨declaration,query,program,compiled,queryCompiled,member,history,metadata⟩ := authored_emitted (.events verb field) environment entries prepared
    accepted name outputName present [.element (.sum bound)] threshold B ranked consistent
  have admitted := admitted_sum environment prepared.domains verb field bound query queryCompiled
  refine ⟨program,compiled,?_⟩
  intro A unique growth reached
  obtain ⟨code,codeCompiled,result⟩ := StateNativeEventSum.sum_success_or_fault environment prepared.domains verb field bound admitted.1 admitted.2
    A B unique growth nonnegative reached name outputName declaration (StateScopePool.normalize_ranked B ranked) consistent
  have same : code = query := Option.some.inj (codeCompiled.symm.trans queryCompiled)
  subst code
  rcases result with success | ⟨evidence,fault⟩
  · exact Or.inl (dispatch_member (.events verb field) environment prepared.domains B declaration name outputName query program
      member history metadata _ success)
  · exact Or.inr ⟨evidence,dispatch_member (.events verb field) environment prepared.domains B declaration name outputName query program
      member history metadata _ fault⟩

/-- A named sum success in an actual compiled vector recovers its
full-history native witness, without supplying native membership or admission. -/
theorem native_success (environment : Environment) (entries : List Entry) (prepared : Prepared)
    (accepted : prepareStatic environment entries = some prepared) (name outputName verb field : String) (bound : Int)
    (present : (name,StateAuthoredBindings.Rule.legacy (.events verb field)) ∈ rawFields entries)
    (threshold : Entry.threshold outputName name [.element (.sum bound)] ∈ entries)
    (A : List Act) (nonnegative : ∀ act ∈ A, act.verb = verb → 0 ≤ amount field act) (ranked : StateExecutableFreeze.Ranked A)
    (consistent : ∀ a ∈ A, ∀ b ∈ A, a.addr = b.addr → a = b)
    (program : CompiledObservation) (compiled : compileAuthored environment entries A = some program)
    (reached : (outputName,.data (.reached (.element (.sum bound)))) ∈ program.observe) :
    bound ≤ sumField field (StateDomainSupportLocality.selected prepared.domains [verb] (StateScopePool.normalize A)) := by
  obtain ⟨declaration,query,queryCompiled,observed⟩ := authored_reached (.events verb field) environment entries prepared accepted name outputName
    present [.element (.sum bound)] threshold A ranked consistent program compiled _ reached
  have admitted := admitted_sum environment prepared.domains verb field bound query queryCompiled
  obtain ⟨code,codeCompiled,run⟩ := StateNativeEventSum.compiled_sum environment prepared.domains verb field bound admitted.1 admitted.2
  have same : code = query := Option.some.inj (codeCompiled.symm.trans queryCompiled)
  subst code
  have result := congrArg Prod.snd observed
  let raw := StateThresholdDispatch.referenceScope A program.program.freezes name
  let source := sourceValue A (StateNativeDataFreeze.decorate prepared.domains [verb] A declaration
    ((Head.events verb field).bare environment prepared.domains))
  change query.run raw source = .data (.reached (.element (.sum bound))) at result
  have rawUnique := StateNativeEventSum.raw_unique A program.program.freezes name consistent
  cases dataResult : source with
  | fault evidence => simp only [dataResult,StateNativeDataFreeze.query_fault] at result; contradiction
  | data payload =>
    rw [dataResult,run raw rawUnique] at result
    have success : bound ≤ sumField field (StateDomainSupportLocality.selected prepared.domains [verb] raw) := by
      apply Classical.byContradiction
      intro failure
      simp [failure] at result
    have inside : ∀ act ∈ raw, act ∈ StateScopePool.normalize A := fun act member =>
      (StateScopePool.normalize_setEq A act).mpr (raw_inside A program.program.freezes name act member)
    have positive : ∀ act ∈ StateDomainSupportLocality.selected prepared.domains [verb] (StateScopePool.normalize A), 0 ≤ amount field act := by
      intro act member
      obtain ⟨eligible,verbMatch⟩ := List.mem_filter.mp member
      exact nonnegative act ((StateScopePool.normalize_setEq A act).mp (List.mem_filter.mp eligible).1) (by simpa using verbMatch)
    exact Int.le_trans success (StateNativeEventSum.sum_grows prepared.domains verb field raw (StateScopePool.normalize A) rawUnique inside positive)

/-- Event sums is preserved between actual successive compiled
observations of the same prepared dialect, for every fault-freeze root outcome. -/
theorem successive_compiled (environment : Environment) (entries : List Entry) (prepared : Prepared)
    (accepted : prepareStatic environment entries = some prepared) (name outputName verb field : String) (bound : Int)
    (present : (name,StateAuthoredBindings.Rule.legacy (.events verb field)) ∈ rawFields entries)
    (threshold : Entry.threshold outputName name [.element (.sum bound)] ∈ entries)
    (A B : List Act) (nonnegative : ∀ act ∈ B, act.verb = verb → 0 ≤ amount field act) (growth : ∀ act ∈ A, act ∈ B)
    (rankedA : StateExecutableFreeze.Ranked A) (rankedB : StateExecutableFreeze.Ranked B)
    (consistentA : ∀ a ∈ A, ∀ b ∈ A, a.addr = b.addr → a = b)
    (consistentB : ∀ a ∈ B, ∀ b ∈ B, a.addr = b.addr → a = b)
    (earlier later : CompiledObservation) (compiledA : compileAuthored environment entries A = some earlier)
    (compiledB : compileAuthored environment entries B = some later)
    (reached : (outputName,.data (.reached (.element (.sum bound)))) ∈ earlier.observe) :
    (outputName,.data (.reached (.element (.sum bound)))) ∈ later.observe ∨ ∃ evidence, (outputName,.fault evidence) ∈ later.observe := by
  have native := native_success environment entries prepared accepted name outputName verb field bound present threshold A (fun act member => nonnegative act (growth act member)) rankedA consistentA
    earlier compiledA reached
  obtain ⟨program,compiled,stable⟩ := program_stability environment entries prepared accepted name outputName verb field bound present threshold B nonnegative rankedB consistentB
  have same : program = later := Option.some.inj (compiled.symm.trans compiledB)
  simpa only [same] using stable (StateScopePool.normalize A) (StateScopePool.normalize_unique A consistentA)
    (fun act member => growth act ((StateScopePool.normalize_setEq A act).mp member)) native

end CBCL.StateAuthoredEventSum
