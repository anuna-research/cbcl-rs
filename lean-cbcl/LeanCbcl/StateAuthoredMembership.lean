import LeanCbcl.StateNativeMembership

/-! Set-union membership in actual authored compiled observations. Source,
scalar query admission, emitted occurrence and freeze identities are derived
from preparation and compilation. Earlier success is an actual named output. -/
set_option autoImplicit false
namespace CBCL.StateAuthoredMembership
open State StateLift StateLVar StateObservation StateObservationPlan StateInstalledCompiler
open StateInstalledLegacy StateInstalledLowering StateAuthoredBindings StateOutputCompiler
open StateAuthoredDataProvenance StateAuthoredDataOutputs StateAuthoredDataPreservation

/-- Structured member queries cannot bypass source-owned scalar admission. -/
theorem admitted_member (environment : Environment) (domains : List StateInstalledDomains.Domain)
    (verb field : String) (value : Val) (query : Query Value)
    (compiled : compileQuery [.element (.member value)] ((Head.setUnion verb field).definition environment domains) = some query) :
    scalar value = true := by
  cases valid : scalar value with
  | true => rfl
  | false => simp [compileQuery,Head.definition,Head.expression,Head.rule,primitive,queryPolicy,readCheck,StateInstalledLegacy.allowed,valid] at compiled

/-- Authored set-union membership reaches the complete actual compiled vector
from a prior native witness, or exposes the observed source's named fault. -/
theorem program_stability (environment : Environment) (entries : List Entry) (prepared : Prepared)
    (accepted : prepareStatic environment entries = some prepared) (name outputName verb field : String) (value : Val)
    (present : (name,StateAuthoredBindings.Rule.legacy (.setUnion verb field)) ∈ rawFields entries)
    (threshold : Entry.threshold outputName name [.element (.member value)] ∈ entries)
    (B : List Act) (ranked : StateExecutableFreeze.Ranked B)
    (consistent : ∀ a ∈ B, ∀ b ∈ B, a.addr = b.addr → a = b) :
    ∃ program, compileAuthored environment entries B = some program ∧
      ∀ A : List Act, (∀ act ∈ A, act ∈ B) →
        has field (StateDomainSupportLocality.selected prepared.domains [verb] A) value = true →
        (outputName,.data (.reached (.element (.member value)))) ∈ program.observe ∨ ∃ evidence, (outputName,.fault evidence) ∈ program.observe := by
  obtain ⟨declaration,query,program,compiled,queryCompiled,member,history,metadata⟩ := authored_emitted (.setUnion verb field) environment entries prepared
    accepted name outputName present [.element (.member value)] threshold B ranked consistent
  have admitted := admitted_member environment prepared.domains verb field value query queryCompiled
  refine ⟨program,compiled,?_⟩
  intro A growth reached
  obtain ⟨code,codeCompiled,result⟩ := StateNativeMembership.member_success_or_fault environment prepared.domains verb field value admitted
    A B growth reached name outputName declaration (StateScopePool.normalize_ranked B ranked)
  have same : code = query := Option.some.inj (codeCompiled.symm.trans queryCompiled)
  subst code
  rcases result with success | ⟨evidence,fault⟩
  · exact Or.inl (dispatch_member (.setUnion verb field) environment prepared.domains B declaration name outputName query program
      member history metadata _ success)
  · exact Or.inr ⟨evidence,dispatch_member (.setUnion verb field) environment prepared.domains B declaration name outputName query program
      member history metadata _ fault⟩

/-- A named membership success in an actual compiled vector recovers its
full-history native witness, without supplying native membership or admission. -/
theorem native_success (environment : Environment) (entries : List Entry) (prepared : Prepared)
    (accepted : prepareStatic environment entries = some prepared) (name outputName verb field : String) (value : Val)
    (present : (name,StateAuthoredBindings.Rule.legacy (.setUnion verb field)) ∈ rawFields entries)
    (threshold : Entry.threshold outputName name [.element (.member value)] ∈ entries)
    (A : List Act) (ranked : StateExecutableFreeze.Ranked A)
    (consistent : ∀ a ∈ A, ∀ b ∈ A, a.addr = b.addr → a = b)
    (program : CompiledObservation) (compiled : compileAuthored environment entries A = some program)
    (reached : (outputName,.data (.reached (.element (.member value)))) ∈ program.observe) :
    has field (StateDomainSupportLocality.selected prepared.domains [verb] A) value = true := by
  obtain ⟨declaration,query,queryCompiled,observed⟩ := authored_reached (.setUnion verb field) environment entries prepared accepted name outputName
    present [.element (.member value)] threshold A ranked consistent program compiled _ reached
  obtain ⟨code,codeCompiled,run⟩ := StateNativeMembership.compiled_member environment prepared.domains verb field value
    (admitted_member environment prepared.domains verb field value query queryCompiled)
  have same : code = query := Option.some.inj (codeCompiled.symm.trans queryCompiled)
  subst code
  have result := congrArg Prod.snd observed
  let raw := StateThresholdDispatch.referenceScope A program.program.freezes name
  let source := sourceValue A (StateNativeDataFreeze.decorate prepared.domains [verb] A declaration
    ((Head.setUnion verb field).bare environment prepared.domains))
  change query.run raw source = .data (.reached (.element (.member value))) at result
  cases dataResult : source with
  | fault evidence => simp only [dataResult,StateNativeDataFreeze.query_fault] at result; contradiction
  | data payload =>
    rw [dataResult,run] at result
    have member : has field (StateDomainSupportLocality.selected prepared.domains [verb] raw) value = true := by
      cases matching : has field (StateDomainSupportLocality.selected prepared.domains [verb] raw) value with
      | true => rfl
      | false => simp [matching] at result
    exact StateNativeMembership.member_grows prepared.domains verb field value (raw_inside A program.program.freezes name) member

/-- Set-union membership is preserved between actual successive compiled
observations of the same prepared dialect, for every fault-freeze root outcome. -/
theorem successive_compiled (environment : Environment) (entries : List Entry) (prepared : Prepared)
    (accepted : prepareStatic environment entries = some prepared) (name outputName verb field : String) (value : Val)
    (present : (name,StateAuthoredBindings.Rule.legacy (.setUnion verb field)) ∈ rawFields entries)
    (threshold : Entry.threshold outputName name [.element (.member value)] ∈ entries)
    (A B : List Act) (growth : ∀ act ∈ A, act ∈ B)
    (rankedA : StateExecutableFreeze.Ranked A) (rankedB : StateExecutableFreeze.Ranked B)
    (consistentA : ∀ a ∈ A, ∀ b ∈ A, a.addr = b.addr → a = b)
    (consistentB : ∀ a ∈ B, ∀ b ∈ B, a.addr = b.addr → a = b)
    (earlier later : CompiledObservation) (compiledA : compileAuthored environment entries A = some earlier)
    (compiledB : compileAuthored environment entries B = some later)
    (reached : (outputName,.data (.reached (.element (.member value)))) ∈ earlier.observe) :
    (outputName,.data (.reached (.element (.member value)))) ∈ later.observe ∨ ∃ evidence, (outputName,.fault evidence) ∈ later.observe := by
  have native := native_success environment entries prepared accepted name outputName verb field value present threshold A rankedA consistentA
    earlier compiledA reached
  obtain ⟨program,compiled,stable⟩ := program_stability environment entries prepared accepted name outputName verb field value present threshold B rankedB consistentB
  have same : program = later := Option.some.inj (compiled.symm.trans compiledB)
  simpa only [same] using stable A growth native

end CBCL.StateAuthoredMembership
