import LeanCbcl.StateAuthoredDataPreservation
import LeanCbcl.StateProgressFreeze

/-! Complete actual authored progress observations. Source/footprint metadata,
query policy and output occurrence are derived from the shared compiler. The
kernel context uses retained-history causal reconstruction with immutable decoding. -/
set_option autoImplicit false
namespace CBCL.StateAuthoredProgress
open State StateLift StateLVar StateObservation StateObservationPlan StateInstalledCompiler
open StateInstalledLegacy StateInstalledLowering StateAuthoredBindings StateOutputCompiler
open StateAuthoredDataProvenance StateAuthoredDataOutputs StateAuthoredDataPreservation StateProgressStore

/-- Install the concrete causal interpretation without changing other immutable
metadata, source factories or query policies. -/
noncomputable def installed (environment : Environment) (decode : Act → Repeat.Evidence) : Environment :=
  {environment with context := StateProgressStore.context environment.context decode}

/-- Actual successful progress query compilation derives bound admission and
its closure strategy, with no separately supplied source-policy identity. -/
theorem admitted_query (environment : Environment) (domains : List StateInstalledDomains.Domain)
    (verb : String) (bound : Nat) (query : Query Value)
    (compiled : compileQuery [.element (.progress bound)] ((Head.progress verb).definition environment domains) = some query) :
    bound < 2^63 ∧ query = .closure [.element (.progress bound)] readTest := by
  simp [compileQuery,Head.definition,Head.expression,Head.rule,primitive,queryPolicy,readCheck,allowed] at compiled
  exact ⟨by simpa using compiled.1,compiled.2.symm⟩

/-- Actual authored output construction composes the progress factory's
reached-or-fault result with its complete emitted vector. -/
theorem program_stability (environment : Environment) (decode : Act → Repeat.Evidence)
    (entries : List Entry) (prepared : Prepared)
    (accepted : prepareStatic (installed environment decode) entries = some prepared) (name outputName verb : String) (bound : Nat)
    (present : (name,StateAuthoredBindings.Rule.legacy (.progress verb)) ∈ rawFields entries)
    (threshold : Entry.threshold outputName name [.element (.progress bound)] ∈ entries)
    (B : List Act) (ranked : StateExecutableFreeze.Ranked B)
    (consistent : ∀ a ∈ B, ∀ b ∈ B, a.addr = b.addr → a = b)
    (coherent : ∀ act, (decode act).verb = act.verb) :
    ∃ program, compileAuthored (installed environment decode) entries B = some program ∧
      ∀ A : List Act, (∀ act ∈ A, act ∈ B) →
        bound ≤ protocolProgress (store decode A) environment.context.thread verb (environment.context.limit verb) A →
        (outputName,.data (.reached (.element (.progress bound)))) ∈ program.observe ∨
          ∃ evidence, (outputName,.fault evidence) ∈ program.observe := by
  obtain ⟨declaration,query,program,compiled,queryCompiled,member,history,metadata⟩ := authored_emitted (.progress verb)
    (installed environment decode) entries prepared accepted name outputName present [.element (.progress bound)] threshold B ranked consistent
  have admitted := (admitted_query (installed environment decode) prepared.domains verb bound query queryCompiled).1
  refine ⟨program,compiled,?_⟩
  intro A growth reached
  obtain ⟨code,codeCompiled,result⟩ := StateProgressFreeze.success_or_fault environment decode prepared.domains verb bound admitted coherent
    A B growth consistent reached name outputName declaration ((Head.progress verb).metadata prepared.domains (StateScopePool.normalize B) name declaration)
  have same : code = query := Option.some.inj (codeCompiled.symm.trans queryCompiled)
  subst code
  rcases result with success | ⟨evidence,fault⟩
  · exact Or.inl (dispatch_member (.progress verb) (installed environment decode) prepared.domains B declaration name outputName query program
      member history metadata _ success)
  · exact Or.inr ⟨evidence,dispatch_member (.progress verb) (installed environment decode) prepared.domains B declaration name outputName query program
      member history metadata _ fault⟩

/-- Invert an actual named reached output, recover its real displayed scope,
and derive full-history progress via the reconstructed store's growth theorem. -/
theorem native_success (environment : Environment) (decode : Act → Repeat.Evidence)
    (entries : List Entry) (prepared : Prepared)
    (accepted : prepareStatic (installed environment decode) entries = some prepared) (name outputName verb : String) (bound : Nat)
    (present : (name,StateAuthoredBindings.Rule.legacy (.progress verb)) ∈ rawFields entries)
    (threshold : Entry.threshold outputName name [.element (.progress bound)] ∈ entries)
    (A : List Act) (ranked : StateExecutableFreeze.Ranked A)
    (consistent : ∀ a ∈ A, ∀ b ∈ A, a.addr = b.addr → a = b)
    (program : CompiledObservation) (compiled : compileAuthored (installed environment decode) entries A = some program)
    (reached : (outputName,.data (.reached (.element (.progress bound)))) ∈ program.observe) :
    bound ≤ protocolProgress (store decode A) environment.context.thread verb (environment.context.limit verb) A := by
  obtain ⟨declaration,query,queryCompiled,observed⟩ := authored_reached (.progress verb) (installed environment decode) entries prepared accepted
    name outputName present [.element (.progress bound)] threshold A ranked consistent program compiled _ reached
  have queryEq := (admitted_query (installed environment decode) prepared.domains verb bound query queryCompiled).2
  subst query
  have result := congrArg Prod.snd observed
  have decoration := head_decorate_setEq (.progress verb) prepared.domains (StateScopePool.normalize_setEq A) declaration
    ((Head.progress verb).bare (installed environment decode) prepared.domains)
  rw [← decoration] at result
  let bare := (Head.progress verb).bare (installed environment decode) prepared.domains
  let source := (Head.progress verb).decorate prepared.domains (StateScopePool.normalize A) declaration bare
  change (Query.closure [.element (.progress bound)] readTest).run (StateThresholdDispatch.referenceScope A program.program.freezes name) (sourceValue A source) = .data (.reached (.element (.progress bound))) at result
  cases fault : errors (fun act => act ∈ StateScopePool.normalize A) (path source) (StateScopePool.normalize A) with
  | some evidence =>
    simp only [sourceValue,observe,fault,Query.run,StateReaderValues.unfrozen,StateRuleRefinement.nativeClosureThreshold] at result
    contradiction
  | none =>
    obtain ⟨scope,subset,_,payload⟩ := StateProgressFreeze.healthy_payload (installed environment decode) prepared.domains
      (StateScopePool.normalize A) verb declaration fault
    simp only [sourceValue,observe,fault] at result
    have native := StateProgressFreeze.payload_success environment.context decode prepared.domains verb bound scope (StateThresholdDispatch.referenceScope A program.program.freezes name) _ payload result
    have inside : ∀ act ∈ scope, act ∈ A := fun act member => (StateScopePool.normalize_setEq A act).mp (subset act member)
    exact Nat.le_trans native (progress_grows decode scope A environment.context.thread verb (environment.context.limit verb) inside consistent)

/-- Actual successive complete observations preserve the same named reached
progress result or report a named fault, for every authored fault-freeze outcome. -/
theorem successive_compiled (environment : Environment) (decode : Act → Repeat.Evidence)
    (entries : List Entry) (prepared : Prepared)
    (accepted : prepareStatic (installed environment decode) entries = some prepared) (name outputName verb : String) (bound : Nat)
    (present : (name,StateAuthoredBindings.Rule.legacy (.progress verb)) ∈ rawFields entries)
    (threshold : Entry.threshold outputName name [.element (.progress bound)] ∈ entries)
    (A B : List Act) (growth : ∀ act ∈ A, act ∈ B)
    (rankedA : StateExecutableFreeze.Ranked A) (rankedB : StateExecutableFreeze.Ranked B)
    (consistentA : ∀ a ∈ A, ∀ b ∈ A, a.addr = b.addr → a = b)
    (consistentB : ∀ a ∈ B, ∀ b ∈ B, a.addr = b.addr → a = b)
    (coherent : ∀ act, (decode act).verb = act.verb)
    (earlier later : CompiledObservation) (compiledA : compileAuthored (installed environment decode) entries A = some earlier)
    (compiledB : compileAuthored (installed environment decode) entries B = some later)
    (reached : (outputName,.data (.reached (.element (.progress bound)))) ∈ earlier.observe) :
    (outputName,.data (.reached (.element (.progress bound)))) ∈ later.observe ∨ ∃ evidence, (outputName,.fault evidence) ∈ later.observe := by
  have native := native_success environment decode entries prepared accepted name outputName verb bound present threshold A rankedA consistentA
    earlier compiledA reached
  obtain ⟨program,compiled,stable⟩ := program_stability environment decode entries prepared accepted name outputName verb bound present threshold B rankedB consistentB coherent
  have same : program = later := Option.some.inj (compiled.symm.trans compiledB)
  simpa only [same] using stable A growth native

end CBCL.StateAuthoredProgress
