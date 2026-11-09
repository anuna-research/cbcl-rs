import LeanCbcl.StateAuthoredEventMembership
import LeanCbcl.StateAuthoredDataPreservationTests

/-! Event membership shares mixed domains with count/existence while
retaining its own scalar admission and source-owned raw query. -/
namespace CBCL.StateAuthoredEventMembershipTests
open State StateLift StateLVar StateObservation StateObservationPlan StateInstalledCompiler
open StateInstalledLegacy StateInstalledLowering StateAuthoredBindings StateOutputCompiler

/-- Extend an actual authored mixed-domain fixture with a event source. -/
def entries (value : Val) (fault : Bool) : List Entry := StateAuthoredDataPreservationTests.entries true ++ [
  .field "log" (.legacy (.events "mark" "target")),
  .threshold "logged" "log" [.element (.member value)],
  .freeze "log" "close" fault]

/-- Actual installation admits a scalar member query. -/
theorem installation_succeeds (context : StateKernelSEC.Context) :
    (prepareStatic (StateAuthoredSourceProvenanceTests.environment context) (entries (.str "@a") true)).isSome = true := by rfl

/-- Structured members fail the actual source policy. -/
theorem structured_member_rejected (context : StateKernelSEC.Context) :
    prepareStatic (StateAuthoredSourceProvenanceTests.environment context) (entries (.list []) true) = none := by rfl

/-- Revisable supersede sources cannot supply this stable member threshold. -/
theorem supersede_rejected (context : StateKernelSEC.Context) :
    prepareStatic (StateAuthoredSourceProvenanceTests.environment context) (entries (.str "@a") false) = none := by rfl

/-- A second typed writer has the same payload but a different address/signer.
This is a low-level event identity fixture, not a protocol-admission trace. -/
def other : Act := { StateDomainSupportLocalityTests.writer with addr := 7, signer := "@b" }

/-- Reverse and duplicate delivery preserves both event records. -/
def eventHistory : List Act := [other,StateDomainSupportLocalityTests.writer,other]

/-- Address identity is established independently of clock ordering. -/
theorem event_consistent : ∀ a ∈ eventHistory, ∀ b ∈ eventHistory, a.addr = b.addr → a = b := by
  let world := [other,StateDomainSupportLocalityTests.writer]
  have unique : NodupAddr world := by unfold NodupAddr world; decide
  have inside : ∀ act ∈ eventHistory, act ∈ world := by
    intro act member
    rcases List.mem_cons.mp member with rfl | member
    · exact List.mem_cons_self
    · rcases List.mem_cons.mp member with rfl | member
      · exact List.mem_cons_of_mem _ List.mem_cons_self
      · have same : act = other := by simpa using member
        subst act
        exact List.mem_cons_self
  exact fun a ma b mb same => unique.eq_of_addr (inside a ma) (inside b mb) same

/-- Equal values are separate events when their addresses differ. -/
theorem two_address_entries (context : StateKernelSEC.Context) :
    (StateKernelQueries.evalMap context.clock context.rank eventHistory (StateEventMapKernel.plan "mark" "target")).keys.length = 2 := by rfl

/-- The first record retains its own signer and payload. -/
theorem first_event_retained (context : StateKernelSEC.Context) :
    (StateKernelQueries.evalMap context.clock context.rank eventHistory (StateEventMapKernel.plan "mark" "target")).read
      (.int StateDomainSupportLocalityTests.writer.addr) = .event "@a" (.str "@a") := by
  exact StateEventMapKernel.read_event context.clock context.rank eventHistory "mark" "target" event_consistent
    StateDomainSupportLocalityTests.writer (by simp [eventHistory]) rfl (.str "@a") rfl

/-- The second record retains its different signer despite equal payloads. -/
theorem other_event_retained (context : StateKernelSEC.Context) :
    (StateKernelQueries.evalMap context.clock context.rank eventHistory (StateEventMapKernel.plan "mark" "target")).read
      (.int other.addr) = .event "@b" (.str "@a") := by
  exact StateEventMapKernel.read_event context.clock context.rank eventHistory "mark" "target" event_consistent
    other (by simp [eventHistory]) rfl (.str "@a") rfl

/-- Actual kernel event membership ignores delivery duplicates. -/
theorem duplicate_native_member (context : StateKernelSEC.Context) :
    readTest (.element (.member (.str "@a"))) (.kernel (StateInstalledDomains.evaluate context []
      (.mapped (StateEventMapKernel.plan "mark" "target")) (rawHistory eventHistory))) = true := by
  rw [StateEventMapKernel.native_member context [] "mark" "target" (.str "@a") eventHistory event_consistent]
  rfl

/-- A low-level emitted event query reaches from raw selected state with a pending payload. -/
theorem pending_payload_reaches (context : StateKernelSEC.Context) : ∃ code,
    compileQuery [.element (.member (.str "@a"))]
      ((StateAuthoredDataProvenance.Head.events "mark" "target").definition
        (StateAuthoredSourceProvenanceTests.environment context) []) = some code ∧
      code.run eventHistory (.data .pending) = .data (.reached (.element (.member (.str "@a")))) := by
  obtain ⟨code,compiled,run⟩ := StateNativeEventMembership.compiled_member (StateAuthoredSourceProvenanceTests.environment context)
    [] "mark" "target" (.str "@a") rfl
  refine ⟨code,compiled,?_⟩
  rw [run eventHistory event_consistent]
  rfl

/-- Both actual programs are constructed. The earlier native witness is
computed; preservation itself starts from an earlier named compiled result. -/
theorem constructed_programs_preserve_member (context : StateKernelSEC.Context) :
    ∃ prepared earlier later,
      prepareStatic (StateAuthoredSourceProvenanceTests.environment context) (entries (.str "@a") true) = some prepared ∧
      compileAuthored (StateAuthoredSourceProvenanceTests.environment context) (entries (.str "@a") true)
        StateFiniteOutputStabilityTests.beforeClose = some earlier ∧
      compileAuthored (StateAuthoredSourceProvenanceTests.environment context) (entries (.str "@a") true)
        StateAuthoredFiniteStabilityTests.history = some later ∧
      has "target" (StateDomainSupportLocality.selected prepared.domains ["mark"] StateFiniteOutputStabilityTests.beforeClose) (.str "@a") = true ∧
      (("logged",.data (.reached (.element (.member (.str "@a"))))) ∈ earlier.observe →
        ("logged",.data (.reached (.element (.member (.str "@a"))))) ∈ later.observe ∨ ∃ evidence, ("logged",.fault evidence) ∈ later.observe) := by
  let environment := StateAuthoredSourceProvenanceTests.environment context
  let A := StateFiniteOutputStabilityTests.beforeClose
  let B := StateAuthoredFiniteStabilityTests.history
  have uniqueA : NodupAddr A := by unfold NodupAddr A StateFiniteOutputStabilityTests.beforeClose; decide
  have uniqueB : NodupAddr B := by unfold NodupAddr B StateAuthoredFiniteStabilityTests.history; decide
  have consistentA : ∀ a ∈ A, ∀ b ∈ A, a.addr = b.addr → a = b := fun a ma b mb same => uniqueA.eq_of_addr ma mb same
  have consistentB : ∀ a ∈ B, ∀ b ∈ B, a.addr = b.addr → a = b := fun a ma b mb same => uniqueB.eq_of_addr ma mb same
  have rankedA : StateExecutableFreeze.Ranked A := StateCausalRank.causalCheck_sound _ (by decide)
  have rankedB : StateExecutableFreeze.Ranked B := StateCausalRank.causalCheck_sound _ (by decide)
  have growth : ∀ act ∈ A, act ∈ B := by
    intro act member
    have full : B = A ++ [StateDomainSupportLocalityTests.freezer] := rfl
    rw [full]
    exact List.mem_append_left _ member
  cases installed : prepareStatic environment (entries (.str "@a") true) with
  | none => have accepted := installation_succeeds context; simp [environment,installed] at accepted
  | some prepared =>
    have field : ("log",StateAuthoredBindings.Rule.legacy (.events "mark" "target")) ∈ rawFields (entries (.str "@a") true) := by
      simp [entries,StateAuthoredDataPreservationTests.entries,rawFields]
    have threshold : Entry.threshold "logged" "log" [.element (.member (.str "@a"))] ∈ entries (.str "@a") true := by simp [entries]
    obtain ⟨earlier,compiledA,_⟩ := StateAuthoredEventMembership.program_stability environment (entries (.str "@a") true) prepared installed
      "log" "logged" "mark" "target" (.str "@a") field threshold A rankedA consistentA
    obtain ⟨later,compiledB,_⟩ := StateAuthoredEventMembership.program_stability environment (entries (.str "@a") true) prepared installed
      "log" "logged" "mark" "target" (.str "@a") field threshold B rankedB consistentB
    obtain ⟨_,_,domainResult,_,_,_⟩ := StateAuthoredSourceProvenance.static_trace environment (entries (.str "@a") true) prepared installed
    have domainsBuilt : domains environment (entries (.str "@a") true) = some StateDomainSupportLocalityTests.domains := by rfl
    have domainsEq := Option.some.inj (domainResult.symm.trans domainsBuilt)
    refine ⟨prepared,earlier,later,rfl,compiledA,compiledB,?_,?_⟩
    · rw [domainsEq]
      rfl
    · exact fun reached => StateAuthoredEventMembership.successive_compiled environment (entries (.str "@a") true) prepared installed
        "log" "logged" "mark" "target" (.str "@a") field threshold A B growth rankedA rankedB consistentA consistentB
        earlier later compiledA compiledB reached

end CBCL.StateAuthoredEventMembershipTests
