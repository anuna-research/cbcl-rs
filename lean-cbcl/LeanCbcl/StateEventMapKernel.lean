import LeanCbcl.StateAuthoredMembership

/-! Address-keyed event maps retain each writer's value and signer. Content
consistency, rather than address ordering or assumed map membership, connects
the actual map evaluator to native event membership. Duplicate delivery is safe. -/
set_option autoImplicit false
namespace CBCL.StateEventMapKernel
open State StateLift StateLVar StateKernelSemantics StateKernelQueries StateKernelAggregates
open StateInstalledLegacy StateDomainSupportLocality

/-- The exact event plan emitted by the existing legacy rule compiler. -/
def plan (verb field : String) : MapPlan := ⟨.withField (.verb verb) field,.address,.address,field,true⟩

/-- Every supported event key has an actual source writer and present payload. -/
theorem key_origin (clock : Clock) (rank : SignerRank) (A : List Act) (verb field : String) (key : Val)
    (member : key ∈ (evalMap clock rank A (plan verb field)).keys) :
    ∃ act value, act ∈ A ∧ act.verb = verb ∧ act.get field = some value ∧ key = .int act.addr := by
  have meaning := map_correct clock rank A (plan verb field)
  obtain ⟨act,chosen,keyEq⟩ := meaning.2.1 key |>.mp member
  have selected : (act ∈ A ∧ act.verb = verb) ∧ (act.get field).isSome = true := chosen
  cases data : act.get field with
  | none => simp [data] at selected
  | some value =>
    have same : Val.int act.addr = key := Option.some.inj keyEq
    exact ⟨act,value,selected.1.1,selected.1.2,data,same.symm⟩

/-- A content-address group retains the originating writer's
signer/value pair. No monotonic-clock or winner equality premise is supplied. -/
theorem read_event (clock : Clock) (rank : SignerRank) (A : List Act) (verb field : String)
    (consistent : ∀ a ∈ A, ∀ b ∈ A, a.addr = b.addr → a = b)
    (act : Act) (member : act ∈ A) (verbEq : act.verb = verb) (value : Val) (data : act.get field = some value) :
    (evalMap clock rank A (plan verb field)).read (.int act.addr) = .event act.signer value := by
  have meaning := map_correct clock rank A (plan verb field)
  have selected : Selected (fun act => act ∈ A) (plan verb field).source act := ⟨⟨member,verbEq⟩,by simp [data]⟩
  have keyMember : Val.int act.addr ∈ (evalMap clock rank A (plan verb field)).keys :=
    (meaning.2.1 _).mpr ⟨act,selected,rfl⟩
  obtain ⟨candidate,choice,projected⟩ := meaning.2.2 _ keyMember
  rcases choice with ⟨absent,rfl⟩ | ⟨other,key,chosen,evidence,maximal,rfl⟩
  · exact False.elim (absent ⟨act,⟨0,0,0,act.addr⟩,⟨selected,rfl⟩,rfl⟩)
  · have otherMember : other ∈ A := chosen.1.1.1
    have addressInt : (other.addr : Int) = (act.addr : Int) := by simpa [plan,groupKey] using chosen.2
    have address : other.addr = act.addr := Int.ofNat.inj addressInt
    have same := consistent other otherMember act member address
    subst other
    have equal := (projection_complete field true (some act) _).mp projected
    simpa [project,data] using equal

/-- Event-map membership is exactly field membership of source writers. -/
theorem member_value (clock : Clock) (rank : SignerRank) (A : List Act) (verb field : String) (value : Val)
    (consistent : ∀ a ∈ A, ∀ b ∈ A, a.addr = b.addr → a = b) :
    (evalMap clock rank A (plan verb field)).keys.any
      (fun key => cellScalar ((evalMap clock rank A (plan verb field)).read key) == some value) =
      has field (acts verb A) value := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro reached
    obtain ⟨key,supported,matching⟩ := List.any_eq_true.mp reached
    obtain ⟨act,payload,member,verbEq,data,keyEq⟩ := key_origin clock rank A verb field key supported
    rw [keyEq,read_event clock rank A verb field consistent act member verbEq payload data] at matching
    have same : payload = value := by simpa [cellScalar] using matching
    subst payload
    exact List.any_eq_true.mpr ⟨act,List.mem_filter.mpr ⟨member,by simpa using verbEq⟩,by simp [data]⟩
  · intro reached
    obtain ⟨act,member,matching⟩ := List.any_eq_true.mp reached
    obtain ⟨inside,verbBool⟩ := List.mem_filter.mp member
    have verbEq : act.verb = verb := by simpa using verbBool
    have data : act.get field = some value := by simpa using matching
    have meaning := map_correct clock rank A (plan verb field)
    have selected : Selected (fun act => act ∈ A) (plan verb field).source act := ⟨⟨inside,verbEq⟩,by simp [data]⟩
    have keyMember : Val.int act.addr ∈ (evalMap clock rank A (plan verb field)).keys := (meaning.2.1 _).mpr ⟨act,selected,rfl⟩
    exact List.any_eq_true.mpr ⟨.int act.addr,keyMember,by rw [read_event clock rank A verb field consistent act inside verbEq value data]; simp [cellScalar]⟩

/-- The actual canonical domain-aware kernel event query observes the same
field-membership predicate as the selected raw accepted history. -/
theorem native_member (context : StateKernelSEC.Context) (domains : List StateInstalledDomains.Domain)
    (verb field : String) (value : Val) (A : List Act)
    (consistent : ∀ a ∈ A, ∀ b ∈ A, a.addr = b.addr → a = b) :
    readTest (.element (.member value)) (.kernel (StateInstalledDomains.evaluate context domains (.mapped (plan verb field)) (rawHistory A))) =
      has field (selected domains [verb] A) value := by
  have selectedConsistent : ∀ a ∈ StateInstalledDomains.select domains (history (rawHistory A)),
      ∀ b ∈ StateInstalledDomains.select domains (history (rawHistory A)), a.addr = b.addr → a = b := by
    intro a ma b mb same
    exact consistent a ((history_setEq A a).mp (List.mem_filter.mp ma).1)
      b ((history_setEq A b).mp (List.mem_filter.mp mb).1) same
  have events := member_value context.clock context.rank (StateInstalledDomains.select domains (history (rawHistory A))) verb field value selectedConsistent
  have same := State.has_setEq (StateNativeDataPolicies.selected_setEq domains [verb] (history_setEq A)) field value
  simpa [StateInstalledDomains.evaluate,StateInstalledDomains.rawExpression,StateKernel.evaluate,StateKernelSEC.Context.input,
    StateNativeDataPolicies.admitted_nil,readTest,selected,acts] using events.trans (by simpa [selected,acts] using same)

end CBCL.StateEventMapKernel
