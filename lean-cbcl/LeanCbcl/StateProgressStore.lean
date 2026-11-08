import LeanCbcl.StateOutputCompiler

/-! Retained-history causal store reconstruction for single-verb progress.
Only immutable per-act evidence decoding is a parameter. Store extension is
proved from accepted growth, not supplied by a whole-history callback. -/
set_option autoImplicit false
namespace CBCL.StateProgressStore
open State StateLift StateLVar StateInstalledLegacy

/-- Reconstruct address lookup from the same retained accepted-act carrier used
by the kernel. Canonicalization makes the function extensional for all histories. -/
noncomputable def store (decode : Act → Repeat.Evidence) (A : List Act) : Repeat.Store :=
  fun address => ((history (rawHistory A)).find? (fun act => act.addr == address)).map decode

/-- Every stored evidence item comes from an actual retained act at that address. -/
theorem origin (decode : Act → Repeat.Evidence) (A : List Act) (address : Nat) (evidence : Repeat.Evidence)
    (found : store decode A address = some evidence) :
    ∃ act, act ∈ A ∧ act.addr = address ∧ decode act = evidence := by
  unfold store at found
  cases selected : (history (rawHistory A)).find? (fun act => act.addr == address) with
  | none => simp [selected] at found
  | some act =>
    have member := List.mem_of_find?_eq_some selected
    have addressEq : act.addr = address := by simpa using List.find?_some selected
    exact ⟨act,(history_setEq A act).mp member,addressEq,by simpa [selected] using found⟩

/-- Content consistency identifies the selected stored act with every delivered
copy of that address, independently of the canonical representative's order. -/
theorem lookup (decode : Act → Repeat.Evidence) (A : List Act)
    (consistent : ∀ a ∈ A, ∀ b ∈ A, a.addr = b.addr → a = b)
    (act : Act) (member : act ∈ A) : store decode A act.addr = some (decode act) := by
  have present := (history_setEq A act).mpr member
  unfold store
  cases selected : (history (rawHistory A)).find? (fun other => other.addr == act.addr) with
  | none =>
    have absent := List.find?_eq_none.mp selected act present
    exact False.elim (absent (by simp))
  | some other =>
    have inside := (history_setEq A other).mp (List.mem_of_find?_eq_some selected)
    have addressEq : other.addr = act.addr := by simpa using List.find?_some selected
    have same := consistent other inside act member addressEq
    subst other
    rfl

/-- Reconstruction is exactly equal for equal accepted sets, including repeated
and reordered delivery. No consistency premise is needed for this equality. -/
theorem store_setEq (decode : Act → Repeat.Evidence) (A B : List Act) (same : SetEq A B) :
    store decode A = store decode B := by
  exact congrArg (fun carrier : FinSet Act => fun address =>
    ((history carrier).find? (fun act => act.addr == address)).map decode) (rawHistory_setEq same)

/-- Every old immutable evidence item remains present after consistent accepted
history growth. The caller supplies no store-extension law. -/
theorem store_growth (decode : Act → Repeat.Evidence) (A B : List Act)
    (growth : ∀ act ∈ A, act ∈ B)
    (consistent : ∀ a ∈ B, ∀ b ∈ B, a.addr = b.addr → a = b) :
    Repeat.Extends (store decode A) (store decode B) := by
  intro address evidence found
  obtain ⟨act,member,addressEq,decoded⟩ := origin decode A address evidence found
  rw [← addressEq,lookup decode B consistent act (growth act member),decoded]

/-- Canonical retained lookup agrees with the executable delivery-list lookup
when equal addresses denote the same act. This also exposes a computable oracle. -/
theorem find_agreement (decode : Act → Repeat.Evidence) (A : List Act)
    (consistent : ∀ a ∈ A, ∀ b ∈ A, a.addr = b.addr → a = b) (address : Nat) :
    store decode A address = (A.find? (fun act => act.addr == address)).map decode := by
  cases selected : A.find? (fun act => act.addr == address) with
  | none =>
    cases found : store decode A address with
    | none => rfl
    | some evidence =>
      obtain ⟨act,member,addressEq,_⟩ := origin decode A address evidence found
      have absent := List.find?_eq_none.mp selected act member
      exact False.elim (absent (by simpa using addressEq))
  | some act =>
    have addressEq : act.addr = address := by simpa using List.find?_some selected
    rw [← addressEq,lookup decode A consistent act (List.mem_of_find?_eq_some selected)]
    rfl

/-- The retained-history store has an executable representative under the store
invariant, without adding a final-result premise. -/
theorem executable_store (decode : Act → Repeat.Evidence) (A : List Act)
    (consistent : ∀ a ∈ A, ∀ b ∈ A, a.addr = b.addr → a = b) :
    store decode A = fun address => (A.find? (fun act => act.addr == address)).map decode :=
  funext (find_agreement decode A consistent)

/-- Install actual history-backed reconstruction in an existing immutable kernel
context. Its equality law is derived from retained-history equality. -/
noncomputable def context (base : StateKernelSEC.Context) (decode : Act → Repeat.Evidence) : StateKernelSEC.Context :=
  { base with causal := store decode, causal_ext := store_setEq decode }

/-- Actual domain-aware kernel progress projects the reconstructed causal store;
progress is a raw-history source, independent of application domains. -/
theorem kernel_value (base : StateKernelSEC.Context) (decode : Act → Repeat.Evidence)
    (domains : List StateInstalledDomains.Domain) (verb : String) (A : List Act) :
    StateInstalledDomains.evaluate (context base decode) domains (.progress verb) (rawHistory A) =
      .integer (Int.ofNat (protocolProgress (store decode A) base.thread verb (base.limit verb) A)) := by
  have same := history_setEq A
  have stores := store_setEq decode (history (rawHistory A)) A same
  have value := protocolProgress_setEq (store decode A) base.thread verb (base.limit verb) same
  simp only [StateInstalledDomains.evaluate,StateInstalledDomains.rawExpression,StateKernel.evaluate,
    StateKernelSEC.Context.input,context,stores]
  simp only [ite_true]
  rw [value]

/-- Accepted-history growth advances the concrete reconstructed progress value. -/
theorem progress_grows (decode : Act → Repeat.Evidence) (A B : List Act) (thread : Nat) (verb : String) (limit : Nat)
    (growth : ∀ act ∈ A, act ∈ B)
    (consistent : ∀ a ∈ B, ∀ b ∈ B, a.addr = b.addr → a = b) :
    protocolProgress (store decode A) thread verb limit A ≤ protocolProgress (store decode B) thread verb limit B := by
  apply StateProgress.progress_monotone (store_growth decode A B growth consistent)
  intro address member
  obtain ⟨act,inside,rfl⟩ := List.mem_map.mp member
  exact List.mem_map.mpr ⟨act,growth act inside,rfl⟩

/-- The actual kernel progress threshold tests the reconstructed causal value. -/
theorem kernel_test (base : StateKernelSEC.Context) (decode : Act → Repeat.Evidence)
    (domains : List StateInstalledDomains.Domain) (verb : String) (bound : Nat) (A : List Act) :
    readTest (.element (.progress bound))
      (.kernel (StateInstalledDomains.evaluate (context base decode) domains (.progress verb) (rawHistory A))) =
      decide (bound ≤ protocolProgress (store decode A) base.thread verb (base.limit verb) A) := by
  rw [kernel_value]
  simp [readTest]

/-- Once the concrete raw kernel progress test reaches a bound, consistent
accepted growth preserves that same query's truth. -/
theorem kernel_test_stable (base : StateKernelSEC.Context) (decode : Act → Repeat.Evidence)
    (domains : List StateInstalledDomains.Domain) (verb : String) (bound : Nat) (A B : List Act)
    (growth : ∀ act ∈ A, act ∈ B)
    (consistent : ∀ a ∈ B, ∀ b ∈ B, a.addr = b.addr → a = b)
    (reached : readTest (.element (.progress bound))
      (.kernel (StateInstalledDomains.evaluate (context base decode) domains (.progress verb) (rawHistory A))) = true) :
    readTest (.element (.progress bound))
      (.kernel (StateInstalledDomains.evaluate (context base decode) domains (.progress verb) (rawHistory B))) = true := by
  rw [kernel_test] at reached ⊢
  have before : bound ≤ protocolProgress (store decode A) base.thread verb (base.limit verb) A := of_decide_eq_true reached
  exact decide_eq_true (Nat.le_trans before (progress_grows decode A B base.thread verb (base.limit verb) growth consistent))

/-- The existing progress source compiles to a closure query over its displayed
kernel value, using the concrete reconstructed store. This is not raw dispatch. -/
theorem compiled_query (environment : StateAuthoredBindings.Environment) (decode : Act → Repeat.Evidence)
    (domains : List StateInstalledDomains.Domain) (verb : String) (bound : Nat) (bounded : bound < 2^63) :
    let installed := { environment with context := context environment.context decode }
    ∃ code, StateOutputCompiler.compileQuery [.element (.progress bound)]
      (StateAuthoredBindings.primitive installed domains (.progress verb) (.progress verb)) = some code ∧
      ∀ A : List Act, code.run A (.data (.snapshot (.kernel
        (StateInstalledDomains.evaluate installed.context domains (.progress verb) (rawHistory A))))) =
        if bound ≤ protocolProgress (store decode A) environment.context.thread verb (environment.context.limit verb) A
        then .data (.reached (.element (.progress bound))) else .data .pending := by
  intro installed
  refine ⟨.closure [.element (.progress bound)] readTest,?_,?_⟩
  · have bounded' : bound < 9223372036854775808 := by simpa using bounded
    simp [StateOutputCompiler.compileQuery,StateAuthoredBindings.primitive,queryPolicy,readCheck,allowed,bounded']
  · intro A
    have value := kernel_test environment.context decode domains verb bound A
    simp only [StateOutputCompiler.Query.run,StateReaderValues.unfrozen,StateRuleRefinement.nativeClosureThreshold,
      StateObservationPlan.Data.payload,List.find?_cons]
    dsimp only [installed]
    rw [value]
    by_cases reached : bound ≤ protocolProgress (store decode A) environment.context.thread verb (environment.context.limit verb) A <;> simp [reached]

end CBCL.StateProgressStore
