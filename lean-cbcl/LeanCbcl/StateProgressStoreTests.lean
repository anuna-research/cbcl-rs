import LeanCbcl.StateProgressStore
import LeanCbcl.StateAuthoredEventSumTests

/-! Concrete typed single-verb repeat evidence; decoding here is a fixture
convention, not a proof of native thread/cause parsing or protocol admission. -/
namespace CBCL.StateProgressStoreTests
open State StateLVar StateInstalledLegacy StateProgressStore

/-- Fixture evidence uses empty predecessors as its explicit begin marker. -/
def decode (act : Act) : Repeat.Evidence :=
  ⟨if act.signer == "@foreign" then 8 else 7,act.verb,match act.preds with
    | [] => .begin | [parent] => .previous parent | _ => .absent⟩
/-- First repeat act. -/
def first : Act := ⟨11,"tick","@a",[],[],[]⟩
/-- Second repeat position. -/
def second : Act := ⟨23,"tick","@a",[11],[],[]⟩
/-- A competing act occupies the same second position. -/
def competing : Act := ⟨37,"tick","@b",[11],[],[]⟩
/-- Third repeat position. -/
def third : Act := ⟨41,"tick","@a",[23],[],[]⟩
/-- Foreign-thread evidence must not advance the pinned thread. -/
def foreign : Act := ⟨55,"tick","@foreign",[],[],[]⟩
/-- Earlier accepted chain. -/
def before : List Act := [first,second]
/-- Reverse, competing and duplicate delivery plus foreign-thread evidence. -/
def after : List Act := [foreign,third,competing,second,first,third]

/-- The typed world has distinct addresses. -/
theorem world_unique : NodupAddr [first,second,competing,third,foreign] := by
  change ([11,23,37,41,55] : List Nat).Nodup
  decide

/-- Later duplicate delivery still has consistent address contents. -/
theorem after_consistent : ∀ a ∈ after, ∀ b ∈ after, a.addr = b.addr → a = b := by
  have inside : ∀ act ∈ after, act ∈ [first,second,competing,third,foreign] := by
    intro act member
    simp only [after,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  exact fun _ ha _ hb eq => world_unique.eq_of_addr (inside _ ha) (inside _ hb) eq

/-- Earlier contents are consistent too. -/
theorem before_consistent : ∀ a ∈ before, ∀ b ∈ before, a.addr = b.addr → a = b := by
  have unique : NodupAddr before := by change ([11,23] : List Nat).Nodup; decide
  exact fun _ ha _ hb eq => unique.eq_of_addr ha hb eq

/-- The earlier concrete reconstructed store resolves position two. -/
theorem before_progress : protocolProgress (store decode before) 7 "tick" 3 before = 2 := by
  rw [executable_store decode before before_consistent]
  decide

/-- Competing and duplicate identities do not inflate progress; foreign thread
metadata contributes nothing to the pinned thread's causal positions. -/
theorem after_progress : protocolProgress (store decode after) 7 "tick" 3 after = 3 := by
  rw [executable_store decode after after_consistent]
  decide

/-- Missing causal evidence yields zero rather than a claimed sender position. -/
theorem missing_ancestor : protocolProgress (store decode [third]) 7 "tick" 3 [third] = 0 := by
  have unique : NodupAddr [third] := by change ([41] : List Nat).Nodup; decide
  rw [executable_store decode [third] (fun _ ha _ hb eq => unique.eq_of_addr ha hb eq)]
  decide

/-- The actual kernel expression projects the reconstructed later value. -/
theorem kernel_three (base : StateKernelSEC.Context) :
    StateInstalledDomains.evaluate (context {base with thread := 7,limit := fun _ => 3} decode) [] (.progress "tick") (rawHistory after) = .integer 3 := by
  rw [kernel_value]
  exact congrArg StateKernel.Observation.integer (congrArg Int.ofNat after_progress)

/-- The actual existing closure query reaches from the computed kernel display. -/
theorem compiled_reaches (base : StateKernelSEC.Context) :
    let environment := StateAuthoredEventSumTests.environment {base with thread := 7,limit := fun _ => 3}
    let installed := {environment with context := context environment.context decode}
    ∃ code, StateOutputCompiler.compileQuery [.element (.progress 2)]
      (StateAuthoredBindings.primitive installed [] (.progress "tick") (.progress "tick")) = some code ∧
      code.run before (.data (.snapshot (.kernel
        (StateInstalledDomains.evaluate installed.context [] (.progress "tick") (rawHistory before))))) =
        .data (.reached (.element (.progress 2))) := by
  intro environment installed
  obtain ⟨code,compiled,run⟩ := compiled_query environment decode [] "tick" 2 (by decide)
  refine ⟨code,compiled,?_⟩
  have result := run before
  have reached : 2 ≤ protocolProgress (store decode before) environment.context.thread "tick" (environment.context.limit "tick") before := by
    change 2 ≤ protocolProgress (store decode before) 7 "tick" 3 before
    rw [before_progress]
    exact Nat.le_refl _
  exact result.trans (if_pos reached)

/-- An actually reached raw kernel test remains reached through the concrete
consistent extension; the earlier success is computed rather than assumed. -/
theorem kernel_preserves (base : StateKernelSEC.Context) :
    readTest (.element (.progress 2)) (.kernel (StateInstalledDomains.evaluate
      (context {base with thread := 7,limit := fun _ => 3} decode) [] (.progress "tick") (rawHistory after))) = true := by
  have growth : ∀ act ∈ before, act ∈ after := by
    intro act member
    simp only [before,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> simp [after]
  apply kernel_test_stable {base with thread := 7,limit := fun _ => 3} decode [] "tick" 2 before after growth after_consistent
  rw [kernel_test]
  change decide (2 ≤ protocolProgress (store decode before) 7 "tick" 3 before) = true
  rw [before_progress]
  rfl

end CBCL.StateProgressStoreTests
