import LeanCbcl.StateFiniteReplay
import LeanCbcl.StateFiniteFreezePolicyTests

/-! Replay context must retain concurrent initializer support. Native protocol
admission does not require the initializer to dominate each domain writer. -/
set_option autoImplicit false
namespace CBCL.StateFiniteReplayTests
open StateWitnessReplay State StateLift StateInstalledFinite StateFiniteReplay StateInstalledDomains
open StateDomainSupportLocalityTests

/-- The writer remains eligible while its initializer is causally concurrent. -/
def concurrentWriter : Act := {writer with preds := [root.addr]}

/-- Both domains select this writer without an initializer ancestry edge. -/
theorem concurrent_writer_selected : concurrentWriter ∈ selected StateFiniteFreezePolicyTests.field
    [root,opener,concurrentWriter] := by decide

/-- A concurrent initializer is explicitly reported as replay context. -/
theorem concurrent_initializer_reported : opener.addr ∈ domainEvidence StateFiniteFreezePolicyTests.field
    [root,opener,concurrentWriter] := by
  refine ⟨⟨"mark","target",.initial "open" "options"⟩,?_,rfl,opener,by simp,rfl,rfl⟩
  simp [StateFiniteFreezePolicyTests.field,domains]

/-- The sealed roster root is also part of the replay certificate. -/
theorem roster_root_reported : root.addr ∈ domainEvidence StateFiniteFreezePolicyTests.field
    [root,opener,concurrentWriter] := by
  refine ⟨⟨"mark","target",.roster profile "reviewer"⟩,?_,rfl,root,by simp,rfl,rfl⟩
  simp [StateFiniteFreezePolicyTests.field,domains]

/-- Finite guard replay now applies without causal-domain dominance or an
extra support checker that could exclude admitted histories. -/
theorem concurrent_finite_replay : Replays (StateInstalledFinite.errorSpec StateFiniteFreezePolicyTests.field).read
    [root,opener,concurrentWriter] [concurrentWriter,root,opener] :=
  finite_error_replays StateFiniteFreezePolicyTests.field _ _

end CBCL.StateFiniteReplayTests
