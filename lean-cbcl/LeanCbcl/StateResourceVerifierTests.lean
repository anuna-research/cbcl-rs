import LeanCbcl.StateResourceVerifier
import LeanCbcl.StateResourceAggregateTests

namespace CBCL.StateResourceVerifierTests
open State CheckpointEvidence StateResource StateResourceTests StateResourceAggregateTests
open StateResourceVerifier StateResourcePreflight StateResourceAggregate

private theorem installed_config : unsupportedCheck config = false →
    NativeConfiguration config ∧ (config.initialVerb :: operationNames config).Nodup := by
  intro _
  exact ⟨(configurationCheck_iff config).mp (by decide),by decide⟩

private def input (facts : Facts) (unique : (facts.map Fact.id).Nodup := by decide)
    (sliceBound : facts.length ≤ 2^63 - 1 := by decide)
    (accountSlice : ∀ node ∈ facts, ((accounts node.data.selected.initialAllocations).map Prod.fst).length ≤ 2^63 - 1 := by decide) : Input :=
  ⟨config,facts,unique,sliceBound,installed_config,accountSlice⟩

private def isPending : StateResourceValidated.Read → Bool
  | .pending => true
  | _ => false

private def isReady : StateResourceValidated.Read → Bool
  | .ready _ => true
  | _ => false

theorem absent_opener_pending : isPending (observe (input [root])) = true := by decide

theorem absent_root_pending : isPending (observe (input [opener])) = true := by decide

theorem empty_resource_ready : isReady (observe (input [root,opener])) = true := by decide

theorem unfunded_burn_fault : StateResourceValidated.isFault (observe (input [root,opener,burn])) = true := by decide

theorem closed_funding_ready : StateResourceValidated.isFault
    (observe (input [root,opener,fundedBurn,pay])) = false := by decide

end CBCL.StateResourceVerifierTests
