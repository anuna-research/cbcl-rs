import LeanCbcl.StateInstalledLowering

namespace CBCL.StateInstalledLoweringTests
open State StateLift StateLVar StateObservation StateObservationPlan StateInstalledCompiler
open StateInstalledLattice StateInstalledLowering StateRuleRefinement

def quiet : StateInstalledLattice.Field (WithTop Bool) :=
  ⟨WithTop Bool,inferInstance,inferInstance,(fun _ => .of false),id,id,some,by intros; rfl⟩

def active : StateInstalledLattice.Field (WithTop Bool) :=
  {quiet with contribution := fun _ => .of true}

def activeQuery : Query active := ⟨[.of true],by decide⟩

def vote : Act := ⟨1,"vote","@alice",[],[],[]⟩

theorem empty_query_rejected : (prepareQuery quiet []).isSome = false := by decide

theorem duplicate_query_rejected : (prepareQuery quiet [.of true,.of true]).isSome = false := by decide

theorem conflict_top_query_rejected : (prepareQuery quiet [.top]).isSome = false := by decide

theorem compatible_alternatives_rejected : (prepareQuery quiet [.of false,.of true]).isSome = false := by decide

/-- Successful lattice reads retain the reached tag through element rendering. -/
theorem native_lattice_read_reached : nativeLiftThreshold activeQuery.spec active.renderElement
    (.data (.snapshot (.of false))) [vote] = .data (.reached (.of true)) := by
  simp [nativeLiftThreshold,activeQuery,Query.spec,active,quiet,thresholdError,thresholdRead,
    sourceError,unionError,lift_cons,lift_nil,WithTop.join,Below,rawHistory_eq,StateLift.bot_join,StateLift.join_bot,StateLift.join_idem,
    WithTop.instBoundedJoinSemilattice]

/-- A supersede freeze cannot be installed on a threshold source. -/
theorem supersede_threshold_source_rejected : compile
    (Clause.mk [.field "flag" (.lattice quiet),.threshold "ready" "flag" [.of true]]
      [("flag",⟨"close",fun _ => true,false⟩)]) = none := by
  simp [compile,ValidMetadata,stableDeclarations,stableSource,Declaration.name,List.lookup]

/-- The fault policy remains a valid freeze for a threshold source. -/
theorem fault_threshold_source_accepted_metadata : ValidMetadata
    (Clause.mk [.field "flag" (.lattice quiet),.threshold "ready" "flag" [.of true]]
      [("flag",⟨"close",fun _ => true,true⟩)]) := by
  simp [ValidMetadata,stableDeclarations,stableSource,Declaration.name,List.lookup]

end CBCL.StateInstalledLoweringTests
