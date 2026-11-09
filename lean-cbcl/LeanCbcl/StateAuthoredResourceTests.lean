import LeanCbcl.StateCausalRank
import LeanCbcl.StateAuthoredResource
import LeanCbcl.StateAuthoredBindingsTests
import LeanCbcl.StateResourceVerifierTests

/-! Concrete typed resource outputs from complete authored programs. Native
configuration, verifier input bounds and accepted projection are constructed;
wire/signature/metadata extraction remains a separate boundary. -/
namespace CBCL.StateAuthoredResourceTests
open State StateLift StateLVar StateObservation StateObservationPlan StateInstalledCompiler
open StateInstalledLegacy StateInstalledLowering StateAuthoredBindings StateOutputCompiler
open CheckpointEvidence StateResource StateResourcePreflight StateResourceAggregate StateResourceTests

/-- The existing concrete native fixture satisfies installed configuration laws. -/
theorem installed_config : NativeConfiguration config ∧
    (config.initialVerb :: operationNames config).Nodup := by
  exact ⟨(configurationCheck_iff config).mp (by decide),by decide⟩

/-- Installed concrete native resource profile. -/
def profile : StateInstalledResource.Profile := ⟨config,fun _ => installed_config⟩

/-- Immutable typed metadata for the three concrete resource identities. -/
def decode (act : Act) : ResourceData :=
  if act.addr == 1 then root.data else if act.addr == 2 then opener.data else burn.data

/-- Accepted-state view of the root identity. -/
def rootAct : Act := ⟨1,"begin","@treasury",[],[],[]⟩
/-- Accepted-state view of the initializer identity. -/
def openerAct : Act := ⟨2,"open","@treasury",[1],[],[]⟩
/-- Accepted-state view of an unfunded decrement. -/
def burnAct : Act := ⟨3,"burn","@alice",[2],[],[]⟩

/-- Concrete bounded-counter factory, with no caller-supplied result classifier. -/
def resource : Resource := ⟨profile,decode⟩
/-- Recognized environment contains the actual installed resource. -/
def environment (context : StateKernelSEC.Context) : Environment :=
  {StateAuthoredBindingsTests.environment context with resources := [("coins",resource)]}
/-- A resource field without a threshold or freezer. -/
def entries : List Entry := [.field "coins" (.legacy (.boundedCounter "coins"))]
/-- Exact static preparation result. -/
noncomputable def prepared (context : StateKernelSEC.Context) : Prepared :=
  ⟨[.field "coins" (StateAuthoredResource.definition (environment context) [] "coins" resource)],[],[]⟩

/-- Actual preparation accepts the concrete resource field. -/
theorem preparation (context : StateKernelSEC.Context) :
    prepareStatic (environment context) entries = some (prepared context) := by rfl

/-- Resource snapshots cannot supply successful threshold alternatives. -/
theorem threshold_rejected (context : StateKernelSEC.Context) :
    prepareStatic (environment context) (entries ++ [.threshold "enough" "coins" [.element (.count 1)]]) = none := by rfl

/-- Physically bounded concrete verifier inputs used by the emitted output. -/
def input (facts : Facts) (unique : (facts.map Fact.id).Nodup := by decide)
    (sliceBound : facts.length ≤ 2^63 - 1 := by decide)
    (accountSlice : ∀ node ∈ facts, ((accounts node.data.selected.initialAllocations).map Prod.fst).length ≤ 2^63 - 1 := by decide) : StateResourceVerifier.Input :=
  ⟨config,facts,unique,sliceBound,(fun _ => installed_config),accountSlice⟩

/-- Root and initializer produce the actual finalized native value. -/
theorem ready_value : (match StateResourceVerifier.observe (input [root,opener]) with
    | .ready snapshot => some snapshot.value | _ => none) = some 1000 := by decide

/-- The unfunded decrement is classified by the actual native verifier. -/
theorem burn_fault : StateResourceValidated.isFault (StateResourceVerifier.observe (input [root,opener,burn])) = true := by decide

/-- Complete actual authored compilation emits the ready native resource read,
whose value is independently computed above. -/
theorem ready_program (context : StateKernelSEC.Context) : ∃ program,
    compileAuthored (environment context) entries [rootAct,openerAct] = some program ∧
      ("coins",.data (.snapshot (.nativeResource (StateResourceVerifier.observe (input [root,opener]))))) ∈ program.observe := by
  have unique : NodupAddr [rootAct,openerAct] := by change ([1,2] : List Nat).Nodup; decide
  obtain ⟨program,compiled,member⟩ := StateAuthoredResource.authored_native_read (environment context) entries (prepared context)
    (preparation context) "coins" "coins" resource rfl (by simp [entries,rawFields]) rfl rfl [rootAct,openerAct]
    (StateCausalRank.causalCheck_sound _ (by decide)) (fun _ ha _ hb eq => unique.eq_of_addr ha hb eq)
    (input [root,opener]) rfl rfl
  have healthy : StateResourceVerifier.nativeFaultRead (input [root,opener]) = none := by rfl
  refine ⟨program,compiled,?_⟩
  simpa [healthy,nativeGuard,StateRuleRefinement.sourceError,unionError] using member

/-- Complete actual authored compilation promotes the real native resource
fault into the common field error channel with its exact witness set. -/
theorem fault_program (context : StateKernelSEC.Context) : ∃ program,
    compileAuthored (environment context) entries [rootAct,openerAct,burnAct] = some program ∧
      ("coins",.fault (StateResourceVerifier.factsEvidence config [root,opener,burn])) ∈ program.observe := by
  have unique : NodupAddr [rootAct,openerAct,burnAct] := by change ([1,2,3] : List Nat).Nodup; decide
  obtain ⟨program,compiled,member⟩ := StateAuthoredResource.authored_native_read (environment context) entries (prepared context)
    (preparation context) "coins" "coins" resource rfl (by simp [entries,rawFields]) rfl rfl [rootAct,openerAct,burnAct]
    (StateCausalRank.causalCheck_sound _ (by decide)) (fun _ ha _ hb eq => unique.eq_of_addr ha hb eq)
    (input [root,opener,burn]) rfl rfl
  refine ⟨program,compiled,?_⟩
  simpa [StateResourceVerifier.nativeFaultRead,burn_fault,nativeGuard,StateRuleRefinement.sourceError,unionError] using member

end CBCL.StateAuthoredResourceTests
