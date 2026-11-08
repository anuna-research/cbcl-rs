import LeanCbcl.StateInstalledLegacy
import LeanCbcl.StateResourceReadEquivalence

/-! Concrete resource leaf factory. It calls the verified native typed verifier
for snapshot data and the equivalent certificate read for its fault channel.
The factory accepts installed configuration evidence and checks finite native
representation bounds; it receives no resource classifier or display oracle. -/
namespace CBCL.StateInstalledResource
open State StateLift StateLVar StateObservation StateObservationPlan StateInstalledCompiler
open CheckpointEvidence StateResource StateResourceAggregate StateResourcePreflight

/-- The installed configuration and immutable typed metadata used by this source. -/
structure Profile where
  /-- The installed resource configuration. -/
  config : ResourceConfig
  installed : unsupportedCheck config = false → NativeConfiguration config ∧
    (config.initialVerb :: operationNames config).Nodup

/-- Check that the accepted resource account count fits the installed bound. -/
def accountBoundCheck (facts : Facts) : Bool := facts.all (fun node =>
  decide (((accounts node.data.selected.initialAllocations).map Prod.fst).length ≤ 2^63 - 1))

/-- Build a native verifier input after checking representation bounds and unique identities. -/
def makeInput (profile : Profile) (facts : Facts) : Option StateResourceVerifier.Input :=
  if unique : (facts.map Fact.id).Nodup then
    if sliceBound : facts.length ≤ 2^63 - 1 then
      if accountBound : accountBoundCheck facts = true then
        some ⟨profile.config,facts,unique,sliceBound,profile.installed,
          fun node member => of_decide_eq_true ((List.all_eq_true.mp accountBound) node member)⟩
      else none
    else none
  else none

theorem makeInput_complete (profile : Profile) (input : StateResourceVerifier.Input)
    (config : input.config = profile.config) : makeInput profile input.facts = some input := by
  have accounts : accountBoundCheck input.facts = true := by
    apply List.all_eq_true.mpr
    intro node member
    exact decide_eq_true (input.accountSlice node member)
  cases input
  cases config
  simp_all [makeInput]

/-- Read the actual native resource verifier on canonical accepted facts. -/
noncomputable def snapshot (profile : Profile) (decode : Act → ResourceData) (carrier : FinSet Act) : StateInstalledLegacy.Value :=
  let facts := project decode (StateInstalledLegacy.history carrier)
  match makeInput profile facts with
  | none => .nativeResource .pending
  | some input => .nativeResource (StateResourceVerifier.observe input)

/-- Factor the native resource snapshot through the retained accepted-act set. -/
noncomputable def term (profile : Profile) (decode : Act → ResourceData) : StateInstalledTerm.Term StateInstalledLegacy.Value := {
  Carrier := FinSet Act
  state := id
  project := snapshot profile decode
  guards := [.resource profile.config decode]
  algebra := inferInstance
  state_bottom := rfl
  state_merge := fun _ _ => rfl }

/-- Guard the native resource snapshot with independently checkable resource faults. -/
noncomputable def source (profile : Profile) (decode : Act → ResourceData) : Source StateInstalledLegacy.Value :=
  StateInstalledTerm.source (term profile decode)

theorem source_unfold (profile : Profile) (decode : Act → ResourceData) :
    source profile decode = .resource profile.config decode (.snapshot (snapshot profile decode)) := rfl

/-- Every physically representable recognized accepted projection uses the
actual verifier for the factory's native resource snapshot. -/
theorem snapshot_native_refinement (profile : Profile) (decode : Act → ResourceData)
    (carrier : FinSet Act) (input : StateResourceVerifier.Input) (config : input.config = profile.config)
    (projection : input.facts = project decode (StateInstalledLegacy.history carrier)) :
    snapshot profile decode carrier = .nativeResource (StateResourceVerifier.observe input) := by
  simp only [snapshot,← projection,makeInput_complete profile input config]

/-- The concrete factory's fault wrapper uses native evidence and presence,
with only config/projection identities as premises. -/
theorem source_native_fault_refinement (profile : Profile) (decode : Act → ResourceData)
    (A : List Act) (input : StateResourceVerifier.Input) (config : input.config = profile.config)
    (projection : input.facts = project decode A) :
    sourceRead (source profile decode) A =
      nativeGuard (StateResourceVerifier.nativeFaultRead input)
        (.data (.snapshot (snapshot profile decode (rawHistory A)))) := by
  have bridge := StateInstalledClause.native_resource_source_refinement input decode
    (.snapshot (snapshot profile decode)) A projection
  simpa [source_unfold,config,sourceRead] using bridge

/-- A valid accepted projection supplies all physical bounds for the chosen
duplicate-free representative. No bound or success oracle is assumed for it. -/
theorem canonical_input (profile : Profile) (decode : Act → ResourceData) (A : List Act)
    (input : StateResourceVerifier.Input) (config : input.config = profile.config)
    (projection : input.facts = project decode A) :
    ∃ canonical, makeInput profile (project decode (StateInstalledLegacy.history (rawHistory A))) = some canonical ∧
      canonical.config = input.config ∧ canonical.facts.Perm input.facts := by
  have unique : NodupAddr A := by
    simpa [projection,project,List.map_map,NodupAddr,Function.comp_def] using input.unique
  have historyPerm := perm_of_setEq (StateInstalledLegacy.history_unique unique) unique (StateInstalledLegacy.history_setEq A)
  have factsPerm : (project decode (StateInstalledLegacy.history (rawHistory A))).Perm input.facts := by
    rw [projection]
    exact historyPerm.map (fun act => Fact.mk act.addr (decode act))
  let canonical : StateResourceVerifier.Input := {
    config := profile.config
    facts := project decode (StateInstalledLegacy.history (rawHistory A))
    unique := (factsPerm.map Fact.id).symm.nodup input.unique
    sliceBound := by rw [factsPerm.length_eq]; exact input.sliceBound
    installed := profile.installed
    accountSlice := fun node member => input.accountSlice node (factsPerm.mem_iff.mp member) }
  exact ⟨canonical,makeInput_complete profile canonical rfl,config.symm,factsPerm⟩

/-- Complete successful-value/status parity with the actual accepted history,
including account and headroom functions. This closes the factory's snapshot
bridge, beyond its separately proved fault-wrapper equivalence. -/
theorem snapshot_actual_history_refinement (profile : Profile) (decode : Act → ResourceData)
    (A : List Act) (input : StateResourceVerifier.Input) (config : input.config = profile.config)
    (projection : input.facts = project decode A) :
    snapshot profile decode (rawHistory A) = .nativeResource (StateResourceVerifier.observe input) := by
  obtain ⟨canonical,built,sameConfig,sameFacts⟩ := canonical_input profile decode A input config projection
  simp only [snapshot,built]
  rw [StateResourceReadEquivalence.native_observe_perm canonical input sameConfig sameFacts]

/-- The installed resource source is the actual native typed read, with native
fault evidence promoted into the common terminal error channel. -/
theorem concrete_resource_read_refinement (profile : Profile) (decode : Act → ResourceData)
    (A : List Act) (input : StateResourceVerifier.Input) (config : input.config = profile.config)
    (projection : input.facts = project decode A) :
    sourceRead (source profile decode) A =
      match StateResourceVerifier.nativeFaultRead input with
      | some evidence => .fault evidence
      | none => .data (.snapshot (.nativeResource (StateResourceVerifier.observe input))) := by
  rw [source_native_fault_refinement profile decode A input config projection,
    snapshot_actual_history_refinement profile decode A input config projection]
  cases StateResourceVerifier.nativeFaultRead input <;> rfl

end CBCL.StateInstalledResource
