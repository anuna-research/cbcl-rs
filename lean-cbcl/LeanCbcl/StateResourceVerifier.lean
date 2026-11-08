import LeanCbcl.StateResourcePreflight

/-! Complete typed native verifier/certificate equivalence. Input contains the
installed immutable configuration, accepted identity map and native physical
representation bounds. Preflight is executable validation, not a caller-supplied
resource/fault classifier. Wire/signature/selected-metadata extraction is the
separate admission boundary documented in CheckpointEvidence. -/
namespace CBCL.StateResourceVerifier
open State CheckpointEvidence StateResource StateResourceNative StateResourceStructure StateResourceCycle StateResourceDependency
open StateResourcePreflight StateResourceAggregate StateResourceWorklist

structure Input where
  config : ResourceConfig
  facts : Facts
  unique : (facts.map Fact.id).Nodup
  sliceBound : facts.length ≤ 2^63 - 1
  installed : unsupportedCheck config = false → NativeConfiguration config ∧ (config.initialVerb :: operationNames config).Nodup
  accountSlice : ∀ node ∈ facts, ((accounts node.data.selected.initialAllocations).map Prod.fst).length ≤ 2^63 - 1

inductive Preparation (c : ResourceConfig) (F : Facts) where
  | fault (certificate : Cause c F)
  | pending (noCertificate : ¬Cause c F)
  | checked (prepared : Prepared c F)

def prepare (input : Input) : Preparation input.config input.facts :=
  let c := input.config
  let F := input.facts
  if rejected : unsupportedCheck c = true then .fault (.unsupported ((unsupportedCheck_iff c).mp rejected)) else
  have supported : unsupportedCheck c = false := check_false _ rejected
  match openers : initialNodes c F with
  | [] => .pending (by
      apply no_opener_no_cause c F supported
      intro node member selected
      have inside := (initial_member c F node).mpr ⟨member,selected⟩
      rw [openers] at inside
      contradiction)
  | op :: [] =>
    have accepted : op ∈ F ∧ initial c op := (initial_member c F op).mp (by rw [openers]; simp)
    have uniqueOpener : ∀ node ∈ F, initial c node → node = op := by
      intro node member selected
      have inside := (initial_member c F node).mpr ⟨member,selected⟩
      rw [openers] at inside
      exact List.mem_singleton.mp inside
    match predecessors : op.data.selected.predecessors with
    | [] => .fault (.openerArity accepted.1 accepted.2 (by simp [predecessors]))
    | address :: [] =>
      match rootFound : StateResourceGraph.lookup F address with
      | none => .pending (missing_root_no_cause c F op address input.unique supported uniqueOpener predecessors rootFound)
      | some root =>
        have rootAccepted : root ∈ F := List.mem_of_find?_eq_some rootFound
        have identity : root.id = address := by simpa using List.find?_some rootFound
        have link : rootOf op root := by simpa [rootOf,identity] using predecessors
        if initialization : initializationCheck c op root = true then
          if operations : (nodes c F).all (operationCheck c op root) = true then
            if forks : forkCheck (nodes c F) = true then
              if foreign : foreignCheck c op F (nodes c F) = true then
                if structural : StateResourceKahn.nativeKahn (StateResourceCycle.parents (nodes c F)) (nodes c F) = [] then
                  .checked ⟨op,root,accepted.1,rootAccepted,accepted.2,link,uniqueOpener,supported,initialization,operations,forks,foreign,structural⟩
                else .fault (native_cycle_rejection_cause c F op root accepted.1 rootAccepted accepted.2 link (by
                  have nonempty : (StateResourceKahn.nativeKahn (StateResourceCycle.parents (nodes c F)) (nodes c F)).isEmpty = false := by
                    cases remaining : StateResourceKahn.nativeKahn (StateResourceCycle.parents (nodes c F)) (nodes c F) with
                    | nil => exact False.elim (structural remaining)
                    | cons _ _ => rfl
                  exact nonempty))
              else .fault (foreign_rejection_cause c op root F (nodes c F) input.unique accepted.1 rootAccepted accepted.2 link
                (fun _ member => (List.mem_filter.mp member).1)
                (fun node member => (operationVerbCheck_iff c node).mp (List.mem_filter.mp member).2) (check_false _ foreign))
            else .fault (fork_rejection_cause c F (nodes c F) op root accepted.1 rootAccepted accepted.2 link
              (fun _ member => (List.mem_filter.mp member).1)
              (fun node member => (operationVerbCheck_iff c node).mp (List.mem_filter.mp member).2) (check_false _ forks))
          else .fault (by
            obtain ⟨node,member,bad⟩ := rejected_item (nodes c F) (operationCheck c op root) (check_false _ operations)
            exact operation_rejection_certificate c F op root node accepted.1 rootAccepted (List.mem_filter.mp member).1 accepted.2 link
              ((operationVerbCheck_iff c node).mp (List.mem_filter.mp member).2) bad)
        else .fault (initialization_rejection_certificate c F op root accepted.1 rootAccepted accepted.2 link (check_false _ initialization))
    | first :: second :: rest => .fault (.openerArity accepted.1 accepted.2 (by simp [predecessors]))
  | first :: second :: rest => .fault (by
      have acceptedFirst : first ∈ F ∧ initial c first := (initial_member c F first).mp (by rw [openers]; simp)
      have acceptedSecond : second ∈ F ∧ initial c second := (initial_member c F second).mp (by rw [openers]; simp)
      have unique : ((initialNodes c F).map Fact.id).Nodup := input.unique.sublist (List.Sublist.map Fact.id List.filter_sublist)
      rw [openers] at unique
      have different : first.id ≠ second.id := by
        intro equal
        have absent := (List.nodup_cons.mp unique).1
        exact absent (by simp [equal])
      exact .openers acceptedFirst.1 acceptedSecond.1 acceptedFirst.2 acceptedSecond.2 different)

def observe (input : Input) : StateResourceValidated.Read :=
  match prepare input with
  | .fault _ => .fault
  | .pending _ => .pending
  | .checked prepared =>
    let distinct := (List.nodup_cons.mp (input.installed prepared.supported).2).1
    StateResourceValidated.observe (prepared.environment input.unique distinct input.sliceBound)

/-- Top-level complete native typed classifier iff a concrete accepted resource
certificate checks. The preflight, actual faulting worklist and every final
aggregate rejection are composed, with no delegated fault/persistence oracle. -/
theorem native_verifier_certificate_iff (input : Input) :
    StateResourceValidated.isFault (observe input) = true ↔ Cause input.config input.facts := by
  cases prepared : prepare input with
  | fault certificate =>
    constructor
    · intro _; exact certificate
    · intro _; simp [observe,prepared,StateResourceValidated.isFault]
  | pending noCertificate => simp [observe,prepared,StateResourceValidated.isFault,noCertificate]
  | checked verified =>
    have profile := input.installed verified.supported
    have distinct := (List.nodup_cons.mp profile.2).1
    simpa [observe,prepared] using prepared_native_certificate_iff verified input.unique distinct input.sliceBound
      profile.1 (input.accountSlice verified.opener verified.openerAccepted)


theorem cause_mono (c : ResourceConfig) {A B : Facts} (inside : Included A B) (cause : Cause c A) : Cause c B := by
  cases cause with
  | unsupported bad => exact .unsupported bad
  | openers ha hb ia ib different => exact .openers (inside _ ha) (inside _ hb) ia ib different
  | openerArity member selected bad => exact .openerArity (inside _ member) selected bad
  | initialization ho hr selected parent bad => exact .initialization (inside _ ho) (inside _ hr) selected parent bad
  | malformed ho hr ha selected parent op bad => exact .malformed (inside _ ho) (inside _ hr) (inside _ ha) selected parent op bad
  | fork ho hr selected parent ha hb oa ob owner previous different =>
    exact .fork (inside _ ho) (inside _ hr) selected parent (inside _ ha) (inside _ hb) oa ob owner previous different
  | foreign ho hr parent ha hb selected op edge bad =>
    exact .foreign (inside _ ho) (inside _ hr) parent (inside _ ha) (inside _ hb) selected op edge bad
  | cycle ho hr selected parent coneInside ops ha hb edge back =>
    exact .cycle (inside _ ho) (inside _ hr) selected parent (fun node member => inside node (coneInside node member)) ops ha hb edge back
  | budget ho hr selected parent initial coneInside exactCone ops bad =>
    exact .budget (inside _ ho) (inside _ hr) selected parent initial (fun node member => inside node (coneInside node member)) exactCone ops bad

/-- The existential finite-support certificate grammar is equivalent to
checking the complete accepted typed fact projection. -/
theorem fault_iff_complete_cause (c : ResourceConfig) (decode : Act → ResourceData) (A : List Act) :
    Fault c decode A ↔ Cause c (project decode A) := by
  constructor
  · rintro ⟨support,inside,cause⟩
    apply cause_mono c (A := project decode support) (B := project decode A) ?_ cause
    intro fact member
    obtain ⟨act,ha,rfl⟩ := List.mem_map.mp member
    exact List.mem_map.mpr ⟨act,inside act ha,rfl⟩
  · intro cause
    exact ⟨A,(fun _ member => member),cause⟩

def factsEvidence (c : ResourceConfig) (F : Facts) : Lattice.Set Nat :=
  fun address => unsupportedCheck c = false ∧ ∃ node ∈ F, node.id = address ∧
    (relevant c node ∨ ∃ parent ∈ F, relevant c parent ∧ cited parent address)

theorem supported_iff (c : ResourceConfig) :
    unsupportedCheck c = false ↔ ¬(c.ownership = .collective ∨ ∃ policy, c.certification = .quorum policy) := by
  rw [← unsupportedCheck_iff]
  cases unsupportedCheck c <;> simp

theorem evidence_projection (c : ResourceConfig) (decode : Act → ResourceData) (A : List Act) :
    factsEvidence c (project decode A) = evidence c decode A := by
  funext address
  apply propext
  constructor
  · rintro ⟨supported,node,member,addressEq,relevantNode | ⟨parent,parentMember,parentRelevant,link⟩⟩
    · obtain ⟨act,ha,rfl⟩ := List.mem_map.mp member
      exact ⟨(supported_iff c).mp supported,act,ha,addressEq,Or.inl relevantNode⟩
    · obtain ⟨act,ha,rfl⟩ := List.mem_map.mp member
      obtain ⟨parentAct,hp,rfl⟩ := List.mem_map.mp parentMember
      exact ⟨(supported_iff c).mp supported,act,ha,addressEq,Or.inr ⟨parentAct,hp,parentRelevant,link⟩⟩
  · rintro ⟨supported,act,member,addressEq,relevantNode | ⟨parent,parentMember,parentRelevant,link⟩⟩
    · exact ⟨(supported_iff c).mpr supported,⟨act.addr,decode act⟩,List.mem_map.mpr ⟨act,member,rfl⟩,addressEq,Or.inl relevantNode⟩
    · exact ⟨(supported_iff c).mpr supported,⟨act.addr,decode act⟩,List.mem_map.mpr ⟨act,member,rfl⟩,addressEq,
        Or.inr ⟨⟨parent.addr,decode parent⟩,List.mem_map.mpr ⟨parent,parentMember,rfl⟩,parentRelevant,link⟩⟩

def nativeFaultRead (input : Input) : Option (Lattice.Set Nat) :=
  if StateResourceValidated.isFault (observe input) then some (factsEvidence input.config input.facts) else none

/-- Native verifier plus contextual evidence wrapper equals the concrete LVar
certificate read, including the exact returned evidence set. This is a proved
refinement of the executable typed verifier, not an extensionality port. -/
theorem native_certificate_read_refinement (input : Input) (decode : Act → ResourceData) (A : List Act)
    (projection : input.facts = project decode A) : nativeFaultRead input = faultRead input.config decode A := by
  classical
  have classification : StateResourceValidated.isFault (observe input) = true ↔ Fault input.config decode A := by
    rw [native_verifier_certificate_iff,projection]
    exact (fault_iff_complete_cause input.config decode A).symm
  unfold nativeFaultRead faultRead
  simp only [classification,projection,evidence_projection]

/-- The native verifier inherits fault-witness persistence from the completed
certificate equivalence. No native persistence premise is supplied. -/
theorem native_fault_persists (left right : Input) (decode : Act → ResourceData) (A B : List Act)
    (sameConfig : right.config = left.config) (leftProjection : left.facts = project decode A)
    (rightProjection : right.facts = project decode B) (growth : Included A B) (evidence : Lattice.Set Nat)
    (fault : nativeFaultRead left = some evidence) :
    ∃ enlarged, nativeFaultRead right = some enlarged ∧ ∀ address ∈ evidence, address ∈ enlarged := by
  rw [native_certificate_read_refinement left decode A leftProjection] at fault
  rw [native_certificate_read_refinement right decode B rightProjection,sameConfig]
  exact faultRead_persists left.config decode growth fault

end CBCL.StateResourceVerifier
