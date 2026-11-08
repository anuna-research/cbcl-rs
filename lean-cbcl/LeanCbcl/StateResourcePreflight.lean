import LeanCbcl.StateResourceValidated

/-! Native preflight cross-reference validation on complete accepted typed
facts. A reference absent from the accepted set remains pending; an accepted
non-resource reference is a foreign-link fault. -/
namespace CBCL.StateResourcePreflight
open State CheckpointEvidence StateResource StateResourceNative StateResourceStructure StateResourceCycle StateResourceDependency

def operationNames (c : ResourceConfig) : List String :=
  [c.increment.verb,c.decrement.verb] ++ (c.transfer.toList.map ResourceOperation.verb) ++
    (c.transferHeadroom.toList.map ResourceOperation.verb)

theorem operation_names (c : ResourceConfig) (node : ResourceFact) :
    operation c node ↔ node.data.selected.verb ∈ operationNames c := by
  simp [operation,operationNames,Option.mem_toList]
  grind

def foreignCheck (c : ResourceConfig) (op : ResourceFact) (F known : Facts) : Bool :=
  known.all fun node => (links node).all fun address =>
    if address = op.id then true else match StateResourceGraph.lookup F address with
    | none => true
    | some parent => operationVerbCheck c parent.data.selected.verb &&
        (if node.data.prev == some address then node.data.signer == parent.data.signer else true)

def NoForeign (c : ResourceConfig) (op : ResourceFact) (F known : Facts) : Prop :=
  ∀ node ∈ known, ∀ parent ∈ F, parent.id ∈ links node → parent.id ≠ op.id →
    operation c parent ∧ (node.data.prev = some parent.id → node.data.signer = parent.data.signer)

theorem foreignCheck_iff (c : ResourceConfig) (op : ResourceFact) (F known : Facts)
    (unique : (F.map Fact.id).Nodup) : foreignCheck c op F known = true ↔ NoForeign c op F known := by
  simp only [foreignCheck,List.all_eq_true]
  constructor
  · intro checked node hn parent hp edge notRoot
    have accepted := checked node hn parent.id edge
    rw [if_neg notRoot,StateResourceGraph.lookup_known F unique parent hp] at accepted
    simp only [Bool.and_eq_true] at accepted
    have recognized := accepted.1
    refine ⟨(operationVerbCheck_iff c parent).mp recognized,?_⟩
    intro previous
    have owner := accepted.2
    simpa [previous] using owner
  · intro safe node hn address edge
    by_cases root : address = op.id
    · simp [root]
    · rw [if_neg root]
      cases found : StateResourceGraph.lookup F address with
      | none => rfl
      | some parent =>
        have member := List.mem_of_find?_eq_some found
        have identity : parent.id = address := by simpa using List.find?_some found
        have relation := safe node hn parent member (by simpa [identity] using edge) (by simpa [identity] using root)
        simp only [Bool.and_eq_true]
        refine ⟨(operationVerbCheck_iff c parent).mpr relation.1,?_⟩
        by_cases previous : node.data.prev = some address
        · have same := relation.2 (by simpa [identity] using previous)
          simp [previous,same]
        · simp [previous]

theorem foreign_rejection_cause (c : ResourceConfig) (op root : ResourceFact) (F known : Facts)
    (unique : (F.map Fact.id).Nodup) (opAccepted : op ∈ F) (rootAccepted : root ∈ F)
    (isOpener : initial c op) (parent : rootOf op root) (inside : Included known F)
    (operations : ∀ node ∈ known, operation c node) (rejected : foreignCheck c op F known = false) : Cause c F := by
  classical
  have invalidReferences : ¬NoForeign c op F known := by
    rw [← foreignCheck_iff c op F known unique]
    simp [rejected]
  simp only [NoForeign,Classical.not_forall,Classical.not_imp] at invalidReferences
  obtain ⟨a,ha,b,hb,edge,notRoot,bad⟩ := invalidReferences
  apply Cause.foreign opAccepted rootAccepted parent (inside a ha) hb isOpener (operations a ha) edge
  refine ⟨notRoot,?_⟩
  by_cases valid : operation c b
  · right
    have noOwner : ¬(a.data.prev = some b.id → a.data.signer = b.data.signer) := fun owner => bad ⟨valid,owner⟩
    exact Classical.not_imp.mp noOwner
  · exact Or.inl valid

/-- The complete foreign-reference check entails the owner-only precondition
used by the verified budget worklist; no separate owner oracle is needed. -/
theorem foreign_implies_previous_check (c : ResourceConfig) (op : ResourceFact) (F known : Facts)
    (unique : (F.map Fact.id).Nodup) (inside : Included known F) (checked : foreignCheck c op F known = true) :
    previousOwnerCheck op.id known = true := by
  apply (previousOwnerCheck_iff op.id known).mpr
  intro node hn parent hp previous notRoot
  have edge : parent.id ∈ links node := by simp [links,previous]
  have relation := ((foreignCheck_iff c op F known unique).mp checked) node hn parent (inside parent hp) edge notRoot
  exact (relation.2 previous).symm


def unsupportedCheck (c : ResourceConfig) : Bool :=
  c.ownership == .collective || match c.certification with
    | .legacy => false
    | .quorum _ => true

theorem unsupportedCheck_iff (c : ResourceConfig) :
    unsupportedCheck c = true ↔ c.ownership = .collective ∨ ∃ policy, c.certification = .quorum policy := by
  cases mode : c.certification <;> simp [unsupportedCheck,mode]

structure Prepared (c : ResourceConfig) (F : Facts) where
  opener : ResourceFact
  root : ResourceFact
  openerAccepted : opener ∈ F
  rootAccepted : root ∈ F
  isOpener : initial c opener
  rootLink : rootOf opener root
  uniqueOpener : ∀ node ∈ F, initial c node → node = opener
  supported : unsupportedCheck c = false
  initialization : initializationCheck c opener root = true
  operations : (nodes c F).all (operationCheck c opener root) = true
  forks : forkCheck (nodes c F) = true
  foreign : foreignCheck c opener F (nodes c F) = true
  structural : StateResourceKahn.nativeKahn (StateResourceCycle.parents (nodes c F)) (nodes c F) = []

namespace Prepared

theorem known_inside {c : ResourceConfig} {F : Facts} (_p : Prepared c F) : Included (nodes c F) F :=
  fun _ member => (List.mem_filter.mp member).1

theorem known_operation {c : ResourceConfig} {F : Facts} (_p : Prepared c F) :
    ∀ node ∈ nodes c F, operation c node :=
  fun node member => (operationVerbCheck_iff c node).mp (List.mem_filter.mp member).2

theorem operation_known {c : ResourceConfig} {F : Facts} (_p : Prepared c F) (node : ResourceFact)
    (member : node ∈ F) (selected : operation c node) : node ∈ nodes c F :=
  List.mem_filter.mpr ⟨member,(operationVerbCheck_iff c node).mpr selected⟩

theorem known_unique {c : ResourceConfig} {F : Facts} (_p : Prepared c F) (unique : (F.map Fact.id).Nodup) :
    ((nodes c F).map Fact.id).Nodup := unique.sublist (List.Sublist.map Fact.id List.filter_sublist)

theorem opener_excluded {c : ResourceConfig} {F : Facts} (p : Prepared c F)
    (unique : (F.map Fact.id).Nodup) (distinct : c.initialVerb ∉ operationNames c) :
    ∀ node ∈ nodes c F, node.id ≠ p.opener.id := by
  intro node member equal
  have same := unique_ids_consistent F unique node (p.known_inside node member) p.opener p.openerAccepted equal
  have selected := p.known_operation node member
  have name := (operation_names c node).mp selected
  have opener : p.opener.data.selected.verb = c.initialVerb := p.isOpener
  exact distinct (by simpa [same,initial,opener] using name)

def environment {c : ResourceConfig} {F : Facts} (p : Prepared c F)
    (unique : (F.map Fact.id).Nodup) (distinct : c.initialVerb ∉ operationNames c) (sliceBound : F.length ≤ 2^63 - 1) :
    StateResourceWorklist.Environment := {
  config := c,opener := p.opener,root := p.root,known := nodes c F,
  unique := p.known_unique unique,initialization := p.initialization,operationsCheck := p.operations,forks := p.forks,
  foreign := foreign_implies_previous_check c p.opener F (nodes c F) unique p.known_inside p.foreign,
  excludesOpener := p.opener_excluded unique distinct,structural := p.structural,
  sliceBound := Nat.le_trans (List.length_filter_le _ F) sliceBound }

theorem root_unique {c : ResourceConfig} {F : Facts} (p : Prepared c F) (unique : (F.map Fact.id).Nodup)
    (op root : ResourceFact) (ho : op ∈ F) (hr : root ∈ F) (isOpener : initial c op) (link : rootOf op root) :
    op = p.opener ∧ root = p.root := by
  have sameOp := p.uniqueOpener op ho isOpener
  subst op
  have identity : root.id = p.root.id := by
    have same := link.symm.trans p.rootLink
    simpa [rootOf] using same
  exact ⟨rfl,unique_ids_consistent F unique root hr p.root p.rootAccepted identity⟩

end Prepared


/-- Once actual preflight checks pass, every supported cause must be a budget
witness. This eliminates all other certificate constructors from the verifier
continuation, rather than postulating a complete resource classifier. -/
theorem prepared_cause_is_budget {c : ResourceConfig} {F : Facts} (p : Prepared c F)
    (unique : (F.map Fact.id).Nodup) (cause : Cause c F) :
    ∃ node, StateResourceWitness.BudgetWitness c p.opener node (nodes c F) := by
  cases cause with
  | unsupported bad =>
    have rejected := (unsupportedCheck_iff c).mpr bad
    rw [p.supported] at rejected
    contradiction
  | @openers a b ha hb ia ib different =>
    have sameA := p.uniqueOpener a ha ia
    have sameB := p.uniqueOpener b hb ib
    subst a; subst b
    exact False.elim (different rfl)
  | @openerArity op member isOpener bad =>
    have same := p.uniqueOpener op member isOpener
    subst op
    have link : p.opener.data.selected.predecessors = [p.root.id] := p.rootLink
    simp [link] at bad
  | @initialization op root ho hr isOpener link bad =>
    obtain ⟨sameOp,sameRoot⟩ := p.root_unique unique op root ho hr isOpener link
    subst op; subst root
    exact False.elim (bad ((initializationCheck_iff _ _ _).mp p.initialization))
  | @malformed op root a ho hr ha isOpener link selected bad =>
    obtain ⟨sameOp,sameRoot⟩ := p.root_unique unique op root ho hr isOpener link
    subst op; subst root
    have checked := List.all_eq_true.mp p.operations a (p.operation_known a ha selected)
    exact False.elim (bad ((operationCheck_iff _ _ _ _).mp checked))
  | @fork op root a b ho hr isOpener link ha hb oa ob owner previous different =>
    have acceptedA := p.operation_known a ha oa
    have acceptedB := p.operation_known b hb ob
    have ordinary := (forkCheck_iff (nodes c F) (unique_ids_consistent _ (p.known_unique unique))).mp p.forks
    have same := ordinary a acceptedA b acceptedB owner previous
    exact False.elim (different (congrArg Fact.id same))
  | @foreign op root a b ho hr link ha hb isOpener selected edge bad =>
    obtain ⟨sameOp,sameRoot⟩ := p.root_unique unique op root ho hr isOpener link
    subst op; subst root
    have safe := ((foreignCheck_iff c p.opener F (nodes c F) unique).mp p.foreign) a
      (p.operation_known a ha selected) b hb edge bad.1
    rcases bad.2 with notOperation | ⟨previous,different⟩
    · exact False.elim (notOperation safe.1)
    · exact False.elim (different (safe.2 previous))
  | @cycle op root a b C ho hr isOpener link inside ops ha hb edge back =>
    have certificate : CycleCertificate c F := ⟨C,a,b,inside,ops,ha,hb,edge,back⟩
    have rejected := (native_cycle_certificate_iff c F).mpr certificate
    have ordinary : nativeCycleCheck c F = true := by simp [nativeCycleCheck,p.structural]
    rw [ordinary] at rejected
    contradiction
  | @budget op root a C ho hr isOpener link valid inside exactCone ops bad =>
    obtain ⟨sameOp,sameRoot⟩ := p.root_unique unique op root ho hr isOpener link
    subst op; subst root
    exact ⟨a,C,(fun entry member => p.operation_known entry (inside entry member) (ops entry member).1),exactCone,bad⟩

/-- Post-preflight + budget + final aggregate fault iff a complete accepted
certificate checks, for the same fixed native configuration and typed facts. -/
theorem prepared_native_certificate_iff {c : ResourceConfig} {F : Facts} (p : Prepared c F)
    (unique : (F.map Fact.id).Nodup) (distinct : c.initialVerb ∉ operationNames c) (sliceBound : F.length ≤ 2^63 - 1)
    (configuration : StateResourceAggregate.NativeConfiguration c)
    (accountSlice : ((accounts p.opener.data.selected.initialAllocations).map Prod.fst).length ≤ 2^63 - 1) :
    StateResourceValidated.isFault (StateResourceValidated.observe (p.environment unique distinct sliceBound)) = true ↔ Cause c F := by
  have correspondence := StateResourceValidated.native_validated_certificate_iff (p.environment unique distinct sliceBound) configuration accountSlice
  constructor
  · intro failed
    obtain ⟨node,witness⟩ := correspondence.mp failed
    exact StateResourceWitness.budget_witness_cause c p.opener p.root node (nodes c F) F p.openerAccepted p.rootAccepted
      p.isOpener p.rootLink ((initializationCheck_iff _ _ _).mp p.initialization) p.known_inside
      (fun entry member => ⟨p.known_operation entry member,
        (operationCheck_iff _ _ _ _).mp (List.all_eq_true.mp p.operations entry member)⟩) witness
  · intro cause
    apply correspondence.mpr
    exact prepared_cause_is_budget p unique cause


def initialNodes (c : ResourceConfig) (F : Facts) : Facts :=
  F.filter (fun node => node.data.selected.verb == c.initialVerb)

theorem initial_member (c : ResourceConfig) (F : Facts) (node : ResourceFact) :
    node ∈ initialNodes c F ↔ node ∈ F ∧ initial c node := by simp [initialNodes,initial]

theorem check_false (check : Bool) (failed : check ≠ true) : check = false := by cases check <;> simp_all

theorem rejected_item {α : Type} (items : List α) (check : α → Bool) (rejected : items.all check = false) :
    ∃ item ∈ items, check item = false := by
  classical
  have failed : ¬∀ item ∈ items, check item = true := by
    intro good
    have valid := List.all_eq_true.mpr good
    rw [rejected] at valid
    contradiction
  simp only [Classical.not_forall] at failed
  obtain ⟨item,member,wrong⟩ := failed
  exact ⟨item,member,check_false _ wrong⟩

theorem no_opener_no_cause (c : ResourceConfig) (F : Facts) (supported : unsupportedCheck c = false)
    (noOpener : ∀ node ∈ F, ¬initial c node) : ¬Cause c F := by
  have noUnsupported : ¬(c.ownership = .collective ∨ ∃ policy, c.certification = .quorum policy) := by
    intro bad
    have value := (unsupportedCheck_iff c).mpr bad
    rw [supported] at value
    contradiction
  intro cause
  cases cause <;> grind

theorem missing_root_no_cause (c : ResourceConfig) (F : Facts) (op : ResourceFact) (address : Nat)
    (unique : (F.map Fact.id).Nodup) (supported : unsupportedCheck c = false)
    (uniqueOpener : ∀ node ∈ F, initial c node → node = op)
    (arity : op.data.selected.predecessors = [address]) (missing : StateResourceGraph.lookup F address = none) : ¬Cause c F := by
  have noUnsupported : ¬(c.ownership = .collective ∨ ∃ policy, c.certification = .quorum policy) := by
    intro bad
    have value := (unsupportedCheck_iff c).mpr bad
    rw [supported] at value
    contradiction
  have noRoot : ∀ root ∈ F, ¬rootOf op root := by
    intro root member link
    have identity : root.id = address := by
      have equal : [root.id] = [address] := link.symm.trans arity
      simpa using equal
    have present := StateResourceGraph.lookup_known F unique root member
    rw [identity,missing] at present
    contradiction
  have length : op.data.selected.predecessors.length = 1 := by simp [arity]
  intro cause
  cases cause <;> grind

end CBCL.StateResourcePreflight
