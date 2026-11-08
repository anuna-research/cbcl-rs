import LeanCbcl.StateResourceCache

/-! Executable cross-operation checks performed before native resource Kahn
traversal. `known` is the identity-consistent operation map, excluding the
initializer; absent references are handled separately as pending evidence. -/
namespace CBCL.StateResourceStructure
open State CheckpointEvidence StateResource StateResourceSummary StateResourceCache

def previousOwnerCheck (opener : Nat) (known : Facts) : Bool :=
  known.all fun node => known.all fun parent =>
    if node.data.prev == some parent.id && parent.id != opener then
      parent.data.signer == node.data.signer else true

theorem previousOwnerCheck_iff (opener : Nat) (known : Facts) :
    previousOwnerCheck opener known = true ↔ SameOwnerPrevious opener known := by
  simp only [previousOwnerCheck,List.all_eq_true,Bool.and_eq_true,beq_iff_eq,bne_iff_ne]
  constructor
  · intro checked node hn parent hp prev notRoot
    simpa [prev,notRoot] using checked node hn parent hp
  · intro checked node hn parent hp
    split
    · rename_i condition
      simpa using checked node hn parent hp condition.1 condition.2
    · rfl

def forkCheck (known : Facts) : Bool :=
  known.all fun left => known.all fun right =>
    if left.data.signer == right.data.signer && left.data.prev == right.data.prev then
      left.id == right.id else true

def IdentityConsistent (known : Facts) : Prop :=
  ∀ left ∈ known, ∀ right ∈ known, left.id = right.id → left = right

def Nonforking (known : Facts) : Prop :=
  ∀ left ∈ known, ∀ right ∈ known, left.data.signer = right.data.signer →
    left.data.prev = right.data.prev → left = right

theorem forkCheck_iff (known : Facts) (identities : IdentityConsistent known) :
    forkCheck known = true ↔ Nonforking known := by
  simp only [forkCheck,List.all_eq_true,Bool.and_eq_true,beq_iff_eq]
  constructor
  · intro checked left hl right hr sameOwner samePrev
    have same : left.id = right.id := by simpa [sameOwner,samePrev] using checked left hl right hr
    exact identities left hl right hr same
  · intro checked left hl right hr
    split
    · rename_i condition
      simpa using congrArg (fun n : ResourceFact => n.id) (checked left hl right hr condition.1 condition.2)
    · rfl

/-- The complete previous-chain cache theorem uses the executable preflight
check, rather than asking the caller to postulate owner correctness. -/
theorem checked_native_cached_prefix (opener : Nat) (known schedule : Facts) (cache : Cache)
    (checked : previousOwnerCheck opener known = true) (scheduled : schedule ⊆ known)
    (success : execute opener schedule emptyCache = some cache)
    (address : Nat) (node : ResourceFact) (summary : Summary)
    (found : cache address = some (node,summary)) :
    ∃ chain, OwnerChain node.data.signer opener chain ∧ tipId opener chain = address ∧
      run chain empty = some summary ∧ summary.sequence = chain.length ∧
      Included chain known ∧ chain.getLast? = some node :=
  native_cached_prefix opener known schedule cache ((previousOwnerCheck_iff _ _).mp checked)
    scheduled success address node summary found


def ForkCertificate (known : Facts) : Prop :=
  ∃ left ∈ known, ∃ right ∈ known, left.data.signer = right.data.signer ∧
    left.data.prev = right.data.prev ∧ left.id ≠ right.id

theorem fork_rejection_iff (known : Facts) : forkCheck known = false ↔ ForkCertificate known := by
  classical
  simp [forkCheck,ForkCertificate,List.all_eq_true,Bool.eq_false_iff,and_assoc]


def ForeignOwnerCertificate (opener : Nat) (known : Facts) : Prop :=
  ∃ node ∈ known, ∃ parent ∈ known, node.data.prev = some parent.id ∧ parent.id ≠ opener ∧
    parent.data.signer ≠ node.data.signer

theorem foreign_owner_rejection_iff (opener : Nat) (known : Facts) :
    previousOwnerCheck opener known = false ↔ ForeignOwnerCertificate opener known := by
  classical
  simp [previousOwnerCheck,ForeignOwnerCertificate,List.all_eq_true,Bool.eq_false_iff,and_assoc]

theorem fork_rejection_cause (c : ResourceConfig) (F known : Facts) (op root : ResourceFact)
    (opAccepted : op ∈ F) (rootAccepted : root ∈ F) (opener : initial c op) (parent : rootOf op root)
    (inside : Included known F) (operations : ∀ node ∈ known, operation c node)
    (rejected : forkCheck known = false) : Cause c F := by
  obtain ⟨a,ha,b,hb,owner,prev,different⟩ := (fork_rejection_iff known).mp rejected
  exact .fork opAccepted rootAccepted opener parent (inside a ha) (inside b hb)
    (operations a ha) (operations b hb) owner prev different

theorem foreign_owner_rejection_cause (c : ResourceConfig) (F known : Facts) (op root : ResourceFact)
    (opAccepted : op ∈ F) (rootAccepted : root ∈ F) (opener : initial c op) (parent : rootOf op root)
    (inside : Included known F) (operations : ∀ node ∈ known, operation c node)
    (rejected : previousOwnerCheck op.id known = false) : Cause c F := by
  obtain ⟨a,ha,b,hb,prev,notRoot,different⟩ := (foreign_owner_rejection_iff _ _).mp rejected
  apply Cause.foreign opAccepted rootAccepted parent (inside a ha) (inside b hb) opener (operations a ha)
  · simp [links,prev]
  · exact ⟨notRoot,Or.inr ⟨prev,Ne.symm different⟩⟩

end CBCL.StateResourceStructure
