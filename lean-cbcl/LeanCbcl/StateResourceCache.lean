import LeanCbcl.StateResourceKahn

/-! Native owner-summary cache. Prefixes are reconstructed from actual previous
lookups, not supplied to the arithmetic theorem. Dependency-frontier tips are
separate and are not established by this invariant. -/
namespace CBCL.StateResourceCache
open State CheckpointEvidence StateResource StateResourceSummary
abbrev Cache := Nat → Option (ResourceFact × Summary)
def emptyCache : Cache := fun _ => none
def tipId (opener : Nat) (chain : Facts) : Nat := chain.foldl (fun _ node => node.id) opener
def Valid (opener : Nat) (known : Facts) (cache : Cache) : Prop :=
  ∀ address node summary, cache address = some (node,summary) →
    node.id = address ∧ ∃ chain, OwnerChain node.data.signer opener chain ∧
      tipId opener chain = node.id ∧ run chain empty = some summary ∧
      Included chain known ∧ chain.getLast? = some node

def previousSummary (opener : Nat) (cache : Cache) (node : ResourceFact) : Option Summary := do
  let previous ← node.data.prev
  if previous = opener then some empty else (cache previous).map Prod.snd

def advance (opener : Nat) (cache : Cache) (node : ResourceFact) : Option Cache := do
  let own ← previousSummary opener cache node
  let next ← record own node
  some (fun address => if address = node.id then some (node,next) else cache address)

theorem empty_valid (opener : Nat) (known : Facts) : Valid opener known emptyCache := by
  intro address node summary found
  simp [emptyCache] at found

theorem tipId_append (opener : Nat) (chain : Facts) (node : ResourceFact) :
    tipId opener (chain ++ [node]) = node.id := by simp [tipId,List.foldl_append]

theorem ownerChain_append (owner : String) (opener : Nat) (chain : Facts) (node : ResourceFact)
    (chainProof : OwnerChain owner opener chain) (sameOwner : node.data.signer = owner)
    (previous : node.data.prev = some (tipId opener chain)) :
    OwnerChain owner opener (chain ++ [node]) := by
  induction chain generalizing opener with
  | nil => simpa [OwnerChain,tipId] using And.intro sameOwner previous
  | cons first rest ih =>
    obtain ⟨same,prev,tail⟩ := chainProof
    exact ⟨same,prev,ih first.id tail (by simpa [tipId] using previous)⟩

theorem run_append_one (chain : Facts) (own next : Summary) (node : ResourceFact)
    (chainProof : run chain empty = some own) (step : record own node = some next) :
    run (chain ++ [node]) empty = some next := by
  simp only [run,List.foldlM_append]
  change (run chain empty >>= fun summary => record summary node >>= pure) = some next
  simp [chainProof,step]

/-- The native structural phase rejects foreign-owner previous links. -/
def PreviousOwner (opener : Nat) (cache : Cache) (node : ResourceFact) : Prop :=
  ∀ address parent summary, node.data.prev = some address → address ≠ opener →
    cache address = some (parent,summary) → parent.data.signer = node.data.signer

theorem previous_prefix (opener : Nat) (known : Facts) (cache : Cache) (node : ResourceFact) (own : Summary)
    (valid : Valid opener known cache) (owner : PreviousOwner opener cache node)
    (found : previousSummary opener cache node = some own) :
    ∃ chain, OwnerChain node.data.signer opener chain ∧
      node.data.prev = some (tipId opener chain) ∧ run chain empty = some own ∧ Included chain known := by
  cases prev : node.data.prev with
  | none => simp [previousSummary,prev] at found
  | some address =>
    by_cases root : address = opener
    · subst address
      have equal : own = empty := by simpa [previousSummary,prev] using found.symm
      subst own
      exact ⟨[], trivial, by simpa [tipId] using prev, rfl,by intro _ h; simp at h⟩
    · cases cached : cache address with
      | none => simp [previousSummary,prev,root,cached] at found
      | some pair =>
        obtain ⟨parent,summary⟩ := pair
        have equal : summary = own := by simpa [previousSummary,prev,root,cached] using found
        subst summary
        obtain ⟨identity,chain,chainProof,tip,folded,included,lastNode⟩ := valid address parent own cached
        have same := owner address parent own prev root cached
        exact ⟨chain,by simpa [same] using chainProof,by simpa [tip,identity] using prev,folded,included⟩

theorem advance_valid (opener : Nat) (known : Facts) (cache next : Cache) (node : ResourceFact)
    (valid : Valid opener known cache) (owner : PreviousOwner opener cache node) (member : node ∈ known)
    (success : advance opener cache node = some next) : Valid opener known next := by
  cases ownRead : previousSummary opener cache node with
  | none => simp [advance,ownRead] at success
  | some own =>
    cases recorded : record own node with
    | none => simp [advance,ownRead,recorded] at success
    | some summary =>
      have same : next = (fun address => if address = node.id then some (node,summary) else cache address) := by
        simpa [advance,ownRead,recorded] using success.symm
      rw [same]
      intro address cachedNode cachedSummary found
      by_cases inserted : address = node.id
      · subst address
        have pair : node = cachedNode ∧ summary = cachedSummary := by simpa using found
        obtain ⟨rfl,rfl⟩ := pair
        obtain ⟨chain,chainProof,prev,folded,included⟩ := previous_prefix opener known cache node own valid owner ownRead
        exact ⟨rfl,chain ++ [node],ownerChain_append _ _ _ _ chainProof rfl prev,
          tipId_append _ _ _,run_append_one _ _ _ _ folded recorded,
          by intro entry h; rcases List.mem_append.mp h with old | fresh
             · exact included entry old
             · simpa using (List.mem_singleton.mp fresh ▸ member),
          by simp⟩
      · exact valid address cachedNode cachedSummary (by simpa [inserted] using found)

def Inside (known : Facts) (cache : Cache) : Prop :=
  ∀ address node summary, cache address = some (node,summary) → node ∈ known

def SameOwnerPrevious (opener : Nat) (known : Facts) : Prop :=
  ∀ node ∈ known, ∀ parent ∈ known, node.data.prev = some parent.id → parent.id ≠ opener →
    parent.data.signer = node.data.signer

theorem previous_owner (opener : Nat) (known : Facts) (cache : Cache) (node : ResourceFact)
    (valid : Valid opener known cache) (inside : Inside known cache)
    (same : SameOwnerPrevious opener known) (member : node ∈ known) : PreviousOwner opener cache node := by
  intro address parent summary prev notRoot found
  have identity := (valid address parent summary found).1
  exact same node member parent (inside address parent summary found) (by simpa [identity] using prev) (by simpa [identity] using notRoot)

theorem advance_inside (opener : Nat) (known : Facts) (cache next : Cache) (node : ResourceFact)
    (inside : Inside known cache) (member : node ∈ known)
    (success : advance opener cache node = some next) : Inside known next := by
  cases ownRead : previousSummary opener cache node with
  | none => simp [advance,ownRead] at success
  | some own =>
    cases recorded : record own node with
    | none => simp [advance,ownRead,recorded] at success
    | some summary =>
      have equal : next = (fun address => if address = node.id then some (node,summary) else cache address) := by
        simpa [advance,ownRead,recorded] using success.symm
      rw [equal]
      intro address cachedNode cachedSummary found
      by_cases inserted : address = node.id
      · have pair : node = cachedNode ∧ summary = cachedSummary := by simpa [inserted] using found
        simpa [← pair.1] using member
      · exact inside address cachedNode cachedSummary (by simpa [inserted] using found)

def execute (opener : Nat) (schedule : Facts) (cache : Cache) : Option Cache :=
  schedule.foldlM (advance opener) cache

theorem execute_valid (opener : Nat) (known schedule : Facts) (cache finalCache : Cache)
    (same : SameOwnerPrevious opener known) (scheduled : schedule ⊆ known)
    (valid : Valid opener known cache) (inside : Inside known cache)
    (success : execute opener schedule cache = some finalCache) :
    Valid opener known finalCache ∧ Inside known finalCache := by
  induction schedule generalizing cache with
  | nil =>
    have equal : cache = finalCache := by simpa [execute] using success
    simpa [← equal] using And.intro valid inside
  | cons node rest ih =>
    have member : node ∈ known := scheduled (by simp)
    cases step : advance opener cache node with
    | none => simp [execute,List.foldlM_cons,step] at success
    | some next =>
      apply ih next (fun _ h => scheduled (by simp [h]))
        (advance_valid _ _ _ _ _ valid (previous_owner _ _ _ _ valid inside same member) member step)
        (advance_inside _ _ _ _ _ inside member step)
      simpa [execute,List.foldlM_cons,step] using success

/-- Whole successful cache execution: the prefix is obtained from native
lookups. Sequence and every cumulative counter now apply to that prefix. -/
theorem native_cached_prefix (opener : Nat) (known schedule : Facts) (finalCache : Cache)
    (same : SameOwnerPrevious opener known) (scheduled : schedule ⊆ known)
    (success : execute opener schedule emptyCache = some finalCache)
    (address : Nat) (node : ResourceFact) (summary : Summary)
    (found : finalCache address = some (node,summary)) :
    ∃ chain, OwnerChain node.data.signer opener chain ∧ tipId opener chain = address ∧
      run chain empty = some summary ∧ summary.sequence = chain.length ∧
      Included chain known ∧ chain.getLast? = some node := by
  have inside : Inside known emptyCache := by intro _ _ _ h; simp [emptyCache] at h
  have valid := (execute_valid opener known schedule emptyCache finalCache same scheduled
    (empty_valid opener known) inside success).1
  obtain ⟨identity,chain,chainProof,tip,folded,included,lastNode⟩ := valid address node summary found
  exact ⟨chain,chainProof,by simpa [identity] using tip,folded,
    native_sequence_is_prefix_length chain summary folded,included,lastNode⟩

/-- Native sequence arbitration of two cached frontier tips. -/
def chooseTip (cache : Cache) (old incoming : Nat) : Option Nat := do
  let left ← cache old
  let right ← cache incoming
  some (if left.2.sequence < right.2.sequence then incoming else old)

/-- The caller supplies cached identities, not owner chains or sequence/length
hypotheses. Those are recovered from the established native cache invariant. -/
theorem cached_tip_union (opener : Nat) (known : Facts) (cache : Cache)
    (valid : Valid opener known cache) (owner : String)
    (nonforking : ∀ x ∈ known, ∀ y ∈ known, x.data.signer = owner → y.data.signer = owner →
      x.data.prev = y.data.prev → x = y)
    (old incoming : Nat) (leftNode rightNode : ResourceFact) (left right : Summary)
    (leftCached : cache old = some (leftNode,left))
    (rightCached : cache incoming = some (rightNode,right))
    (leftOwner : leftNode.data.signer = owner) (rightOwner : rightNode.data.signer = owner) :
    ∃ C D, OwnerChain owner opener C ∧ OwnerChain owner opener D ∧
      tipId opener C = old ∧ tipId opener D = incoming ∧
      chooseTip cache old incoming = some (if C.length < D.length then incoming else old) ∧
      ∀ node, node ∈ mergeOwnerTips C D ↔ node ∈ C ∨ node ∈ D := by
  obtain ⟨leftId,C,leftChain,leftTip,leftRun,leftInside,_⟩ := valid old leftNode left leftCached
  obtain ⟨rightId,D,rightChain,rightTip,rightRun,rightInside,_⟩ := valid incoming rightNode right rightCached
  have cl : OwnerChain owner opener C := by simpa [leftOwner] using leftChain
  have cr : OwnerChain owner opener D := by simpa [rightOwner] using rightChain
  refine ⟨C,D,cl,cr,by simpa [leftId] using leftTip,by simpa [rightId] using rightTip,?_,
    merge_owner_tips_union owner known nonforking cl cr leftInside rightInside⟩
  simp [chooseTip,leftCached,rightCached,native_sequence_is_prefix_length C left leftRun,
    native_sequence_is_prefix_length D right rightRun]


/-- Two successful prefixes for one cached counter are the same prefix,
not merely equal-valued summaries. Nonforking and sequence fix its contents. -/
theorem same_cached_prefix (owner : String) (opener : Nat) (known C D : Facts) (summary : Summary)
    (nonforking : ∀ x ∈ known, ∀ y ∈ known, x.data.signer = owner → y.data.signer = owner →
      x.data.prev = y.data.prev → x = y)
    (left : OwnerChain owner opener C) (right : OwnerChain owner opener D)
    (insideLeft : Included C known) (insideRight : Included D known)
    (leftRun : run C empty = some summary) (rightRun : run D empty = some summary) : C = D := by
  have lengths : C.length = D.length :=
    (native_sequence_is_prefix_length C summary leftRun).symm.trans
      (native_sequence_is_prefix_length D summary rightRun)
  obtain ⟨suffix,equal⟩ := longer_owner_prefix owner known nonforking left right insideLeft insideRight (by omega)
  have lens := congrArg List.length equal
  simp only [List.length_append] at lens
  have nil : suffix = [] := List.length_eq_zero_iff.mp (by omega)
  simpa [nil] using equal


/-- A fresh native insertion preserves every existing cache entry, so old
frontier identities keep referring to the same cumulative counters. -/
theorem advance_preserves_old (opener : Nat) (cache next : Cache) (node : ResourceFact)
    (fresh : cache node.id = none) (success : advance opener cache node = some next)
    (address : Nat) (entry : ResourceFact) (summary : Summary)
    (found : cache address = some (entry,summary)) : next address = some (entry,summary) := by
  cases ownRead : previousSummary opener cache node with
  | none => simp [advance,ownRead] at success
  | some own =>
    cases recorded : record own node with
    | none => simp [advance,ownRead,recorded] at success
    | some updated =>
      have equal : next = (fun address => if address = node.id then some (node,updated) else cache address) := by
        simpa [advance,ownRead,recorded] using success.symm
      have different : address ≠ node.id := by
        intro same
        subst address
        rw [fresh] at found
        contradiction
      simp [equal,different,found]

end CBCL.StateResourceCache
