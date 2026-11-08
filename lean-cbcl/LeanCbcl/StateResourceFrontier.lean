import LeanCbcl.StateResourceStructure

/-! Native dependency-frontier merge versus per-owner prefix union. The
refinement relates actual tip identities and cached counters to the prefixes
whose union supplies cone arithmetic. -/
namespace CBCL.StateResourceFrontier
open State CheckpointEvidence StateResource StateResourceSummary StateResourceCache StateResourceStructure

/-- The frontier tip identities indexed by account owner. -/
abbrev Tips := String → Option Nat
/-- The exact owner-prefix fact lists indexed by owner. -/
abbrev Prefixes := String → Facts

/-- Merge two owner-tip frontiers. -/
def merge (cache : Cache) (left right : Tips) : Tips := fun owner =>
  match left owner,right owner with
  | none,incoming => incoming
  | old,none => old
  | some old,some incoming => chooseTip cache old incoming

/-- Merge two owner-prefix maps. -/
def mergePrefixes (left right : Prefixes) : Prefixes := fun owner => mergeOwnerTips (left owner) (right owner)

/-- The frontier tips represent the corresponding exact owner prefixes. -/
def Represents (opener : Nat) (known : Facts) (cache : Cache) (tips : Tips) (prefixes : Prefixes) : Prop :=
  ∀ owner, match tips owner with
  | none => prefixes owner = []
  | some address => ∃ node summary, cache address = some (node,summary) ∧
      node.data.signer = owner ∧ tipId opener (prefixes owner) = address ∧
      OwnerChain owner opener (prefixes owner) ∧ Included (prefixes owner) known ∧
      run (prefixes owner) empty = some summary

theorem merge_represents (opener : Nat) (known : Facts) (cache : Cache)
    (left right : Tips) (C D : Prefixes)
    (leftRep : Represents opener known cache left C) (rightRep : Represents opener known cache right D) :
    Represents opener known cache (merge cache left right) (mergePrefixes C D) := by
  intro owner
  have cl := leftRep owner
  have cr := rightRep owner
  cases leftRead : left owner with
  | none =>
    have empty : C owner = [] := by simpa [leftRead] using cl
    cases rightRead : right owner with
    | none => simp [merge,mergePrefixes,leftRead,rightRead,mergeOwnerTips,empty,show D owner = [] from by simpa [rightRead] using cr]
    | some incoming =>
      simp only [rightRead] at cr
      have selected : mergeOwnerTips (C owner) (D owner) = D owner := by
        rw [empty]; unfold mergeOwnerTips
        split
        · rfl
        · rename_i h
          simp only [List.length_nil] at h
          have nil : D owner = [] := List.length_eq_zero_iff.mp (by omega)
          simp [nil]
      simpa [merge,mergePrefixes,leftRead,rightRead,selected] using cr
  | some old =>
    simp only [leftRead] at cl
    cases rightRead : right owner with
    | none =>
      have empty : D owner = [] := by simpa [rightRead] using cr
      have selected : mergeOwnerTips (C owner) (D owner) = C owner := by simp [mergeOwnerTips,empty]
      simpa [merge,mergePrefixes,leftRead,rightRead,selected] using cl
    | some incoming =>
      simp only [rightRead] at cr
      have savedLeft := cl
      have savedRight := cr
      obtain ⟨leftNode,leftSummary,leftCached,leftOwner,leftTip,leftChain,leftInside,leftRun⟩ := cl
      obtain ⟨rightNode,rightSummary,rightCached,rightOwner,rightTip,rightChain,rightInside,rightRun⟩ := cr
      have lseq := native_sequence_is_prefix_length (C owner) leftSummary leftRun
      have rseq := native_sequence_is_prefix_length (D owner) rightSummary rightRun
      by_cases longer : (C owner).length < (D owner).length
      · simpa [merge,chooseTip,leftRead,rightRead,leftCached,rightCached,lseq,rseq,longer,
          mergePrefixes,mergeOwnerTips] using
          savedRight
      · simpa [merge,chooseTip,leftRead,rightRead,leftCached,rightCached,lseq,rseq,longer,
          mergePrefixes,mergeOwnerTips] using
          savedLeft


theorem represented_chain (opener : Nat) (known : Facts) (cache : Cache) (tips : Tips) (prefixes : Prefixes)
    (rep : Represents opener known cache tips prefixes) (owner : String) :
    OwnerChain owner opener (prefixes owner) ∧ Included (prefixes owner) known := by
  have meaning := rep owner
  cases selected : tips owner with
  | none =>
    have nil : prefixes owner = [] := by simpa [selected] using meaning
    simp [nil,OwnerChain,Included]
  | some address =>
    simp only [selected] at meaning
    obtain ⟨_,_,_,_,_,chain,inside,_⟩ := meaning
    exact ⟨chain,inside⟩

/-- The represented prefixes cover the required dependency cone. -/
def Covers (prefixes : Prefixes) (cone : Facts) : Prop :=
  ∀ node, node ∈ cone ↔ ∃ owner, node ∈ prefixes owner

theorem merge_prefix_members (opener : Nat) (known : Facts) (cache : Cache)
    (left right : Tips) (C D : Prefixes)
    (leftRep : Represents opener known cache left C) (rightRep : Represents opener known cache right D)
    (nonforking : Nonforking known) (owner : String) (node : ResourceFact) :
    node ∈ mergePrefixes C D owner ↔ node ∈ C owner ∨ node ∈ D owner := by
  obtain ⟨cl,il⟩ := represented_chain opener known cache left C leftRep owner
  obtain ⟨cr,ir⟩ := represented_chain opener known cache right D rightRep owner
  exact merge_owner_tips_union owner known
    (fun x hx y hy ox oy prev => nonforking x hx y hy (ox.trans oy.symm) prev) cl cr il ir node

/-- Merging actual cached dependency tips represents exactly the union of
both dependency cones; no incoming operation can disappear or be invented. -/
theorem merge_covers (opener : Nat) (known : Facts) (cache : Cache)
    (left right : Tips) (C D : Prefixes) (leftCone rightCone : Facts)
    (leftRep : Represents opener known cache left C) (rightRep : Represents opener known cache right D)
    (nonforking : Nonforking known) (leftCovers : Covers C leftCone) (rightCovers : Covers D rightCone) :
    ∀ node, (∃ owner, node ∈ mergePrefixes C D owner) ↔ node ∈ leftCone ∨ node ∈ rightCone := by
  intro node
  constructor
  · rintro ⟨owner,member⟩
    rcases (merge_prefix_members opener known cache left right C D leftRep rightRep nonforking owner node).mp member with l | r
    · exact Or.inl ((leftCovers node).mpr ⟨owner,l⟩)
    · exact Or.inr ((rightCovers node).mpr ⟨owner,r⟩)
  · intro member
    rcases member with l | r
    · obtain ⟨owner,member⟩ := (leftCovers node).mp l
      exact ⟨owner,(merge_prefix_members opener known cache left right C D leftRep rightRep nonforking owner node).mpr (Or.inl member)⟩
    · obtain ⟨owner,member⟩ := (rightCovers node).mp r
      exact ⟨owner,(merge_prefix_members opener known cache left right C D leftRep rightRep nonforking owner node).mpr (Or.inr member)⟩

/-- A dependency frontier cannot contribute an additional operation by the
current owner beyond its previous prefix: nonforking makes the prefixes
comparable, and the unprocessed current operation is absent from dependencies. -/
theorem dependency_own_prefix_before_current (owner : String) (opener : Nat) (known C D : Facts)
    (node : ResourceFact) (nonforking : Nonforking known)
    (current : OwnerChain owner opener (C ++ [node])) (dependency : OwnerChain owner opener D)
    (insideCurrent : Included (C ++ [node]) known) (insideDependency : Included D known)
    (notProcessed : node ∉ D) : D.IsPrefix C := by
  have nf : ∀ x ∈ known, ∀ y ∈ known, x.data.signer = owner → y.data.signer = owner →
      x.data.prev = y.data.prev → x = y :=
    fun x hx y hy ox oy prev => nonforking x hx y hy (ox.trans oy.symm) prev
  have prefixChain : OwnerChain owner opener C := by
    clear dependency insideCurrent insideDependency notProcessed
    induction C generalizing opener with
    | nil => trivial
    | cons first rest ih => exact ⟨current.1,current.2.1,ih first.id current.2.2⟩
  have insideC : Included C known := fun entry member => insideCurrent entry (by simp [member])
  have length : D.length ≤ C.length := by
    by_cases shorter : D.length ≤ C.length
    · exact shorter
    · have preceding : (C ++ [node]).IsPrefix D := longer_owner_prefix owner known nf current dependency
        insideCurrent insideDependency (by simp; omega)
      exact False.elim (notProcessed (preceding.subset (by simp)))
  exact longer_owner_prefix owner known nf dependency prefixChain insideDependency insideC length


/-- Merge a list of owner-tip frontiers. -/
def mergeAll (cache : Cache) : Tips → List Tips → Tips
  | initial,[] => initial
  | initial,tip :: rest => mergeAll cache (merge cache initial tip) rest

/-- Merge a list of owner-prefix maps. -/
def mergeAllPrefixes : Prefixes → List Prefixes → Prefixes
  | initial,[] => initial
  | initial,tip :: rest => mergeAllPrefixes (mergePrefixes initial tip) rest

/-- The complete dependency-tip merge loop preserves the representation,
not just one pairwise merge. The paired list is a proof annotation; the native
loop reads only its first projection. -/
theorem mergeAll_represents (opener : Nat) (known : Facts) (cache : Cache)
    (initial : Tips) (initialPrefixes : Prefixes) (dependencies : List (Tips × Prefixes))
    (initialRep : Represents opener known cache initial initialPrefixes)
    (dependencyReps : ∀ entry ∈ dependencies, Represents opener known cache entry.1 entry.2) :
    Represents opener known cache
      (mergeAll cache initial (dependencies.map Prod.fst))
      (mergeAllPrefixes initialPrefixes (dependencies.map Prod.snd)) := by
  induction dependencies generalizing initial initialPrefixes with
  | nil => exact initialRep
  | cons entry rest ih =>
    exact ih (merge cache initial entry.1) (mergePrefixes initialPrefixes entry.2)
      (merge_represents opener known cache initial entry.1 initialPrefixes entry.2 initialRep
        (dependencyReps entry (by simp)))
      (fun next member => dependencyReps next (by simp [member]))

/-- All dependency prefixes appear exactly in the loop's represented union. -/
theorem mergeAll_members (opener : Nat) (known : Facts) (cache : Cache)
    (initial : Tips) (initialPrefixes : Prefixes) (dependencies : List (Tips × Prefixes))
    (initialRep : Represents opener known cache initial initialPrefixes)
    (dependencyReps : ∀ entry ∈ dependencies, Represents opener known cache entry.1 entry.2)
    (nonforking : Nonforking known) (owner : String) (node : ResourceFact) :
    node ∈ mergeAllPrefixes initialPrefixes (dependencies.map Prod.snd) owner ↔
      node ∈ initialPrefixes owner ∨ ∃ entry ∈ dependencies, node ∈ entry.2 owner := by
  induction dependencies generalizing initial initialPrefixes with
  | nil => simp [mergeAllPrefixes]
  | cons entry rest ih =>
    have entryRep := dependencyReps entry (by simp)
    have restReps : ∀ next ∈ rest, Represents opener known cache next.1 next.2 :=
      fun next member => dependencyReps next (by simp [member])
    have tail := ih (merge cache initial entry.1) (mergePrefixes initialPrefixes entry.2)
      (merge_represents opener known cache initial entry.1 initialPrefixes entry.2 initialRep entryRep) restReps
    simp only [List.map_cons,mergeAllPrefixes]
    rw [tail,merge_prefix_members opener known cache initial entry.1 initialPrefixes entry.2
      initialRep entryRep nonforking owner node]
    simp only [List.mem_cons,exists_eq_or_imp]
    constructor
    · intro member
      rcases member with (old | current) | later
      · exact Or.inl old
      · exact Or.inr (Or.inl current)
      · exact Or.inr (Or.inr later)
    · intro member
      rcases member with old | current | later
      · exact Or.inl (Or.inl old)
      · exact Or.inl (Or.inr current)
      · exact Or.inr later


theorem represents_cache_extension (opener : Nat) (known extended : Facts) (cache next : Cache)
    (tips : Tips) (prefixes : Prefixes) (inside : Included known extended)
    (rep : Represents opener known cache tips prefixes)
    (preserved : ∀ address node summary, cache address = some (node,summary) → next address = some (node,summary)) :
    Represents opener extended next tips prefixes := by
  intro owner
  have meaning := rep owner
  cases selected : tips owner with
  | none => simpa [selected] using meaning
  | some address =>
    simp only [selected] at meaning
    obtain ⟨node,summary,cached,same,tip,chain,part,folded⟩ := meaning
    exact ⟨node,summary,preserved address node summary cached,same,tip,chain,
      fun entry member => inside entry (part entry member),folded⟩

/-- Replace the current owner's frontier tip with the new fact. -/
def setOwn (tips : Tips) (node : ResourceFact) : Tips :=
  fun owner => if owner = node.data.signer then some node.id else tips owner

/-- Append the current fact to its owner prefix. -/
def setOwnPrefix (prefixes : Prefixes) (node : ResourceFact) : Prefixes :=
  fun owner => if owner = node.data.signer then prefixes owner ++ [node] else prefixes owner

/-- Native insertion of the current owner's new tip updates exactly that
owner prefix. All other dependency prefixes retain their cached counters. -/
theorem record_frontier_represents (opener : Nat) (known : Facts) (cache : Cache)
    (tips : Tips) (prefixes : Prefixes) (node : ResourceFact) (own next : Summary)
    (rep : Represents opener known cache tips prefixes) (accepted : node ∈ known)
    (currentChain : OwnerChain node.data.signer opener (prefixes node.data.signer ++ [node]))
    (currentRun : run (prefixes node.data.signer) empty = some own)
    (recorded : record own node = some next) (cached : cache node.id = some (node,next)) :
    Represents opener known cache (setOwn tips node) (setOwnPrefix prefixes node) := by
  intro owner
  by_cases same : owner = node.data.signer
  · subst owner
    simp only [setOwn,if_pos rfl,setOwnPrefix]
    obtain ⟨_,part⟩ := represented_chain opener known cache tips prefixes rep node.data.signer
    exact ⟨node,next,cached,rfl,tipId_append _ _ _,currentChain,
      (fun entry member => by
        rcases List.mem_append.mp member with old | fresh
        · exact part entry old
        · simpa using (List.mem_singleton.mp fresh ▸ accepted)),
      run_append_one _ _ _ _ currentRun recorded⟩
  · simpa [setOwn,setOwnPrefix,same] using rep owner

/-- Replacing the owner's tip after recording adds exactly the current
operation to the represented dependency past. -/
theorem record_frontier_covers (prefixes : Prefixes) (past : Facts) (node : ResourceFact)
    (covers : Covers prefixes past) :
    ∀ entry, (∃ owner, entry ∈ setOwnPrefix prefixes node owner) ↔ entry = node ∨ entry ∈ past := by
  intro entry
  constructor
  · rintro ⟨owner,member⟩
    by_cases same : owner = node.data.signer
    · simp only [setOwnPrefix,if_pos same,List.mem_append,List.mem_singleton] at member
      exact member.elim (fun old => Or.inr ((covers entry).mpr ⟨owner,old⟩)) Or.inl
    · exact Or.inr ((covers entry).mpr ⟨owner,by simpa [setOwnPrefix,same] using member⟩)
  · intro member
    rcases member with equal | old
    · subst entry
      exact ⟨node.data.signer,by simp [setOwnPrefix]⟩
    · obtain ⟨owner,member⟩ := (covers entry).mp old
      by_cases same : owner = node.data.signer
      · exact ⟨owner,by simp only [setOwnPrefix,if_pos same,List.mem_append]; exact Or.inl member⟩
      · exact ⟨owner,by simpa [setOwnPrefix,same] using member⟩

end CBCL.StateResourceFrontier
