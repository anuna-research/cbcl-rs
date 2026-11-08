import LeanCbcl.StateResourceWitness

/-! Post-budget native worklist transition with erased proof annotations.
The actual state contains cumulative summaries and identity-only tip maps;
cones and owner prefixes are separate ghost stores. -/
namespace CBCL.StateResourceMachine
open State CheckpointEvidence StateResource StateResourceSummary StateResourceCache StateResourceStructure
open StateResourceFrontier StateResourceDependency StateResourceOwnPrefix

structure Machine where
  summaries : Cache
  tips : Nat → Tips

structure Ghost where
  cones : StateResourceCones.ConeCache
  prefixes : Nat → Prefixes

structure Invariant (op : ResourceFact) (known : Facts) (machine : Machine) (ghost : Ghost) : Prop where
  summaries : StateResourceCache.Valid op.id known machine.summaries
  parents : ParentInvariant op known machine.summaries ghost.cones machine.tips ghost.prefixes
  ownTips : OwnTips machine.summaries ghost.cones machine.tips
  paired : ∀ address node summary, machine.summaries address = some (node,summary) →
    ∃ cone, ghost.cones address = some (node,cone)
  processed : ∀ address node cone, ghost.cones address = some (node,cone) →
    ∀ entry ∈ cone, ∃ summary, machine.summaries entry.id = some (entry,summary)

def initial : Machine := ⟨emptyCache,fun _ => emptyTips⟩
def initialGhost : Ghost := ⟨fun _ => none,fun _ => emptyPrefixes⟩

theorem initial_invariant (op : ResourceFact) (known : Facts) : Invariant op known initial initialGhost := by
  constructor
  · exact empty_valid op.id known
  · constructor
    · intro _ _ _ impossible; contradiction
    · intro _ _ _ impossible; contradiction
  · intro _ _ _ impossible; contradiction
  · intro _ _ _ impossible; contradiction
  · intro _ _ _ impossible; contradiction

def recordResult (node : ResourceFact) (known : Facts) (machine : Machine) (ghost : Ghost)
    (parents : List (ResourceFact × Facts)) (updated : Summary) : Machine × Ghost :=
  let tips := mergedTips machine.summaries machine.tips parents
  let prefixes := mergedPrefixes ghost.prefixes parents
  let cone := StateResourceCones.unionCone known node parents
  (⟨fun address => if address = node.id then some (node,updated) else machine.summaries address,
    fun address => if address = node.id then setOwn tips node else machine.tips address⟩,
    ⟨fun address => if address = node.id then some (node,cone) else ghost.cones address,
      fun address => if address = node.id then setOwnPrefix prefixes node else ghost.prefixes address⟩)

def recordStep (op node : ResourceFact) (known : Facts) (machine : Machine) (ghost : Ghost) : Option (Machine × Ghost) := do
  let parents ← StateResourceCones.gather op ghost.cones (links node)
  let own ← previousSummary op.id machine.summaries node
  let updated ← record own node
  some (recordResult node known machine ghost parents updated)

theorem fresh_excludes_parent_cones (op node : ResourceFact) (known : Facts) (machine : Machine) (ghost : Ghost)
    (invariant : Invariant op known machine ghost) (fresh : machine.summaries node.id = none)
    (parents : List (ResourceFact × Facts))
    (lookups : StateResourceCones.gather op ghost.cones (links node) = some parents) :
    ∀ parent ∈ parents, ∀ entry ∈ parent.2, entry.id ≠ node.id := by
  intro parent member entry inside equal
  obtain ⟨address,_,_,cached⟩ := (StateResourceCones.gather_lookup op ghost.cones (links node) parents lookups).1 parent member
  obtain ⟨summary,present⟩ := invariant.processed address parent.1 parent.2 cached entry inside
  rw [equal,fresh] at present
  contradiction

/-- A concrete native transition never changes an existing summary identity. -/
theorem recordStep_preserves_old (op node : ResourceFact) (known : Facts) (machine next : Machine) (ghost after : Ghost)
    (fresh : machine.summaries node.id = none)
    (success : recordStep op node known machine ghost = some (next,after))
    (address : Nat) (entry : ResourceFact) (summary : Summary)
    (present : machine.summaries address = some (entry,summary)) : next.summaries address = some (entry,summary) := by
  cases parents : StateResourceCones.gather op ghost.cones (links node) with
  | none => simp [recordStep,parents] at success
  | some parentEntries =>
    cases previous : previousSummary op.id machine.summaries node with
    | none => simp [recordStep,parents,previous] at success
    | some own =>
      cases recorded : record own node with
      | none => simp [recordStep,parents,previous,recorded] at success
      | some updated =>
        have shape := success
        simp [recordStep,parents,previous,recorded] at shape
        simp only [recordResult] at shape
        have equal : address ≠ node.id := by
          intro same; subst address; rw [fresh] at present; contradiction
        have cacheShape := congrArg (fun value : Machine × Ghost => value.1.summaries address) shape
        simpa [equal,present] using cacheShape.symm


theorem recordResult_invariant (op node : ResourceFact) (known : Facts) (machine : Machine) (ghost : Ghost)
    (parents : List (ResourceFact × Facts)) (own updated : Summary)
    (invariant : Invariant op known machine ghost) (fresh : machine.summaries node.id = none)
    (lookups : StateResourceCones.gather op ghost.cones (links node) = some parents)
    (previous : previousSummary op.id machine.summaries node = some own) (recorded : record own node = some updated)
    (nonforking : Nonforking known) (accepted : node ∈ known) (unique : (known.map Fact.id).Nodup)
    (foreignChecked : previousOwnerCheck op.id known = true)
    (structural : StateResourceKahn.nativeKahn (StateResourceCycle.parents known) known = []) :
    Invariant op known (recordResult node known machine ghost parents updated).1
      (recordResult node known machine ghost parents updated).2 := by
  let next := (recordResult node known machine ghost parents updated).1
  let after := (recordResult node known machine ghost parents updated).2
  let cone := StateResourceCones.unionCone known node parents
  let merged := mergedTips machine.summaries machine.tips parents
  let pre := mergedPrefixes ghost.prefixes parents
  have unprocessed := fresh_excludes_parent_cones op node known machine ghost invariant fresh parents lookups
  have advanced : StateResourceCache.advance op.id machine.summaries node = some next.summaries := by
    simp [StateResourceCache.advance,previous,recorded,next,recordResult]
  have inserted : StateResourceCones.insert op known ghost.cones node = some after.cones := by
    simp [StateResourceCones.insert,StateResourceCones.reconstruct,lookups,after,recordResult]
  have preserved : ∀ address entry summary, machine.summaries address = some (entry,summary) →
      next.summaries address = some (entry,summary) :=
    fun address entry summary found => advance_preserves_old op.id machine.summaries next.summaries node fresh advanced
      address entry summary found
  have insideCache : Inside known machine.summaries := by
    intro address entry summary found
    obtain ⟨C,cached⟩ := invariant.paired address entry summary found
    exact (invariant.parents.1 address entry C cached).2.1
  have validNext := advance_valid op.id known machine.summaries next.summaries node invariant.summaries
    (previous_owner op.id known machine.summaries node invariant.summaries insideCache
      ((previousOwnerCheck_iff _ _).mp foreignChecked) accepted) accepted advanced
  obtain ⟨exactCone,preRep,preCovers⟩ := pre_record_frontier_exact op node known machine.summaries ghost.cones machine.tips ghost.prefixes
    parents invariant.parents lookups nonforking accepted unique unprocessed
  obtain ⟨chain,preEqual,chainCurrent,_,chainRun⟩ := merged_previous_prefix op node known machine.summaries ghost.cones machine.tips ghost.prefixes
    parents own invariant.parents invariant.summaries invariant.ownTips lookups nonforking accepted unique foreignChecked unprocessed structural previous
  have repExtended := represents_cache_extension op.id known known machine.summaries next.summaries merged pre
    (fun _ member => member) preRep preserved
  have currentChain : OwnerChain node.data.signer op.id (pre node.data.signer ++ [node]) := by simpa [pre,preEqual] using chainCurrent
  have currentRun : run (pre node.data.signer) empty = some own := by simpa [pre,preEqual] using chainRun
  have newCached : next.summaries node.id = some (node,updated) := by simp [next,recordResult]
  have currentRep := record_frontier_represents op.id known next.summaries merged pre node own updated
    repExtended accepted currentChain currentRun recorded newCached
  have coneInside : Included cone known := fun entry member =>
    ((StateResourceCones.unionCone_member known node entry parents).mp member).1
  have identities := unique_ids_consistent known unique
  have splitCone (entry : ResourceFact) : entry ∈ cone ↔ entry = node ∨ entry ∈ cone.filter (fun entry => entry.id != node.id) := by
    constructor
    · intro member
      by_cases equal : entry.id = node.id
      · exact Or.inl (identities entry (coneInside entry member) node accepted equal)
      · exact Or.inr (List.mem_filter.mpr ⟨member,by simpa using equal⟩)
    · intro member
      rcases member with rfl | old
      · exact exactCone.1
      · exact (List.mem_filter.mp old).1
  have currentCovers : Covers (setOwnPrefix pre node) cone := fun entry =>
    (splitCone entry).trans (record_frontier_covers pre _ node preCovers entry).symm
  have coneValid := StateResourceCones.insert_valid op node known ghost.cones after.cones invariant.parents.1 accepted unique inserted
  refine ⟨validNext,⟨coneValid,?_⟩,?_,?_,?_⟩
  · intro address entry C found
    by_cases current : address = node.id
    · subst address
      have pair : node = entry ∧ cone = C := by simpa [after,recordResult,cone] using found
      obtain ⟨rfl,rfl⟩ := pair
      simpa [next,after,recordResult,merged,pre] using And.intro currentRep currentCovers
    · have old : ghost.cones address = some (entry,C) := by simpa [after,recordResult,current] using found
      have oldRep := represents_cache_extension op.id known known machine.summaries next.summaries
        (machine.tips address) (ghost.prefixes address) (fun _ member => member)
        (invariant.parents.2 address entry C old).1 preserved
      simpa [next,after,recordResult,current] using And.intro oldRep (invariant.parents.2 address entry C old).2
  · intro address entry C found
    by_cases current : address = node.id
    · subst address
      have pair : node = entry ∧ cone = C := by simpa [after,recordResult,cone] using found
      obtain ⟨rfl,rfl⟩ := pair
      exact ⟨updated,newCached,by simp [next,recordResult,setOwn]⟩
    · have old : ghost.cones address = some (entry,C) := by simpa [after,recordResult,current] using found
      obtain ⟨summary,cached,tip⟩ := invariant.ownTips address entry C old
      exact ⟨summary,preserved address entry summary cached,by simpa [next,recordResult,current] using tip⟩
  · intro address entry summary found
    by_cases current : address = node.id
    · subst address
      have pair : node = entry ∧ updated = summary := by simpa [next,recordResult] using found
      obtain ⟨rfl,rfl⟩ := pair
      exact ⟨cone,by simp [after,recordResult,cone]⟩
    · have old : machine.summaries address = some (entry,summary) := by simpa [next,recordResult,current] using found
      obtain ⟨C,cached⟩ := invariant.paired address entry summary old
      exact ⟨C,by simpa [after,recordResult,current] using cached⟩
  · intro address entry C found ancestor member
    by_cases current : address = node.id
    · subst address
      have pair : node = entry ∧ cone = C := by simpa [after,recordResult,cone] using found
      obtain ⟨rfl,rfl⟩ := pair
      rcases (splitCone ancestor).mp member with rfl | old
      · exact ⟨updated,newCached⟩
      · have sound := (StateResourceCones.gather_lookup op ghost.cones (links node) parents lookups).1
        have inside : ∀ parent ∈ parents, Included parent.2 known := by
          intro parent hp
          obtain ⟨id,_,_,cached⟩ := sound parent hp
          exact (invariant.parents.1 id parent.1 parent.2 cached).2.2.1
        obtain ⟨parent,hp,inParent⟩ := (unionCone_past known node ancestor parents inside unprocessed).mp old
        obtain ⟨id,_,_,cached⟩ := sound parent hp
        obtain ⟨summary,present⟩ := invariant.processed id parent.1 parent.2 cached ancestor inParent
        exact ⟨summary,preserved ancestor.id ancestor summary present⟩
    · have old : ghost.cones address = some (entry,C) := by simpa [after,recordResult,current] using found
      obtain ⟨summary,present⟩ := invariant.processed address entry C old ancestor member
      exact ⟨summary,preserved ancestor.id ancestor summary present⟩


theorem recordStep_invariant (op node : ResourceFact) (known : Facts) (machine next : Machine) (ghost after : Ghost)
    (invariant : Invariant op known machine ghost) (fresh : machine.summaries node.id = none)
    (nonforking : Nonforking known) (accepted : node ∈ known) (unique : (known.map Fact.id).Nodup)
    (foreignChecked : previousOwnerCheck op.id known = true)
    (structural : StateResourceKahn.nativeKahn (StateResourceCycle.parents known) known = [])
    (success : recordStep op node known machine ghost = some (next,after)) : Invariant op known next after := by
  cases lookups : StateResourceCones.gather op ghost.cones (links node) with
  | none => simp [recordStep,lookups] at success
  | some parents =>
    cases previous : previousSummary op.id machine.summaries node with
    | none => simp [recordStep,lookups,previous] at success
    | some own =>
      cases recorded : record own node with
      | none => simp [recordStep,lookups,previous,recorded] at success
      | some updated =>
        have result : recordResult node known machine ghost parents updated = (next,after) := by
          simpa [recordStep,lookups,previous,recorded] using success
        have valid := recordResult_invariant op node known machine ghost parents own updated invariant fresh
          lookups previous recorded nonforking accepted unique foreignChecked structural
        simpa [result] using valid

theorem recordStep_unchanged (op node : ResourceFact) (known : Facts) (machine next : Machine) (ghost after : Ghost)
    (success : recordStep op node known machine ghost = some (next,after)) (address : Nat) (different : address ≠ node.id) :
    next.summaries address = machine.summaries address := by
  cases lookups : StateResourceCones.gather op ghost.cones (links node) with
  | none => simp [recordStep,lookups] at success
  | some parents =>
    cases previous : previousSummary op.id machine.summaries node with
    | none => simp [recordStep,lookups,previous] at success
    | some own =>
      cases recorded : record own node with
      | none => simp [recordStep,lookups,previous,recorded] at success
      | some updated =>
        have result : recordResult node known machine ghost parents updated = (next,after) := by
          simpa [recordStep,lookups,previous,recorded] using success
        have value := congrArg (fun pair : Machine × Ghost => pair.1.summaries address) result
        simpa [recordResult,different] using value.symm

def Absent (schedule : Facts) (machine : Machine) : Prop :=
  ∀ node ∈ schedule, machine.summaries node.id = none

def execute (op : ResourceFact) (known schedule : Facts) (state : Machine × Ghost) : Option (Machine × Ghost) :=
  schedule.foldlM (fun state node => recordStep op node known state.1 state.2) state

/-- The joint cache/cone/frontier invariants are preserved over the entire
successful native record schedule. No per-node prefix or cone oracle remains. -/
theorem execute_invariant (op : ResourceFact) (known schedule : Facts) (machine next : Machine) (ghost after : Ghost)
    (invariant : Invariant op known machine ghost) (absent : Absent schedule machine)
    (scheduleUnique : (schedule.map Fact.id).Nodup) (scheduled : schedule ⊆ known)
    (nonforking : Nonforking known) (unique : (known.map Fact.id).Nodup)
    (foreignChecked : previousOwnerCheck op.id known = true)
    (structural : StateResourceKahn.nativeKahn (StateResourceCycle.parents known) known = [])
    (success : execute op known schedule (machine,ghost) = some (next,after)) : Invariant op known next after := by
  induction schedule generalizing machine ghost with
  | nil =>
    have same : machine = next ∧ ghost = after := by simpa [execute] using success
    obtain ⟨rfl,rfl⟩ := same
    exact invariant
  | cons node rest ih =>
    obtain ⟨notIn,uniqueRest⟩ := List.nodup_cons.mp scheduleUnique
    cases step : recordStep op node known machine ghost with
    | none => simp [execute,List.foldlM_cons,step] at success
    | some result =>
      obtain ⟨mid,annotations⟩ := result
      have midValid := recordStep_invariant op node known machine mid ghost annotations invariant
        (absent node (by simp)) nonforking (scheduled (by simp)) unique foreignChecked structural step
      have restAbsent : Absent rest mid := by
        intro entry member
        have different : entry.id ≠ node.id := by
          intro equal
          exact notIn (List.mem_map.mpr ⟨entry,member,equal⟩)
        rw [recordStep_unchanged op node known machine mid ghost annotations step entry.id different]
        exact absent entry (by simp [member])
      apply ih mid annotations midValid restAbsent uniqueRest (fun _ member => scheduled (by simp [member]))
      simpa [execute,List.foldlM_cons,step] using success

/-- Whole successful native cache traversal, starting with empty summaries,
cones and tips. The final joint invariant is derived rather than assumed. -/
theorem native_execution_invariant (op : ResourceFact) (known schedule : Facts) (machine : Machine) (ghost : Ghost)
    (scheduleUnique : (schedule.map Fact.id).Nodup) (scheduled : schedule ⊆ known)
    (nonforking : Nonforking known) (unique : (known.map Fact.id).Nodup)
    (foreignChecked : previousOwnerCheck op.id known = true)
    (structural : StateResourceKahn.nativeKahn (StateResourceCycle.parents known) known = [])
    (success : execute op known schedule (initial,initialGhost) = some (machine,ghost)) :
    Invariant op known machine ghost :=
  execute_invariant op known schedule initial machine initialGhost ghost (initial_invariant op known)
    (by intro _ _; rfl) scheduleUnique scheduled nonforking unique foreignChecked structural success

end CBCL.StateResourceMachine
