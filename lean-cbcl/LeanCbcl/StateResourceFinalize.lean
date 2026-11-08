import LeanCbcl.StateResourceSolvency

/-! Native aggregate finish: checked account updates, negative-budget test,
checked rights total plus floor, and bounded-headroom conservation. The result
retains the actual aggregate values; no success/absence oracle is supplied. -/
namespace CBCL.StateResourceFinalize
open State CheckpointEvidence StateResource StateResourceNative StateResourceSummary StateResourceBudget
open StateResourceMachine StateResourceWorklist StateResourceAggregate StateResourceSolvency

structure AggregateSnapshot where
  value : Int
  rights : String → Int
  headroom : Option (String → Int)

def finishBalances (c : ResourceConfig) (owners : List String) (rights : String → Int)
    (headroom : Option (String → Int)) : Option AggregateSnapshot :=
  if owners.any (fun owner => decide (rights owner < 0)) ||
      headroom.any (fun space => owners.any (fun owner => decide (space owner < 0))) then none else do
    let totalRights ← checkedSum (owners.map rights)
    let value ← checkedAdd totalRights c.floor
    match c.ceiling with
    | none => some ⟨value,rights,headroom⟩
    | some cap =>
      let space ← headroom
      let totalSpace ← checkedSum (owners.map space)
      if checkedAdd value totalSpace == some cap then some ⟨value,rights,headroom⟩ else none

def finish (c : ResourceConfig) (op : ResourceFact) (facts : Facts) : Option AggregateSnapshot := do
  let owners := (accounts op.data.selected.initialAllocations).map Prod.fst
  let rights ← applySideAll owners false facts (allocation (accounts op.data.selected.initialAllocations))
  let headroom ← if c.headroomKey.isSome then do
    let space ← applySideAll owners true facts (allocation (accounts op.data.selected.headroomAllocations))
    some (some space)
    else some none
  finishBalances c owners rights headroom

theorem no_negative_check (owners : List String) (values : String → Int) (positive : ∀ owner, 0 ≤ values owner) :
    owners.any (fun owner => decide (values owner < 0)) = false := by
  cases selected : owners.any (fun owner => decide (values owner < 0)) with
  | false => rfl
  | true =>
    obtain ⟨owner,_,bad⟩ := List.any_eq_true.mp selected
    have negative : values owner < 0 := of_decide_eq_true bad
    have bound := positive owner
    omega

theorem signed64_i128 (value : Int) (bounded : signed64 value) : i128 value := by
  unfold signed64 i128 at *
  simp only [show (2 : Int)^63 = 9223372036854775808 from rfl,
    show (2 : Int)^127 = 170141183460469231731687303715884105728 from rfl] at *
  constructor <;> omega

theorem finishBalances_unbounded (c : ResourceConfig) (owners : List String) (rights : String → Int) (value : Int)
    (noNegative : owners.any (fun owner => decide (rights owner < 0)) = false)
    (total : checkedSum (owners.map rights) = some (owners.map rights).sum)
    (checked : checkedAdd (owners.map rights).sum c.floor = some value) (ceiling : c.ceiling = none) :
    finishBalances c owners rights none = some ⟨value,rights,none⟩ := by
  simp [finishBalances,noNegative,total,checked,ceiling]

theorem finishBalances_bounded (c : ResourceConfig) (owners : List String) (rights space : String → Int) (value cap : Int)
    (noRightsNegative : owners.any (fun owner => decide (rights owner < 0)) = false)
    (noSpaceNegative : owners.any (fun owner => decide (space owner < 0)) = false)
    (rightsTotal : checkedSum (owners.map rights) = some (owners.map rights).sum)
    (spaceTotal : checkedSum (owners.map space) = some (owners.map space).sum)
    (checked : checkedAdd (owners.map rights).sum c.floor = some value)
    (conservation : checkedAdd value (owners.map space).sum = some cap) (ceiling : c.ceiling = some cap) :
    finishBalances c owners rights (some space) = some ⟨value,rights,some space⟩ := by
  simp [finishBalances,noRightsNegative,noSpaceNegative,rightsTotal,spaceTotal,checked,conservation,ceiling]

/-- All native final aggregate rejection branches are unreachable after a
complete successful budget worklist, for installed numeric configuration and
native account-list representation bounds. -/
theorem native_aggregate_finishes (e : Environment) (worklist : StateResourceCounters.Worklist) (machine : Machine) (ghost : Ghost)
    (completed : StateResourceWorklist.run e = .complete worklist machine ghost) (size : worklist.processed.length = e.known.length)
    (configuration : NativeConfiguration e.config)
    (accountSlice : ((accounts e.opener.data.selected.initialAllocations).map Prod.fst).length ≤ 2^63 - 1) :
    ∃ snapshot, finish e.config e.opener e.known = some snapshot ∧
      snapshot.rights = accountBalance (initialSide e false) false e.known ∧
      snapshot.value = (((accounts e.opener.data.selected.initialAllocations).map Prod.fst).map snapshot.rights).sum + e.config.floor := by
  let owners := (accounts e.opener.data.selected.initialAllocations).map Prod.fst
  let rights := accountBalance (initialSide e false) false e.known
  let space := accountBalance (initialSide e true) true e.known
  let value := (owners.map rights).sum + e.config.floor
  have positive := completed_size_balances_nonnegative e worklist machine ghost completed size
  have rightPositive : ∀ owner, 0 ≤ rights owner := positive false (by intro impossible; contradiction)
  have noRightNegative := no_negative_check owners rights rightPositive
  have initialRights : ∀ owner, natural64 (initialSide e false owner) := initial_side_natural e false (by intro impossible; contradiction)
  have recognized : ∀ node ∈ e.known, natural64 node.data.amount := by
    intro node member
    obtain ⟨_,_,_,_,_,_,amount,_⟩ := e.operations node member
    exact amount
  obtain ⟨rows,rowValue,_,unique,_⟩ := e.initialValid.2.2.1
  have distinct : owners.Nodup := by simpa [owners,accounts,rowValue] using unique
  have rightsFold := native_rights_fold e.config e.opener e.root e.known e.initialValid e.operations e.sliceBound
  have rightsTotal := native_total_refinement (initialSide e false) false e.known owners initialRights e.sliceBound accountSlice recognized distinct
  have valueBound := partial_total_i128 (initialSide e false) false e.known owners e.config.floor distinct initialRights e.sliceBound accountSlice recognized configuration.1
  have valueCheck : checkedAdd (owners.map rights).sum e.config.floor = some value :=
    (checkedAdd_iff _ _ _).mpr ⟨valueBound,rfl⟩
  cases headroom : e.config.headroomKey with
  | none =>
    have noCeiling : e.config.ceiling = none := by
      cases ceiling : e.config.ceiling with
      | none => rfl
      | some cap => have impossible := configuration.2.2.1; simp [headroom,ceiling] at impossible
    refine ⟨⟨value,rights,none⟩,?_,rfl,rfl⟩
    have finalized := finishBalances_unbounded e.config owners rights value noRightNegative rightsTotal valueCheck noCeiling
    simpa [finish,headroom,rightsFold,initialSide,owners,rights] using finalized
  | some key =>
    have active : e.config.headroomKey.isSome = true := by simp [headroom]
    have spacePositive : ∀ owner, 0 ≤ space owner := positive true (by intro _; exact active)
    have noSpaceNegative := no_negative_check owners space spacePositive
    have initialSpace : ∀ owner, natural64 (initialSide e true owner) := initial_side_natural e true (by intro _; exact active)
    have spaceFold := native_headroom_fold e.config e.opener e.root e.known e.initialValid active e.operations e.sliceBound
    have spaceTotal := native_total_refinement (initialSide e true) true e.known owners initialSpace e.sliceBound accountSlice recognized distinct
    cases ceiling : e.config.ceiling with
    | none => have impossible := configuration.2.2.1; simp [headroom,ceiling] at impossible
    | some cap =>
      have conservation : value + (owners.map space).sum = cap :=
        aggregate_conservation e.config e.opener e.root e.known cap e.initialValid ceiling e.operations
      have capBound : i128 cap := signed64_i128 cap (configuration.2.1 cap ceiling).1
      have conservationCheck : checkedAdd value (owners.map space).sum = some cap :=
        (checkedAdd_iff _ _ _).mpr ⟨by simpa [conservation] using capBound,conservation.symm⟩
      refine ⟨⟨value,rights,some space⟩,?_,rfl,rfl⟩
      have finalized := finishBalances_bounded e.config owners rights space value cap noRightNegative noSpaceNegative
        rightsTotal spaceTotal valueCheck conservationCheck ceiling
      simpa [finish,headroom,rightsFold,spaceFold,initialSide,owners,rights,space] using finalized

end CBCL.StateResourceFinalize
