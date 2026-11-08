import LeanCbcl.StateResourceAggregate

/-! Local checked budgets versus linear account balances. Successful budgets
retain every intermediate check; the equality below interprets their returned
value rather than replacing a checked computation with an unchecked one. -/
namespace CBCL.StateResourceAccounting
open State CheckpointEvidence StateResource StateResourceNative StateResourceSummary StateResourceBudget StateResourceAggregate

def creditPredicate (headroom : Bool) (owner : String) (node : ResourceFact) : Bool :=
  node.data.signer == owner && node.data.kind == (if headroom then ResourceKind.decrement else ResourceKind.increment)
def debitPredicate (headroom : Bool) (owner : String) (node : ResourceFact) : Bool :=
  node.data.signer == owner && node.data.kind == (if headroom then ResourceKind.increment else ResourceKind.decrement)
def outgoingPredicate (headroom : Bool) (owner : String) (node : ResourceFact) : Bool :=
  node.data.signer == owner && node.data.kind == (if headroom then ResourceKind.transferHeadroom else ResourceKind.transfer)

theorem delta_components (c : ResourceConfig) (op root node : ResourceFact) (headroom : Bool) (owner : String)
    (valid : validOperation c op root node) :
    delta headroom owner node =
      (if creditPredicate headroom owner node then node.data.amount else 0) -
      (if debitPredicate headroom owner node then node.data.amount else 0) -
      (if outgoingPredicate headroom owner node then node.data.amount else 0) +
      (if incomingPredicate owner headroom node then node.data.amount else 0) := by
  have notSelf (transfer : node.data.kind = .transfer ∨ node.data.kind = .transferHeadroom) :
      node.data.selected.recipient ≠ some node.data.signer := by
    obtain ⟨_,recipient,value,different,_⟩ := valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2 transfer
    intro same
    have equal : recipient = node.data.signer := Option.some.inj (value.symm.trans same)
    exact different equal
  by_cases own : node.data.signer = owner <;> by_cases receives : node.data.selected.recipient = some owner <;>
    cases headroom <;> cases kind : node.data.kind <;>
    simp_all [delta,rightsDelta,headroomDelta,creditPredicate,debitPredicate,outgoingPredicate,incomingPredicate,Ne.symm] <;> omega

theorem sum_map_sub {α : Type} (facts : List α) (left right : α → Int) :
    (facts.map (fun node => left node - right node)).sum = (facts.map left).sum - (facts.map right).sum := by
  induction facts with
  | nil => rfl
  | cons first rest ih => simp only [List.map_cons,List.sum_cons]; rw [ih]; omega

theorem balance_components (c : ResourceConfig) (op root : ResourceFact) (facts : Facts) (headroom : Bool) (owner : String)
    (valid : ∀ node ∈ facts, validOperation c op root node) :
    (facts.map (delta headroom owner)).sum =
      (amounts (creditPredicate headroom owner) facts).sum - (amounts (debitPredicate headroom owner) facts).sum -
      (amounts (outgoingPredicate headroom owner) facts).sum + (amounts (incomingPredicate owner headroom) facts).sum := by
  have mapped := List.map_congr_left (fun node member => delta_components c op root node headroom owner (valid node member))
  rw [mapped,StateResourceOutgoing.sum_map_add,sum_map_sub,sum_map_sub]
  simp only [amounts_sum]

theorem checkedFold_value (values : List Int) (start result : Int)
    (success : values.foldlM checkedAdd start = some result) : result = start + values.sum := by
  induction values generalizing start with
  | nil => simpa using success.symm
  | cons first rest ih =>
    cases added : checkedAdd start first with
    | none => simp [List.foldlM_cons,added] at success
    | some next =>
      have tail : rest.foldlM checkedAdd next = some result := by simpa [List.foldlM_cons,added] using success
      have equal := (checkedAdd_iff _ _ _).mp added
      have value := ih next tail
      simp only [List.sum_cons]
      omega

theorem ownTotal_value (facts : Facts) (owner : String) (kind : ResourceKind) (value : Int)
    (success : ownTotal facts owner kind = some value) :
    value = (amounts (fun node => node.data.signer == owner && node.data.kind == kind) (ordered facts)).sum := by
  exact (checkedFold_value _ 0 value success).trans (Int.zero_add _)


theorem localBudget_value (c : ResourceConfig) (op root node : ResourceFact) (cone : Facts) (headroom : Bool) (value : Int)
    (valid : ∀ entry ∈ cone, validOperation c op root entry) (success : localBudget op node cone headroom = some value) :
    value = accountBalance (allocation (accounts (if headroom then op.data.selected.headroomAllocations
      else op.data.selected.initialAllocations))) headroom (cone.filter (fun entry => entry.id != node.id)) node.data.signer := by
  let past := cone.filter (fun entry => entry.id != node.id)
  let owner := node.data.signer
  let initial := allocation (accounts (if headroom then op.data.selected.headroomAllocations else op.data.selected.initialAllocations)) owner
  let kind := if headroom then ResourceKind.transferHeadroom else ResourceKind.transfer
  have validPast : ∀ entry ∈ ordered past, validOperation c op root entry := by
    intro entry member
    have accepted := (List.mergeSort_perm past (fun a b => a.id ≤ b.id)).mem_iff.mp member
    exact valid entry (List.mem_filter.mp accepted).1
  have components := balance_components c op root (ordered past) headroom owner validPast
  have canonical := StateKernelAggregates.sum_perm ((List.mergeSort_perm past (fun a b => a.id ≤ b.id)).map (delta headroom owner))
  cases credits : ownTotal past owner .increment with
  | none => simp [localBudget,past,owner,credits] at success
  | some credited =>
    cases debits : ownTotal past owner .decrement with
    | none => simp [localBudget,past,owner,credits,debits] at success
    | some debited =>
      cases outgoing : ownTotal past owner kind with
      | none => simp [localBudget,past,owner,kind,credits,debits,outgoing] at success
      | some sent =>
        cases raised : checkedAdd initial (if headroom then debited else credited) with
        | none => simp [localBudget,past,owner,kind,initial,credits,debits,outgoing,raised] at success
        | some high =>
          cases lowered : checkedSub high (if headroom then credited else debited) with
          | none => simp [localBudget,past,owner,kind,initial,credits,debits,outgoing,raised,lowered] at success
          | some low =>
            cases available : checkedSub low sent with
            | none => simp [localBudget,past,owner,kind,initial,credits,debits,outgoing,raised,lowered,available] at success
            | some budget =>
              have incomingSuccess : (amounts (incomingPredicate owner headroom) (ordered past)).foldlM checkedAdd budget = some value := by
                simpa [localBudget,past,owner,kind,initial,credits,debits,outgoing,raised,lowered,available,
                  amounts,List.foldlM_map,incomingPredicate] using success
              have incomingValue := checkedFold_value _ budget value incomingSuccess
              have creditValue := ownTotal_value past owner .increment credited credits
              have debitValue := ownTotal_value past owner .decrement debited debits
              have outgoingValue := ownTotal_value past owner kind sent outgoing
              have raisedValue := ((checkedAdd_iff _ _ _).mp raised).2
              have loweredValue := ((checkedSub_iff _ _ _).mp lowered).2
              have availableValue := ((checkedSub_iff _ _ _).mp available).2
              have creditExpanded : creditPredicate headroom owner = (fun entry => entry.data.signer == owner &&
                  entry.data.kind == (if headroom then ResourceKind.decrement else ResourceKind.increment)) := rfl
              have debitExpanded : debitPredicate headroom owner = (fun entry => entry.data.signer == owner &&
                  entry.data.kind == (if headroom then ResourceKind.increment else ResourceKind.decrement)) := rfl
              have outgoingExpanded : outgoingPredicate headroom owner = (fun entry => entry.data.signer == owner &&
                  entry.data.kind == (if headroom then ResourceKind.transferHeadroom else ResourceKind.transfer)) := rfl
              rw [creditExpanded,debitExpanded,outgoingExpanded] at components
              change value = initial + (past.map (delta headroom owner)).sum
              cases headroom <;>
                simp [creditPredicate,debitPredicate,outgoingPredicate,kind] at components outgoingValue raisedValue loweredValue <;>
                rw [← creditValue,← debitValue,← outgoingValue] at components <;>
                change ((ordered past).map (delta _ owner)).sum = (past.map (delta _ owner)).sum at canonical <;>
                omega


theorem delta_other_nonnegative (headroom : Bool) (owner : String) (node : ResourceFact)
    (other : node.data.signer ≠ owner) (recognized : natural64 node.data.amount) : 0 ≤ delta headroom owner node := by
  by_cases receives : node.data.selected.recipient = some owner <;> cases headroom <;> cases kind : node.data.kind <;>
    simp [delta,rightsDelta,headroomDelta,other,receives,kind] <;> exact recognized.1

theorem sum_map_partition {α : Type} (facts : List α) (predicate : α → Bool) (value : α → Int) :
    (facts.map value).sum = ((facts.filter predicate).map value).sum +
      ((facts.filter (fun node => !predicate node)).map value).sum := by
  induction facts with
  | nil => rfl
  | cons node rest ih =>
    cases selected : predicate node <;> simp [List.filter_cons,selected] <;> rw [ih] <;> omega

/-- Added observations can only add funding when the owner's own prefix is
unchanged. The existing selected contributions may be signed; only the newly
observed other-owner contributions need to be nonnegative. -/
theorem account_balance_mono (initial : String → Int) (headroom : Bool) (owner : String) (small large : Facts)
    (uniqueSmall : small.Nodup) (uniqueLarge : large.Nodup) (inside : Included small large)
    (sameOwn : ∀ node ∈ large, node ∉ small → node.data.signer ≠ owner)
    (recognized : ∀ node ∈ large, natural64 node.data.amount) :
    accountBalance initial headroom small owner ≤ accountBalance initial headroom large owner := by
  have selected : (large.filter (fun node => small.contains node)).Perm small := by
    apply (List.perm_ext_iff_of_nodup (uniqueLarge.sublist List.filter_sublist) uniqueSmall).mpr
    intro node
    constructor
    · intro member
      simpa using (List.mem_filter.mp member).2
    · intro member
      exact List.mem_filter.mpr ⟨inside node member,by simpa using member⟩
  have selectedSum := StateKernelAggregates.sum_perm (selected.map (delta headroom owner))
  have extraNonnegative : 0 ≤ (((large.filter (fun node => !small.contains node)).map (delta headroom owner)).sum) := by
    apply sum_nonnegative
    intro value member
    obtain ⟨node,hn,rfl⟩ := List.mem_map.mp member
    have selected := List.mem_filter.mp hn
    have notInside : node ∉ small := by simpa using selected.2
    exact delta_other_nonnegative headroom owner node (sameOwn node selected.1 notInside) (recognized node selected.1)
  have partition := sum_map_partition large (fun node => small.contains node) (delta headroom owner)
  unfold accountBalance
  omega

end CBCL.StateResourceAccounting
