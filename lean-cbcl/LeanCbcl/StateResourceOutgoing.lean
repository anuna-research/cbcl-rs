import LeanCbcl.StateResourceBudget

/-! Native finite recipient-map totals versus owner-prefix transfer facts.
Validated recipients belong to the initializer's distinct account roster;
absent map entries are zero in the extensional native Summary model. -/
namespace CBCL.StateResourceOutgoing
open State CheckpointEvidence StateResource StateResourceNative StateResourceSummary StateResourceBudget

theorem sum_map_add {α : Type} (xs : List α) (f g : α → Int) :
    (xs.map (fun x => f x + g x)).sum = (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => rfl
  | cons x rest ih => simp only [List.map_cons,List.sum_cons]; rw [ih]; omega

theorem sum_map_zero {α : Type} (xs : List α) : (xs.map (fun _ => (0 : Int))).sum = 0 := by
  induction xs <;> simp_all

theorem recipient_indicator (owners : List String) (unique : owners.Nodup) (target : String) (amount : Int) :
    (owners.map (fun owner => if target = owner then amount else 0)).sum =
      if target ∈ owners then amount else 0 := by
  induction owners with
  | nil => simp
  | cons first rest ih =>
    obtain ⟨absent,tailUnique⟩ := List.nodup_cons.mp unique
    by_cases equal : target = first
    · subst target
      simp [ih tailUnique,absent]
    · simp [ih tailUnique,equal]

/-- Extract the amounts sent to the requested recipient. -/
def recipientAmounts (kind : ResourceKind) (recipient : String) (chain : Facts) : List Int :=
  chain.map (fun node => if node.data.kind = kind ∧ node.data.selected.recipient = some recipient then node.data.amount else 0)

theorem recipient_partition_sum (owners : List String) (kind : ResourceKind) (chain : Facts)
    (unique : owners.Nodup)
    (recipientValid : ∀ node ∈ chain, node.data.kind = kind →
      ∃ recipient ∈ owners, node.data.selected.recipient = some recipient) :
    (owners.map (fun recipient => (recipientAmounts kind recipient chain).sum)).sum =
      (amounts (fun node => node.data.kind == kind) chain).sum := by
  induction chain with
  | nil => simp [recipientAmounts,amounts,sum_map_zero]
  | cons node rest ih =>
    have tailValid : ∀ entry ∈ rest, entry.data.kind = kind →
        ∃ recipient ∈ owners, entry.data.selected.recipient = some recipient :=
      fun entry member selected => recipientValid entry (by simp [member]) selected
    change (owners.map (fun recipient =>
      (if node.data.kind = kind ∧ node.data.selected.recipient = some recipient then node.data.amount else 0) +
      (recipientAmounts kind recipient rest).sum)).sum = _
    rw [sum_map_add,ih tailValid]
    by_cases selected : node.data.kind = kind
    · obtain ⟨recipient,member,value⟩ := recipientValid node (by simp) selected
      simp [amounts,selected,value,recipient_indicator owners unique recipient node.data.amount,member]
    · simp [amounts,selected,sum_map_zero]

/-- Compute outgoing transfers from native owner summaries. -/
def nativeOutgoing (owners : List String) (summary : Summary) (headroom : Bool) : Option Int :=
  checkedSum (owners.map (fun recipient => if headroom then summary.sentHeadroom recipient else summary.sentRights recipient))

/-- The stored per-recipient maps, including native checked accumulation,
refine the outgoing operations of the actual successful owner prefix. -/
theorem native_outgoing_refinement (c : ResourceConfig) (op root : ResourceFact) (chain : Facts) (summary : Summary)
    (initial : validInitial c op root) (operations : ∀ node ∈ chain, validOperation c op root node)
    (success : run chain empty = some summary) (headroom : Bool) :
    nativeOutgoing ((accounts op.data.selected.initialAllocations).map Prod.fst) summary headroom =
      checkedSum (amounts (fun node => node.data.kind ==
        (if headroom then ResourceKind.transferHeadroom else ResourceKind.transfer)) chain) := by
  let owners := (accounts op.data.selected.initialAllocations).map Prod.fst
  obtain ⟨rows,value,_,unique,_⟩ := initial.2.2.1
  have distinct : owners.Nodup := by simpa [owners,accounts,value] using unique
  let kind := if headroom then ResourceKind.transferHeadroom else ResourceKind.transfer
  have selectedValid : ∀ node ∈ chain, node.data.kind = kind →
      ∃ recipient ∈ owners, node.data.selected.recipient = some recipient := by
    intro node member selected
    have kindTransfer : node.data.kind = .transfer ∨ node.data.kind = .transferHeadroom := by
      cases headroom <;> simp_all [kind]
    obtain ⟨_,recipient,recipientValue,_,inRoster⟩ := (operations node member).2.2.2.2.2.2.2.2.2.2.2.2.2.2 kindTransfer
    exact ⟨recipient,inRoster,recipientValue⟩
  have counters := (native_counters_refinement chain summary success).2.2
  have mapValues (recipient : String) :
      (if headroom then summary.sentHeadroom recipient else summary.sentRights recipient) =
        (recipientAmounts kind recipient chain).sum := by
    cases headroom with
    | false => simpa [kind,recipientAmounts] using (counters recipient).1
    | true => simpa [kind,recipientAmounts] using (counters recipient).2
  have sameSum := recipient_partition_sum owners kind chain distinct selectedValid
  have recognized : ∀ node ∈ chain, 0 ≤ node.data.amount := by
    intro node member
    obtain ⟨_,_,_,_,_,_,amount,_⟩ := operations node member
    exact amount.1
  have flatPositive : ∀ amount ∈ amounts (fun node => node.data.kind == kind) chain, 0 ≤ amount := by
    intro amount member
    obtain ⟨node,hn,rfl⟩ := List.mem_map.mp member
    exact recognized node (List.mem_filter.mp hn).1
  have mapPositive : ∀ amount ∈ owners.map (fun recipient =>
      if headroom then summary.sentHeadroom recipient else summary.sentRights recipient), 0 ≤ amount := by
    intro amount member
    obtain ⟨recipient,_,rfl⟩ := List.mem_map.mp member
    rw [mapValues]
    apply sum_nonnegative
    intro amount member
    obtain ⟨node,hn,equal⟩ := List.mem_map.mp member
    rw [← equal]
    split
    · exact recognized node hn
    · omega
  have mapped := List.map_congr_left (fun recipient (_ : recipient ∈ owners) => mapValues recipient)
  change checkedSum (owners.map (fun recipient => if headroom then summary.sentHeadroom recipient else summary.sentRights recipient)) = _
  rw [checkedSum_nonnegative _ mapPositive,checkedSum_nonnegative _ flatPositive]
  rw [mapped,sameSum]

end CBCL.StateResourceOutgoing
