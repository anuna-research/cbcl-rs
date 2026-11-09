import LeanCbcl.StateResourceWorklist

/-! Native aggregate account arithmetic. Configuration ranges are recognized
explicitly: ResourceConfig's mathematical Int fields alone do not imply Rust's
i64 floor/ceiling bounds. Global conservation/positivity build on the account
fold and the budget worklist, rather than becoming assumed classifiers. -/
namespace CBCL.StateResourceAggregate
open State CheckpointEvidence StateResource StateResourceNative StateResourceSummary StateResourceBudget

/-- The signed 64-bit range of native operation amounts. -/
def signed64 (value : Int) : Prop := -(2^63) ≤ value ∧ value < 2^63
instance (value : Int) : Decidable (signed64 value) := inferInstanceAs (Decidable (-(2^63) ≤ value ∧ value < 2^63))

/-- Check the numeric bounds of the installed resource configuration. -/
def configurationCheck (c : ResourceConfig) : Bool :=
  decide (signed64 c.floor) && c.ceiling.all (fun cap => decide (signed64 cap ∧ c.floor ≤ cap)) &&
    (c.ceiling.isSome == c.headroomKey.isSome) && (c.transferHeadroom.isNone || c.ceiling.isSome)

/-- The installed numeric bounds required by native arithmetic. -/
def NativeConfiguration (c : ResourceConfig) : Prop :=
  signed64 c.floor ∧ (∀ cap, c.ceiling = some cap → signed64 cap ∧ c.floor ≤ cap) ∧
    c.ceiling.isSome = c.headroomKey.isSome ∧ (c.transferHeadroom.isSome → c.ceiling.isSome)

theorem configurationCheck_iff (c : ResourceConfig) : configurationCheck c = true ↔ NativeConfiguration c := by
  cases ceiling : c.ceiling <;> cases transfer : c.transferHeadroom <;>
    simp [configurationCheck,NativeConfiguration,ceiling,transfer,and_assoc]

theorem allocation_natural64 (rows : ResourceAccounts) (recognized : ∀ row ∈ rows, natural64 row.2) (owner : String) :
    natural64 (allocation rows owner) := by
  induction rows with
  | nil => simp [allocation,List.lookup,natural64]
  | cons row rest ih =>
    obtain ⟨key,value⟩ := row
    by_cases same : key = owner
    · subst key
      simpa [allocation,List.lookup] using recognized (owner,value) (by simp)
    · have different : (owner == key) = false := beq_eq_false_iff_ne.mpr (Ne.symm same)
      simpa [allocation,List.lookup,different] using
        ih (fun row member => recognized row (by simp [member]))

/-- The signed change contributed by one fact to one account. -/
def delta (headroom : Bool) (owner : String) (node : ResourceFact) : Int :=
  if headroom then headroomDelta owner node else rightsDelta owner node

theorem delta_bound (headroom : Bool) (owner : String) (node : ResourceFact)
    (recognized : natural64 node.data.amount) : -(2^63) ≤ delta headroom owner node ∧ delta headroom owner node ≤ 2^63 := by
  by_cases same : node.data.signer = owner <;>
    by_cases recipient : node.data.selected.recipient = some owner <;>
    cases headroom <;> cases kind : node.data.kind <;>
    simp [delta,rightsDelta,headroomDelta,same,recipient,kind] <;> unfold natural64 at recognized <;> omega

/-- The account balance obtained from initial allocations and accepted deltas. -/
def accountBalance (initial : String → Int) (headroom : Bool) (facts : Facts) (owner : String) : Int :=
  initial owner + (facts.map (delta headroom owner)).sum

theorem account_balance_append (initial : String → Int) (headroom : Bool) (facts : Facts)
    (node : ResourceFact) (owner : String) :
    accountBalance initial headroom (facts ++ [node]) owner = accountBalance initial headroom facts owner + delta headroom owner node := by
  simp [accountBalance,List.map_append,List.sum_append,Int.add_assoc]

/-- Every account fold prefix and intermediate native account update fits
i128. This derives the bound from actual recognized amounts and slice length. -/
theorem account_balance_i128 (initial : String → Int) (headroom : Bool) (facts : Facts) (owner : String)
    (allocationBound : natural64 (initial owner)) (sliceBound : facts.length ≤ 2^63 - 1)
    (recognized : ∀ node ∈ facts, natural64 node.data.amount) : i128 (accountBalance initial headroom facts owner) := by
  have bounds := sum_bounds (2^63) (facts.map (delta headroom owner)) (by
    intro value member
    obtain ⟨node,hn,rfl⟩ := List.mem_map.mp member
    exact delta_bound headroom owner node (recognized node hn))
  simp only [List.length_map] at bounds
  unfold natural64 at allocationBound
  unfold i128 accountBalance
  have count : (facts.length : Int) ≤ 2^63 - 1 := by omega
  simp only [show (2 : Int)^63 = 9223372036854775808 from rfl,
    show (2 : Int)^127 = 170141183460469231731687303715884105728 from rfl] at *
  constructor <;> omega


/-- Apply an operation's signed change to the aggregate value. -/
def changeValue (values : String → Int) (owner : String) (amount : Int) : String → Int :=
  fun key => if key = owner then values key + amount else values key

/-- Apply a checked delta to one account. -/
def addAccount (owners : List String) (values : String → Int) (owner : String) (amount : Int) : Option (String → Int) := do
  if owners.contains owner then
    let value ← checkedAdd (values owner) amount
    some (update values owner value)
  else none

theorem addAccount_success (owners : List String) (values : String → Int) (owner : String) (amount : Int)
    (member : owner ∈ owners) (bounded : i128 (values owner + amount)) :
    addAccount owners values owner amount = some (changeValue values owner amount) := by
  have checked : checkedAdd (values owner) amount = some (values owner + amount) :=
    (checkedAdd_iff _ _ _).mpr ⟨bounded,rfl⟩
  have equal : update values owner (values owner + amount) = changeValue values owner amount := by
    funext key
    by_cases same : key = owner <;> simp [update,changeValue,same]
  simp [addAccount,member,checked,equal]

/-- Apply a checked transfer between two accounts. -/
def transferAccounts (owners : List String) (values : String → Int) (source recipient : String) (amount : Int) : Option (String → Int) := do
  let debited ← addAccount owners values source (-amount)
  addAccount owners debited recipient amount

theorem transferAccounts_success (owners : List String) (values : String → Int) (source recipient : String) (amount : Int)
    (sourceMember : source ∈ owners) (recipientMember : recipient ∈ owners) (different : recipient ≠ source)
    (debitBound : i128 (values source - amount)) (creditBound : i128 (values recipient + amount)) :
    transferAccounts owners values source recipient amount =
      some (changeValue (changeValue values source (-amount)) recipient amount) := by
  have debit := addAccount_success owners values source (-amount) sourceMember (by simpa [Int.sub_eq_add_neg] using debitBound)
  have credit := addAccount_success owners (changeValue values source (-amount)) recipient amount recipientMember
    (by simpa [changeValue,different] using creditBound)
  simp [transferAccounts,debit,credit]

/-- Apply one operation to rights or headroom balances. -/
def applySide (owners : List String) (headroom : Bool) (node : ResourceFact) (values : String → Int) : Option (String → Int) :=
  match node.data.kind with
  | .increment => addAccount owners values node.data.signer (if headroom then -node.data.amount else node.data.amount)
  | .decrement => addAccount owners values node.data.signer (if headroom then node.data.amount else -node.data.amount)
  | .transfer =>
    if headroom then some values else do
      let recipient ← node.data.selected.recipient
      transferAccounts owners values node.data.signer recipient node.data.amount
  | .transferHeadroom =>
    if headroom then do
      let recipient ← node.data.selected.recipient
      transferAccounts owners values node.data.signer recipient node.data.amount
    else some values
  | _ => none

/-- The account effect of one operation on the selected balance side. -/
def sideEffect (values : String → Int) (headroom : Bool) (node : ResourceFact) : String → Int :=
  fun owner => values owner + delta headroom owner node

theorem unary_effect (values : String → Int) (headroom : Bool) (node : ResourceFact)
    (kind : node.data.kind = .increment ∨ node.data.kind = .decrement) :
    sideEffect values headroom node = changeValue values node.data.signer
      (if node.data.kind = .increment then (if headroom then -node.data.amount else node.data.amount)
        else if headroom then node.data.amount else -node.data.amount) := by
  funext owner
  by_cases same : node.data.signer = owner <;> cases headroom <;> rcases kind with kind | kind <;>
    simp [sideEffect,delta,rightsDelta,headroomDelta,changeValue,kind,same,Ne.symm]

theorem transfer_effect (values : String → Int) (headroom : Bool) (node : ResourceFact) (recipient : String)
    (kind : node.data.kind = if headroom then ResourceKind.transferHeadroom else ResourceKind.transfer)
    (selected : node.data.selected.recipient = some recipient) :
    sideEffect values headroom node =
      changeValue (changeValue values node.data.signer (-node.data.amount)) recipient node.data.amount := by
  funext owner
  by_cases same : node.data.signer = owner <;> by_cases receives : recipient = owner <;>
    cases headroom <;> simp_all [sideEffect,delta,rightsDelta,headroomDelta,changeValue,Int.sub_eq_add_neg,Int.add_assoc,Ne.symm]


theorem active_transfer_complete (owners : List String) (values : String → Int) (headroom : Bool)
    (node : ResourceFact) (recipient : String)
    (kind : node.data.kind = if headroom then ResourceKind.transferHeadroom else ResourceKind.transfer)
    (selected : node.data.selected.recipient = some recipient)
    (sourceMember : node.data.signer ∈ owners) (recipientMember : recipient ∈ owners)
    (different : recipient ≠ node.data.signer)
    (bounded : ∀ owner, i128 (sideEffect values headroom node owner)) :
    applySide owners headroom node values = some (sideEffect values headroom node) := by
  have effect := transfer_effect values headroom node recipient kind selected
  have debitBound : i128 (values node.data.signer - node.data.amount) := by
    have bound := bounded node.data.signer
    rw [effect] at bound
    simpa [changeValue,Ne.symm different,Int.sub_eq_add_neg] using bound
  have creditBound : i128 (values recipient + node.data.amount) := by
    have bound := bounded recipient
    rw [effect] at bound
    simpa [changeValue,different] using bound
  have applied := transferAccounts_success owners values node.data.signer recipient node.data.amount
    sourceMember recipientMember different debitBound creditBound
  rw [effect]
  cases headroom <;> simp_all [applySide]

theorem applySide_complete (c : ResourceConfig) (op root node : ResourceFact) (headroom : Bool)
    (values : String → Int) (valid : validOperation c op root node)
    (bounded : ∀ owner, i128 (sideEffect values headroom node owner)) :
    applySide ((accounts op.data.selected.initialAllocations).map Prod.fst) headroom node values =
      some (sideEffect values headroom node) := by
  let owners := (accounts op.data.selected.initialAllocations).map Prod.fst
  have sourceMember : node.data.signer ∈ owners := valid.2.2.2.1
  have allowed := valid.1
  cases kind : node.data.kind
  all_goals try { simp [kindMatches,kind] at allowed }
  case increment =>
    have effect := unary_effect values headroom node (Or.inl kind)
    simp [kind] at effect
    have bound := bounded node.data.signer
    rw [effect] at bound
    simp only [changeValue,if_pos rfl] at bound
    have applied := addAccount_success owners values node.data.signer _ sourceMember bound
    rw [effect]
    simpa [applySide,kind,owners] using applied
  case decrement =>
    have effect := unary_effect values headroom node (Or.inr kind)
    simp [kind] at effect
    have bound := bounded node.data.signer
    rw [effect] at bound
    simp only [changeValue,if_pos rfl] at bound
    have applied := addAccount_success owners values node.data.signer _ sourceMember bound
    rw [effect]
    simpa [applySide,kind,owners] using applied
  case transfer =>
    cases headroom with
    | true =>
      have equal : sideEffect values true node = values := by
        funext owner; simp [sideEffect,delta,headroomDelta,kind]
      simp [applySide,kind,equal]
    | false =>
      obtain ⟨_,recipient,selected,different,member⟩ := valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2 (Or.inl kind)
      exact active_transfer_complete owners values false node recipient kind selected sourceMember member different bounded
  case transferHeadroom =>
    cases headroom with
    | false =>
      have equal : sideEffect values false node = values := by
        funext owner; simp [sideEffect,delta,rightsDelta,kind]
      simp [applySide,kind,equal]
    | true =>
      obtain ⟨_,recipient,selected,different,member⟩ := valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2 (Or.inr kind)
      exact active_transfer_complete owners values true node recipient kind selected sourceMember member different bounded


/-- Fold operations over the selected balance side. -/
def applySideAll (owners : List String) (headroom : Bool) (facts : Facts) (values : String → Int) : Option (String → Int) :=
  facts.foldlM (fun values node => applySide owners headroom node values) values

theorem applySideAll_prefix (c : ResourceConfig) (op root : ResourceFact) (known rest prefixFacts : Facts)
    (initial : String → Int) (headroom : Bool)
    (allocationBound : ∀ owner, natural64 (initial owner))
    (operations : ∀ node ∈ known, validOperation c op root node) (sliceBound : known.length ≤ 2^63 - 1)
    (length : prefixFacts.length + rest.length ≤ known.length) (inside : Included (prefixFacts ++ rest) known) :
    applySideAll ((accounts op.data.selected.initialAllocations).map Prod.fst) headroom rest
      (accountBalance initial headroom prefixFacts) =
      some (accountBalance initial headroom (prefixFacts ++ rest)) := by
  induction rest generalizing prefixFacts with
  | nil => simp [applySideAll]
  | cons node rest ih =>
    have accepted : node ∈ known := inside node (by simp)
    have stepInside : Included (prefixFacts ++ [node]) known := by
      intro entry member
      rcases List.mem_append.mp member with old | current
      · exact inside entry (List.mem_append.mpr (Or.inl old))
      · have same : entry = node := List.mem_singleton.mp current
        simpa [same] using accepted
    have bounded : ∀ owner, i128 (accountBalance initial headroom (prefixFacts ++ [node]) owner) := by
      intro owner
      apply account_balance_i128 initial headroom (prefixFacts ++ [node]) owner (allocationBound owner)
      · simp only [List.length_append,List.length_singleton,List.length_cons,List.length_nil] at length ⊢
        omega
      · intro entry member
        obtain ⟨_,_,_,_,_,_,amount,_⟩ := operations entry (stepInside entry member)
        exact amount
    have effect : sideEffect (accountBalance initial headroom prefixFacts) headroom node =
        accountBalance initial headroom (prefixFacts ++ [node]) := by
      funext owner
      exact (account_balance_append initial headroom prefixFacts node owner).symm
    have applied := applySide_complete c op root node headroom (accountBalance initial headroom prefixFacts)
      (operations node accepted) (fun owner => by simpa [effect] using bounded owner)
    rw [effect] at applied
    have continued := ih (prefixFacts ++ [node]) (by
      simp only [List.length_append,List.length_singleton,List.length_cons,List.length_nil] at length ⊢
      omega) (by simpa [List.append_assoc] using inside)
    simpa [applySideAll,List.foldlM_cons,applied,List.append_assoc] using continued

/-- All native aggregate account updates succeed and equal the linear balance
fold. Failures are not silently replaced with unbounded integer operations. -/
theorem native_account_fold_refinement (c : ResourceConfig) (op root : ResourceFact) (known : Facts)
    (initial : String → Int) (headroom : Bool) (allocationBound : ∀ owner, natural64 (initial owner))
    (operations : ∀ node ∈ known, validOperation c op root node) (sliceBound : known.length ≤ 2^63 - 1) :
    applySideAll ((accounts op.data.selected.initialAllocations).map Prod.fst) headroom known initial =
      some (accountBalance initial headroom known) := by
  have start : accountBalance initial headroom [] = initial := by funext owner; simp [accountBalance]
  simpa [start] using applySideAll_prefix c op root known known [] initial headroom allocationBound operations sliceBound
    (by simp) (fun _ member => member)


theorem native_rights_fold (c : ResourceConfig) (op root : ResourceFact) (known : Facts)
    (initialValid : validInitial c op root) (operations : ∀ node ∈ known, validOperation c op root node)
    (sliceBound : known.length ≤ 2^63 - 1) :
    applySideAll ((accounts op.data.selected.initialAllocations).map Prod.fst) false known
      (allocation (accounts op.data.selected.initialAllocations)) =
      some (accountBalance (allocation (accounts op.data.selected.initialAllocations)) false known) := by
  obtain ⟨rows,value,_,_,recognized⟩ := initialValid.2.2.1
  apply native_account_fold_refinement c op root known _ false
  · intro owner
    simpa [accounts,value] using allocation_natural64 rows (fun row member => (recognized row member).2) owner
  · exact operations
  · exact sliceBound

theorem native_headroom_fold (c : ResourceConfig) (op root : ResourceFact) (known : Facts)
    (initialValid : validInitial c op root) (active : c.headroomKey.isSome = true)
    (operations : ∀ node ∈ known, validOperation c op root node) (sliceBound : known.length ≤ 2^63 - 1) :
    applySideAll ((accounts op.data.selected.initialAllocations).map Prod.fst) true known
      (allocation (accounts op.data.selected.headroomAllocations)) =
      some (accountBalance (allocation (accounts op.data.selected.headroomAllocations)) true known) := by
  obtain ⟨rows,value,_,_,recognized⟩ := (initialValid.2.2.2.2.2.1 active).1
  apply native_account_fold_refinement c op root known _ true
  · intro owner
    simpa [accounts,value] using allocation_natural64 rows (fun row member => (recognized row member).2) owner
  · exact operations
  · exact sliceBound

/-- The net aggregate change of an operation. -/
def netDelta (headroom : Bool) (node : ResourceFact) : Int :=
  match node.data.kind with
  | .increment => if headroom then -node.data.amount else node.data.amount
  | .decrement => if headroom then node.data.amount else -node.data.amount
  | _ => 0

theorem total_delta (c : ResourceConfig) (op root node : ResourceFact) (headroom : Bool)
    (initialValid : validInitial c op root) (valid : validOperation c op root node) :
    (((accounts op.data.selected.initialAllocations).map Prod.fst).map (fun owner => delta headroom owner node)).sum = netDelta headroom node := by
  let owners := (accounts op.data.selected.initialAllocations).map Prod.fst
  obtain ⟨rows,value,_,unique,_⟩ := initialValid.2.2.1
  have distinct : owners.Nodup := by simpa [owners,accounts,value] using unique
  have sourceMember : node.data.signer ∈ owners := valid.2.2.2.1
  have sender (amount : Int) : (owners.map (fun owner => if node.data.signer = owner then amount else 0)).sum = amount := by
    simpa [sourceMember] using StateResourceOutgoing.recipient_indicator owners distinct node.data.signer amount
  have allowed := valid.1
  change (owners.map (fun owner => delta headroom owner node)).sum = _
  cases headroom <;> cases kind : node.data.kind
  all_goals try { simp [kindMatches,kind] at allowed }
  all_goals try { simp [delta,rightsDelta,headroomDelta,netDelta,kind,sender,StateResourceOutgoing.sum_map_zero] }
  case false.transfer =>
    obtain ⟨_,recipient,selected,_,member⟩ := valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2 (Or.inl kind)
    have ownedRecipient : recipient ∈ owners := member
    have receiver : (owners.map (fun owner => if recipient = owner then node.data.amount else 0)).sum = node.data.amount := by
      simpa [ownedRecipient] using StateResourceOutgoing.recipient_indicator owners distinct recipient node.data.amount
    simp [delta,rightsDelta,kind,selected]
    rw [StateResourceOutgoing.sum_map_add,sender,receiver]
    simp only [netDelta,kind]
    omega
  case true.transferHeadroom =>
    obtain ⟨_,recipient,selected,_,member⟩ := valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2 (Or.inr kind)
    have ownedRecipient : recipient ∈ owners := member
    have receiver : (owners.map (fun owner => if recipient = owner then node.data.amount else 0)).sum = node.data.amount := by
      simpa [ownedRecipient] using StateResourceOutgoing.recipient_indicator owners distinct recipient node.data.amount
    simp [delta,headroomDelta,kind,selected]
    rw [StateResourceOutgoing.sum_map_add,sender,receiver]
    simp only [netDelta,kind]
    omega


theorem sum_swap {α β : Type} (left : List α) (right : List β) (function : α → β → Int) :
    (left.map (fun a => (right.map (function a)).sum)).sum =
      (right.map (fun b => (left.map (fun a => function a b)).sum)).sum := by
  induction right with
  | nil => simp [StateResourceOutgoing.sum_map_zero]
  | cons first rest ih =>
    simp only [List.map_cons,List.sum_cons]
    rw [StateResourceOutgoing.sum_map_add,ih]

theorem total_account_balance (initial : String → Int) (headroom : Bool) (facts : Facts) (owners : List String) :
    (owners.map (accountBalance initial headroom facts)).sum =
      (owners.map initial).sum + (facts.map (fun node => (owners.map (fun owner => delta headroom owner node)).sum)).sum := by
  unfold accountBalance
  rw [StateResourceOutgoing.sum_map_add,sum_swap]

theorem global_total_refinement (c : ResourceConfig) (op root : ResourceFact) (known : Facts)
    (initial : String → Int) (headroom : Bool) (initialValid : validInitial c op root)
    (operations : ∀ node ∈ known, validOperation c op root node) :
    (((accounts op.data.selected.initialAllocations).map Prod.fst).map (accountBalance initial headroom known)).sum =
      (((accounts op.data.selected.initialAllocations).map Prod.fst).map initial).sum + (known.map (netDelta headroom)).sum := by
  rw [total_account_balance]
  have equal := List.map_congr_left (fun node member => total_delta c op root node headroom initialValid (operations node member))
  rw [equal]

theorem net_delta_duality (facts : Facts) : (facts.map (netDelta false)).sum + (facts.map (netDelta true)).sum = 0 := by
  induction facts with
  | nil => rfl
  | cons node rest ih =>
    have current : netDelta false node + netDelta true node = 0 := by
      cases kind : node.data.kind <;> simp [netDelta,kind] <;> omega
    simp only [List.map_cons,List.sum_cons]
    omega

theorem allocation_row (rows : ResourceAccounts) (unique : (rows.map Prod.fst).Nodup)
    (owner : String) (amount : Int) (member : (owner,amount) ∈ rows) : allocation rows owner = amount := by
  induction rows with
  | nil => simp at member
  | cons row rest ih =>
    obtain ⟨key,value⟩ := row
    obtain ⟨notIn,uniqueRest⟩ := List.nodup_cons.mp unique
    rcases List.mem_cons.mp member with same | member
    · have fields : owner = key ∧ amount = value := Prod.mk.inj same
      obtain ⟨rfl,rfl⟩ := fields
      simp [allocation,List.lookup]
    · have different : owner ≠ key := by
        intro same
        exact notIn (List.mem_map.mpr ⟨(owner,amount),member,by simpa [same]⟩)
      simpa [allocation,List.lookup,beq_eq_false_iff_ne.mpr different] using ih uniqueRest member

theorem initial_roster_total (rows : ResourceAccounts) (unique : (rows.map Prod.fst).Nodup) :
    ((rows.map Prod.fst).map (allocation rows)).sum = (rows.map Prod.snd).sum := by
  rw [List.map_map]
  have equal := List.map_congr_left (fun (row : String × Int) member => allocation_row rows unique row.1 row.2 member)
  exact congrArg List.sum equal

/-- Bounded aggregate conservation follows from recognized initializer keys
and per-operation cancellation, independently of operation/address order. -/
theorem aggregate_conservation (c : ResourceConfig) (op root : ResourceFact) (known : Facts) (cap : Int)
    (initialValid : validInitial c op root) (ceiling : c.ceiling = some cap)
    (operations : ∀ node ∈ known, validOperation c op root node) :
    let owners := (accounts op.data.selected.initialAllocations).map Prod.fst
    (owners.map (accountBalance (allocation (accounts op.data.selected.initialAllocations)) false known)).sum + c.floor +
      (owners.map (accountBalance (allocation (accounts op.data.selected.headroomAllocations)) true known)).sum = cap := by
  obtain ⟨initialValue,budget⟩ := initialValid.2.2.2.2.2.2
  have ceilingData := budget.2.2.2.2 cap ceiling
  obtain ⟨rightRows,rightValue,_,rightUnique,_⟩ := initialValid.2.2.1
  have headroomActive : c.headroomKey.isSome = true := ceilingData.2.1
  obtain ⟨headRows,headValue,_,headUnique,_⟩ := ((initialValid.2.2.2.2.2.1 headroomActive).1)
  have sameKeys := ((initialValid.2.2.2.2.2.1 headroomActive).2)
  have rosterPermutation : (rightRows.map Prod.fst).Perm (headRows.map Prod.fst) := by
    apply (List.perm_ext_iff_of_nodup rightUnique headUnique).mpr
    intro owner
    simpa [accounts,rightValue,headValue] using (sameKeys owner).symm
  have headTotal : (((accounts op.data.selected.initialAllocations).map Prod.fst).map
      (allocation (accounts op.data.selected.headroomAllocations))).sum = (headRows.map Prod.snd).sum := by
    simp only [rightValue,headValue,accounts]
    rw [StateKernelAggregates.sum_perm (rosterPermutation.map (allocation headRows)),initial_roster_total headRows headUnique]
  have rightTotal : (((accounts op.data.selected.initialAllocations).map Prod.fst).map
      (allocation (accounts op.data.selected.initialAllocations))).sum = (rightRows.map Prod.snd).sum := by
    simpa [accounts,rightValue] using initial_roster_total rightRows rightUnique
  dsimp only
  rw [global_total_refinement c op root known _ false initialValid operations,
    global_total_refinement c op root known _ true initialValid operations,rightTotal,headTotal]
  have dual := net_delta_duality known
  have valueEq := budget.2.2.1
  have capacity := ceilingData.2.2.2.2.2
  simp only [rightValue,headValue,accounts] at valueEq capacity
  omega


/-- A partial account-roster total counts each transfer with coefficient -1,
0 or 1, never once per account. This is the bound needed by native total's
checked intermediate prefixes. -/
theorem partial_delta_bound (owners : List String) (unique : owners.Nodup) (headroom : Bool) (node : ResourceFact)
    (recognized : natural64 node.data.amount) :
    -(2^63) ≤ (owners.map (fun owner => delta headroom owner node)).sum ∧
      (owners.map (fun owner => delta headroom owner node)).sum ≤ 2^63 := by
  have sender (amount : Int) := StateResourceOutgoing.recipient_indicator owners unique node.data.signer amount
  have receiver (amount : Int) : (owners.map (fun owner =>
      if node.data.selected.recipient = some owner then amount else 0)).sum =
      match node.data.selected.recipient with
      | none => 0
      | some recipient => if recipient ∈ owners then amount else 0 := by
    cases selected : node.data.selected.recipient with
    | none => simp [StateResourceOutgoing.sum_map_zero]
    | some recipient => simpa using StateResourceOutgoing.recipient_indicator owners unique recipient amount
  cases headroom <;> cases kind : node.data.kind <;>
    simp [delta,rightsDelta,headroomDelta,kind,StateResourceOutgoing.sum_map_add,sender,receiver,StateResourceOutgoing.sum_map_zero]
  all_goals cases selected : node.data.selected.recipient
  all_goals try dsimp only
  all_goals repeat' split
  all_goals simp_all [natural64]
  all_goals omega


/-- Bounds every native total-fold prefix, including transient signed account
balances. Each operation contributes at most one amount to a partial roster. -/
theorem partial_total_i128 (initial : String → Int) (headroom : Bool) (facts : Facts) (owners : List String) (floor : Int)
    (unique : owners.Nodup) (allocationBound : ∀ owner, natural64 (initial owner))
    (factSlice : facts.length ≤ 2^63 - 1) (accountSlice : owners.length ≤ 2^63 - 1)
    (recognized : ∀ node ∈ facts, natural64 node.data.amount) (floorRange : signed64 floor) :
    i128 ((owners.map (accountBalance initial headroom facts)).sum + floor) := by
  have initialBounds := sum_bounds (2^63) (owners.map initial) (by
    intro value member
    obtain ⟨owner,_,rfl⟩ := List.mem_map.mp member
    have range := allocationBound owner
    unfold natural64 at range
    constructor <;> omega)
  have deltaBounds := sum_bounds (2^63)
    (facts.map (fun node => (owners.map (fun owner => delta headroom owner node)).sum)) (by
      intro value member
      obtain ⟨node,hn,rfl⟩ := List.mem_map.mp member
      exact partial_delta_bound owners unique headroom node (recognized node hn))
  simp only [List.length_map] at initialBounds deltaBounds
  have factCount : (facts.length : Int) ≤ 2^63 - 1 := by omega
  have accountCount : (owners.length : Int) ≤ 2^63 - 1 := by omega
  rw [total_account_balance]
  unfold i128 signed64 at *
  simp only [show (2 : Int)^63 = 9223372036854775808 from rfl,
    show (2 : Int)^127 = 170141183460469231731687303715884105728 from rfl] at *
  constructor <;> omega

theorem checkedRosterFold_prefix (initial : String → Int) (headroom : Bool) (facts : Facts)
    (prefixOwners remaining : List String) (allocationBound : ∀ owner, natural64 (initial owner))
    (factSlice : facts.length ≤ 2^63 - 1) (accountSlice : prefixOwners.length + remaining.length ≤ 2^63 - 1)
    (recognized : ∀ node ∈ facts, natural64 node.data.amount) (unique : (prefixOwners ++ remaining).Nodup) :
    ((remaining.map (accountBalance initial headroom facts)).foldlM checkedAdd
      (prefixOwners.map (accountBalance initial headroom facts)).sum) =
      some (((prefixOwners ++ remaining).map (accountBalance initial headroom facts)).sum) := by
  induction remaining generalizing prefixOwners with
  | nil => simp
  | cons owner rest ih =>
    have prefixUnique : (prefixOwners ++ [owner]).Nodup := by
      obtain ⟨left,right,cross⟩ := List.nodup_append.mp unique
      apply List.nodup_append.mpr
      refine ⟨left,by simp,?_⟩
      intro first hf last hl
      have same : last = owner := List.mem_singleton.mp hl
      subst last
      exact cross first hf owner (by simp)
    have prefixBound : (prefixOwners ++ [owner]).length ≤ 2^63 - 1 := by
      simp only [List.length_append,List.length_cons,List.length_nil] at accountSlice ⊢
      omega
    have bound := partial_total_i128 initial headroom facts (prefixOwners ++ [owner]) 0 prefixUnique allocationBound
      factSlice prefixBound recognized (by decide)
    have raised : checkedAdd (prefixOwners.map (accountBalance initial headroom facts)).sum
        (accountBalance initial headroom facts owner) =
        some (((prefixOwners ++ [owner]).map (accountBalance initial headroom facts)).sum) := by
      apply (checkedAdd_iff _ _ _).mpr
      constructor
      · simpa [List.map_append,List.sum_append] using bound
      · simp [List.map_append,List.sum_append]
    have continued := ih (prefixOwners ++ [owner]) (by
      simp only [List.length_append,List.length_cons,List.length_nil] at accountSlice ⊢
      omega) (by simpa [List.append_assoc] using unique)
    simpa [List.map_cons,List.foldlM_cons,raised,List.append_assoc] using continued

/-- Native BTreeMap total (in its canonical unique key order) cannot overflow
on aggregate account values, even if an intermediate account balance is signed. -/
theorem native_total_refinement (initial : String → Int) (headroom : Bool) (facts : Facts) (owners : List String)
    (allocationBound : ∀ owner, natural64 (initial owner)) (factSlice : facts.length ≤ 2^63 - 1)
    (accountSlice : owners.length ≤ 2^63 - 1) (recognized : ∀ node ∈ facts, natural64 node.data.amount)
    (unique : owners.Nodup) :
    checkedSum (owners.map (accountBalance initial headroom facts)) =
      some (owners.map (accountBalance initial headroom facts)).sum := by
  simpa [checkedSum] using checkedRosterFold_prefix initial headroom facts [] owners allocationBound factSlice
    (by simpa using accountSlice) recognized (by simpa using unique)


theorem headroom_transfer_requires_active (c : ResourceConfig) (op root node : ResourceFact)
    (configuration : NativeConfiguration c) (valid : validOperation c op root node) (kind : node.data.kind = .transferHeadroom) :
    c.headroomKey.isSome = true := by
  have allowed := valid.1
  simp [kindMatches,kind] at allowed
  obtain ⟨mapping,present,_⟩ := allowed
  have selected : c.transferHeadroom.isSome = true := by simp [present]
  have ceiling := configuration.2.2.2 selected
  rw [← configuration.2.2.1]
  exact ceiling

end CBCL.StateResourceAggregate
