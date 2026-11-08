import LeanCbcl.StateResource

/-! Executable recognizers and native transition refinements. These definitions
are separate from the certificate propositions, so an equivalence is a checked
bridge, not a renamed premise or a supplied classifier. -/
namespace CBCL.StateResourceNative
open State StateLift CheckpointEvidence StateResource

def accountCheck (s : String) : Bool := decide (s.toList.head? = some '@') && decide (1 < s.length)
def amountCheck (n : Int) : Bool := decide (0 ≤ n) && decide (n < 2^63)

def rowsCheck : ResourceAccounts → Bool
  | [] => true
  | (name,amount) :: rest => accountCheck name && amountCheck amount &&
      !(rest.map Prod.fst).contains name && rowsCheck rest

def allocationsCheck : ResourceField ResourceAccounts → Bool
  | .value rows => !rows.isEmpty && rowsCheck rows
  | _ => false

theorem accountCheck_iff (s : String) : accountCheck s = true ↔ accountName s := by
  simp [accountCheck,accountName]

theorem amountCheck_iff (n : Int) : amountCheck n = true ↔ natural64 n := by
  simp [amountCheck,natural64]

theorem rowsCheck_iff (rows : ResourceAccounts) : rowsCheck rows = true ↔
    (rows.map Prod.fst).Nodup ∧ ∀ row ∈ rows, accountName row.1 ∧ natural64 row.2 := by
  induction rows with
  | nil => simp [rowsCheck]
  | cons row rest ih =>
    rcases row with ⟨name,amount⟩
    simp only [rowsCheck,Bool.and_eq_true,Bool.not_eq_true',List.contains_eq_mem,
      accountCheck_iff,amountCheck_iff,ih,List.map_cons,List.nodup_cons,List.mem_cons,
      forall_eq_or_imp,Prod.fst,Prod.snd]
    constructor
    · rintro ⟨⟨good,fresh⟩,nodup,tail⟩
      exact ⟨⟨by simpa using fresh,nodup⟩,good,tail⟩
    · rintro ⟨⟨fresh,nodup⟩,good,tail⟩
      exact ⟨⟨good,by simpa using fresh⟩,nodup,tail⟩

theorem allocationsCheck_iff (field : ResourceField ResourceAccounts) :
    allocationsCheck field = true ↔ validAccounts field := by
  cases field <;> simp [allocationsCheck,validAccounts,rowsCheck_iff]

/-- Checked addition/subtraction recognize exactly i128, including intermediate
checks. These bridges do not replace bounded arithmetic with unbounded Int. -/
theorem checkedAdd_iff (a b value : Int) : checkedAdd a b = some value ↔
    i128 (a + b) ∧ value = a + b := by
  change (if i128 (a + b) then some (a + b) else none) = some value ↔ _
  by_cases h : i128 (a + b) <;> simp [h,eq_comm]

theorem checkedSub_iff (a b value : Int) : checkedSub a b = some value ↔
    i128 (a - b) ∧ value = a - b := by
  change (if i128 (a - b) then some (a - b) else none) = some value ↔ _
  by_cases h : i128 (a - b) <;> simp [h,eq_comm]

theorem sum_nonnegative (xs : List Int) (nonnegative : ∀ x ∈ xs, 0 ≤ x) : 0 ≤ xs.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have head := nonnegative x (by simp)
    have tail := ih (fun a ha => nonnegative a (by simp [ha]))
    simp only [List.sum_cons]
    omega

/-- Every intermediate prefix is bounded by the total when amounts are
nonnegative. This discharges native allocation-total overflow exactly. -/
theorem checkedFold_nonnegative (xs : List Int) (nonnegative : ∀ x ∈ xs, 0 ≤ x)
    (start : Int) (bounded : i128 start) :
    xs.foldlM checkedAdd start =
      (if -(2^127) ≤ start + xs.sum ∧ start + xs.sum < 2^127
        then some (start + xs.sum) else none) := by
  induction xs generalizing start with
  | nil =>
    simpa only [List.foldlM_nil,List.sum_nil,Int.add_zero] using
      (show (if i128 start then some start else none) = some start from if_pos bounded).symm
  | cons x rest ih =>
    have hx := nonnegative x (by simp)
    have tailPositive := sum_nonnegative rest (fun y hy => nonnegative y (by simp [hy]))
    have tail := fun s hb => ih (fun y hy => nonnegative y (by simp [hy])) s hb
    by_cases safe : i128 (start + x)
    · have first : checkedAdd start x = some (start + x) := (checkedAdd_iff _ _ _).mpr ⟨safe,rfl⟩
      simp only [List.foldlM_cons,first,Option.bind_some,List.sum_cons]
      change rest.foldlM checkedAdd (start + x) = _
      rw [tail (start + x) safe]
      simp only [Int.add_assoc]
    · have first : checkedAdd start x = none := by
        unfold checkedAdd checked
        exact if_neg safe
      have large : 2^127 ≤ start + x := by
        have lower := bounded.1
        unfold i128 at safe
        omega
      have totalLarge : ¬ (-(2^127) ≤ start + (x + rest.sum) ∧ start + (x + rest.sum) < 2^127) := by omega
      simp [List.foldlM_cons,first,List.sum_cons,totalLarge]
      omega

theorem checkedSum_nonnegative (xs : List Int) (nonnegative : ∀ x ∈ xs, 0 ≤ x) :
    checkedSum xs = if -(2^127) ≤ xs.sum ∧ xs.sum < 2^127 then some xs.sum else none := by
  simpa only [checkedSum,Int.zero_add] using checkedFold_nonnegative xs nonnegative 0 (by decide)

/-- The native total checks the complete recognized allocation list. Its
arithmetic result is independent of map insertion/enumeration order. -/
def allocationTotal (field : ResourceField ResourceAccounts) : Option Int :=
  if allocationsCheck field then checkedSum ((accounts field).map Prod.snd) else none

theorem allocationTotal_iff (field : ResourceField ResourceAccounts) (value : Int) :
    allocationTotal field = some value ↔ validAccounts field ∧
      i128 ((accounts field).map Prod.snd).sum ∧ value = ((accounts field).map Prod.snd).sum := by
  by_cases good : validAccounts field
  · have check : allocationsCheck field = true := (allocationsCheck_iff field).mpr good
    have nonnegative : ∀ x ∈ (accounts field).map Prod.snd, 0 ≤ x := by
      obtain ⟨rows,equal,_,_,valid⟩ := good
      subst field
      rintro x member
      obtain ⟨row,inside,rfl⟩ := List.mem_map.mp member
      exact (valid row inside).2.1
    simp only [allocationTotal,check,if_true,checkedSum_nonnegative _ nonnegative]
    change (if i128 ((accounts field).map Prod.snd).sum then _ else _) = some value ↔ _
    by_cases bound : i128 ((accounts field).map Prod.snd).sum <;> simp [bound,good,eq_comm]
  · have check : allocationsCheck field = false := by
      cases h : allocationsCheck field
      · rfl
      · exact False.elim (good ((allocationsCheck_iff field).mp h))
    simp [allocationTotal,check,good]

theorem empty_allocations_rejected : allocationsCheck (.value []) = false := rfl

theorem malformed_account_rejected : allocationsCheck (.value [("alice",1)]) = false := by decide

def rootCheck (field : ResourceField (List ResourceRoleBinding)) : Bool :=
  match field with
  | .value rows => rows.all (fun role => role.accounts.all accountCheck)
  | _ => false

theorem rootCheck_iff (field : ResourceField (List ResourceRoleBinding)) : rootCheck field = true ↔
    ∃ rows, field = .value rows ∧ ∀ role ∈ rows, ∀ account ∈ role.accounts, accountName account := by
  cases field <;> simp [rootCheck,accountCheck_iff]

def kindCheck (c : ResourceConfig) (a : ResourceFact) : Bool :=
  (a.data.kind == .increment && a.data.selected.verb == c.increment.verb) ||
  (a.data.kind == .decrement && a.data.selected.verb == c.decrement.verb) ||
  (a.data.kind == .transfer && c.transfer.any (fun t => a.data.selected.verb == t.verb)) ||
  (a.data.kind == .transferHeadroom && c.transferHeadroom.any (fun t => a.data.selected.verb == t.verb))

theorem kindCheck_iff (c : ResourceConfig) (a : ResourceFact) : kindCheck c a = true ↔ kindMatches c a := by
  simp [kindCheck,kindMatches,Option.any_eq_true,or_assoc]

/-- Recognized native operation checks: source instance/account, authenticated
from, amount, previous/dependency shape, issuer authority and recipient. -/
def operationCheck (c : ResourceConfig) (op root a : ResourceFact) : Bool :=
  kindCheck c a && decide (a.data.selected.thread = op.data.selected.thread) &&
  decide (a.data.selected.language = op.data.selected.language) &&
  ((accounts op.data.selected.initialAllocations).map Prod.fst).contains a.data.signer &&
  decide (a.data.selected.authenticatedFrom = .value a.data.signer) &&
  (a.data.selected.amountStatus == .recognized) && amountCheck a.data.amount && decide (0 < a.data.amount) &&
  (a.data.selected.previousStatus == .recognized) && a.data.prev.isSome &&
  (a.data.selected.dependenciesStatus == .recognized) && decide a.data.deps.Nodup &&
  a.data.prev.all (fun p => !a.data.deps.contains p) &&
  (a.data.kind != .increment || (issuers c root).contains a.data.signer) &&
  (!(a.data.kind == .transfer || a.data.kind == .transferHeadroom) ||
    ((a.data.selected.recipientStatus == .recognized) &&
      a.data.selected.recipient.any (fun recipient => recipient != a.data.signer &&
        ((accounts op.data.selected.initialAllocations).map Prod.fst).contains recipient)))

theorem operationCheck_iff (c : ResourceConfig) (op root a : ResourceFact) :
    operationCheck c op root a = true ↔ validOperation c op root a := by
  cases kind : a.data.kind <;>
    simp [operationCheck,validOperation,kindCheck,kindMatches,amountCheck,natural64,
      kind,Option.any_eq_true,Option.all_eq_true,List.contains_eq_mem,and_assoc]

/-- Native initialization arithmetic, in branch order. The headroom parser is
not used when no ceiling is configured; the structural headroom check remains
in the initialization validation phase. -/
def initialValue (c : ResourceConfig) (op : ResourceFact) : Option Int := do
  let rights ← allocationTotal op.data.selected.initialAllocations
  let value ← checkedAdd rights c.floor
  match c.ceiling with
  | none => some value
  | some ceiling =>
    if c.floor ≤ ceiling ∧ c.headroomKey.isSome then do
      let space ← allocationTotal op.data.selected.headroomAllocations
      let capacity ← checkedAdd space value
      if capacity = ceiling then some value else none
    else none

theorem initialValue_iff (c : ResourceConfig) (op : ResourceFact) (value : Int) :
    initialValue c op = some value ↔ InitialBudget c op value := by
  cases ceiling : c.ceiling with
  | none =>
    simp [initialValue,InitialBudget,ceiling,Option.bind_eq_some_iff,
      allocationTotal_iff,checkedAdd_iff,and_assoc]
    intro _ _
    constructor
    · rintro ⟨bounded,rfl⟩; exact ⟨rfl,bounded⟩
    · rintro ⟨rfl,bounded⟩; exact ⟨bounded,rfl⟩
  | some cap =>
    simp [initialValue,InitialBudget,ceiling,Option.bind_eq_some_iff,
      allocationTotal_iff,checkedAdd_iff,and_assoc]
    intro _ _
    constructor
    · rintro ⟨bounded,floor,headroom,validSpace,spaceBound,capacityBound,capacity,valueEq⟩
      subst value
      exact ⟨rfl,bounded,floor,headroom,validSpace,spaceBound,capacityBound,capacity⟩
    · rintro ⟨rfl,bounded,floor,headroom,validSpace,spaceBound,capacityBound,capacity⟩
      exact ⟨bounded,floor,headroom,validSpace,spaceBound,capacityBound,capacity,rfl⟩

theorem mutual_keys_iff (left right : List String) :
    (left.all right.contains && right.all left.contains) = true ↔
      ∀ owner, owner ∈ left ↔ owner ∈ right := by
  simp only [Bool.and_eq_true,List.all_eq_true,List.contains_iff]
  constructor
  · rintro ⟨lr,rl⟩ owner
    exact ⟨lr owner,rl owner⟩
  · intro same
    exact ⟨fun owner h => (same owner).mp h,fun owner h => (same owner).mpr h⟩

/-- Equality of the native maps' canonical key lists is equality of these key
sets. Duplicate associations have already failed allocationsCheck. -/
def headroomCheck (c : ResourceConfig) (op : ResourceFact) : Bool :=
  if c.headroomKey.isSome then
    allocationsCheck op.data.selected.headroomAllocations &&
      (((accounts op.data.selected.headroomAllocations).map Prod.fst).all
        ((accounts op.data.selected.initialAllocations).map Prod.fst).contains &&
       ((accounts op.data.selected.initialAllocations).map Prod.fst).all
        ((accounts op.data.selected.headroomAllocations).map Prod.fst).contains)
  else true

theorem headroomCheck_iff (c : ResourceConfig) (op : ResourceFact) : headroomCheck c op = true ↔
    (c.headroomKey.isSome → validAccounts op.data.selected.headroomAllocations ∧
      ∀ owner, owner ∈ (accounts op.data.selected.headroomAllocations).map Prod.fst ↔
        owner ∈ (accounts op.data.selected.initialAllocations).map Prod.fst) := by
  cases key : c.headroomKey <;> simp [headroomCheck,allocationsCheck_iff,key]
  intro _
  constructor
  · rintro ⟨lr,rl⟩ owner
    exact ⟨fun ⟨amount,h⟩ => lr owner amount h,fun ⟨amount,h⟩ => rl owner amount h⟩
  · intro same
    exact ⟨fun owner amount h => (same owner).mp ⟨amount,h⟩,
      fun owner amount h => (same owner).mpr ⟨amount,h⟩⟩

def initializationCheck (c : ResourceConfig) (op root : ResourceFact) : Bool :=
  rootCheck root.data.selected.bindings && (members root).contains op.data.signer &&
  allocationsCheck op.data.selected.initialAllocations &&
  (accounts op.data.selected.initialAllocations).all (fun p => (members root).contains p.1) &&
  (issuers c root).all (fun owner => ((accounts op.data.selected.initialAllocations).map Prod.fst).contains owner) &&
  headroomCheck c op && (initialValue c op).isSome

theorem initializationCheck_iff (c : ResourceConfig) (op root : ResourceFact) :
    initializationCheck c op root = true ↔ validInitial c op root := by
  simp [initializationCheck,validInitial,rootCheck_iff,allocationsCheck_iff,headroomCheck_iff,
    initialValue_iff,Option.isSome_iff_exists,and_assoc]

/-- Native rejection in the initialization phase is exactly the concrete
initialization-certificate condition, with no classifier/persistence premise. -/
theorem initialization_rejection_iff (c : ResourceConfig) (op root : ResourceFact) :
    initializationCheck c op root = false ↔ ¬validInitial c op root := by
  rw [← initializationCheck_iff]
  cases initializationCheck c op root <;> simp

theorem operation_rejection_iff (c : ResourceConfig) (op root a : ResourceFact) :
    operationCheck c op root a = false ↔ ¬validOperation c op root a := by
  rw [← operationCheck_iff]
  cases operationCheck c op root a <;> simp

/-- The native input-validation phases produce accepted finite certificates. -/
theorem initialization_rejection_certificate (c : ResourceConfig) (F : Facts) (op root : ResourceFact)
    (opAccepted : op ∈ F) (rootAccepted : root ∈ F) (opener : initial c op) (parent : rootOf op root)
    (rejected : initializationCheck c op root = false) : Cause c F :=
  .initialization opAccepted rootAccepted opener parent ((initialization_rejection_iff c op root).mp rejected)

theorem operation_rejection_certificate (c : ResourceConfig) (F : Facts) (op root a : ResourceFact)
    (opAccepted : op ∈ F) (rootAccepted : root ∈ F) (accepted : a ∈ F)
    (opener : initial c op) (parent : rootOf op root) (operates : operation c a)
    (rejected : operationCheck c op root a = false) : Cause c F :=
  .malformed opAccepted rootAccepted accepted opener parent operates ((operation_rejection_iff c op root a).mp rejected)

def addIncoming (balance : Int) (ownerAmounts : List Int) : Option Int := do
  let total ← checkedSum ownerAmounts
  checkedAdd balance total

/-- Native local_budgets adds cumulative incoming amounts by owner tip. -/
def groupedIncoming (chunks : List (List Int)) (start : Int) : Option Int :=
  chunks.foldlM addIncoming start

theorem addIncoming_eq (chunk : List Int) (nonnegative : ∀ x ∈ chunk, 0 ≤ x)
    (bounded : i128 chunk.sum) (start : Int) :
    addIncoming start chunk = checkedAdd start chunk.sum := by
  have sum : checkedSum chunk = some chunk.sum := by
    rw [checkedSum_nonnegative chunk nonnegative]
    exact if_pos bounded
  unfold addIncoming
  rw [sum]
  rfl

theorem groupedIncoming_as_totals (chunks : List (List Int))
    (nonnegative : ∀ chunk ∈ chunks, ∀ x ∈ chunk, 0 ≤ x)
    (bounded : ∀ chunk ∈ chunks, i128 chunk.sum) (start : Int) :
    groupedIncoming chunks start = (chunks.map List.sum).foldlM checkedAdd start := by
  induction chunks generalizing start with
  | nil => rfl
  | cons chunk rest ih =>
    simp only [groupedIncoming,List.foldlM_cons,List.map_cons]
    rw [addIncoming_eq chunk (nonnegative chunk (by simp)) (bounded chunk (by simp)) start]
    cases next : checkedAdd start chunk.sum with
    | none => rfl
    | some value =>
      exact ih (fun c hc => nonnegative c (by simp [hc])) (fun c hc => bounded c (by simp [hc])) value

/-- The checked native grouped-tip sum and a fact-by-fact checked cone sum
agree, including overflow and a negative starting budget. Partition is supplied
by the owner-prefix/tip invariant, not by an assumption about the result. -/
theorem groupedIncoming_refinement (chunks : List (List Int)) (amounts : List Int)
    (partition : chunks.flatten.Perm amounts)
    (nonnegative : ∀ chunk ∈ chunks, ∀ x ∈ chunk, 0 ≤ x)
    (bounded : ∀ chunk ∈ chunks, i128 chunk.sum) (start : Int) (startBound : i128 start) :
    groupedIncoming chunks start = amounts.foldlM checkedAdd start := by
  have totalsPositive : ∀ total ∈ chunks.map List.sum, 0 ≤ total := by
    intro total member
    obtain ⟨chunk,hc,rfl⟩ := List.mem_map.mp member
    exact sum_nonnegative chunk (nonnegative chunk hc)
  have amountsPositive : ∀ amount ∈ amounts, 0 ≤ amount := by
    intro amount member
    have flattened := partition.mem_iff.mpr member
    obtain ⟨chunk,hc,inside⟩ := List.mem_flatten.mp flattened
    exact nonnegative chunk hc amount inside
  rw [groupedIncoming_as_totals chunks nonnegative bounded start,
    checkedFold_nonnegative _ totalsPositive start startBound,
    checkedFold_nonnegative amounts amountsPositive start startBound]
  have sums : (chunks.map List.sum).sum = amounts.sum := List.sum_flatten.symm.trans (StateKernelAggregates.sum_perm partition)
  rw [sums]

end CBCL.StateResourceNative
