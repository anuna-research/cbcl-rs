import LeanCbcl.StateContext
import LeanCbcl.CheckpointEvidence

/-! Resource faults as finite, independently checkable certificates. The input
boundary is the immutable typed ResourceData projection, not a classifier or a
persistence axiom. A certificate names a dependency-closed cone: missing evidence
in another component cannot invalidate it. Native worklist/certificate refinement
is a separate obligation; this module does not assert that refinement by fiat. -/
namespace CBCL.StateResource
open State StateLift StateLVar CheckpointEvidence

/-- The accepted list of typed resource facts. -/
abbrev Facts := List ResourceFact

/-- Membership inclusion between fact lists. -/
def Included (A B : List α) : Prop := ∀ a ∈ A, a ∈ B

/-- The signed 128-bit range used by checked native arithmetic. -/
def i128 (n : Int) : Prop := -(2^127) ≤ n ∧ n < 2^127

instance (n : Int) : Decidable (i128 n) :=
  inferInstanceAs (Decidable (-(2^127) ≤ n ∧ n < 2^127))

/-- The nonnegative portion of the signed 64-bit amount range. -/
def natural64 (n : Int) : Prop := 0 ≤ n ∧ n < 2^63

/-- Return an integer only when it fits the native signed 128-bit range. -/
def checked (n : Int) : Option Int := if -(2^127) ≤ n ∧ n < 2^127 then some n else none

/-- Native amount recognition is i64. A successful native slice allocation
has at most isize::MAX elements even when each element occupies only one byte;
account lists are bounded by the installed u32 max-list. These are explicit
representation premises, not an assumption that an overflowing sum persists. -/
theorem aggregate_i128_bound (n accounts : Int)
    (nodesNonnegative : 0 ≤ n) (nodesBound : n ≤ 2^63 - 1)
    (accountsNonnegative : 0 ≤ accounts) (accountsBound : accounts ≤ 2^32 - 1)
    (value : Int)
    (lower : -(n + accounts + 1) * (2^63 - 1) ≤ value)
    (upper : value ≤ (n + accounts + 1) * (2^63 - 1)) : i128 value := by
  unfold i128
  simp only [show (2: Int)^63 = 9223372036854775808 from rfl,
    show (2: Int)^32 = 4294967296 from rfl,
    show (2: Int)^127 = 170141183460469231731687303715884105728 from rfl] at *
  omega

/-- Bounds for a signed fold, including every intermediate prefix. Each act
contributes at most once to a selected account/total. -/
theorem sum_bounds (bound : Int) (xs : List Int)
    (recognized : ∀ x ∈ xs, -bound ≤ x ∧ x ≤ bound) :
    -((xs.length : Int) * bound) ≤ xs.sum ∧ xs.sum ≤ (xs.length : Int) * bound := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
    have hx := recognized x (by simp)
    have tail := ih (fun y hy => recognized y (by simp [hy]))
    simp only [List.sum_cons,List.length_cons,Int.natCast_add,Int.natCast_one,Int.add_mul,Int.one_mul]
    omega

/-- Checked signed 128-bit addition. -/
def checkedAdd (a b : Int) : Option Int := checked (a + b)

/-- Checked signed 128-bit subtraction. -/
def checkedSub (a b : Int) : Option Int := checked (a - b)

/-- Extract account allocations, using an empty list for an absent or malformed field. -/
def accounts : ResourceField ResourceAccounts → ResourceAccounts
  | .value xs => xs
  | _ => []

/-- Extract role bindings, using an empty list for an absent or malformed field. -/
def bindings : ResourceField (List ResourceRoleBinding) → List ResourceRoleBinding
  | .value xs => xs
  | _ => []

/-- Look up an account allocation, defaulting to zero. -/
def allocation (xs : ResourceAccounts) (owner : String) : Int :=
  (xs.lookup owner).getD 0

/-- A nonempty account identifier beginning with `@`. -/
def accountName (name : String) : Prop := name.toList.head? = some '@' ∧ 1 < name.length

instance (name : String) : Decidable (accountName name) :=
  inferInstanceAs (Decidable (name.toList.head? = some '@' ∧ 1 < name.length))

/-- Well-formed, nonempty, uniquely named account allocations. -/
def validAccounts (field : ResourceField ResourceAccounts) : Prop :=
  ∃ xs, field = .value xs ∧ xs ≠ [] ∧ (xs.map Prod.fst).Nodup ∧
    ∀ x ∈ xs, accountName x.1 ∧ natural64 x.2

/-- The accounts named by the root role bindings. -/
def members (root : ResourceFact) : List String :=
  (bindings root.data.selected.bindings).flatMap ResourceRoleBinding.accounts

/-- The accounts authorized to issue resources. -/
def issuers (c : ResourceConfig) (root : ResourceFact) : List String :=
  ((bindings root.data.selected.bindings).filter (fun r => r.role == c.issuerRole)).flatMap ResourceRoleBinding.accounts

/-- Whether a fact selects the configured resource opener verb. -/
def initial (c : ResourceConfig) (a : ResourceFact) : Prop :=
  a.data.selected.verb = c.initialVerb

/-- Whether a fact selects one of the configured resource operation verbs. -/
def operation (c : ResourceConfig) (a : ResourceFact) : Prop :=
  a.data.selected.verb = c.increment.verb ∨ a.data.selected.verb = c.decrement.verb ∨
  (∃ t, c.transfer = some t ∧ a.data.selected.verb = t.verb) ∨
  (∃ t, c.transferHeadroom = some t ∧ a.data.selected.verb = t.verb)

/-- The previous and dependency addresses cited by a fact. -/
def links (a : ResourceFact) : List Nat := a.data.prev.toList ++ a.data.deps

/-- Whether a root fact is the opener's referenced thread root. -/
def rootOf (op root : ResourceFact) : Prop := op.data.selected.predecessors = [root.id]

/-- Exact checked initialization arithmetic, including the native allocation
parser and the intermediate totals before adding the floor or ceiling. -/
def InitialBudget (c : ResourceConfig) (op : ResourceFact) (value : Int) : Prop :=
  validAccounts op.data.selected.initialAllocations ∧
  i128 (((accounts op.data.selected.initialAllocations).map Prod.snd).sum) ∧
  value = ((accounts op.data.selected.initialAllocations).map Prod.snd).sum + c.floor ∧
  i128 value ∧
  ∀ ceiling, c.ceiling = some ceiling → c.floor ≤ ceiling ∧ c.headroomKey.isSome ∧
    validAccounts op.data.selected.headroomAllocations ∧
    i128 (((accounts op.data.selected.headroomAllocations).map Prod.snd).sum) ∧
    i128 (((accounts op.data.selected.headroomAllocations).map Prod.snd).sum + value) ∧
    ((accounts op.data.selected.headroomAllocations).map Prod.snd).sum + value = ceiling

/-- The resource initializer validity conditions. -/
def validInitial (c : ResourceConfig) (op root : ResourceFact) : Prop :=
  (∃ xs, root.data.selected.bindings = .value xs ∧
    ∀ role ∈ xs, ∀ account ∈ role.accounts, accountName account) ∧
  op.data.signer ∈ members root ∧ validAccounts op.data.selected.initialAllocations ∧
  (∀ p ∈ accounts op.data.selected.initialAllocations, p.1 ∈ members root) ∧
  (∀ owner ∈ issuers c root, owner ∈ (accounts op.data.selected.initialAllocations).map Prod.fst) ∧
  (c.headroomKey.isSome → validAccounts op.data.selected.headroomAllocations ∧
    ∀ owner, owner ∈ (accounts op.data.selected.headroomAllocations).map Prod.fst ↔
      owner ∈ (accounts op.data.selected.initialAllocations).map Prod.fst) ∧
  ∃ value, InitialBudget c op value

/-- Whether a typed operation matches its installed operation kind. -/
def kindMatches (c : ResourceConfig) (a : ResourceFact) : Prop :=
  (a.data.kind = .increment ∧ a.data.selected.verb = c.increment.verb) ∨
  (a.data.kind = .decrement ∧ a.data.selected.verb = c.decrement.verb) ∨
  (a.data.kind = .transfer ∧ ∃ t, c.transfer = some t ∧ a.data.selected.verb = t.verb) ∨
  (a.data.kind = .transferHeadroom ∧ ∃ t, c.transferHeadroom = some t ∧ a.data.selected.verb = t.verb)

/-- The configured resource operation validity conditions. -/
def validOperation (c : ResourceConfig) (op root a : ResourceFact) : Prop :=
  kindMatches c a ∧ a.data.selected.thread = op.data.selected.thread ∧
  a.data.selected.language = op.data.selected.language ∧
  a.data.signer ∈ (accounts op.data.selected.initialAllocations).map Prod.fst ∧
  a.data.selected.authenticatedFrom = .value a.data.signer ∧
  a.data.selected.amountStatus = .recognized ∧ natural64 a.data.amount ∧ 0 < a.data.amount ∧
  a.data.selected.previousStatus = .recognized ∧ a.data.prev.isSome ∧
  a.data.selected.dependenciesStatus = .recognized ∧ a.data.deps.Nodup ∧
  (∀ p, a.data.prev = some p → p ∉ a.data.deps) ∧
  (a.data.kind = .increment → a.data.signer ∈ issuers c root) ∧
  (a.data.kind = .transfer ∨ a.data.kind = .transferHeadroom →
    a.data.selected.recipientStatus = .recognized ∧
    ∃ recipient, a.data.selected.recipient = some recipient ∧ recipient ≠ a.data.signer ∧
      recipient ∈ (accounts op.data.selected.initialAllocations).map Prod.fst)

/-- Escrow reachability uses the selected resource links, never protocol edges. -/
inductive Reaches (F : Facts) : ResourceFact → ResourceFact → Prop where
  | refl {a} : Reaches F a a
  | step {a b d} : b ∈ F → b.id ∈ links a → Reaches F b d → Reaches F a d

/-- Every referenced identity is supplied, except the designated opener. Every
member actually belongs to the operation's cone, so unrelated funding cannot
be invented by a certificate. -/
def ExactCone (op a : ResourceFact) (C : Facts) : Prop :=
  a ∈ C ∧ (C.map Fact.id).Nodup ∧
  (∀ n ∈ C, ∀ id ∈ links n, id = op.id ∨ ∃ p ∈ C, p.id = id) ∧
  ∀ n ∈ C, Reaches C a n

/-- Following immutable escrow links in a closed certificate cannot discover
new funding in a different closed certificate. Identity consistency comes from
the accepted content-addressed store, not from arithmetic. -/
theorem reaches_in_closed {C D : Facts} {op a n : ResourceFact}
    (closedD : ∀ node ∈ D, ∀ id ∈ links node, id = op.id ∨ ∃ p ∈ D, p.id = id)
    (excludes : ∀ node ∈ C, node.id ≠ op.id)
    (identity : ∀ x ∈ C, ∀ y ∈ D, x.id = y.id → x = y)
    (reach : Reaches C a n) (accepted : a ∈ D) : n ∈ D := by
  induction reach with
  | refl => exact accepted
  | @step a b d member edge rest ih =>
    apply ih
    rcases closedD a accepted b.id edge with opener | ⟨p,hp,equal⟩
    · exact False.elim (excludes b member opener)
    · have same := identity b member p hp equal.symm
      simpa [same] using hp

/-- Complete cones for one act agree as sets. This is the substantive locality
bridge: extension cannot change its observed incoming funding or own prefix. -/
theorem exact_cone_unique {C D : Facts} {op a : ResourceFact}
    (left : ExactCone op a C) (right : ExactCone op a D)
    (excludeC : ∀ node ∈ C, node.id ≠ op.id)
    (excludeD : ∀ node ∈ D, node.id ≠ op.id)
    (identity : ∀ x ∈ C, ∀ y ∈ D, x.id = y.id → x = y) :
    FactSetEq C D := by
  intro n
  constructor
  · intro hn
    exact reaches_in_closed right.2.2.1 excludeC identity (left.2.2.2 n hn) right.1
  · intro hn
    exact reaches_in_closed left.2.2.1 excludeD
      (fun x hx y hy equal => (identity y hy x hx equal.symm).symm)
      (right.2.2.2 n hn) left.1

/-- The owner's immutable previous-link prefix, in issuance order. -/
def OwnerChain (owner : String) : Nat → Facts → Prop
  | _, [] => True
  | previous, node :: rest => node.data.signer = owner ∧ node.data.prev = some previous ∧
      OwnerChain owner node.id rest

/-- Nonforking ownership makes any two observed prefixes comparable. Native
sequence arbitration is therefore prefix union, rather than arbitrary LWW. -/
theorem owner_chains_comparable (owner : String) (F : Facts)
    (nonforking : ∀ x ∈ F, ∀ y ∈ F, x.data.signer = owner → y.data.signer = owner →
      x.data.prev = y.data.prev → x = y)
    {previous : Nat} {C D : Facts} (left : OwnerChain owner previous C)
    (right : OwnerChain owner previous D) (insideC : Included C F) (insideD : Included D F) :
    C.IsPrefix D ∨ D.IsPrefix C := by
  induction C generalizing previous D with
  | nil => exact Or.inl ⟨D,rfl⟩
  | cons x rest ih =>
    cases D with
    | nil => exact Or.inr ⟨x :: rest,rfl⟩
    | cons y tail =>
      have same := nonforking x (insideC x (by simp)) y (insideD y (by simp))
        left.1 right.1 (left.2.1.trans right.2.1.symm)
      subst y
      rcases ih left.2.2 right.2.2
          (fun a ha => insideC a (by simp [ha]))
          (fun a ha => insideD a (by simp [ha])) with ⟨suffix,equal⟩ | ⟨suffix,equal⟩
      · exact Or.inl ⟨suffix,by simp [equal]⟩
      · exact Or.inr ⟨suffix,by simp [equal]⟩

theorem longer_owner_prefix (owner : String) (F : Facts)
    (nonforking : ∀ x ∈ F, ∀ y ∈ F, x.data.signer = owner → y.data.signer = owner →
      x.data.prev = y.data.prev → x = y)
    {previous : Nat} {C D : Facts} (left : OwnerChain owner previous C)
    (right : OwnerChain owner previous D) (insideC : Included C F) (insideD : Included D F)
    (length : C.length ≤ D.length) : C.IsPrefix D := by
  rcases owner_chains_comparable owner F nonforking left right insideC insideD with pre | ⟨suffix,equal⟩
  · exact pre
  · have lens := congrArg List.length equal
    simp only [List.length_append] at lens
    have empty : suffix = [] := by
      cases suffix with
      | nil => rfl
      | cons x xs => simp only [List.length_cons] at lens; omega
    subst suffix
    simp only [List.append_nil] at equal
    subst C
    exact ⟨[],by simp⟩

/-- Once native sequence is identified with chain length, its comparison
selects this prefix. The selected prefix covers both inputs and introduces no
fact outside them; the sequence/length bridge is a refinement obligation. -/
def mergeOwnerTips (C D : Facts) : Facts := if C.length < D.length then D else C

theorem merge_owner_tips_union (owner : String) (F : Facts)
    (nonforking : ∀ x ∈ F, ∀ y ∈ F, x.data.signer = owner → y.data.signer = owner →
      x.data.prev = y.data.prev → x = y)
    {previous : Nat} {C D : Facts} (left : OwnerChain owner previous C)
    (right : OwnerChain owner previous D) (insideC : Included C F) (insideD : Included D F) :
    ∀ node, node ∈ mergeOwnerTips C D ↔ node ∈ C ∨ node ∈ D := by
  intro node
  unfold mergeOwnerTips
  split
  · rename_i length
    have pre := longer_owner_prefix owner F nonforking left right insideC insideD (by omega)
    exact ⟨fun h => Or.inr h,fun h => h.elim (fun h => pre.subset h) id⟩
  · rename_i length
    have pre := longer_owner_prefix owner F nonforking right left insideD insideC (by omega)
    exact ⟨fun h => Or.inl h,fun h => h.elim id (fun h => pre.subset h)⟩

/-- The effect of a fact on one account's resource rights. -/
def rightsDelta (owner : String) (a : ResourceFact) : Int :=
  (if a.data.signer = owner then
    match a.data.kind with
    | .increment => a.data.amount
    | .decrement | .transfer => -a.data.amount
    | _ => 0
   else 0) +
  (if a.data.kind = .transfer ∧ a.data.selected.recipient = some owner then a.data.amount else 0)

/-- The effect of a fact on one account's bounded-counter headroom. -/
def headroomDelta (owner : String) (a : ResourceFact) : Int :=
  (if a.data.signer = owner then
    match a.data.kind with
    | .decrement => a.data.amount
    | .increment | .transferHeadroom => -a.data.amount
    | _ => 0
   else 0) +
  (if a.data.kind = .transferHeadroom ∧ a.data.selected.recipient = some owner then a.data.amount else 0)

/-- Canonical fact order is explicit for checked intermediate arithmetic. -/
def ordered (C : Facts) : Facts := C.mergeSort (fun a b => a.id ≤ b.id)

theorem ordered_of_perm {C D : Facts} (perm : C.Perm D)
    (identity : ∀ x ∈ C, ∀ y ∈ D, x.id = y.id → x = y) : ordered C = ordered D := by
  have sorted : ∀ F : Facts, (ordered F).Pairwise (fun a b => a.id ≤ b.id) := by
    intro F
    have trans : ∀ a b d : ResourceFact, decide (a.id ≤ b.id) = true →
        decide (b.id ≤ d.id) = true → decide (a.id ≤ d.id) = true := by
      intro a b d ab bd
      exact decide_eq_true (Nat.le_trans (of_decide_eq_true ab) (of_decide_eq_true bd))
    have total : ∀ a b : ResourceFact, (decide (a.id ≤ b.id) || decide (b.id ≤ a.id)) = true := by
      intro a b
      simpa only [Bool.or_eq_true,decide_eq_true_eq] using Nat.le_total a.id b.id
    simpa only [ordered,decide_eq_true_eq] using List.pairwise_mergeSort trans total F
  apply List.Perm.eq_of_pairwise (le := fun a b => a.id ≤ b.id) ?_ (sorted C) (sorted D)
    ((List.mergeSort_perm C _).trans (perm.trans (List.mergeSort_perm D _).symm))
  intro a b ha hb ab ba
  exact identity a (List.mem_mergeSort.mp ha) b (List.mem_mergeSort.mp hb) (Nat.le_antisymm ab ba)

/-- Fold amounts using checked native arithmetic. -/
def checkedSum (xs : List Int) : Option Int := xs.foldlM checkedAdd 0

/-- The cumulative total of one owner's operations. -/
def ownTotal (C : Facts) (owner : String) (kind : ResourceKind) : Option Int :=
  checkedSum (((ordered C).filter (fun a => a.data.signer == owner && a.data.kind == kind)).map (fun a => a.data.amount))

/-- Checked component arithmetic: initial + credits - debits - outgoing,
then incoming transfers. The model sums incoming facts by identity; equivalence
to native grouped owner-tip summaries is a separate refinement obligation.
Every intermediate i128 check and the usize sequence range is retained. -/
def localBudget (op a : ResourceFact) (C : Facts) (headroom : Bool) : Option Int := do
  let past := C.filter (fun n => n.id != a.id)
  let credited ← ownTotal past a.data.signer .increment
  let debited ← ownTotal past a.data.signer .decrement
  let kind := if headroom then ResourceKind.transferHeadroom else ResourceKind.transfer
  let outgoing ← ownTotal past a.data.signer kind
  let initial := allocation (accounts (if headroom then op.data.selected.headroomAllocations
    else op.data.selected.initialAllocations)) a.data.signer
  let raised ← checkedAdd initial (if headroom then debited else credited)
  let lowered ← checkedSub raised (if headroom then credited else debited)
  let available ← checkedSub lowered outgoing
  let incoming := (ordered past).filter (fun n =>
    n.data.signer != a.data.signer && n.data.kind == kind && n.data.selected.recipient == some a.data.signer)
  incoming.foldlM (fun balance n => checkedAdd balance n.data.amount) available

theorem localBudget_perm (op a : ResourceFact) {C D : Facts} (perm : C.Perm D)
    (identity : ∀ x ∈ C, ∀ y ∈ D, x.id = y.id → x = y) (headroom : Bool) :
    localBudget op a C headroom = localBudget op a D headroom := by
  have past := ordered_of_perm (perm.filter (fun n => n.id != a.id))
    (fun x hx y hy same => identity x (List.mem_filter.mp hx).1 y (List.mem_filter.mp hy).1 same)
  simp only [localBudget,ownTotal,past]

/-- The checked budget of an act is unchanged in another exact closed cone.
No unbounded-Int replacement of the checked arithmetic is used here. -/
theorem localBudget_cone_unique {C D : Facts} {op a : ResourceFact}
    (left : ExactCone op a C) (right : ExactCone op a D)
    (excludeC : ∀ node ∈ C, node.id ≠ op.id)
    (excludeD : ∀ node ∈ D, node.id ≠ op.id)
    (identity : ∀ x ∈ C, ∀ y ∈ D, x.id = y.id → x = y) (headroom : Bool) :
    localBudget op a C headroom = localBudget op a D headroom := by
  have nodupC : C.Nodup := List.Pairwise.of_map Fact.id
    (fun x y different equal => different (congrArg Fact.id equal)) left.2.1
  have nodupD : D.Nodup := List.Pairwise.of_map Fact.id
    (fun x y different equal => different (congrArg Fact.id equal)) right.2.1
  exact localBudget_perm op a
    ((List.perm_ext_iff_of_nodup nodupC nodupD).mpr (exact_cone_unique left right excludeC excludeD identity))
    identity headroom

/-- A certificate of invalid owner-summary arithmetic. -/
def summaryFault (a : ResourceFact) (C : Facts) : Prop :=
  let ownCount := (C.filter (fun n => n.data.signer == a.data.signer)).length
  -- This model targets the repository's 64-bit native profile.
  2^64 ≤ ownCount ∨ ownTotal C a.data.signer .increment = none ∨
    ownTotal C a.data.signer .decrement = none ∨
    ∃ recipient, checkedSum (((ordered C).filter (fun n =>
      n.data.signer == a.data.signer && n.data.kind == a.data.kind &&
      n.data.selected.recipient == some recipient)).map (fun n => n.data.amount)) = none

/-- A certificate that an operation exceeds its available causal budget. -/
def budgetFault (c : ResourceConfig) (op a : ResourceFact) (C : Facts) : Prop :=
  let usesHeadroom := a.data.kind = .increment ∨ a.data.kind = .transferHeadroom
  summaryFault a C ∨ localBudget op a C false = none ∨
  (c.headroomKey.isSome ∧ localBudget op a C true = none) ∨
  (if usesHeadroom then c.headroomKey.isSome else True) ∧
    ∃ budget, localBudget op a C (decide usesHeadroom) = some budget ∧ budget < a.data.amount

/-- Concrete certificate grammar, rather than a supplied classifier. Each
constructor reads only immutable finite support. -/
inductive Cause (c : ResourceConfig) (F : Facts) : Prop where
  | unsupported (bad : c.ownership = .collective ∨ ∃ p, c.certification = .quorum p) : Cause c F
  | openers {a b} (ha : a ∈ F) (hb : b ∈ F) (ia : initial c a) (ib : initial c b)
      (different : a.id ≠ b.id) : Cause c F
  | openerArity {op} (h : op ∈ F) (i : initial c op)
      (bad : op.data.selected.predecessors.length ≠ 1) : Cause c F
  | initialization {op root} (ho : op ∈ F) (hr : root ∈ F)
      (i : initial c op) (r : rootOf op root) (bad : ¬validInitial c op root) : Cause c F
  | malformed {op root a} (ho : op ∈ F) (hr : root ∈ F) (ha : a ∈ F)
      (i : initial c op) (r : rootOf op root) (operation : operation c a)
      (bad : ¬validOperation c op root a) : Cause c F
  | fork {op root a b} (ho : op ∈ F) (hr : root ∈ F) (i : initial c op)
      (r : rootOf op root) (ha : a ∈ F) (hb : b ∈ F) (oa : operation c a) (ob : operation c b)
      (owner : a.data.signer = b.data.signer) (previous : a.data.prev = b.data.prev)
      (different : a.id ≠ b.id) : Cause c F
  | foreign {op root a b} (ho : op ∈ F) (hr : root ∈ F) (r : rootOf op root)
      (ha : a ∈ F) (hb : b ∈ F) (i : initial c op) (oa : operation c a) (link : b.id ∈ links a)
      (bad : b.id ≠ op.id ∧ (¬operation c b ∨
        (a.data.prev = some b.id ∧ a.data.signer ≠ b.data.signer))) : Cause c F
  | cycle {op root a b C} (ho : op ∈ F) (hr : root ∈ F) (i : initial c op)
      (r : rootOf op root) (inside : Included C F) (ops : ∀ n ∈ C, operation c n)
      (ha : a ∈ C) (hb : b ∈ C) (edge : b.id ∈ links a)
      (back : Reaches C b a) : Cause c F
  | budget {op root a C} (ho : op ∈ F) (hr : root ∈ F)
      (i : initial c op) (r : rootOf op root) (valid : validInitial c op root)
      (inside : Included C F) (cone : ExactCone op a C)
      (ops : ∀ n ∈ C, operation c n ∧ validOperation c op root n)
      (bad : budgetFault c op a C) : Cause c F

/-- An observation faults iff an accepted finite support checks as a cause.
The cause carries its closed cone; no global completeness premise is needed. -/
def Fault (c : ResourceConfig) (decode : Act → ResourceData) (A : List Act) : Prop :=
  ∃ support : List Act, Included support A ∧ Cause c (project decode support)

/-- Whether a fact contributes to the resource configuration. -/
def relevant (c : ResourceConfig) (a : ResourceFact) : Prop :=
  initial c a ∨ operation c a ∨ a.data.selected.bindings ≠ .absent

/-- Whether an address occurs among the fact's references. -/
def cited (a : ResourceFact) (id : Nat) : Prop :=
  id ∈ a.data.selected.predecessors ∨ id ∈ links a

/-- Match the contextual certificate convention: all resource facts and
accepted cited context, not just the first diagnostic's minimal blame.
Unsupported native profiles retain their history-independent empty fault. -/
def evidence (c : ResourceConfig) (decode : Act → ResourceData) (A : List Act) : Lattice.Set Nat :=
  fun id => ¬(c.ownership = .collective ∨ ∃ p, c.certification = .quorum p) ∧
    ∃ a ∈ A, a.addr = id ∧
    (relevant c ⟨a.addr, decode a⟩ ∨
      ∃ b ∈ A, relevant c ⟨b.addr, decode b⟩ ∧ cited ⟨b.addr, decode b⟩ id)

/-- Read the independently checkable resource fault evidence. -/
noncomputable def faultRead (c : ResourceConfig) (decode : Act → ResourceData)
    (A : List Act) : Option (Lattice.Set Nat) := by
  classical
  exact if Fault c decode A then some (evidence c decode A) else none

theorem unsupported_fault (c : ResourceConfig) (decode : Act → ResourceData) (A : List Act)
    (bad : c.ownership = .collective ∨ ∃ p, c.certification = .quorum p) :
    faultRead c decode A = some (evidence c decode A) := by
  classical
  have cause : Fault c decode A := ⟨[],by simp [Included],Cause.unsupported bad⟩
  simp [faultRead,cause]

theorem unsupported_empty_evidence (c : ResourceConfig) (decode : Act → ResourceData) (A : List Act)
    (bad : c.ownership = .collective ∨ ∃ p, c.certification = .quorum p) :
    evidence c decode A = ∅ := by
  funext id
  apply propext
  constructor
  · intro ⟨supported,_⟩
    exact False.elim (supported bad)
  · intro impossible
    exact False.elim impossible

theorem fault_growth (c : ResourceConfig) (decode : Act → ResourceData) {A B : List Act}
    (growth : Included A B) (fault : Fault c decode A) : Fault c decode B := by
  obtain ⟨support, inside, cause⟩ := fault
  exact ⟨support, fun a ha => growth a (inside a ha), cause⟩

theorem fault_setEq (c : ResourceConfig) (decode : Act → ResourceData) {A B : List Act}
    (same : SetEq A B) : Fault c decode A ↔ Fault c decode B :=
  ⟨fault_growth c decode (fun a ha => (same a).mp ha),
   fault_growth c decode (fun a ha => (same a).mpr ha)⟩

theorem evidence_growth (c : ResourceConfig) (decode : Act → ResourceData) {A B : List Act}
    (growth : Included A B) : ∀ id ∈ evidence c decode A, id ∈ evidence c decode B := by
  rintro id ⟨supported,a, ha, address, relevantA | ⟨b, hb, relevantB, link⟩⟩
  · exact ⟨supported,a, growth a ha, address, Or.inl relevantA⟩
  · exact ⟨supported,a, growth a ha, address, Or.inr ⟨b, growth b hb, relevantB, link⟩⟩

theorem evidence_setEq (c : ResourceConfig) (decode : Act → ResourceData) {A B : List Act}
    (same : SetEq A B) : evidence c decode A = evidence c decode B := by
  funext id
  exact propext ⟨evidence_growth c decode (fun a ha => (same a).mp ha) id,
    evidence_growth c decode (fun a ha => (same a).mpr ha) id⟩

theorem faultRead_setEq (c : ResourceConfig) (decode : Act → ResourceData) {A B : List Act}
    (same : SetEq A B) : faultRead c decode A = faultRead c decode B := by
  classical
  simp only [faultRead, fault_setEq c decode same, evidence_setEq c decode same]

theorem faultRead_persists (c : ResourceConfig) (decode : Act → ResourceData) {A B : List Act}
    (growth : Included A B) {e : Lattice.Set Nat} (fault : faultRead c decode A = some e) :
    ∃ enlarged, faultRead c decode B = some enlarged ∧ ∀ id ∈ e, id ∈ enlarged := by
  classical
  unfold faultRead at fault
  split at fault
  · rename_i cause
    have equal : evidence c decode A = e := Option.some.inj fault
    refine ⟨evidence c decode B, by simp [faultRead, fault_growth c decode growth cause], ?_⟩
    rw [← equal]
    exact evidence_growth c decode growth
  · contradiction

/-- Every address in a returned witness has an accepted act, so the complete
contextual witness is finite even though the evidence representation is a set. -/
theorem evidence_accepted (c : ResourceConfig) (decode : Act → ResourceData) (A : List Act)
    {id : Nat} (member : id ∈ evidence c decode A) : id ∈ A.map Act.addr := by
  obtain ⟨_, a, ha, rfl, _⟩ := member
  exact List.mem_map.mpr ⟨a, ha, rfl⟩

open StateKernelDelivery AdmissionStratification

theorem eventual_resource_fault {adm : Admission} {auth : Act → Prop} {H : ValidHistory adm}
    (left right : Replica adm auth H) (c : ResourceConfig) (decode : Act → ResourceData)
    (atTime : Nat) {e : Lattice.Set Nat}
    (fault : faultRead c decode (left.run atTime).accepted = some e) :
    ∃ t, ∀ n, t ≤ n → ∃ enlarged,
      faultRead c decode (right.run n).accepted = some enlarged ∧ ∀ id ∈ e, id ∈ enlarged := by
  obtain ⟨t, all⟩ := witness_dissemination left right (left.run atTime).accepted atTime (by simp)
  exact ⟨t, fun n hn => faultRead_persists c decode (all n hn) fault⟩

end CBCL.StateResource
