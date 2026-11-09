import Batteries.Tactic.Lint
import LeanCbcl.State
import LeanCbcl.Lattice.Store
import LeanCbcl.HlcRegister
import LeanCbcl.StateKernelSemantics

/-!
# SPEC-038 Causal Lattice Observation Kernel (CLOK) — the lift theorem (REQ-3800, REQ-3801)

Every state field is a *term*: a selector on accepted acts, a per-act
*contribution* `g : Act → L` into a bounded join-semilattice *carrier* `L`,
the *lift* `A ↦ ⋁_{a ∈ A} g a`, and a *display* from the carrier to the
rendered value (SPEC-038 Vocabulary, CON-3800). The R7 fold of SPEC-019 is
the lift followed by the display.

## The lift theorem

`lift g A = A.foldl (fun acc a => acc ⊔ g a) ⊥`. For any contribution `g`
into any carrier,

* `lift_setEq` — equal accepted sets give equal lifts: the lift is order
  independent and duplicate insensitive. No `NodupAddr` is needed: order
  independence is commutativity and associativity of `⊔`, duplicate
  insensitivity is its idempotence (REQ-3801).
* `lift_append` — `lift g (A ++ B) = lift g A ⊔ lift g B`, the
  join-homomorphism law of REQ-3800.

Proved once, generically; the per-head invariance conjuncts of
`State.fold_perm_invariant` are then corollaries (`fold_perm_invariant_lift`),
each head being a display of a lift with a specific `g`.

## Correspondence limits

The address-ordered `Chain` and the original `State` head corollaries below
retain that module's historical semantics. Current HLC arbitration is proved
separately by `HlcLift` and the `hlc_*_invariant` corollaries, using typed
clock-recognition evidence and `HlcRegister`'s lexicographic picker. The wire
parser and order-preserving signer-rank mapping remain outside this model.
The current conflict-aware domain selector is `initialDomain`; the older
`actsDom` result is retained only to recover the historical `State` theorem.

## Carriers

Mirrors `crates/cbcl-core/src/lattice.rs` (`L`, `Contribute`, `Sole`):
`Bool` under `or`; `FinSet α` (a finite set as the quotient of lists by
membership) under union, for addresses, values and keyed amounts; `Chain`,
the greatest contribution by address, with a tie between different values a
conflict (`Rust` never ties: addresses are unique); `Sole`, the `initial`
carrier of ADR-3803 (`⊥`, exactly one, or `⊤` with evidence); products; and
`WithTop`, which adjoins the conflict top of ADR-3803 to any carrier that,
like a finite set, has none of its own.

The join-semilattice class `Lattice.JoinSemiLattice` is reused from
`Lattice/Store.lean`; `JoinSemilatticeBot` adds the bottom the lift starts
from, `BoundedJoinSemilattice` the top.
-/

namespace CBCL
namespace StateLift

open State

/-! ## Carriers -/

/-- A join-semilattice with a bottom: the seed of a lift (REQ-3801, `σ := ⊥`). -/
class JoinSemilatticeBot (α : Type u) extends Lattice.JoinSemiLattice α where
  /-- The bottom element: the value of a field over the empty accepted set. -/
  bot : α
  /-- Bottom is the identity of join. -/
  bot_join : ∀ a : α, join bot a = a

/-- A bounded join-semilattice: a bottom and a conflict top (ADR-3803). -/
class BoundedJoinSemilattice (α : Type u) extends JoinSemilatticeBot α where
  /-- The top element: conflict. -/
  top : α
  /-- Top absorbs. -/
  join_top : ∀ a : α, join a top = top

@[inherit_doc] scoped notation "⊥" => JoinSemilatticeBot.bot
@[inherit_doc] scoped notation "⊤" => BoundedJoinSemilattice.top

section Laws

variable {L : Type u} [JoinSemilatticeBot L]

theorem join_assoc (a b c : L) : a ⊔ b ⊔ c = a ⊔ (b ⊔ c) :=
  Lattice.JoinSemiLattice.join_assoc a b c

theorem join_comm (a b : L) : a ⊔ b = b ⊔ a := Lattice.JoinSemiLattice.join_comm a b

theorem join_idem (a : L) : a ⊔ a = a := Lattice.JoinSemiLattice.join_idem a

theorem bot_join (a : L) : ⊥ ⊔ a = a := JoinSemilatticeBot.bot_join a

theorem join_bot (a : L) : a ⊔ ⊥ = a := by rw [join_comm, bot_join]

theorem join_left_comm (a b c : L) : a ⊔ (b ⊔ c) = b ⊔ (a ⊔ c) := by
  rw [← join_assoc, join_comm a b, join_assoc]

theorem join_top {L : Type u} [BoundedJoinSemilattice L] (a : L) : a ⊔ ⊤ = ⊤ :=
  BoundedJoinSemilattice.join_top a

theorem top_join {L : Type u} [BoundedJoinSemilattice L] (a : L) : ⊤ ⊔ a = ⊤ := by
  rw [join_comm, join_top]

end Laws

/-! ## The lift (SPEC-038 Vocabulary, "Lift") -/

section Lift

variable {L : Type u} [JoinSemilatticeBot L]

/-- The lift of a contribution: the join of `g` over the accepted acts, seeded
at `⊥`. The R7 fold is this followed by a display. -/
def lift (g : Act → L) (A : List Act) : L := A.foldl (fun acc a => acc ⊔ g a) ⊥

theorem lift_nil (g : Act → L) : lift g [] = ⊥ := rfl

/-- A fold from any seed is the seed joined with the lift. -/
theorem foldl_join (g : Act → L) (A : List Act) (c : L) :
    A.foldl (fun acc a => acc ⊔ g a) c = c ⊔ A.foldl (fun acc a => acc ⊔ g a) ⊥ := by
  induction A generalizing c with
  | nil => simp only [List.foldl_nil, join_bot]
  | cons t rest ih =>
    rw [List.foldl_cons, List.foldl_cons, ih, ih (⊥ ⊔ g t), bot_join, join_assoc]

/-- **Put** (REQ-3801): admitting an act joins its contribution. -/
theorem lift_cons (g : Act → L) (a : Act) (A : List Act) :
    lift g (a :: A) = g a ⊔ lift g A := by
  unfold lift
  rw [List.foldl_cons, foldl_join, bot_join]

/-- **The join-homomorphism law** (REQ-3800): the lift of a union is the join
of the lifts. -/
theorem lift_append (g : Act → L) (A B : List Act) : lift g (A ++ B) = lift g A ⊔ lift g B := by
  unfold lift
  rw [List.foldl_append, foldl_join]

/-- Order independence: a permutation of the accepted list gives the same lift. -/
theorem lift_perm (g : Act → L) {A B : List Act} (h : A.Perm B) : lift g A = lift g B :=
  h.foldl_eq' (fun x _ y _ z => by rw [join_assoc, join_assoc, join_comm (g x) (g y)]) ⊥

/-- Every member's contribution is below the lift. -/
theorem join_lift_of_mem (g : Act → L) {a : Act} {A : List Act} (ha : a ∈ A) :
    g a ⊔ lift g A = lift g A := by
  induction A with
  | nil => exact absurd ha List.not_mem_nil
  | cons t rest ih =>
    rw [lift_cons]
    rcases List.mem_cons.1 ha with rfl | ha
    · rw [← join_assoc, join_idem]
    · rw [join_left_comm, ih ha]

/-- The lift is below every upper bound of the contributions. -/
theorem lift_join_of_forall (g : Act → L) {A : List Act} {u : L}
    (h : ∀ a ∈ A, g a ⊔ u = u) : lift g A ⊔ u = u := by
  induction A with
  | nil => exact bot_join u
  | cons t rest ih =>
    rw [lift_cons, join_assoc, ih (fun a ha => h a (List.mem_cons_of_mem t ha)),
      h t List.mem_cons_self]

/-- **The lift theorem** (REQ-3800, REQ-3801): equal accepted sets give equal
lifts. Order independence and duplicate insensitivity in one statement, with
no `NodupAddr` hypothesis: the lift is the least upper bound of the
contributions of the members, and that depends on membership alone. -/
theorem lift_setEq (g : Act → L) {A B : List Act} (h : SetEq A B) : lift g A = lift g B := by
  have h1 : lift g A ⊔ lift g B = lift g B :=
    lift_join_of_forall g fun a ha => join_lift_of_mem g ((h a).1 ha)
  have h2 : lift g B ⊔ lift g A = lift g A :=
    lift_join_of_forall g fun a ha => join_lift_of_mem g ((h a).2 ha)
  rw [← h2, join_comm, h1]

/-- The store's insertion is a put. -/
theorem lift_insertAct (g : Act → L) (a : Act) (A : List Act) :
    lift g (insertAct a A) = g a ⊔ lift g A := by
  rw [lift_setEq g (insertAct_setEq a A), lift_cons]

/-- Duplicate delivery changes nothing. -/
theorem lift_cons_of_mem (g : Act → L) {a : Act} {A : List Act} (ha : a ∈ A) :
    lift g (a :: A) = lift g A := by
  rw [lift_cons, join_lift_of_mem g ha]

/-- The lift is monotone in the accepted set. -/
theorem lift_sublist (g : Act → L) {A B : List Act} (s : A.Sublist B) :
    lift g A ⊔ lift g B = lift g B :=
  lift_join_of_forall g fun _ ha => join_lift_of_mem g (s.subset ha)

end Lift

/-! ## Products (REQ-3809: the LVar store is the product lattice) -/

instance instJoinSemilatticeBotProd {α β : Type u} [JoinSemilatticeBot α]
    [JoinSemilatticeBot β] : JoinSemilatticeBot (α × β) where
  join a b := (a.1 ⊔ b.1, a.2 ⊔ b.2)
  join_assoc a b c := Prod.ext (join_assoc a.1 b.1 c.1) (join_assoc a.2 b.2 c.2)
  join_comm a b := Prod.ext (join_comm a.1 b.1) (join_comm a.2 b.2)
  join_idem a := Prod.ext (join_idem a.1) (join_idem a.2)
  bot := (⊥, ⊥)
  bot_join a := Prod.ext (bot_join a.1) (bot_join a.2)

/-- A pair of contributions lifts to the pair of lifts. -/
theorem lift_pair {α β : Type u} [JoinSemilatticeBot α] [JoinSemilatticeBot β]
    (g : Act → α) (h : Act → β) (A : List Act) :
    lift (fun a => (g a, h a)) A = (lift g A, lift h A) := by
  induction A with
  | nil => rfl
  | cons t rest ih => rw [lift_cons, lift_cons, lift_cons, ih]; rfl

/-! ## `WithTop`: the conflict top adjoined (ADR-3803) -/

/-- A carrier with a conflict top adjoined. -/
inductive WithTop (α : Type u) where
  /-- An element of the carrier. -/
  | of (a : α)
  /-- Conflict. -/
  | top
  deriving DecidableEq

namespace WithTop

variable {α : Type u} [JoinSemilatticeBot α]

/-- The join: pointwise below, absorbing at the top. -/
def join : WithTop α → WithTop α → WithTop α
  | of a, of b => of (a ⊔ b)
  | of _, top => top
  | top, _ => top

instance instBoundedJoinSemilattice : BoundedJoinSemilattice (WithTop α) where
  join := join
  join_assoc a b c := by
    cases a <;> cases b <;> cases c <;> simp only [join, StateLift.join_assoc]
  join_comm a b := by
    cases a <;> cases b <;> simp only [join, StateLift.join_comm]
  join_idem a := by cases a <;> simp only [join, StateLift.join_idem]
  bot := of ⊥
  bot_join a := by cases a <;> simp only [join, StateLift.bot_join]
  top := top
  join_top a := by cases a <;> rfl

/-- A contribution into `α` lifts under `of` to the same lift. -/
theorem lift_of (g : Act → α) (A : List Act) : lift (fun a => of (g a)) A = of (lift g A) := by
  induction A with
  | nil => rfl
  | cons t rest ih => rw [lift_cons, lift_cons, ih]; rfl

end WithTop

/-! ## `Bool` under `or` (`L::Bool`) -/

instance instBoundedJoinSemilatticeBool : BoundedJoinSemilattice Bool where
  join a b := a || b
  join_assoc := Bool.or_assoc
  join_comm := Bool.or_comm
  join_idem := Bool.or_self
  bot := false
  bot_join := Bool.false_or
  top := true
  join_top := Bool.or_true

/-- `any` is the lift of its predicate into `Bool`. -/
theorem any_eq_lift (p : Act → Bool) (A : List Act) : A.any p = lift p A := by
  induction A with
  | nil => rfl
  | cons t rest ih => rw [List.any_cons, lift_cons, ih]; rfl

/-! ## Finite sets under union (`L::Addrs`, `L::Vals`, `L::Amounts`) -/

/-- Lists up to membership. -/
def listSetoid (α : Type u) : Setoid (List α) where
  r A B := ∀ x, x ∈ A ↔ x ∈ B
  iseqv :=
    ⟨fun _ _ => Iff.rfl, fun h x => (h x).symm, fun h₁ h₂ x => (h₁ x).trans (h₂ x)⟩

/-- A finite set: a list up to membership. Mirrors the `BTreeSet`/`BTreeMap`
carriers of `lattice.rs`, which are sets by construction. -/
def FinSet (α : Type u) : Type u := Quotient (listSetoid α)

namespace FinSet

variable {α : Type u}

/-- The set of a list's members. -/
def mk (l : List α) : FinSet α := Quotient.mk (listSetoid α) l

/-- The setoid relation, read as membership equivalence. -/
theorem forall_mem_of_equiv {A B : List α} (h : (listSetoid α).r A B) :
    ∀ x, x ∈ A ↔ x ∈ B := h

/-- Membership, lifted from the list. -/
protected def Mem (x : α) (s : FinSet α) : Prop :=
  Quotient.lift (s := listSetoid α) (fun l : List α => x ∈ l)
    (fun _ _ h => propext (forall_mem_of_equiv h x)) s

instance : Membership α (FinSet α) := ⟨fun s x => FinSet.Mem x s⟩

theorem mem_mk {x : α} {l : List α} : x ∈ mk l ↔ x ∈ l := Iff.rfl

/-- Extensionality: a finite set is its members. -/
theorem ext {s t : FinSet α} (h : ∀ x, x ∈ s ↔ x ∈ t) : s = t := by
  induction s using Quotient.ind
  induction t using Quotient.ind
  exact Quotient.sound h

/-- Union. -/
def union (s t : FinSet α) : FinSet α :=
  Quotient.lift₂ (s₁ := listSetoid α) (s₂ := listSetoid α) (fun A B => mk (A ++ B))
    (fun _ _ _ _ h₁ h₂ => Quotient.sound fun x => by
      simp only [List.mem_append]
      exact or_congr (forall_mem_of_equiv h₁ x) (forall_mem_of_equiv h₂ x)) s t

theorem mem_union {x : α} {s t : FinSet α} : x ∈ union s t ↔ x ∈ s ∨ x ∈ t :=
  Quotient.inductionOn₂ s t fun _ _ => List.mem_append

instance instJoinSemilatticeBot : JoinSemilatticeBot (FinSet α) where
  join := union
  join_assoc s t u := ext fun x => by simp only [mem_union, or_assoc]
  join_comm s t := ext fun x => by simp only [mem_union, or_comm]
  join_idem s := ext fun x => by simp only [mem_union, or_self]
  bot := mk []
  bot_join s := ext fun x => by simp only [mem_union, mem_mk, List.not_mem_nil, false_or]

theorem mem_join {x : α} {s t : FinSet α} : x ∈ s ⊔ t ↔ x ∈ s ∨ x ∈ t := mem_union

theorem not_mem_bot {x : α} : ¬ x ∈ (⊥ : FinSet α) := fun h => List.not_mem_nil (mem_mk.1 h)

/-- The set of an optional element. -/
def ofOption : Option α → FinSet α
  | some x => mk [x]
  | none => mk []

theorem mem_ofOption {x : α} {o : Option α} : x ∈ ofOption o ↔ o = some x := by
  cases o with
  | none =>
    simp only [ofOption, mem_mk, List.not_mem_nil, false_iff]
    exact nofun
  | some y =>
    simp only [ofOption, mem_mk, List.mem_singleton, Option.some.injEq]
    exact eq_comm

/-- Decidable membership. -/
def contains [DecidableEq α] (x : α) (s : FinSet α) : Bool :=
  Quotient.lift (s := listSetoid α) (fun l : List α => decide (x ∈ l))
    (fun _ _ h => decide_eq_decide.2 (forall_mem_of_equiv h x)) s

theorem contains_eq_true [DecidableEq α] {x : α} {s : FinSet α} :
    contains x s = true ↔ x ∈ s :=
  Quotient.inductionOn (s := listSetoid α) s fun _ => decide_eq_true_iff

theorem contains_eq_false [DecidableEq α] {x : α} {s : FinSet α} :
    contains x s = false ↔ ¬ x ∈ s := by
  rw [← Bool.not_eq_true, contains_eq_true]

/-- Duplicate removal, for the cardinality and the sum. -/
def dedup [DecidableEq α] : List α → List α
  | [] => []
  | x :: xs => if x ∈ xs then dedup xs else x :: dedup xs

theorem mem_dedup [DecidableEq α] {x : α} {l : List α} : x ∈ dedup l ↔ x ∈ l := by
  induction l with
  | nil => exact Iff.rfl
  | cons y ys ih =>
    rw [dedup]
    split
    · rename_i hy
      rw [ih, List.mem_cons]
      exact ⟨Or.inr, fun h => h.elim (fun e => e ▸ hy) id⟩
    · rw [List.mem_cons, List.mem_cons, ih]

theorem nodup_dedup [DecidableEq α] (l : List α) : (dedup l).Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons y ys ih =>
    rw [dedup]
    split
    · exact ih
    · rename_i hy
      exact List.nodup_cons.2 ⟨fun h => hy (mem_dedup.1 h), ih⟩

theorem dedup_of_nodup [DecidableEq α] {l : List α} (h : l.Nodup) : dedup l = l := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    have ⟨hy, hys⟩ := List.nodup_cons.1 h
    rw [dedup, if_neg hy, ih hys]

theorem dedup_perm_of_setEq [DecidableEq α] {A B : List α} (h : ∀ x, x ∈ A ↔ x ∈ B) :
    (dedup A).Perm (dedup B) :=
  (List.perm_ext_iff_of_nodup (nodup_dedup A) (nodup_dedup B)).2 fun x => by
    rw [mem_dedup, mem_dedup]; exact h x

/-- Cardinality (`Post::Size`). -/
def card [DecidableEq α] (s : FinSet α) : Nat :=
  Quotient.lift (s := listSetoid α) (fun l : List α => (dedup l).length)
    (fun _ _ h => (dedup_perm_of_setEq (forall_mem_of_equiv h)).length_eq) s

theorem card_mk_of_nodup [DecidableEq α] {l : List α} (h : l.Nodup) : card (mk l) = l.length := by
  show (dedup l).length = l.length
  rw [dedup_of_nodup h]

/-- The sum of an integer measure over the members (`Post::Difference`'s halves). -/
def sumBy [DecidableEq α] (f : α → Int) (s : FinSet α) : Int :=
  Quotient.lift (s := listSetoid α) (fun l : List α => (dedup l).foldl (fun acc a => acc + f a) 0)
    (fun _ _ h => (dedup_perm_of_setEq (forall_mem_of_equiv h)).foldl_eq'
      (fun _ _ _ _ z => by simp only [Int.add_right_comm]) 0) s

theorem sumBy_mk_of_nodup [DecidableEq α] (f : α → Int) {l : List α} (h : l.Nodup) :
    sumBy f (mk l) = l.foldl (fun acc a => acc + f a) 0 := by
  show (dedup l).foldl _ 0 = _
  rw [dedup_of_nodup h]

end FinSet

/-- Membership in a lift into finite sets: some member contributes it. -/
theorem mem_lift {β : Type u} (g : Act → FinSet β) {x : β} {A : List Act} :
    x ∈ lift g A ↔ ∃ a ∈ A, x ∈ g a := by
  induction A with
  | nil =>
    rw [lift_nil]
    exact ⟨fun h => absurd h FinSet.not_mem_bot, fun ⟨_, h, _⟩ => absurd h List.not_mem_nil⟩
  | cons t rest ih =>
    rw [lift_cons, FinSet.mem_join, ih]
    constructor
    · rintro (h | ⟨a, ha, hx⟩)
      · exact ⟨t, List.mem_cons_self, h⟩
      · exact ⟨a, List.mem_cons_of_mem t ha, hx⟩
    · rintro ⟨a, ha, hx⟩
      rcases List.mem_cons.1 ha with rfl | ha
      · exact Or.inl hx
      · exact Or.inr ⟨a, ha, hx⟩

/-- A singleton contribution lifts to the set of the mapped list. -/
theorem lift_mk_single {β : Type u} (f : Act → β) (A : List Act) :
    lift (fun a => FinSet.mk [f a]) A = FinSet.mk (A.map f) := by
  induction A with
  | nil => rfl
  | cons t rest ih => rw [lift_cons, ih]; rfl

/-! ## `Chain`: the historical greatest-address carrier -/

/-- The chain carrier: nothing yet, the value written at the greatest
address so far, or a conflict at that address. The greater address wins
outright, so a conflict is local to its address and a later write resolves
it; at one address two different values clash (ADR-3803). `lattice.rs`
never meets a clash, since its keys carry the unique address. The order is
lexicographic, address first: the ordinal sum of the address chain with a
flat lattice of values. -/
inductive Chain where
  /-- No contribution. -/
  | bot
  /-- The value `v` written at address `addr`. -/
  | win (addr : Nat) (v : Option Val)
  /-- Two different values at `addr`. -/
  | clash (addr : Nat)
  deriving DecidableEq

namespace Chain

/-- The join: the greater address wins; at the same address values must agree. -/
def join : Chain → Chain → Chain
  | bot, y => y
  | win a v, bot => win a v
  | clash a, bot => clash a
  | win a v, win b w =>
    if a < b then win b w else if b < a then win a v else if v = w then win a v else clash a
  | win a v, clash b => if a < b then clash b else if b < a then win a v else clash a
  | clash a, win b w => if a < b then win b w else clash a
  | clash a, clash b => if a < b then clash b else clash a

instance instJoinSemilatticeBot : JoinSemilatticeBot Chain where
  join := join
  join_assoc a b c := by cases a <;> cases b <;> cases c <;> grind [join]
  join_comm a b := by cases a <;> cases b <;> grind [join]
  join_idem a := by cases a <;> simp [join]
  bot := bot
  bot_join a := rfl

/-- The display: the winning value, if any (`Post::Identity` on `L::Chain`). -/
def display : Chain → Option Val
  | win _ v => v
  | _ => none

end Chain

/-! ## `Sole`: the `initial` carrier (ADR-3803) -/

/-- The `initial` carrier: no opener, exactly one, or a conflict with
evidence. Mirrors `lattice::Sole`; the evidence is the set of addresses in
conflict, so that `top` of the whole address space is the greatest element. -/
inductive Sole where
  /-- No opener. -/
  | bot
  /-- Exactly one opener, at `addr`, with its value. -/
  | one (addr : Nat) (v : Option Val)
  /-- Conflict, with the addresses in conflict as evidence. -/
  | top (evidence : Lattice.Set Nat)

namespace Sole

/-- The addresses an element has seen. -/
def evidence : Sole → Lattice.Set Nat
  | bot => ∅
  | one a _ => {a}
  | top t => t

/-- The join of ADR-3803: `⊥` is the identity, the same opener twice is that
opener, two different openers are a conflict naming both. -/
def join : Sole → Sole → Sole
  | bot, y => y
  | one a v, bot => one a v
  | top t, bot => top t
  | one a v, one b w => if a = b ∧ v = w then one a v else top ({a} ∪ {b})
  | one a _, top t => top ({a} ∪ t)
  | top t, one b _ => top (t ∪ {b})
  | top t, top u => top (t ∪ u)

theorem set_union_assoc (s t u : Lattice.Set Nat) : s ∪ t ∪ u = s ∪ (t ∪ u) :=
  Lattice.Set.ext fun _ => by simp only [Lattice.Set.mem_union, or_assoc]

theorem set_union_comm (s t : Lattice.Set Nat) : s ∪ t = t ∪ s :=
  Lattice.Set.ext fun _ => by simp only [Lattice.Set.mem_union, or_comm]

theorem set_union_idem (s : Lattice.Set Nat) : s ∪ s = s :=
  Lattice.Set.ext fun _ => by simp only [Lattice.Set.mem_union, or_self]

/-- The whole address space: the evidence of the greatest element. -/
def univ : Lattice.Set Nat := fun _ => True

theorem set_union_univ (s : Lattice.Set Nat) : s ∪ univ = univ :=
  Lattice.Set.ext fun _ => by
    simp only [Lattice.Set.mem_union]
    exact ⟨fun _ => trivial, fun h => Or.inr h⟩

instance : Std.Associative (fun s t : Lattice.Set Nat => s ∪ t) := ⟨set_union_assoc⟩
instance : Std.Commutative (fun s t : Lattice.Set Nat => s ∪ t) := ⟨set_union_comm⟩
instance : Std.IdempotentOp (fun s t : Lattice.Set Nat => s ∪ t) := ⟨set_union_idem⟩

instance instBoundedJoinSemilattice : BoundedJoinSemilattice Sole where
  join := join
  join_assoc a b c := by
    cases a <;> cases b <;> cases c <;> simp only [join] <;> grind
  join_comm a b := by
    cases a <;> cases b <;> simp only [join] <;> grind
  join_idem a := by cases a <;> simp [join, set_union_idem]
  bot := bot
  bot_join a := rfl
  top := top univ
  join_top a := by cases a <;> simp [join, set_union_univ]

/-- The display: the one opener's value (`Post::Identity` on `L::Sole`). -/
def display : Sole → Option Val
  | one _ v => v
  | _ => none

end Sole

/-! ## Contributions (`lattice::Contribute`) -/

/-- `Contribute::Flag`: presence. -/
-- The uniform contribution API takes an act even for constant presence.
@[nolint unusedArguments]
def flag (_ : Act) : Bool := true

/-- `Contribute::Address`: the act's address. -/
def address (a : Act) : FinSet Nat := FinSet.mk [a.addr]

/-- `Contribute::Field(k)`: the act's value at `k`, if any. -/
def field (k : String) (a : Act) : FinSet Val := FinSet.ofOption (a.get k)

/-- `Contribute::Amount(k)`: the act's integer amount at `k`, keyed by its
address so that it is counted once (`sumField_insert`). An act without an
integer at `k` contributes the amount `0`, as `State.amount` reads it. -/
def amountOf (k : String) (a : Act) : FinSet (Nat × Int) := FinSet.mk [(a.addr, amount k a)]

/-- `Contribute::Clocked`: the value at `k`, keyed by the act's address. -/
def clocked (k : String) (a : Act) : Chain := Chain.win a.addr (a.get k)

/-- `Contribute::Sole(k)`: the act as the one opener. -/
def sole (k : String) (a : Act) : Sole := Sole.one a.addr (a.get k)

/-! ## Conflict-aware initial fields and domains (REQ-3804, REQ-3809)

`State.allowedOf` retains the older address-winner model. The Rust kernel
instead reads an `initial` field: distinct openers join to conflict, and a
conflicting field supplies no domain values. These definitions model that
selector directly; they do not assume that admission excludes opener forks.
-/

/-- The raw opener lift used by Rust's `initial` field. -/
def initialCarrier (ov k : String) (A : List Act) : Sole :=
  lift (sole k) (acts ov A)

/-- A fault or absent opener supplies no domain values. -/
def initialAllowed (ov k : String) (A : List Act) : List Val :=
  match Sole.display (initialCarrier ov k A) with
  | some (.list xs) => xs.map Scalar.toVal
  | _ => []

/-- Domain selection through the conflict-aware opener lift. -/
def initialDomain (v k ov F : String) (A : List Act) : List Act :=
  (acts v A).filter (inDomain k (initialAllowed ov F A))

theorem initialCarrier_invariant {A B : List Act} (h : SetEq A B) (ov k : String) :
    initialCarrier ov k A = initialCarrier ov k B :=
  lift_setEq _ (acts_setEq h ov)

theorem initialAllowed_invariant {A B : List Act} (h : SetEq A B) (ov k : String) :
    initialAllowed ov k A = initialAllowed ov k B := by
  unfold initialAllowed
  rw [initialCarrier_invariant h ov k]

theorem initialDomain_invariant {A B : List Act} (h : SetEq A B)
    (v k ov F : String) : SetEq (initialDomain v k ov F A) (initialDomain v k ov F B) := by
  unfold initialDomain
  rw [initialAllowed_invariant h ov F]
  exact (acts_setEq h v).filter _

/-- Every contribution lift remains invariant after the current domain
selector, including when the opener lift is in conflict. -/
theorem initialDomain_lift_invariant {L : Type u} [JoinSemilatticeBot L]
    (g : Act → L) {A B : List Act} (h : SetEq A B) (v k ov F : String) :
    lift g (initialDomain v k ov F A) = lift g (initialDomain v k ov F B) :=
  lift_setEq g (initialDomain_invariant h v k ov F)

/-- Apply every declared data-domain filter against raw opener evidence.
Unrelated verbs, including a map's delete verb, remain in the source unless
their own domain declaration filters them. -/
def domainActs (domains : List StateKernelSemantics.Domain) (A : List Act) : List Act :=
  A.filter fun a => domains.all fun d => a.verb != d.verb ||
    inDomain d.key (initialAllowed d.opener d.field A) a

theorem domainActs_invariant {A B : List Act} (same : SetEq A B)
    (domains : List StateKernelSemantics.Domain) :
    SetEq (domainActs domains A) (domainActs domains B) := by
  unfold domainActs
  simp only [initialAllowed_invariant same]
  exact same.filter _

theorem domainActs_unique {A : List Act} (unique : NodupAddr A)
    (domains : List StateKernelSemantics.Domain) : NodupAddr (domainActs domains A) :=
  unique.filter _

/-- Two different openers cannot select a winner's list for a domain. -/
theorem initialAllowed_fork (a b : Act) (ov k : String)
    (ha : a.verb = ov) (hb : b.verb = ov) (hne : a.addr ≠ b.addr) :
    initialAllowed ov k [a, b] = [] := by
  simp [initialAllowed, initialCarrier, acts, ha, hb, lift_cons, lift_nil,
    sole, Lattice.JoinSemiLattice.join, Sole.join, hne, Sole.display]

/-! ## HLC arbitration as a display of a contribution lift

Reuse the finite-set carrier and `HlcRegister`'s verified lexicographic picker.
Clock recognition is explicit: a missing or invalid clock supplies `none` and
therefore contributes bottom. Physical/logical components and signer ranks are
typed evidence supplied by recognition, as in `HlcRegister.decorate`; this is
not a proof of the wire parser or of the signer-byte rank mapping.
-/

namespace HlcLift

/-- The causal and address stamp of a chain candidate. -/
abbrev Stamp := Nat × Nat × Nat
/-- A candidate value paired with its causal stamp. -/
abbrev Candidate := HlcRegister.Candidate Act

/-- An act contributes only if its supplied clock was recognized. -/
def candidate (clock : Act → Option Stamp) (a : Act) : Option Candidate :=
  (clock a).map fun stamp => HlcRegister.decorate (fun _ => stamp) a

/-- The lattice element contributed by one accepted act. -/
def contribution (clock : Act → Option Stamp) (a : Act) : FinSet Candidate :=
  FinSet.ofOption (candidate clock a)

theorem carrier_eq (clock : Act → Option Stamp) (A : List Act) :
    lift (contribution clock) A = FinSet.mk (A.filterMap (candidate clock)) := by
  apply FinSet.ext
  intro x
  simp only [mem_lift, contribution, FinSet.mem_ofOption, FinSet.mem_mk,
    List.mem_filterMap]

/-- Recognition and decoration preserve immutable-address consistency. -/
theorem candidates_consistent {A : List Act} (unique : NodupAddr A)
    (clock : Act → Option Stamp) :
    HlcRegister.Consistent (A.filterMap (candidate clock)) := by
  intro x hx y hy same
  obtain ⟨a, ha, hax⟩ := List.mem_filterMap.mp hx
  obtain ⟨b, hb, hby⟩ := List.mem_filterMap.mp hy
  have address_of {a : Act} {x : Candidate} (hx : candidate clock a = some x) :
      x.key.address = a.addr := by
    unfold candidate at hx
    cases h : clock a with
    | none => simp [h] at hx
    | some stamp =>
      simp only [h, Option.map_some, Option.some.injEq] at hx
      rw [← hx]
      rfl
  have eqab : a = b := unique.eq_of_addr ha hb
    ((address_of hax).symm.trans (same.trans (address_of hby)))
  subst b
  exact Option.some.inj (hax.symm.trans hby)

theorem consistent_setEq {T U : List Candidate}
    (same : ∀ x, x ∈ T ↔ x ∈ U) :
    HlcRegister.Consistent T ↔ HlcRegister.Consistent U := by
  constructor
  · intro h a ha b hb eqaddr
    exact h a ((same a).mpr ha) b ((same b).mpr hb) eqaddr
  · intro h a ha b hb eqaddr
    exact h a ((same a).mp ha) b ((same b).mp hb) eqaddr

/-- The display is total; an inconsistent address set has no winner.
Accepted histories cannot take that branch, by `candidates_consistent`. -/
noncomputable def readList (T : List Candidate) : Option Candidate := by
  classical
  exact if HlcRegister.Consistent T then HlcRegister.pick T else none

theorem readList_setEq {T U : List Candidate} (same : ∀ x, x ∈ T ↔ x ∈ U) :
    readList T = readList U := by
  classical
  unfold readList
  by_cases h : HlcRegister.Consistent U
  · rw [if_pos h, if_pos ((consistent_setEq same).mpr h)]
    exact HlcRegister.pick_setEq h same
  · rw [if_neg h, if_neg (fun ht => h ((consistent_setEq same).mp ht))]

/-- HLC arbitration is a well-defined post-map of the joined carrier. -/
noncomputable def display : FinSet Candidate → Option Candidate :=
  Quotient.lift readList (fun _ _ same => readList_setEq same)

/-- Rust's summarized greatest-candidate merge, on consistent candidates.
Ties choose the right operand; immutable-address consistency makes tied
candidates identical on every accepted set. -/
def merge : Option Candidate → Option Candidate → Option Candidate
  | none, y => y
  | some x, none => some x
  | some x, some y => some (if HlcRegister.LE x.key y.key then y else x)

theorem merge_assoc (x y z : Option Candidate) :
    merge (merge x y) z = merge x (merge y z) := by
  cases x <;> cases y <;> cases z <;> simp only [merge]
  grind [HlcRegister.LE]

theorem merge_idem (x : Option Candidate) : merge x x = x := by
  cases x <;> simp [merge, HlcRegister.le_refl]

theorem pick_cons (a : Candidate) (T : List Candidate) :
    HlcRegister.pick (a :: T) = merge (some a) (HlcRegister.pick T) := by
  cases h : HlcRegister.pick T <;> simp [HlcRegister.pick, merge, h]

/-- Candidate-set union compresses to the summarized chain merge. -/
theorem pick_append (T U : List Candidate) :
    HlcRegister.pick (T ++ U) = merge (HlcRegister.pick T) (HlcRegister.pick U) := by
  induction T with
  | nil => rfl
  | cons a T ih =>
    rw [List.cons_append, pick_cons, ih, pick_cons, merge_assoc]

/-- The alternative finite-set factorization compresses homomorphically to
the specified chain on consistent histories. -/
theorem display_union (T U : List Candidate) (consistent : HlcRegister.Consistent (T ++ U)) :
    display (FinSet.mk T ⊔ FinSet.mk U) =
      merge (display (FinSet.mk T)) (display (FinSet.mk U)) := by
  classical
  have ht : HlcRegister.Consistent T := fun a ha b hb h =>
    consistent a (List.mem_append_left U ha) b (List.mem_append_left U hb) h
  have hu : HlcRegister.Consistent U := fun a ha b hb h =>
    consistent a (List.mem_append_right T ha) b (List.mem_append_right T hb) h
  change readList (T ++ U) = merge (readList T) (readList U)
  simp only [readList, if_pos consistent, if_pos ht, if_pos hu]
  exact pick_append T U

/-- The HLC picker on a recognized accepted set equals a display of its lift. -/
theorem pick_eq_lift {A : List Act} (unique : NodupAddr A)
    (clock : Act → Option Stamp) :
    HlcRegister.pick (A.filterMap (candidate clock)) =
      display (lift (contribution clock) A) := by
  classical
  rw [carrier_eq]
  change _ = readList _
  rw [readList, if_pos (candidates_consistent unique clock)]

/-- Compressing the joined contribution carrier gives the chain join, for
any pair of histories whose combined candidates have immutable addresses. -/
theorem compressed_join (clock : Act → Option Stamp) (A B : List Act)
    (consistent : HlcRegister.Consistent ((A ++ B).filterMap (candidate clock))) :
    display (lift (contribution clock) (A ++ B)) =
      merge (display (lift (contribution clock) A))
        (display (lift (contribution clock) B)) := by
  rw [lift_append, carrier_eq clock A, carrier_eq clock B]
  exact display_union _ _ (by simpa only [List.filterMap_append] using consistent)

theorem display_invariant {A B : List Act} (same : SetEq A B)
    (clock : Act → Option Stamp) :
    display (lift (contribution clock) A) = display (lift (contribution clock) B) := by
  rw [lift_setEq _ same]

theorem pick_invariant {A B : List Act} (uniqueA : NodupAddr A) (uniqueB : NodupAddr B)
    (same : SetEq A B) (clock : Act → Option Stamp) :
    HlcRegister.pick (A.filterMap (candidate clock)) =
      HlcRegister.pick (B.filterMap (candidate clock)) := by
  rw [pick_eq_lift uniqueA, pick_eq_lift uniqueB, display_invariant same clock]

/-- Extracting the selected value preserves invariance, including absence. -/
theorem field_invariant {A B : List Act} (uniqueA : NodupAddr A) (uniqueB : NodupAddr B)
    (same : SetEq A B) (clock : Act → Option Stamp) (key : String) :
    (HlcRegister.pick (A.filterMap (candidate clock))).bind (fun c => c.value.get key) =
    (HlcRegister.pick (B.filterMap (candidate clock))).bind (fun c => c.value.get key) := by
  rw [pick_invariant uniqueA uniqueB same clock]

/-- Missing or invalid clocks contribute no candidate. -/
theorem unrecognized_is_bottom (clock : Act → Option Stamp) (a : Act)
    (missing : clock a = none) : contribution clock a = ⊥ := by
  simp [contribution, candidate, missing, FinSet.ofOption]
  rfl

theorem unrecognized_put_unchanged (clock : Act → Option Stamp) (a : Act) (A : List Act)
    (missing : clock a = none) :
    lift (contribution clock) (a :: A) = lift (contribution clock) A := by
  rw [lift_cons, unrecognized_is_bottom clock a missing, bot_join]

/-! Executable regressions for the recognized-candidate bridge. In each
case address 1 loses an address-only arbitration to address 2. -/
private def sample (addr : Nat) : Act :=
  ⟨addr, "write", if addr = 1 then "@a" else "@b", [], [], []⟩

private def winner (first second : Option Stamp) : Option Nat :=
  let clock := fun a : Act => if a.addr = 1 then first else second
  (HlcRegister.pick ([sample 1, sample 2].filterMap (candidate clock))).map
    (fun c => c.value.addr)

theorem physical_precedes_address :
    winner (some (20, 0, 0)) (some (10, 0, 1)) = some 1 := by decide

theorem logical_precedes_address :
    winner (some (20, 2, 0)) (some (20, 1, 1)) = some 1 := by decide

theorem signer_precedes_address :
    winner (some (20, 0, 2)) (some (20, 0, 1)) = some 1 := by decide

theorem address_breaks_tie :
    winner (some (20, 0, 1)) (some (20, 0, 1)) = some 2 := by decide

theorem unrecognized_high_address_ignored :
    winner (some (20, 0, 0)) none = some 1 := by decide

theorem all_unrecognized_have_no_winner : winner none none = none := by decide

end HlcLift

/-! ## The heads as displays of lifts (ADR-3804) -/

/-- `exists v` is the flag lift, displayed as itself. -/
theorem existsRule_eq_lift (v : String) (A : List Act) :
    existsRule v A = lift flag (acts v A) := by
  unfold existsRule
  generalize acts v A = T
  induction T with
  | nil => rfl
  | cons t rest _ => rw [lift_cons]; rfl

/-- `size` is the address lift, displayed by cardinality. -/
theorem size_eq_lift {T : List Act} (hT : NodupAddr T) :
    size T = FinSet.card (lift address T) := by
  unfold size address
  rw [lift_mk_single, FinSet.card_mk_of_nodup hT, List.length_map]

/-- `count v` is the address lift over `acts v`, displayed by cardinality. -/
theorem count_eq_lift {A : List Act} (hA : NodupAddr A) (v : String) :
    count v A = FinSet.card (lift address (acts v A)) :=
  size_eq_lift (hA.acts v)

/-- `has` is the field lift, displayed by membership. -/
theorem has_eq_lift (k : String) (T : List Act) (x : Val) :
    has k T x = FinSet.contains x (lift (field k) T) := by
  apply Bool.eq_iff_iff.2
  rw [FinSet.contains_eq_true, mem_lift]
  simp only [has, List.any_eq_true, beq_iff_eq, field, FinSet.mem_ofOption]

/-- `set-union v :k` is the field lift over `acts v`, displayed by membership. -/
theorem setUnion_eq_lift (v k : String) (A : List Act) (x : Val) :
    setUnion v k A x = FinSet.contains x (lift (field k) (acts v A)) :=
  has_eq_lift k _ x

theorem nodup_map_amount (k : String) {T : List Act} (hT : NodupAddr T) :
    (T.map fun a => (a.addr, amount k a)).Nodup :=
  List.Pairwise.of_map (S := fun x y : Nat => x ≠ y) Prod.fst
    (fun _ _ h e => h (congrArg Prod.fst e)) (by rw [List.map_map]; exact hT)

/-- `sum` is the amount lift, displayed by the sum of the amounts. -/
theorem sumField_eq_lift {T : List Act} (hT : NodupAddr T) (k : String) :
    sumField k T = FinSet.sumBy Prod.snd (lift (amountOf k) T) := by
  unfold amountOf
  rw [lift_mk_single, FinSet.sumBy_mk_of_nodup _ (nodup_map_amount k hT)]
  unfold sumField
  rw [List.foldl_map]

/-- `counter inc dec :k` is the pair of amount lifts, displayed by difference. -/
theorem counter_eq_lift {A : List Act} (hA : NodupAddr A) (inc dec k : String) :
    counter inc dec k A =
      FinSet.sumBy Prod.snd (lift (amountOf k) (acts inc A)) -
        FinSet.sumBy Prod.snd (lift (amountOf k) (acts dec A)) := by
  unfold counter
  rw [sumField_eq_lift (hA.acts inc), sumField_eq_lift (hA.acts dec)]

/-- The chain lift over a `NodupAddr` list is the value at its greatest address. -/
theorem lift_clocked_of_max {k : String} {T : List Act} (hT : NodupAddr T) {m : Act} (hm : m ∈ T)
    (hmax : ∀ b ∈ T, b.addr ≤ m.addr) : lift (clocked k) T = Chain.win m.addr (m.get k) := by
  induction T generalizing m with
  | nil => exact absurd hm List.not_mem_nil
  | cons t rest ih =>
    simp only [NodupAddr, List.map_cons, List.nodup_cons, List.mem_map] at hT
    obtain ⟨hta, hrest⟩ := hT
    rw [lift_cons]
    cases rest with
    | nil =>
      rw [lift_nil, join_bot]
      simp only [List.mem_singleton] at hm
      subst hm
      rfl
    | cons r rs =>
      obtain ⟨m', hm', hmax'⟩ := exists_top (T := r :: rs) (List.cons_ne_nil r rs)
      rw [ih hrest hm' hmax']
      have hne : t.addr ≠ m'.addr := fun e => hta ⟨m', hm', e.symm⟩
      have hm'T : m' ∈ t :: r :: rs := List.mem_cons_of_mem t hm'
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · have : m = m' := by
          rcases List.mem_cons.1 hm with rfl | hmr
          · exact absurd (hmax m' hm'T) (Nat.not_le.2 hlt)
          · exact (NodupAddr.eq_of_addr hrest hmr hm'
              (Nat.le_antisymm (hmax' m hmr) (hmax m' hm'T)))
        subst this
        show Chain.join _ _ = _
        simp only [clocked, Chain.join, if_pos hlt]
      · have : m = t := by
          rcases List.mem_cons.1 hm with rfl | hmr
          · rfl
          · exact absurd (hmax t List.mem_cons_self)
              (Nat.not_le.2 (Nat.lt_of_le_of_lt (hmax' m hmr) hgt))
        subst this
        show Chain.join _ _ = _
        simp only [clocked, Chain.join, if_neg (Nat.lt_asymm hgt), if_pos hgt]

/-- `pick` is the chain lift, displayed by the winning value. -/
theorem pick_eq_lift {T : List Act} (hT : NodupAddr T) (k : String) :
    pick k T = Chain.display (lift (clocked k) T) := by
  cases hp : pickAct T with
  | none =>
    have := pickAct_eq_none_iff.1 hp
    subst this
    rfl
  | some m =>
    obtain ⟨hm, hmax⟩ := pickAct_spec hp
    rw [lift_clocked_of_max hT hm hmax]
    unfold pick
    rw [hp]
    rfl

/-- `last v :k` is the chain lift over `acts v`, displayed by the winning value. -/
theorem last_eq_lift {A : List Act} (hA : NodupAddr A) (v k : String) :
    last v k A = Chain.display (lift (clocked k) (acts v A)) :=
  pick_eq_lift (hA.acts v) k

/-- `latest-per-key v :kk :k` is the chain lift over the acts of `v` keyed `x`. -/
theorem latestPerKey_eq_lift {A : List Act} (hA : NodupAddr A) (v kk k : String) (x : Val) :
    latestPerKey v kk k A x =
      Chain.display (lift (clocked k) ((acts v A).filter (fun a => a.get kk == some x))) :=
  pick_eq_lift ((hA.acts v).filter _) k

/-- `all` is the negated lift of the negated predicate. -/
theorem all_eq_lift (p : Act → Bool) (A : List Act) : A.all p = !(lift (fun a => !p a) A) := by
  induction A with
  | nil => rfl
  | cons t rest ih =>
    rw [List.all_cons, lift_cons, ih]
    generalize lift (fun a => !p a) rest = L
    cases p t <;> cases L <;> rfl

/-- `isTop` is a display of a `Bool` lift. -/
theorem isTop_eq_lift (T : List Act) (a : Act) :
    isTop T a = !(lift (fun b => !decide (b.addr ≤ a.addr)) T) :=
  all_eq_lift _ T

theorem isTop_lift_setEq {T U : List Act} (h : SetEq T U) (a : Act) : isTop T a = isTop U a := by
  rw [isTop_eq_lift, isTop_eq_lift, lift_setEq _ h]

/-! ## Supersession: the two grow-only halves (`Contribute::Write`, `Contribute::Replaced`) -/

/-- `Contribute::Write(group)`: the write's address, keyed by its group. -/
def write {κ : Type} (group : Act → κ) (a : Act) : FinSet (Nat × κ) :=
  FinSet.mk [(a.addr, group a)]

/-- `Contribute::Replaced(group)`: the `(group, address)` pairs the act's `:replaces` names. -/
def replaced {κ : Type} (group : Act → κ) (r : Act) : FinSet (κ × Nat) :=
  FinSet.mk (r.replaces.map fun x => (group r, x))

/-- `Post::Current`: the projection `W \ R`, read back through the accepted
acts by address, as `lattice.rs` reads `self.acts.get(addr)`. -/
def currentOf {κ : Type} [DecidableEq κ] (group : Act → κ) (W : FinSet (Nat × κ))
    (R : FinSet (κ × Nat)) (A : List Act) : List Act :=
  A.filter fun a => W.contains (a.addr, group a) && !R.contains (group a, a.addr)

theorem mem_currentOf {κ : Type} [DecidableEq κ] {group : Act → κ} {W : FinSet (Nat × κ)}
    {R : FinSet (κ × Nat)} {A : List Act} {a : Act} :
    a ∈ currentOf group W R A ↔
      a ∈ A ∧ (a.addr, group a) ∈ W ∧ ¬ (group a, a.addr) ∈ R := by
  simp only [currentOf, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true',
    FinSet.contains_eq_true, FinSet.contains_eq_false]

theorem currentOf_setEq {κ : Type} [DecidableEq κ] {A B : List Act} (h : SetEq A B)
    (group : Act → κ) (W : FinSet (Nat × κ)) (R : FinSet (κ × Nat)) :
    SetEq (currentOf group W R A) (currentOf group W R B) :=
  h.filter _

/-- The current writes of `v` under key `k` and delete verb `d`, as the
projection of the two lifts (`lattice.rs`: `pair(Write, Replaced)` under
`Post::Current`). -/
def currentLift (v : String) (k d : Option String) (A : List Act) : List Act :=
  currentOf (keyOf k) (lift (write (keyOf k)) (acts v A))
    (lift (replaced (keyOf k)) (replacers v d A)) A

/-- The signer register's current writes, likewise with the signer as group. -/
def currentOwnLift (v : String) (A : List Act) : List Act :=
  currentOf Act.signer (lift (write Act.signer) (acts v A))
    (lift (replaced Act.signer) (acts v A)) A

theorem setEq_trans {A B C : List Act} (h₁ : SetEq A B) (h₂ : SetEq B C) : SetEq A C :=
  fun a => (h₁ a).trans (h₂ a)

/-- The join halves respect set equality by the lift theorem, the projection
by `SetEq.filter`; no `NodupAddr` is needed. -/
theorem currentLift_setEq {A B : List Act} (h : SetEq A B) (v : String) (k d : Option String) :
    SetEq (currentLift v k d A) (currentLift v k d B) := by
  unfold currentLift
  rw [lift_setEq _ (acts_setEq h v), lift_setEq _ (replacers_setEq h v d)]
  exact h.filter _

theorem currentOwnLift_setEq {A B : List Act} (h : SetEq A B) (v : String) :
    SetEq (currentOwnLift v A) (currentOwnLift v B) := by
  unfold currentOwnLift
  rw [lift_setEq (write Act.signer) (acts_setEq h v),
    lift_setEq (replaced Act.signer) (acts_setEq h v)]
  exact h.filter _

/-- **`current` is the projection `W \ R` of two lifts** (CON-3800): on a
`NodupAddr` accepted list, the kernel's `current` has the members of
`currentLift`. -/
theorem current_eq_currentLift {A : List Act} (hA : NodupAddr A) (v : String)
    (k d : Option String) : SetEq (current v k d A) (currentLift v k d A) := by
  intro a
  unfold currentLift
  rw [mem_current_iff, mem_currentOf, mem_lift, mem_lift]
  simp only [write, replaced, FinSet.mem_mk, List.mem_singleton, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨ha, hr⟩
    refine ⟨(List.mem_filter.1 ha).1, ⟨a, ha, rfl, rfl⟩, ?_⟩
    rintro ⟨r, hrm, x, hx, hk, rfl⟩
    exact hr r hrm hk hx
  · rintro ⟨haA, ⟨b, hb, hab, _⟩, hn⟩
    have : a = b := hA.eq_of_addr haA (List.mem_filter.1 hb).1 hab
    subst this
    exact ⟨hb, fun r hr hk hx => hn ⟨r, hr, a.addr, hx, hk, rfl⟩⟩

/-- `currentOwn` likewise, with the signer as the group. -/
theorem currentOwn_eq_currentOwnLift {A : List Act} (hA : NodupAddr A) (v : String) :
    SetEq (currentOwn v A) (currentOwnLift v A) := by
  intro a
  unfold currentOwnLift
  rw [mem_currentOwn_iff, mem_currentOf, mem_lift, mem_lift]
  simp only [write, replaced, FinSet.mem_mk, List.mem_singleton, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨ha, hr⟩
    refine ⟨(List.mem_filter.1 ha).1, ⟨a, ha, rfl, rfl⟩, ?_⟩
    rintro ⟨r, hrm, x, hx, hk, rfl⟩
    exact hr r hrm hk hx
  · rintro ⟨haA, ⟨b, hb, hab, _⟩, hn⟩
    have : a = b := hA.eq_of_addr haA (List.mem_filter.1 hb).1 hab
    subst this
    exact ⟨hb, fun r hr hk hx => hn ⟨r, hr, a.addr, hx, hk, rfl⟩⟩

/-- `values v :k` is the field lift over the current writes, displayed by membership. -/
theorem values_eq_lift {A : List Act} (hA : NodupAddr A) (v k : String) (x : Val) :
    values v k A x = FinSet.contains x (lift (field k) (currentLift v none none A)) := by
  unfold values
  rw [has_eq_lift, lift_setEq _ (current_eq_currentLift hA v none none)]

/-- `values-per-key v :kk :k [d]` is the field lift over the current writes keyed `x`. -/
theorem valuesPerKey_eq_lift {A : List Act} (hA : NodupAddr A) (v kk k : String)
    (d : Option String) (x y : Val) :
    valuesPerKey v kk k d A x y =
      FinSet.contains y (lift (field k)
        ((currentLift v (some kk) d A).filter (fun a => a.get kk == some x))) := by
  unfold valuesPerKey
  rw [has_eq_lift, lift_setEq _ ((current_eq_currentLift hA v (some kk) d).filter _)]

/-- `register-per-key v :kk :k [d]` is the chain lift over the current writes keyed `x`. -/
theorem registerPerKey_eq_lift {A : List Act} (hA : NodupAddr A) (v kk k : String)
    (d : Option String) (x : Val) :
    registerPerKey v kk k d A x =
      Chain.display (lift (clocked k)
        ((currentLift v (some kk) d A).filter (fun a => a.get kk == some x))) := by
  unfold registerPerKey
  rw [pick_eq_lift ((hA.current v (some kk) d).filter _),
    lift_setEq _ ((current_eq_currentLift hA v (some kk) d).filter _)]

/-- `observed-set` is the field lift over the current writes keyed by the value. -/
theorem observedSet_eq_lift {A : List Act} (hA : NodupAddr A) (add rem k : String) (x : Val) :
    observedSet add rem k A x =
      FinSet.contains x (lift (field k) (currentLift add (some k) (some rem) A)) := by
  unfold observedSet
  rw [has_eq_lift, lift_setEq _ (current_eq_currentLift hA add (some k) (some rem))]

/-- `latest-per-signer v :k` is the chain lift over the signer's current writes. -/
theorem latestPerSigner_eq_lift {A : List Act} (hA : NodupAddr A) (v k : String) (s : String) :
    latestPerSigner v k A s =
      Chain.display (lift (clocked k) ((currentOwnLift v A).filter (fun a => a.signer == s))) := by
  unfold latestPerSigner
  rw [pick_eq_lift ((hA.currentOwn v).filter _),
    lift_setEq _ ((currentOwn_eq_currentOwnLift hA v).filter _)]

/-- A histogram over a per-group pick, as a display: the number of acts that
top their group and satisfy `q`. Both halves are displays of lifts (`size`
of the address lift, `isTop` of a `Bool` lift), so the count is a set
function on `NodupAddr` lists. -/
theorem topCount_setEq {T U : List Act} (hT : NodupAddr T) (hU : NodupAddr U) (h : SetEq T U)
    (p : Act → Act → Bool) (q : Act → Bool → Bool) :
    (T.filter (fun a => q a (isTop (T.filter (p a)) a))).length =
      (U.filter (fun a => q a (isTop (U.filter (p a)) a))).length := by
  show size _ = size _
  rw [size_eq_lift (hT.filter _), size_eq_lift (hU.filter _)]
  apply congrArg FinSet.card
  apply lift_setEq
  intro a
  simp only [List.mem_filter, isTop_lift_setEq (h.filter (p a)) a]
  rw [h a]

/-! ## The thirteen heads are set functions, from the lift theorem -/

theorem existsRule_invariant {A B : List Act} (h : SetEq A B) (v : String) :
    existsRule v A = existsRule v B := by
  rw [existsRule_eq_lift, existsRule_eq_lift, lift_setEq _ (acts_setEq h v)]

theorem count_invariant {A B : List Act} (hA : NodupAddr A) (hB : NodupAddr B) (h : SetEq A B)
    (v : String) : count v A = count v B := by
  rw [count_eq_lift hA, count_eq_lift hB, lift_setEq _ (acts_setEq h v)]

theorem has_invariant {T U : List Act} (h : SetEq T U) (k : String) (x : Val) :
    has k T x = has k U x := by
  rw [has_eq_lift, has_eq_lift, lift_setEq _ h]

theorem setUnion_invariant {A B : List Act} (h : SetEq A B) (v k : String) (x : Val) :
    setUnion v k A x = setUnion v k B x := by
  rw [setUnion_eq_lift, setUnion_eq_lift, lift_setEq _ (acts_setEq h v)]

theorem sumField_invariant {T U : List Act} (hT : NodupAddr T) (hU : NodupAddr U) (h : SetEq T U)
    (k : String) : sumField k T = sumField k U := by
  rw [sumField_eq_lift hT, sumField_eq_lift hU, lift_setEq _ h]

theorem counter_invariant {A B : List Act} (hA : NodupAddr A) (hB : NodupAddr B) (h : SetEq A B)
    (inc dec k : String) : counter inc dec k A = counter inc dec k B := by
  rw [counter_eq_lift hA, counter_eq_lift hB, lift_setEq _ (acts_setEq h inc),
    lift_setEq _ (acts_setEq h dec)]

theorem pick_invariant {T U : List Act} (hT : NodupAddr T) (hU : NodupAddr U) (h : SetEq T U)
    (k : String) : pick k T = pick k U := by
  rw [pick_eq_lift hT, pick_eq_lift hU, lift_setEq _ h]

theorem last_invariant {A B : List Act} (hA : NodupAddr A) (hB : NodupAddr B) (h : SetEq A B)
    (v k : String) : last v k A = last v k B := by
  rw [last_eq_lift hA, last_eq_lift hB, lift_setEq _ (acts_setEq h v)]

theorem latestPerKey_invariant {A B : List Act} (hA : NodupAddr A) (hB : NodupAddr B)
    (h : SetEq A B) (v kk k : String) (x : Val) :
    latestPerKey v kk k A x = latestPerKey v kk k B x := by
  rw [latestPerKey_eq_lift hA, latestPerKey_eq_lift hB, lift_setEq _ ((acts_setEq h v).filter _)]

theorem values_invariant {A B : List Act} (hA : NodupAddr A) (hB : NodupAddr B) (h : SetEq A B)
    (v k : String) (x : Val) : values v k A x = values v k B x := by
  rw [values_eq_lift hA, values_eq_lift hB, lift_setEq _ (currentLift_setEq h v none none)]

theorem valuesPerKey_invariant {A B : List Act} (hA : NodupAddr A) (hB : NodupAddr B)
    (h : SetEq A B) (v kk k : String) (d : Option String) (x y : Val) :
    valuesPerKey v kk k d A x y = valuesPerKey v kk k d B x y := by
  rw [valuesPerKey_eq_lift hA, valuesPerKey_eq_lift hB,
    lift_setEq _ ((currentLift_setEq h v (some kk) d).filter _)]

theorem registerPerKey_invariant {A B : List Act} (hA : NodupAddr A) (hB : NodupAddr B)
    (h : SetEq A B) (v kk k : String) (d : Option String) (x : Val) :
    registerPerKey v kk k d A x = registerPerKey v kk k d B x := by
  rw [registerPerKey_eq_lift hA, registerPerKey_eq_lift hB,
    lift_setEq _ ((currentLift_setEq h v (some kk) d).filter _)]

theorem observedSet_invariant {A B : List Act} (hA : NodupAddr A) (hB : NodupAddr B)
    (h : SetEq A B) (add rem k : String) (x : Val) :
    observedSet add rem k A x = observedSet add rem k B x := by
  rw [observedSet_eq_lift hA, observedSet_eq_lift hB,
    lift_setEq _ (currentLift_setEq h add (some k) (some rem))]

theorem latestPerSigner_invariant {A B : List Act} (hA : NodupAddr A) (hB : NodupAddr B)
    (h : SetEq A B) (v k : String) (s : String) :
    latestPerSigner v k A s = latestPerSigner v k B s := by
  rw [latestPerSigner_eq_lift hA, latestPerSigner_eq_lift hB,
    lift_setEq _ ((currentOwnLift_setEq h v).filter _)]

/-- `currentOwn` lists are set-equal, through their lift presentation. -/
theorem currentOwn_invariant {A B : List Act} (hA : NodupAddr A) (hB : NodupAddr B)
    (h : SetEq A B) (v : String) : SetEq (currentOwn v A) (currentOwn v B) :=
  setEq_trans (currentOwn_eq_currentOwnLift hA v)
    (setEq_trans (currentOwnLift_setEq h v) (currentOwn_eq_currentOwnLift hB v).symm)

theorem histogramPerSigner_invariant {A B : List Act} (hA : NodupAddr A) (hB : NodupAddr B)
    (h : SetEq A B) (v k : String) (x : Val) :
    histogramPerSigner v k A x = histogramPerSigner v k B x :=
  topCount_setEq (hA.currentOwn v) (hB.currentOwn v) (currentOwn_invariant hA hB h v)
    (fun a b => b.signer == a.signer) (fun a t => t && a.get k == some x)

theorem histogramPerKey_invariant {A B : List Act} (hA : NodupAddr A) (hB : NodupAddr B)
    (h : SetEq A B) (v kk k : String) (x : Val) :
    histogramPerKey v kk k A x = histogramPerKey v kk k B x :=
  topCount_setEq (hA.acts v) (hB.acts v) (acts_setEq h v)
    (fun a b => b.get kk == a.get kk) (fun a t => ((a.get kk).isSome && t) && a.get k == some x)

/-- The historical domain list is a display of the address-chain lift.
Current Rust domains instead use `initialAllowed_invariant`. -/
theorem allowedOf_invariant {A B : List Act} (hA : NodupAddr A) (hB : NodupAddr B)
    (h : SetEq A B) (ov F : String) : allowedOf ov F A = allowedOf ov F B := by
  unfold allowedOf
  rw [last_invariant hA hB h ov F]

theorem actsDom_invariant {A B : List Act} (hA : NodupAddr A) (hB : NodupAddr B) (h : SetEq A B)
    (v k ov F : String) : SetEq (actsDom v k ov F A) (actsDom v k ov F B) := by
  unfold actsDom
  rw [allowedOf_invariant hA hB h ov F]
  exact (acts_setEq h v).filter _

/-- **R7 from the lift theorem** (REQ-3801): the historical statement of
`State.fold_perm_invariant`, augmented with the current conflict-aware domain
selector. The historical head conjuncts do not model HLC arbitration; see
the correspondence limits above. -/
theorem fold_perm_invariant_lift {A B : List Act} (hA : NodupAddr A) (hB : NodupAddr B)
    (h : SetEq A B) (v kk k add rem inc dec ov F : String) (d : Option String) (s : String)
    (x y : Val) :
    last v k A = last v k B ∧
    latestPerSigner v k A s = latestPerSigner v k B s ∧
    latestPerKey v kk k A x = latestPerKey v kk k B x ∧
    existsRule v A = existsRule v B ∧
    count v A = count v B ∧
    setUnion v k A x = setUnion v k B x ∧
    values v k A x = values v k B x ∧
    valuesPerKey v kk k d A x y = valuesPerKey v kk k d B x y ∧
    registerPerKey v kk k d A x = registerPerKey v kk k d B x ∧
    observedSet add rem k A x = observedSet add rem k B x ∧
    counter inc dec k A = counter inc dec k B ∧
    histogramPerSigner v k A x = histogramPerSigner v k B x ∧
    histogramPerKey v kk k A x = histogramPerKey v kk k B x ∧
    SetEq (actsDom v kk ov F A) (actsDom v kk ov F B) ∧
    SetEq (initialDomain v kk ov F A) (initialDomain v kk ov F B) :=
  ⟨last_invariant hA hB h v k, latestPerSigner_invariant hA hB h v k s,
    latestPerKey_invariant hA hB h v kk k x, existsRule_invariant h v, count_invariant hA hB h v,
    setUnion_invariant h v k x, values_invariant hA hB h v k x,
    valuesPerKey_invariant hA hB h v kk k d x y, registerPerKey_invariant hA hB h v kk k d x,
    observedSet_invariant hA hB h add rem k x, counter_invariant hA hB h inc dec k,
    histogramPerSigner_invariant hA hB h v k x, histogramPerKey_invariant hA hB h v kk k x,
    actsDom_invariant hA hB h v kk ov F, initialDomain_invariant h v kk ov F⟩

/-! ## Current HLC head invariance, through the lift theorem -/

theorem hlc_register_invariant {A B : List Act} (hA : NodupAddr A) (hB : NodupAddr B)
    (same : SetEq A B) (v : String) (clock : Act → Option HlcLift.Stamp) :
    HlcRegister.pick ((acts v A).filterMap (HlcLift.candidate clock)) =
      HlcRegister.pick ((acts v B).filterMap (HlcLift.candidate clock)) :=
  HlcLift.pick_invariant (hA.acts v) (hB.acts v) (acts_setEq same v) clock

theorem hlc_perSigner_invariant {A B : List Act} (hA : NodupAddr A) (hB : NodupAddr B)
    (same : SetEq A B) (v signer : String) (clock : Act → Option HlcLift.Stamp) :
    HlcRegister.pick (((currentOwn v A).filter (fun a => a.signer == signer)).filterMap
      (HlcLift.candidate clock)) =
    HlcRegister.pick (((currentOwn v B).filter (fun a => a.signer == signer)).filterMap
      (HlcLift.candidate clock)) :=
  HlcLift.pick_invariant ((hA.currentOwn v).filter _) ((hB.currentOwn v).filter _)
    ((currentOwn_invariant hA hB same v).filter _) clock

theorem hlc_map_invariant {A B : List Act} (hA : NodupAddr A) (hB : NodupAddr B)
    (same : SetEq A B) (v k : String) (d : Option String) (x : Val)
    (clock : Act → Option HlcLift.Stamp) :
    HlcRegister.pick (((current v (some k) d A).filter (fun a => a.get k == some x)).filterMap
      (HlcLift.candidate clock)) =
    HlcRegister.pick (((current v (some k) d B).filter (fun a => a.get k == some x)).filterMap
      (HlcLift.candidate clock)) :=
  HlcLift.pick_invariant ((hA.current v (some k) d).filter _) ((hB.current v (some k) d).filter _)
    ((currentLift_setEq same v (some k) d |> fun h =>
      setEq_trans (current_eq_currentLift hA v (some k) d)
        (setEq_trans h (current_eq_currentLift hB v (some k) d).symm)).filter _) clock

/-! ## Displayed HLC field values and maps

Maps are modeled extensionally, as in `State`: a group lookup returns `none`
when the group does not exist and `some none` when it exists but its value is
absent (for example all clocks are invalid). Rust's renderer sorts group keys;
byte serialization is outside these value-level statements.
-/

namespace HlcFields

/-- Read the field from the greatest recognized HLC candidate. -/
def scalar (clock : Act → Option HlcLift.Stamp) (field : String) (T : List Act) : Option Val :=
  (HlcRegister.pick (T.filterMap (HlcLift.candidate clock))).bind (fun c => c.value.get field)

/-- Read one nonempty HLC group, distinguishing an absent field from an empty group. -/
def group (clock : Act → Option HlcLift.Stamp) (field : String) (T : List Act) :
    Option (Option Val) :=
  if T.isEmpty then none else some (scalar clock field T)

/-- Read the current HLC candidate separately for each signer. -/
def perSigner (clock : Act → Option HlcLift.Stamp) (verb field : String) (A : List Act) :
    String → Option (Option Val) :=
  fun signer => group clock field ((currentOwn verb A).filter (fun a => a.signer == signer))

/-- Read the current HLC candidate separately for each key. -/
def keyed (clock : Act → Option HlcLift.Stamp) (verb key field : String) (delete : Option String)
    (A : List Act) : Val → Option (Option Val) :=
  fun x => group clock field ((current verb (some key) delete A).filter (fun a => a.get key == some x))

theorem scalar_invariant {A B : List Act} (hA : NodupAddr A) (hB : NodupAddr B)
    (same : SetEq A B) (clock : Act → Option HlcLift.Stamp) (field : String) :
    scalar clock field A = scalar clock field B :=
  HlcLift.field_invariant hA hB same clock field

theorem group_invariant {A B : List Act} (hA : NodupAddr A) (hB : NodupAddr B)
    (same : SetEq A B) (clock : Act → Option HlcLift.Stamp) (field : String) :
    group clock field A = group clock field B := by
  unfold group
  rw [isEmpty_setEq same, scalar_invariant hA hB same clock field]

theorem perSigner_invariant {A B : List Act} (hA : NodupAddr A) (hB : NodupAddr B)
    (same : SetEq A B) (clock : Act → Option HlcLift.Stamp) (verb field : String) :
    perSigner clock verb field A = perSigner clock verb field B := by
  funext signer
  exact group_invariant ((hA.currentOwn verb).filter _) ((hB.currentOwn verb).filter _)
    ((currentOwn_invariant hA hB same verb).filter _) clock field

theorem keyed_invariant {A B : List Act} (hA : NodupAddr A) (hB : NodupAddr B)
    (same : SetEq A B) (clock : Act → Option HlcLift.Stamp)
    (verb key field : String) (delete : Option String) :
    keyed clock verb key field delete A = keyed clock verb key field delete B := by
  funext x
  have selected := setEq_trans (current_eq_currentLift hA verb (some key) delete)
    (setEq_trans (currentLift_setEq same verb (some key) delete)
      (current_eq_currentLift hB verb (some key) delete).symm)
  exact group_invariant ((hA.current verb (some key) delete).filter _)
    ((hB.current verb (some key) delete).filter _) (selected.filter _) clock field

/-- All current HLC displays, with every domain applied before supersession
and arbitration. Each domain reads the raw, conflict-aware opener lift. -/
theorem domain_heads_invariant {A B : List Act} (hA : NodupAddr A) (hB : NodupAddr B)
    (same : SetEq A B) (domains : List StateKernelSemantics.Domain)
    (clock : Act → Option HlcLift.Stamp) (verb key field : String) (delete : Option String) :
    scalar clock field (acts verb (domainActs domains A)) =
      scalar clock field (acts verb (domainActs domains B)) ∧
    perSigner clock verb field (domainActs domains A) =
      perSigner clock verb field (domainActs domains B) ∧
    keyed clock verb key field delete (domainActs domains A) =
      keyed clock verb key field delete (domainActs domains B) := by
  have ha := domainActs_unique hA domains
  have hb := domainActs_unique hB domains
  have hs := domainActs_invariant same domains
  exact ⟨scalar_invariant (ha.acts verb) (hb.acts verb) (acts_setEq hs verb) clock field,
    perSigner_invariant ha hb hs clock verb field,
    keyed_invariant ha hb hs clock verb key field delete⟩

/-! Executable value-level regressions, including a domain-excluded
replacer that must not erase an admitted write. -/
private def sampleOpener : Act :=
  ⟨1, "open", "@owner", [], [("options", .list [.str "yes"])], []⟩

private def sampleWrite : Act :=
  ⟨2, "write", "@a", [1], [("choice", .str "yes"), ("value", .str "v")], []⟩

private def sampleOutside : Act :=
  ⟨3, "write", "@a", [1], [("choice", .str "no"), ("value", .str "other")], [2]⟩

private def sampleDomain : StateKernelSemantics.Domain :=
  ⟨"write", "choice", "open", "options"⟩

theorem excluded_replacer_cannot_erase_value :
    perSigner (fun _ => some (10, 0, 0)) "write" "value"
      (domainActs [sampleDomain] [sampleOpener, sampleWrite, sampleOutside]) "@a" =
      some (some (.str "v")) := by decide

theorem unrecognized_group_value_is_absent :
    group (fun _ => none) "value" [sampleWrite] = some none := by decide

theorem nonexistent_group_has_no_entry :
    perSigner (fun _ => none) "write" "value" [sampleWrite] "@missing" = none := by decide

theorem unrelated_delete_survives_domain :
    let deletion : Act := ⟨4, "delete", "@a", [2], [], [2]⟩
    domainActs [sampleDomain] [sampleOpener, sampleWrite, deletion] =
      [sampleOpener, sampleWrite, deletion] := by decide

end HlcFields

end StateLift
end CBCL
