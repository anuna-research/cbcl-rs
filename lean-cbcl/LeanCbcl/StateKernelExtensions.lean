import LeanCbcl.StateKernelAggregates
import LeanCbcl.BoundedCounter

/-! SPEC-036 raw causal progress and the explicit resource-verifier observation port. -/
namespace CBCL.StateKernelExtensions
open CBCL.State

/-- Independent progress denotation: least upper bound of established positions. -/
def ProgressMeaning (store : Repeat.Store) (thread : Nat) (verb : String) (limit : Nat)
    (A : List Act) (n : Nat) : Prop :=
  ∀ upper, n ≤ upper ↔ ∀ a ∈ A, ∀ position,
    Repeat.At store thread verb limit a.addr position → position ≤ upper

/-- Resolver soundness/completeness connects the reduction to established ranks. -/
theorem progress_correct (store : Repeat.Store) (thread : Nat) (verb : String) (limit : Nat)
    (A : List Act) : ProgressMeaning store thread verb limit A
      (protocolProgress store thread verb limit A) := by
  intro upper
  unfold protocolProgress StateProgress.progress
  rw [StateProgress.maximum_le]
  constructor
  · intro all a ha position established
    have resolved := Repeat.resolve_complete established (limit + 1) (by have := Repeat.at_bounds established; omega)
    have member : StateProgress.position store thread verb limit a.addr ∈
        List.map (StateProgress.position store thread verb limit) (List.map Act.addr A) :=
      List.mem_map.mpr ⟨a.addr, List.mem_map.mpr ⟨a, ha, rfl⟩, rfl⟩
    have bound := all _ member
    simpa [StateProgress.position, resolved] using bound
  · intro all position member
    obtain ⟨address, hm, rfl⟩ := List.mem_map.mp member
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
    unfold StateProgress.position
    cases h : Repeat.resolve (limit + 1) store thread verb limit a.addr with
    | unknown => exact Nat.zero_le _
    | invalid => exact Nat.zero_le _
    | position rank => exact all a ha rank (Repeat.resolve_sound _ h)

theorem progress_unique {store : Repeat.Store} {thread : Nat} {verb : String} {limit : Nat}
    {A : List Act} {a b : Nat} (ha : ProgressMeaning store thread verb limit A a)
    (hb : ProgressMeaning store thread verb limit A b) : a = b := by
  exact Nat.le_antisymm ((ha b).mpr ((hb b).mp (Nat.le_refl _)))
    ((hb a).mpr ((ha a).mp (Nat.le_refl _)))

/-- The port consumes a verifier outcome, not an unverified external flag.
This type does not prove that the verifier classified the raw history correctly. -/
inductive ResourceInput where
  | pending (missing : List Nat)
  | fault (reason : String) (evidence : List Nat)
  | ready (floor : Int) (accounts : List (String × BoundedCounter.Budget)) (ceiling : Option Int)

/-- Tagged kernel observations never expose a numeric balance for pending/fault. -/
inductive ResourceView where
  | pending (missing : List Nat)
  | fault (reason : String) (evidence : List Nat)
  | ready (value : Int) (rights : List (String × Nat)) (headroom : Option (List (String × Nat)))
  deriving DecidableEq

/-- The observation adapter computes totals and per-owner budgets from typed evidence. -/
def resourceObserve : ResourceInput → ResourceView
  | .pending missing => .pending missing
  | .fault reason evidence => .fault reason evidence
  | .ready floor accounts ceiling => .ready
      (BoundedCounter.value floor (accounts.map Prod.snd))
      (accounts.map (fun (owner, budget) => (owner, budget.rights)))
      (ceiling.map (fun _ => accounts.map (fun (owner, budget) => (owner, budget.headroom))))

/-- Independent graph for the adapter. Classification remains outside this relation. -/
inductive ResourceMeaning : ResourceInput → ResourceView → Prop where
  | pending (missing) : ResourceMeaning (.pending missing) (.pending missing)
  | fault (reason evidence) : ResourceMeaning (.fault reason evidence) (.fault reason evidence)
  | ready (floor : Int) (accounts : List (String × BoundedCounter.Budget))
      (ceiling : Option Int) (value : Int) (rights : List (String × Nat))
      (headroom : Option (List (String × Nat)))
      (balance : value = floor + Int.ofNat ((accounts.map (fun p => p.2.rights)).sum))
      (owned : rights = accounts.map (fun p => (p.1, p.2.rights)))
      (capacity : headroom = match ceiling with
        | none => none
        | some _ => some (accounts.map (fun p => (p.1, p.2.headroom)))) :
      ResourceMeaning (.ready floor accounts ceiling) (.ready value rights headroom)

/-- Complete adapter correctness, without any premise about a desired output. -/
theorem resource_correct (input : ResourceInput) : ResourceMeaning input (resourceObserve input) := by
  cases input with
  | pending missing => exact .pending missing
  | fault reason evidence => exact .fault reason evidence
  | ready floor accounts ceiling =>
      apply ResourceMeaning.ready
      · simp [BoundedCounter.value, BoundedCounter.rightsTotal, List.map_map, Function.comp_def]
      · rfl
      · cases ceiling <;> rfl

/-- Resource adapter semantics has one possible tagged result. -/
theorem resource_unique {input : ResourceInput} {a b : ResourceView}
    (ha : ResourceMeaning input a) (hb : ResourceMeaning input b) : a = b := by
  cases ha <;> cases hb
  case ready.ready balance owned capacity balance' owned' capacity' =>
    simp_all
  all_goals rfl

/-- Numeric extraction makes the pending/fault safety boundary explicit. -/
def ResourceView.balance : ResourceView → Option Int
  | .ready value _ _ => some value
  | _ => none

theorem resource_pending_nonnumeric (missing : List Nat) :
    (resourceObserve (.pending missing)).balance = none := rfl

theorem resource_fault_nonnumeric (reason : String) (evidence : List Nat) :
    (resourceObserve (.fault reason evidence)).balance = none := rfl

/-- Ready lower-bound arithmetic reuses the independent budget model. -/
theorem resource_floor (floor : Int) (accounts : List (String × BoundedCounter.Budget)) :
    floor ≤ BoundedCounter.value floor (accounts.map Prod.snd) :=
  BoundedCounter.floor_preserved floor _

/-- Ceiling claims retain the independently supplied allocation equation. -/
theorem resource_ceiling (floor ceiling : Int) (accounts : List (String × BoundedCounter.Budget))
    (allocation : (BoundedCounter.rightsTotal (accounts.map Prod.snd) : Int) +
      BoundedCounter.headroomTotal (accounts.map Prod.snd) = ceiling - floor) :
    BoundedCounter.value floor (accounts.map Prod.snd) ≤ ceiling :=
  BoundedCounter.ceiling_preserved floor ceiling _ allocation

end CBCL.StateKernelExtensions
