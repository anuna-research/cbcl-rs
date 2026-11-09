import LeanCbcl.StateObservationPlan

/-! SPEC-038 CON-3805: closed conjunction syntax and fault-first Boolean results.
Source-owned query compilation and scope selection remain separate obligations;
these lemmas do not identify arbitrary leaf callbacks with installed sources. -/
set_option autoImplicit false
namespace CBCL.StateCondition
open StateObservation StateObservationPlan

/-- Named fixed-bound reads and authored conjunctions. -/
inductive Condition (V : Type) where
  | read (field : String) (element : V)
  | all (children : List (Condition V))

universe u

/-- Kernel-recursive fold over recognized syntax and its ordered child list. -/
noncomputable def Condition.fold {V : Type} {W : Type u}
    (read : String → V → W) (node : List (Condition V) → List W → W) : Condition V → W :=
  Condition.rec (motive_1 := fun _ => W) (motive_2 := fun _ => List W)
    read node [] (fun _ _ value rest => value :: rest)

/-- The nested recursor retains precisely the original child order. -/
theorem Condition.fold_list {V : Type} {W : Type u}
    (read : String → V → W) (node : List (Condition V) → List W → W) (children : List (Condition V)) :
    Condition.rec_1 (motive_1 := fun _ => W) (motive_2 := fun _ => List W)
      read node [] (fun _ _ value rest => value :: rest) children = children.map (Condition.fold read node) := by
  induction children with
  | nil => rfl
  | cons head tail ih => exact congrArg (List.cons (Condition.fold read node head)) ih

/-- A leaf fold evaluates only its authored fixed-bound source request. -/
@[simp] theorem Condition.fold_read {V : Type} {W : Type u}
    (read : String → V → W) (node : List (Condition V) → List W → W) (field : String) (element : V) :
    Condition.fold read node (.read field element) = read field element := rfl

/-- A conjunction fold visits every child in its authored order. -/
@[simp] theorem Condition.fold_all {V : Type} {W : Type u}
    (read : String → V → W) (node : List (Condition V) → List W → W) (children : List (Condition V)) :
    Condition.fold read node (.all children) = node children (children.map (Condition.fold read node)) := by
  exact congrArg (node children) (Condition.fold_list read node children)

/-- A read counts once; a conjunction counts itself and every child. -/
noncomputable def Condition.size {V : Type} : Condition V → Nat :=
  Condition.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat)
    (fun _ _ => 1) (fun _ total => 1 + total) 0 (fun _ _ value total => value + total)

/-- Kernel-recursive size agrees with the authored sum-of-child-sizes contract. -/
theorem Condition.size_all {V : Type} (children : List (Condition V)) :
    (Condition.all children).size = 1 + (children.map Condition.size).sum := by
  induction children with
  | nil => rfl
  | cons child rest ih =>
    simp only [Condition.size,List.map_cons,List.sum_cons] at *
    omega

/-- Every child fits within the complete conjunction's node budget. -/
theorem Condition.child_size_le {V : Type} (children : List (Condition V)) :
    ∀ child ∈ children, child.size ≤ (Condition.all children).size := by
  induction children with
  | nil => intro child impossible; simp at impossible
  | cons first rest ih =>
    intro child member
    rw [Condition.size_all,List.map_cons,List.sum_cons]
    rcases List.mem_cons.mp member with same | inside
    · subst child; omega
    · have smaller := ih child inside
      rw [Condition.size_all] at smaller
      omega

/-- Constructor validation retains the parser's conjunction arity rule. -/
def Condition.arity {V : Type} : Condition V → Bool
  | .read _ _ => true
  | .all children => decide (2 ≤ children.length) && (children.map Condition.arity).all id

/-- Terminal evidence includes explicitly empty fault sets. -/
def evidence {V : Type} : Observation V → Error
  | .fault ids => some ids
  | .data _ => none

/-- Both fault channels are retained before deciding ordinary success. -/
def merge : Observation Bool → Observation Bool → Observation Bool
  | .fault left, .fault right => .fault (left ∪ right)
  | .fault ids, _ => .fault ids
  | _, .fault ids => .fault ids
  | .data (.reached true), .data (.reached true) => .data (.reached true)
  | _, _ => .data .pending

/-- The empty internal fold is true; authored arity is validated separately. -/
def combine : List (Observation Bool) → Observation Bool
  | [] => .data (.reached true)
  | first :: rest => merge first (combine rest)

/-- Successful leaf alternatives become true; faults retain their evidence. -/
def boolean {V : Type} : Observation V → Observation Bool
  | .fault ids => .fault ids
  | .data (.reached _) => .data (.reached true)
  | .data _ => .data .pending

/-- Interpret recognized syntax through its named source reads. -/
def evaluate {V : Type} (read : String → V → Observation V) : Condition V → Observation Bool
  | .read field element => boolean (read field element)
  | .all children => combine (children.map (evaluate read))

/-- Pending siblings never hide faults. -/
theorem pending_fault (ids : Evidence) : merge (.data .pending) (.fault ids) = .fault ids := rfl

/-- All independent fault witnesses survive. -/
theorem fault_union (left right : Evidence) : merge (.fault left) (.fault right) = .fault (left ∪ right) := rfl

/-- Every successful combination returns exactly true. -/
theorem merge_success (left right : Observation Bool) (value : Bool)
    (success : merge left right = .data (.reached value)) : value = true := by
  cases left with
  | fault ids => cases right <;> simp [merge] at success
  | data left =>
    cases right with
    | fault ids => simp [merge] at success
    | data right =>
      cases left <;> cases right <;> simp [merge] at success
      split at success <;> simp_all

/-- Boolean normalization preserves even empty terminal evidence. -/
theorem boolean_evidence {V : Type} (value : Observation V) : evidence (boolean value) = evidence value := by
  cases value with
  | fault ids => rfl
  | data current => cases current <;> rfl

/-- Conjunction's error channel is exactly the kernel's evidence union. -/
theorem merge_evidence (left right : Observation Bool) :
    evidence (merge left right) = unionError (evidence left) (evidence right) := by
  cases left with
  | fault ids => cases right <;> rfl
  | data left =>
    cases right with
    | fault ids => rfl
    | data right =>
      cases left <;> cases right <;> simp [merge,evidence,unionError]
      rename_i left right
      cases left <;> cases right <;> rfl

/-- Only condition-form reads replace the authored successful alternative. -/
theorem read_success {V : Type} (read : String → V → Observation V) (field : String)
    (element result : V) (success : read field element = .data (.reached result)) :
    evaluate read (.read field element) = .data (.reached true) := by
  simp [evaluate,success,boolean]

/-- The whole conjunction preserves exactly the union of all leaf faults. -/
theorem combine_evidence (values : List (Observation Bool)) :
    evidence (combine values) = (values.map evidence).foldr unionError none := by
  induction values with
  | nil => rfl
  | cons first rest ih => simp only [combine,merge_evidence,List.map_cons,List.foldr_cons,ih]

/-- A successful folded conjunction has no alternative successful Boolean. -/
theorem combine_success (values : List (Observation Bool)) (value : Bool)
    (success : combine values = .data (.reached value)) : value = true := by
  cases values with
  | nil => simpa [combine] using success.symm
  | cons first rest => exact merge_success first (combine rest) value success

/-- Explicitly empty faults remain terminal through all leaf normalization. -/
theorem boolean_fault {V : Type} (ids : Evidence) :
    boolean (V := V) (.fault ids) = .fault ids := rfl

/-- Evidence growth composes without assuming successful or nonempty leaves. -/
theorem combine_grows (left right : List (Observation Bool))
    (growth : List.Forall₂ (fun a b => Grows (evidence a) (evidence b)) left right) :
    Grows (evidence (combine left)) (evidence (combine right)) := by
  induction growth with
  | nil => intro ids impossible; simp [combine,evidence] at impossible
  | cons head tail ih =>
    simpa only [combine,merge_evidence] using unionError_grows head ih

end CBCL.StateCondition
