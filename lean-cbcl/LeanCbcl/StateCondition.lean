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

/-- A read counts once; a conjunction counts itself and every child. -/
def Condition.size {V : Type} : Condition V → Nat
  | .read _ _ => 1
  | .all children => 1 + (children.map Condition.size).sum

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
