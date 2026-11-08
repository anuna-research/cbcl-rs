import LeanCbcl.StateEvidenceSupport

/-! Finite evidence and delivery for complete typed observation plans.
A replay certificate retains the source history as context; reported witness
identities alone do not imply fault reproduction for arbitrary certified guards. -/
set_option autoImplicit false
namespace CBCL.StateQuasiDeterminism
open State StateLift StateLVar StateObservation StateObservationPlan
open StateKernelDelivery AdmissionStratification StateRefinement

/-- Accepting a faulting source history reproduces its fault, retaining every
reported identity. The finite history is explicit replay context. -/
theorem fault_of_accepting_history {V : Type} (world : Act → Prop)
    (plan : Plan V) {A B : List Act} {e : Evidence}
    (closed : CausallyClosed world A) (includes : ∀ act ∈ A, act ∈ B)
    (fault : observe world plan A = .fault e) :
    ∃ enlarged, observe world plan B = .fault enlarged ∧ ∀ id ∈ e, id ∈ enlarged := by
  have original : errors world (path plan) A = some e := by
    cases observed : errors world (path plan) A with
    | none => simp [observe,observed] at fault
    | some actual =>
      have same : actual = e := by simpa [observe,observed] using fault
      simpa [same] using observed
  obtain ⟨enlarged,current,persist⟩ := errors_persist world (path plan) closed includes e original
  exact ⟨enlarged,by simp [observe,current],persist⟩

/-- Every observed replica fault supplies a finite exact list of accepted
witness identities, and reliable fair delivery propagates that fault forever.
Delivery transfers the finite source history, including its context. -/
theorem finite_fault_dissemination {adm : Admission} {auth : Act → Prop}
    {H : ValidHistory adm} (left right : Replica adm auth H)
    (admission : PredecessorAdmission adm H.contains) {V : Type}
    (plan : Plan V) (atTime : Nat) {e : Evidence}
    (fault : observe H.contains plan (left.run atTime).accepted = .fault e) :
    ∃ ids : List Nat,
      (∀ id, id ∈ ids ↔ id ∈ e) ∧
      (∀ id ∈ ids, id ∈ (left.run atTime).accepted.map Act.addr) ∧
      ∃ t, ∀ n, t ≤ n → ∃ enlarged,
        observe H.contains plan (right.run n).accepted = .fault enlarged ∧
        ∀ id ∈ ids, id ∈ enlarged := by
  obtain ⟨ids,exactIds⟩ := StateEvidenceSupport.observation_finite H.contains plan _ e fault
  have support := StateEvidenceSupport.observation_supported H.contains plan _ e fault
  obtain ⟨t,later⟩ := eventual_composed_fault left right admission plan atTime fault
  refine ⟨ids,exactIds,?_,t,?_⟩
  · intro id member
    exact support id ((exactIds id).mp member)
  · intro n hn
    obtain ⟨enlarged,current,persist⟩ := later n hn
    exact ⟨enlarged,current,fun id member => persist id ((exactIds id).mp member)⟩

/-- In the conflict-free specialization, complete finite-history delivery
converges on all typed data observations, not only on the error channel. -/
theorem conflict_free_strong_eventual_consistency {adm : Admission} {auth : Act → Prop}
    {H : ValidHistory adm} (left right : Replica adm auth H)
    {Index : Type} {Value : Index → Type} (plans : (i : Index) → Plan (Value i))
    (history : List Act) (complete : ∀ act, H.contains act ↔ act ∈ history)
    (leftClear : ∀ n i, errors H.contains (path (plans i)) (left.run n).accepted = none)
    (rightClear : ∀ n i, errors H.contains (path (plans i)) (right.run n).accepted = none) :
    ∃ t, ∀ n m, t ≤ n → t ≤ m → ∀ i,
      data H.contains (plans i) (left.run n).accepted =
      data H.contains (plans i) (right.run m).accepted := by
  obtain ⟨t,converges⟩ := composed_strong_eventual_consistency left right plans history complete
  refine ⟨t,fun n m hn hm i => ?_⟩
  have equal := congrFun (converges n m hn hm) i
  simpa [observeClause,observe,leftClear,rightClear] using equal

/-- Divergent successful checked thresholds yield a finite accepted conflict
certificate on the combined history. -/
theorem threshold_agreement_or_finite_fault {V : Type} (world : Act → Prop)
    (spec : ThresholdSpec) (source : Plan V) {A B : List Act} {a b : spec.Carrier}
    (left : observe world (.threshold spec source) A = .data (.reached a))
    (right : observe world (.threshold spec source) B = .data (.reached b)) :
    a = b ∨ ∃ e, observe world (.threshold spec source) (A ++ B) = .fault e ∧
      ∃ ids : List Nat, (∀ id, id ∈ ids ↔ id ∈ e) ∧
        ∀ id ∈ ids, id ∈ (A ++ B).map Act.addr := by
  rcases threshold_quasi_determinism world spec source left right with equal | ⟨e,fault⟩
  · exact Or.inl equal
  · obtain ⟨ids,exactIds⟩ := StateEvidenceSupport.observation_finite world _ _ e fault
    have support := StateEvidenceSupport.observation_supported world _ _ e fault
    exact Or.inr ⟨e,fault,ids,exactIds,fun id member => support id ((exactIds id).mp member)⟩

end CBCL.StateQuasiDeterminism
