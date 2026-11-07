import LeanCbcl.CheckpointSummary

/-! Native render transfer from compact rows: only selected contributions, not
raw histories, agree. Input updates preserve typed clock and signer-rank evidence. -/
namespace CBCL.CheckpointRender
open State StateKernelSemantics StateKernelQueries StateKernel StateKernelSEC
open CheckpointSummary

@[simp] theorem admitted_empty (A : List Act) : admitted [] A = A := by
  induction A with
  | nil => rfl
  | cons a A ih =>
    change a :: admitted [] A = a :: A
    rw [ih]

theorem selected_current {v : String} {k d : Option String} {H : List Act} {s : Row}
    (valid : Invariant (.current v k d) H s) :
    SetEq (select s.live (.current v k d)) (select H (.current v k d)) := by
  intro a
  exact (current_live_fixed valid a).trans (live_current valid a)

theorem selected_own {v : String} {H : List Act} {s : Row}
    (valid : Invariant (.own v) H s) :
    SetEq (select s.live (.own v)) (select H (.own v)) := by
  intro a
  exact (own_live_fixed valid a).trans (live_own valid a)

/-- Multi-value grouping depends only on selected contributors. -/
theorem evalValuesBy_selected {A B : List Act} {source : Selection}
    (same : SetEq (select A source) (select B source)) (key field : String) :
    ValueMapEquivalent (evalValuesBy A source key field) (evalValuesBy B source key field) := by
  simp only [SetEq] at same
  constructor
  · intro k
    simp only [evalValuesBy, uniqueKeys_member, List.mem_filterMap]
    simp only [same]
  · intro k _
    apply funext
    intro v
    apply has_setEq
    intro a
    simp only [List.mem_filter, same]

/-- Grouping and arbitration require only selected-set equality. -/
theorem evalMap_selected {A B : List Act} {plan : MapPlan}
    (same : SetEq (select A plan.source) (select B plan.source))
    (unique : NodupAddr (select B plan.source)) (clock : Clock) (rank : SignerRank) :
    MapEquivalent (evalMap clock rank A plan) (evalMap clock rank B plan) := by
  simp only [SetEq] at same
  constructor
  · intro k
    simp only [evalMap, uniqueKeys_member, List.mem_filterMap]
    simp only [same]
  · intro k _
    change project plan.field plan.event _ = project plan.field plan.event _
    congr 1
    apply choose_setEq (unique.filter _) _ clock rank plan.policy
    intro a
    simp only [List.mem_filter, same]

theorem values_render (input : Input) {H : List Act} {s : Row} {v : String}
    (valid : Invariant (.current v none none) H s) (field : String) :
    Equivalent (evaluate {input with acts := s.live} [] (.distinct (.current v none none) field))
      (evaluate {input with acts := H} [] (.distinct (.current v none none) field)) := by
  change has field (select (admitted [] s.live) (.current v none none)) =
    has field (select (admitted [] H) (.current v none none))
  simpa [admitted_empty] using funext (has_setEq (selected_current valid) field)

theorem valuesPerKey_render (input : Input) {H : List Act} {s : Row}
    {v key : String} {delete : Option String}
    (valid : Invariant (.current v (some key) delete) H s) (field : String) :
    Equivalent (evaluate {input with acts := s.live} [] (.valuesBy (.current v (some key) delete) key field))
      (evaluate {input with acts := H} [] (.valuesBy (.current v (some key) delete) key field)) := by
  simpa [evaluate, Equivalent, admitted_empty] using evalValuesBy_selected (selected_current valid) key field

theorem observedSet_render (input : Input) {H : List Act} {s : Row}
    {add remove field : String}
    (valid : Invariant (.current add (some field) (some remove)) H s) :
    Equivalent (evaluate {input with acts := s.live} [] (.distinct (.current add (some field) (some remove)) field))
      (evaluate {input with acts := H} [] (.distinct (.current add (some field) (some remove)) field)) := by
  change has field (select (admitted [] s.live) (.current add (some field) (some remove))) =
    has field (select (admitted [] H) (.current add (some field) (some remove)))
  simpa [admitted_empty] using funext (has_setEq (selected_current valid) field)

theorem lwwMap_render (input : Input) {H : List Act} {s : Row}
    {v key : String} {delete : Option String}
    (valid : Invariant (.current v (some key) delete) H s)
    (unique : NodupAddr H) (field clockField : String) :
    Equivalent (evaluate {input with acts := s.live} []
      (.mapped ⟨.current v (some key) delete, .key key, .hlc clockField, field, false⟩))
      (evaluate {input with acts := H} []
      (.mapped ⟨.current v (some key) delete, .key key, .hlc clockField, field, false⟩)) := by
  simpa [evaluate, Equivalent, admitted_empty] using
    (evalMap_selected (plan := ⟨.current v (some key) delete, .key key, .hlc clockField, field, false⟩)
      (selected_current valid) (select_unique unique _) input.clock input.signerRank)

theorem lwwPerSigner_render (input : Input) {H : List Act} {s : Row} {v : String}
    (valid : Invariant (.own v) H s) (unique : NodupAddr H) (field clockField : String) :
    Equivalent (evaluate {input with acts := s.live} []
      (.mapped ⟨.own v, .signer, .hlc clockField, field, false⟩))
      (evaluate {input with acts := H} []
      (.mapped ⟨.own v, .signer, .hlc clockField, field, false⟩)) := by
  simpa [evaluate, Equivalent, admitted_empty] using
    (evalMap_selected (plan := ⟨.own v, .signer, .hlc clockField, field, false⟩)
      (selected_own valid) (select_unique unique _) input.clock input.signerRank)

end CBCL.CheckpointRender
