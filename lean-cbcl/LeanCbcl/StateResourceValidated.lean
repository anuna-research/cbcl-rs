import LeanCbcl.StateResourceFinalize

/-! Native verifier continuation after input/structural validation. The native
budget worklist and every final aggregate rejection branch are composed here.
Opener/root/operation selection is the preceding recognition phase, not an
assumption that the completed resource observation is ordinary. -/
namespace CBCL.StateResourceValidated
open State CheckpointEvidence StateResource StateResourceWitness StateResourceWorklist StateResourceAggregate StateResourceFinalize

/-- The validated resource result: pending, fault evidence, or aggregate snapshot. -/
inductive Read where
  | pending
  | ready (snapshot : AggregateSnapshot)
  | fault

/-- Run the checked budget worklist and finalize the aggregate snapshot. -/
def observe (e : Environment) : Read :=
  match StateResourceWorklist.run e with
  | .fault _ _ _ _ | .internalError => .fault
  | .complete worklist _ _ =>
    if worklist.processed.length = e.known.length then
      match finish e.config e.opener e.known with
      | some snapshot => .ready snapshot
      | none => .fault
    else .pending

/-- Test whether a resource read or traversal result is faulted. -/
def isFault : Read → Bool
  | .fault => true
  | _ => false

/-- Complete post-validation native fault/certificate equivalence. Final
aggregation cannot introduce a fault without a witness: its rejection branches
are proved unreachable from actual successful authorization and representation
bounds, rather than deleted or assumed ordinary. -/
theorem native_validated_certificate_iff (e : Environment) (configuration : NativeConfiguration e.config)
    (accountSlice : ((accounts e.opener.data.selected.initialAllocations).map Prod.fst).length ≤ 2^63 - 1) :
    isFault (observe e) = true ↔ ∃ node, BudgetWitness e.config e.opener node e.known := by
  have correspondence := native_budget_worklist_certificate_iff e
  have verified := native_worklist_verified e
  cases result : StateResourceWorklist.run e with
  | internalError => simp [result,Verified] at verified
  | fault node worklist machine ghost =>
    have witness : ∃ node, BudgetWitness e.config e.opener node e.known := correspondence.mp (by simp [result,StateResourceWorklist.isFault])
    simpa [observe,result,isFault] using (iff_of_true True.intro witness)
  | complete worklist machine ghost =>
    have noWitness : ¬∃ node, BudgetWitness e.config e.opener node e.known := by
      intro witness
      have bad := correspondence.mpr witness
      simp [result,StateResourceWorklist.isFault] at bad
    by_cases size : worklist.processed.length = e.known.length
    · obtain ⟨snapshot,finished,_,_⟩ := native_aggregate_finishes e worklist machine ghost result size configuration accountSlice
      simp [observe,result,size,finished,isFault,noWitness]
    · simp [observe,result,size,isFault,noWitness]

/-- A successful returned native aggregate exposes the proved account fold and
value, rather than a separately supplied display callback. -/
theorem ready_aggregate_value (e : Environment) (configuration : NativeConfiguration e.config)
    (accountSlice : ((accounts e.opener.data.selected.initialAllocations).map Prod.fst).length ≤ 2^63 - 1)
    (snapshot : AggregateSnapshot) (ready : observe e = .ready snapshot) :
    snapshot.rights = accountBalance (StateResourceSolvency.initialSide e false) false e.known ∧
      snapshot.value = (((accounts e.opener.data.selected.initialAllocations).map Prod.fst).map snapshot.rights).sum + e.config.floor := by
  cases result : StateResourceWorklist.run e with
  | internalError => simp [observe,result] at ready
  | fault _ _ _ _ => simp [observe,result] at ready
  | complete worklist machine ghost =>
    by_cases size : worklist.processed.length = e.known.length
    · obtain ⟨actual,finished,rights,value⟩ := native_aggregate_finishes e worklist machine ghost result size configuration accountSlice
      have equal : actual = snapshot := by simpa [observe,result,size,finished] using ready
      subst actual
      exact ⟨rights,value⟩
    · simp [observe,result,size] at ready

end CBCL.StateResourceValidated
