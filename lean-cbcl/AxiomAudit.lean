import LeanCbcl.Lattice.NotALattice
import LeanCbcl.ConsensusFree
import LeanCbcl.ConsensusFree.Liveness
import LeanCbcl.ConsensusFree.Scheduler
import LeanCbcl.AbortableHandoff
import LeanCbcl.SealedCheckpoint
import LeanCbcl.ValidatorBudgetRefutation
import LeanCbcl.ValidatorBudget
import LeanCbcl.Lattice.Result
import LeanCbcl.Lattice.Store
import LeanCbcl.Verify
import LeanCbcl.R5
import LeanCbcl.DCFLPreservation
import LeanCbcl.R6DCFLPreservation
import LeanCbcl.State
import LeanCbcl.AdmissionStratification
import LeanCbcl.StateRefinement
import LeanCbcl.MonitoredDCFL

import LeanCbcl.EPPCompletion
import LeanCbcl.ProtocolProjection
import LeanCbcl.ConcreteProjection
import LeanCbcl.Splice
import LeanCbcl.Bridge
import LeanCbcl.Repeat
import LeanCbcl.StateProgress

/-!
# Axiom audit — NFR-511 / TEST-551 / OBS-512

`#print axioms` for each top-level theorem named in CON-510 through
CON-516 (SPEC-005 §Contracts), plus the SPEC-014 EPP-correspondence
family (`EPP.lean`, `EPPCompletion.lean`, `Projectability.lean`,
`ProtocolProjection.lean`, `ConcreteProjection.lean`, `Splice.lean`, `Bridge.lean`), whose axiom
claim in `proofs/epp-correspondence/proof.tex` §Notes ("propext,
Classical.choice, Quot.sound only") is enforced here. The companion shell script
`scripts/check-axioms.sh` runs this file via `lake env lean`, parses the
emitted `'<thm>' depends on axioms: [...]` lines, and fails CI if any
axiom outside the allowlist appears.

Allowlist (kept in sync with the shell script and with NFR-511 +
ADR-515 in `specs/SPEC-005-lean-mechanisation.md`):

* `Classical.choice`, `propext`, `Quot.sound` — the standard Lean kernel
  axioms permitted by NFR-511 clause 1.
* `CBCL.ContentHash`, `CBCL.contentHash`, `CBCL.contentHash_injective` —
  the cryptographic-hash carrier and the injectivity assumption justified
  by ADR-515. Located in `LeanCbcl/Lattice/Store.lean`.
* `CBCL.Message.causedBy` — opaque accessor for the `:caused-by` field of
  the abstract `Message` type, also justified by ADR-515. Located in
  `LeanCbcl/Verify.lean`. The Rust implementation pulls the field from a
  parsed S-expression; the Lean model treats it as an abstract accessor
  since `Message` itself is abstract on the verify side.

NFR-511 clause 2 admits *only* the four project axioms above. Any further
project axiom requires an amendment to ADR-515, not merely an allowlist
edit in the script and this header.

Historical note: an earlier draft also declared
`CBCL.ContentHash.instNonempty : Nonempty ContentHash` as a bookkeeping
axiom anticipating `Option ContentHash`-returning helpers. Empirically
none of CON-510..516 transitively depended on it (the `lookup` proofs
go via `Classical.choice` directly, not via `Option.choice`/`Inhabited`
defaults), so the axiom was removed to keep the allowlist minimal. If
the deferred `LookupSpec` mechanisation needs a `Nonempty ContentHash`
instance it should be reintroduced together with a `#print axioms` line
that exercises it.

If a future theorem joins CON-510..516, add a `#print axioms` line for it
below — the shell script discovers theorems from this file's output, so
editing only this file is enough to extend the audit.
-/

-- CON-510 — Strong Kleene truth-order lattice (Lattice/Result.lean).
#print axioms CBCL.VerificationResult.result_meet_table
#print axioms CBCL.VerificationResult.result_join_table

#print axioms CBCL.VerificationResult.meet_absorption
#print axioms CBCL.VerificationResult.join_absorption
#print axioms CBCL.VerificationResult.meet_distributive
#print axioms CBCL.VerificationResult.join_distributive
#print axioms CBCL.VerificationResult.meet_knowledge_mono
#print axioms CBCL.VerificationResult.join_knowledge_mono

-- CON-511 — Message store G-Set (Lattice/Store.lean).
#print axioms CBCL.MessageStore.union_assoc
#print axioms CBCL.MessageStore.union_comm
#print axioms CBCL.MessageStore.union_idem
#print axioms CBCL.MessageStore.append_eq_union_singleton
#print axioms CBCL.MessageStore.lookup_monotone

#print axioms CBCL.verify_any_empty
#print axioms CBCL.verify_any_singleton

-- CON-512 — `verify` monotonicity (Verify.lean).
#print axioms CBCL.verify_monotone

-- CON-513 — `verify` fan-in lattice-homomorphism (Verify.lean).
#print axioms CBCL.verify_all_is_meet

-- CON-514 — `verify` eventual consistency (Verify.lean).
#print axioms CBCL.verify_eventually_consistent

-- CON-515 — R5 sub-check soundness + completeness (R5.lean).
#print axioms CBCL.check_acyclicity_iff_no_cycle
#print axioms CBCL.check_reachability_iff_all_reachable
#print axioms CBCL.check_performative_definedness_iff_all_defined
#print axioms CBCL.check_step_uniqueness_iff_no_duplicates

-- CON-516 — DCFL preservation (DCFLPreservation.lean).
#print axioms CBCL.DCFLPreservation.dcfl_preserved_under_protocol
#print axioms CBCL.DCFLPreservation.dcfl_preserved_under_shape

-- DCFL preservation at R6: role syntax + trace regularity (R6DCFLPreservation.lean;
-- `proof.tex` Prop. dcfl, SPEC-014 ADR-600/CON-600).
#print axioms CBCL.R6DCFLPreservation.dcfl_preserved_under_roles
#print axioms CBCL.R6DCFLPreservation.dcfl_preserved_under_with_roles
#print axioms CBCL.R6DCFLPreservation.roles_dispatch_currently_unwired
#print axioms CBCL.R6DCFLPreservation.causalTrace_iff_run
#print axioms CBCL.R6DCFLPreservation.causalTrace_regular
#print axioms CBCL.R6DCFLPreservation.causalTrace_isTraceDCFL
#print axioms CBCL.R6DCFLPreservation.storeTrace_iff_run
#print axioms CBCL.R6DCFLPreservation.storeTrace_regular
#print axioms CBCL.R6DCFLPreservation.storeTrace_isTraceDCFL
#print axioms CBCL.R6DCFLPreservation.causalTrace_storeTrace
#print axioms CBCL.R6DCFLPreservation.localTrace_regular
#print axioms CBCL.R6DCFLPreservation.localStoreTrace_regular
#print axioms CBCL.R6DCFLPreservation.localTrace_isTraceDCFL
#print axioms CBCL.R6DCFLPreservation.projection_adds_no_recogniser

-- EPP correspondence, safety + completion levels (EPP.lean, EPPCompletion.lean).
-- `proof.tex` §Notes claims "no sorry; axioms propext, Classical.choice, Quot.sound"
-- for these; this audit enforces that claim in CI (SPEC-014).
#print axioms LeanCbcl.EPP.epp_correspondence
#print axioms LeanCbcl.EPP.soundness_safety
#print axioms LeanCbcl.EPP.completeness_safety
#print axioms LeanCbcl.EPP.reconcile_global
#print axioms LeanCbcl.EPP.valid_stable
#print axioms LeanCbcl.EPP.violation_stable
#print axioms LeanCbcl.EPP.epp_correspondence_complete

-- Theorem 1: causal-locality sufficiency and a nonlocal counterexample (Projectability.lean).
#print axioms LeanCbcl.Projectability.projectability_sufficiency_and_counterexample
#print axioms LeanCbcl.Projectability.nonlocal_protocol_counterexample

-- Protocol-projection agreement interface (ProtocolProjection.lean).
#print axioms LeanCbcl.ProtoProjection.verdict_agree
#print axioms LeanCbcl.ProtoProjection.local_protocol_verification_agrees

-- Splicing necessity / type-opacity / openings (Splice.lean).
#print axioms LeanCbcl.Splice.type_opacity_indistinguishability
#print axioms LeanCbcl.Splice.resolution_requires_preimage
#print axioms LeanCbcl.Splice.spliced_pred_permanently_unknown
#print axioms LeanCbcl.Splice.decidesAll_iff_predsLocal
#print axioms LeanCbcl.Splice.openings_suffice
#print axioms LeanCbcl.Splice.openings_suffice_concrete

-- Temporal bridge (Bridge.lean).
#print axioms LeanCbcl.Bridge.bridge_stability
#print axioms LeanCbcl.Bridge.bridge_compatibility
#print axioms LeanCbcl.Bridge.temporal_bridge

#print axioms LeanCbcl.Bridge.eventually_present_valid
#print axioms LeanCbcl.Bridge.InfinitePredecessorsExample.not_finite_predecessors

-- Concrete raw-edge projection and the paper's filtered view.
#print axioms LeanCbcl.ConcreteProjection.runSteps_refines
#print axioms LeanCbcl.ConcreteProjection.project_steps
#print axioms LeanCbcl.ConcreteProjection.project_protocol
#print axioms LeanCbcl.ConcreteProjection.project_agrees
#print axioms LeanCbcl.ConcreteProjection.projected_verification_agrees
#print axioms LeanCbcl.ConcreteProjection.lookup_restrict
#print axioms LeanCbcl.ConcreteProjection.roleView_agrees
#print axioms LeanCbcl.ConcreteProjection.roleView_verification_agrees
#print axioms LeanCbcl.ConcreteProjection.retained_predecessor
#print axioms LeanCbcl.ConcreteProjection.specifiedStep_isSome
#print axioms LeanCbcl.ConcreteProjection.specifiedStep_of_agreement
#print axioms LeanCbcl.ConcreteProjection.roleView_begin
#print axioms LeanCbcl.ConcreteProjection.RootedExample.projected_valid

#print axioms LeanCbcl.ConcreteProjection.checkAnnotationsConsistent_iff
#print axioms LeanCbcl.ConcreteProjection.specifiedStep_matches_annotation
#print axioms LeanCbcl.ConcreteProjection.concreteStore_eq_project
#print axioms LeanCbcl.ConcreteProjection.concrete_verification_agrees
#print axioms LeanCbcl.ConcreteProjection.RootedExample.concrete_valid
#print axioms LeanCbcl.ConcreteProjection.RootedExample.bystander_erased

-- State layer, R7 (SPEC-019 REQ-1930; State.lean). Every rule is a set
-- function of the accepted acts; registers characterised; sums once per
-- address; the binder's predecessor, :replaces, and supersession are sound.
#print axioms CBCL.State.fold_perm_invariant
#print axioms CBCL.State.fold_dedup_invariant
#print axioms CBCL.State.pickAct_setEq
#print axioms CBCL.State.acts_mono
#print axioms CBCL.State.count_mono
#print axioms CBCL.State.has_mono
#print axioms CBCL.State.exists_mono
#print axioms CBCL.State.mem_current_iff
#print axioms CBCL.State.replaced_never_current
#print axioms CBCL.State.unnamed_is_current
#print axioms CBCL.State.registerPerKey_from_current
#print axioms CBCL.State.sumField_insert
#print axioms CBCL.State.intend_pred_valid
#print axioms CBCL.State.intend_replaces_current
#print axioms CBCL.State.intend_supersedes
#print axioms CBCL.State.intend_current_after
-- Scalar lists, the per-key histogram, and the domain filter (SPEC-019 ADR-1909).
#print axioms CBCL.State.histogramPerKey_setEq
#print axioms CBCL.State.allowedOf_setEq
#print axioms CBCL.State.actsDom_setEq
#print axioms CBCL.State.actsDom_excluded
#print axioms CBCL.State.excluded_not_mem
-- Admission never reads state (SPEC-019 REQ-1914, ADR-1909;
-- AdmissionStratification.lean): stratification, regularity of the R7 store
-- language, and the two necessity results.
#print axioms CBCL.AdmissionStratification.admit_skeleton_invariant
#print axioms CBCL.AdmissionStratification.admit_ignores_data
#print axioms CBCL.AdmissionStratification.fold_reads_data
#print axioms CBCL.AdmissionStratification.storeAccepts_iff
#print axioms CBCL.AdmissionStratification.localStoreTrace_iff_run
#print axioms CBCL.AdmissionStratification.localStoreTrace_regular
#print axioms CBCL.AdmissionStratification.r7Store_regular
#print axioms CBCL.AdmissionStratification.r7Store_isTraceDCFL
#print axioms CBCL.AdmissionStratification.r7Admission_sticky
#print axioms CBCL.AdmissionStratification.pigeonhole
#print axioms CBCL.AdmissionStratification.countGated_not_regular
#print axioms CBCL.AdmissionStratification.domain_feedback_not_sticky

-- Signer-owned register selection and binding (issue 18; TEST-1953).
#print axioms CBCL.State.currentOwn_setEq
#print axioms CBCL.State.mem_currentOwn_iff
#print axioms CBCL.State.currentOwn_crossSigner
#print axioms CBCL.State.currentOwn_replaced
#print axioms CBCL.State.intendOwn_replaces_current
#print axioms CBCL.State.intendOwn_supersedes
#print axioms CBCL.State.intendOwn_crossSigner
#print axioms CBCL.State.intendOwn_pred_valid
#print axioms CBCL.State.intendOwn_current_after

-- State execution refinement (SPEC-019 CON-1906; TEST-1954–1958).
#print axioms CBCL.StateRefinement.initial_wellFormed
#print axioms CBCL.StateRefinement.step_wellFormed
#print axioms CBCL.StateRefinement.reachable_wellFormed
#print axioms CBCL.StateRefinement.accepted_authenticated
#print axioms CBCL.StateRefinement.new_accepted_received
#print axioms CBCL.StateRefinement.accepted_address_conflict_impossible
#print axioms CBCL.StateRefinement.accept_requires_pending
#print axioms CBCL.StateRefinement.internal_preserves_accepted
#print axioms CBCL.StateRefinement.step_simulation
#print axioms CBCL.StateRefinement.reachable_simulation
#print axioms CBCL.StateRefinement.behavior_reachable
#print axioms CBCL.StateRefinement.behavior_refinement
#print axioms CBCL.StateRefinement.fresh_acceptance_effect
#print axioms CBCL.StateRefinement.Examples.false_business_cannot_simulate
#print axioms CBCL.StateRefinement.counter_insert_effect
#print axioms CBCL.StateRefinement.counter_simulation
#print axioms CBCL.StateRefinement.counter_behavior_refinement
#print axioms CBCL.StateRefinement.Examples.out_of_order_reachable
#print axioms CBCL.StateRefinement.Examples.out_of_order_balance
#print axioms CBCL.StateRefinement.Examples.duplicate_does_not_count
#print axioms CBCL.StateRefinement.Examples.decrement_not_addition
#print axioms CBCL.StateRefinement.Examples.receipt_not_acceptance
#print axioms CBCL.StateRefinement.Examples.absent_candidate_cannot_accept
#print axioms CBCL.StateRefinement.Examples.missing_predecessor_cannot_accept
#print axioms CBCL.StateRefinement.Examples.conflicting_history_not_reachable

-- Bounded repeat expansion and causal positions (SPEC-015 REQ-704).
#print axioms CBCL.Repeat.copy_base
#print axioms CBCL.Repeat.copy_injective
#print axioms CBCL.Repeat.expand_length
#print axioms CBCL.Repeat.copy_all
#print axioms CBCL.Repeat.copy_any
#print axioms CBCL.Repeat.at_bounds
#print axioms CBCL.Repeat.no_position_101
#print axioms CBCL.Repeat.resolve_sound
#print axioms CBCL.Repeat.resolve_complete
#print axioms CBCL.Repeat.at_monotone
#print axioms CBCL.Repeat.resolve_stable
#print axioms CBCL.Repeat.absent_invalid
#print axioms CBCL.Repeat.missing_unknown
#print axioms CBCL.Repeat.copyNode_wireNames
#print axioms CBCL.Repeat.mem_expand
#print axioms CBCL.Repeat.copy_not_plain
#print axioms CBCL.Repeat.at_expanded_member

-- Protocol progress state selection and maximum reduction.
#print axioms CBCL.StateProgress.maximum_le
#print axioms CBCL.StateProgress.le_maximum
#print axioms CBCL.StateProgress.maximum_setEq
#print axioms CBCL.StateProgress.progress_empty
#print axioms CBCL.StateProgress.position_bound
#print axioms CBCL.StateProgress.progress_bound
#print axioms CBCL.StateProgress.progress_setEq
#print axioms CBCL.StateProgress.progress_perm
#print axioms CBCL.StateProgress.progress_duplicate
#print axioms CBCL.StateProgress.position_monotone
#print axioms CBCL.StateProgress.progress_monotone
#print axioms CBCL.StateProgress.progress_at_bound_stable
#print axioms CBCL.StateProgress.progress_append
#print axioms CBCL.State.protocolProgress_setEq
#print axioms CBCL.State.protocolProgress_duplicate
#print axioms CBCL.State.protocolProgress_bound
#print axioms CBCL.State.protocolProgress_monotone
#print axioms CBCL.StateProgress.progress_competing
-- Finite-state restrictions: all-word product correspondence and installation.
#print axioms CBCL.FormalLanguage.Monitor.product_step
#print axioms CBCL.FormalLanguage.Monitor.product_run
#print axioms CBCL.FormalLanguage.Monitor.product_accepts
#print axioms CBCL.FormalLanguage.IsRealtimeDCFL.restrict
#print axioms CBCL.InstalledSyntax.Raw.monitored_dcfl_preserved_many
#print axioms CBCL.InstalledSyntax.Raw.monitored_accepted_installations_dcfl
#print axioms CBCL.InstalledSyntax.Raw.monitored_check_correct

-- SPEC-021: validator signing-capacity and finality core; no lifecycle refinement claim.
#print axioms CBCL.ValidatorBudget.quorum_coverage
#print axioms CBCL.ValidatorBudget.certified_consumption_bound
#print axioms CBCL.ValidatorBudget.both_consumption_bounds
#print axioms CBCL.ValidatorBudget.fixed_checkpoint_bounds
#print axioms CBCL.ValidatorBudget.certified_batch_bounds
#print axioms CBCL.ValidatorBudget.reserve_nonnegative
#print axioms CBCL.ValidatorBudget.reservation_replay
#print axioms CBCL.ValidatorBudget.reconciliation_preserves_exposure
#print axioms CBCL.ValidatorBudget.finality_excludes_no_commit
#print axioms CBCL.ValidatorBudget.execute_preserves_discipline
#print axioms CBCL.ValidatorBudget.fence_preserves_discipline
#print axioms CBCL.ValidatorBudget.receipt_monotone
#print axioms CBCL.ValidatorBudget.receipt_replay

-- SPEC-021 BUG-2100: guarded counterexample, not an asynchronous safety proof.
#print axioms CBCL.ValidatorBudgetRefutation.guarded_trace
#print axioms CBCL.ValidatorBudgetRefutation.old_certificates
#print axioms CBCL.ValidatorBudgetRefutation.partial_update_budgets
#print axioms CBCL.ValidatorBudgetRefutation.all_final
#print axioms CBCL.ValidatorBudgetRefutation.final_quorums
#print axioms CBCL.ValidatorBudgetRefutation.overspent
#print axioms CBCL.ValidatorBudgetRefutation.nonnegative_adopters_trace
#print axioms CBCL.ValidatorBudgetRefutation.nonnegative_adopters_budgets
#print axioms CBCL.ValidatorBudgetRefutation.quorum_adopted_partial_update
#print axioms CBCL.ValidatorBudgetRefutation.nonnegative_adopters_overspent
#print axioms CBCL.ValidatorBudgetRefutation.no_funded_refinement

#print axioms CBCL.SealedCheckpoint.step_capacity
#print axioms CBCL.SealedCheckpoint.step_bounded
#print axioms CBCL.SealedCheckpoint.reachable_bounded
#print axioms CBCL.SealedCheckpoint.frozen_step
#print axioms CBCL.SealedCheckpoint.frozen_journal
#print axioms CBCL.SealedCheckpoint.finalized_nonnegative
#print axioms CBCL.SealedCheckpoint.unique_successor
#print axioms CBCL.SealedCheckpoint.late_certificate_carried

#print axioms CBCL.SealedCheckpoint.disjoint_vote_bound
#print axioms CBCL.SealedCheckpoint.honest_intersection

#print axioms CBCL.AbortableHandoff.step_snapshot
#print axioms CBCL.AbortableHandoff.reachable_snapshot
#print axioms CBCL.AbortableHandoff.stopped_step
#print axioms CBCL.AbortableHandoff.stopped_reach
#print axioms CBCL.AbortableHandoff.activation_preserved_in_handoff
#print axioms CBCL.AbortableHandoff.prepare_unique
#print axioms CBCL.AbortableHandoff.reachable_activation_preserved
#print axioms CBCL.AbortableHandoff.recovery_preserves_activation

#print axioms CBCL.ConsensusFree.isum_congr
#print axioms CBCL.ConsensusFree.isum_nonneg
#print axioms CBCL.ConsensusFree.isum_member
#print axioms CBCL.ConsensusFree.isum_update
#print axioms CBCL.ConsensusFree.finRange_unique
#print axioms CBCL.ConsensusFree.isum_add
#print axioms CBCL.ConsensusFree.isum_sub
#print axioms CBCL.ConsensusFree.isum_append

#print axioms CBCL.ConsensusFree.static_facts
#print axioms CBCL.ConsensusFree.known_extension
#print axioms CBCL.ConsensusFree.known_unique
#print axioms CBCL.ConsensusFree.manifest_persistent
#print axioms CBCL.ConsensusFree.slot_known
#print axioms CBCL.ConsensusFree.certificate_same_slot
#print axioms CBCL.ConsensusFree.record_extension
#print axioms CBCL.ConsensusFree.step_archive_extension
#print axioms CBCL.ConsensusFree.record_slot_cases
#print axioms CBCL.ConsensusFree.record_frontier_mono
#print axioms CBCL.ConsensusFree.record_catalogue
#print axioms CBCL.ConsensusFree.catalogue_transport
#print axioms CBCL.ConsensusFree.step_catalogue

#print axioms CBCL.ConsensusFree.step_capacity
#print axioms CBCL.ConsensusFree.sumOn_filter
#print axioms CBCL.ConsensusFree.certified_bound
#print axioms CBCL.ConsensusFree.epoch_final_consumption



#print axioms CBCL.ConsensusFree.old_operation_held
#print axioms CBCL.ConsensusFree.known_refund_cancel
#print axioms CBCL.ConsensusFree.known_credit_final
#print axioms CBCL.ConsensusFree.isum_cast
#print axioms CBCL.ConsensusFree.marked_cast
#print axioms CBCL.ConsensusFree.held_net_identity
#print axioms CBCL.ConsensusFree.epoch_books
#print axioms CBCL.ConsensusFree.manifest_credit_bounded
#print axioms CBCL.ConsensusFree.final_cost_partition
#print axioms CBCL.ConsensusFree.resource_nonnegative

#print axioms CBCL.ConsensusFree.Currency.rights_ne_headroom
#print axioms CBCL.ConsensusFree.Currency.rights_injective
#print axioms CBCL.ConsensusFree.Currency.headroom_injective
#print axioms CBCL.ConsensusFree.Currency.atoms_disjoint
#print axioms CBCL.ConsensusFree.Currency.cost_local
#print axioms CBCL.ConsensusFree.Currency.vectors_disjoint
#print axioms CBCL.ConsensusFree.Currency.mint_requires_issuer
#print axioms CBCL.ConsensusFree.Currency.headroom_requires_cap
#print axioms CBCL.ConsensusFree.Currency.atom_total
#print axioms CBCL.ConsensusFree.Currency.capped_conservation
#print axioms CBCL.ConsensusFree.Currency.business_conservation
#print axioms CBCL.ConsensusFree.Currency.business_run_conservation
#print axioms CBCL.ConsensusFree.Currency.total_split
#print axioms CBCL.ConsensusFree.Currency.currency_floor
#print axioms CBCL.ConsensusFree.Currency.currency_ceiling

#print axioms CBCL.ConsensusFree.step_evidence
#print axioms CBCL.ConsensusFree.step_locals

#print axioms CBCL.ConsensusFree.perform_sound
#print axioms CBCL.ConsensusFree.execute_sound
#print axioms CBCL.ConsensusFree.run_trace
#print axioms CBCL.ConsensusFree.trace_invariant
#print axioms CBCL.ConsensusFree.step_simulation
#print axioms CBCL.ConsensusFree.trace_simulation
#print axioms CBCL.ConsensusFree.full_async_refinement
#print axioms CBCL.ConsensusFree.all_schedules_nonnegative
#print axioms CBCL.ConsensusFree.trace_journals
#print axioms CBCL.ConsensusFree.released_never_finalizes
#print axioms CBCL.ConsensusFree.infinite_async_refinement

#print axioms CBCL.ConsensusFree.two_mono
#print axioms CBCL.ConsensusFree.quorum_mono
#print axioms CBCL.ConsensusFree.quorum_has_core
#print axioms CBCL.ConsensusFree.step_journals
#print axioms CBCL.ConsensusFree.step_sealed_stable
#print axioms CBCL.ConsensusFree.reporter_persistent
#print axioms CBCL.ConsensusFree.final_cancel_exclusive
#print axioms CBCL.ConsensusFree.final_operation
#print axioms CBCL.ConsensusFree.operation_known
#print axioms CBCL.ConsensusFree.checkpoint_unique

#print axioms CBCL.ConsensusFree.effect_final_other
#print axioms CBCL.ConsensusFree.effect_final_mono
#print axioms CBCL.ConsensusFree.newly_final_data
#print axioms CBCL.ConsensusFree.final_rows_new
#print axioms CBCL.ConsensusFree.final_rows_same
#print axioms CBCL.ConsensusFree.step_observed
#print axioms CBCL.ConsensusFree.quorum_empty
#print axioms CBCL.ConsensusFree.sumOn_zero
#print axioms CBCL.ConsensusFree.isum_zero
#print axioms CBCL.ConsensusFree.initial_invariant
#print axioms CBCL.ConsensusFree.step_invariant

-- Conditional multi-parent liveness: fairness and arithmetic admission are
-- explicit theorem premises; no eventual certificate is assumed.
#print axioms CBCL.ConsensusFree.MultiParent.Liveness.eventual_honest_effects
#print axioms CBCL.ConsensusFree.MultiParent.Liveness.eventual_finality
#print axioms CBCL.ConsensusFree.MultiParent.Liveness.envelope_eventual_finality
#print axioms CBCL.ConsensusFree.MultiParent.Liveness.client_eventual_finality
#print axioms CBCL.ConsensusFree.MultiParent.Liveness.observed_certificate_sound

-- Concrete queue/dispatcher discharges both honest action fairness premises.
#print axioms CBCL.ConsensusFree.MultiParent.Liveness.Scheduler.position_serviced
#print axioms CBCL.ConsensusFree.MultiParent.Liveness.Scheduler.admitted_revisited
#print axioms CBCL.ConsensusFree.MultiParent.Liveness.Scheduler.scheduler_fair
#print axioms CBCL.ConsensusFree.MultiParent.Liveness.Scheduler.scheduled_finality
#print axioms CBCL.ConsensusFree.MultiParent.Liveness.Scheduler.scheduled_envelope_finality
#print axioms CBCL.ConsensusFree.MultiParent.Liveness.Scheduler.scheduled_client_finality
