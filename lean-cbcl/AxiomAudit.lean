import LeanCbcl.StateNativeRefinementTests
import LeanCbcl.StateResourceTests
import LeanCbcl.CheckpointKernel
import LeanCbcl.CheckpointAll
import LeanCbcl.StateKernelSECTests
import LeanCbcl.StateKernelClause
import LeanCbcl.HlcRegister
import LeanCbcl.Lattice.KnowledgeOrder
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
import LeanCbcl.StateLift
import LeanCbcl.StateLVar
import LeanCbcl.StateContext
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
-- LVar state kernel, the lift theorem (SPEC-038 REQ-3800, REQ-3801;
-- StateLift.lean): the lift of any contribution into any carrier is a set
-- function and a join-homomorphism; the shipped heads are displays of
-- lifts, so R7 follows from the algebra rather than per rule.
#print axioms CBCL.StateLift.lift_setEq
#print axioms CBCL.StateLift.lift_append
#print axioms CBCL.StateLift.lift_perm
#print axioms CBCL.StateLift.lift_cons
#print axioms CBCL.StateLift.lift_insertAct
#print axioms CBCL.StateLift.lift_cons_of_mem
#print axioms CBCL.StateLift.lift_sublist
#print axioms CBCL.StateLift.lift_pair
#print axioms CBCL.StateLift.WithTop.lift_of
#print axioms CBCL.StateLift.mem_lift
#print axioms CBCL.StateLift.FinSet.ext
#print axioms CBCL.StateLift.FinSet.card_mk_of_nodup
#print axioms CBCL.StateLift.FinSet.sumBy_mk_of_nodup
#print axioms CBCL.StateLift.FinSet.instJoinSemilatticeBot
#print axioms CBCL.StateLift.instBoundedJoinSemilatticeBool
#print axioms CBCL.StateLift.Chain.instJoinSemilatticeBot
#print axioms CBCL.StateLift.Sole.instBoundedJoinSemilattice
#print axioms CBCL.StateLift.WithTop.instBoundedJoinSemilattice
#print axioms CBCL.StateLift.instJoinSemilatticeBotProd
-- Each head as a display of a lift (ADR-3804).
#print axioms CBCL.StateLift.existsRule_eq_lift
#print axioms CBCL.StateLift.count_eq_lift
#print axioms CBCL.StateLift.has_eq_lift
#print axioms CBCL.StateLift.setUnion_eq_lift
#print axioms CBCL.StateLift.sumField_eq_lift
#print axioms CBCL.StateLift.counter_eq_lift
#print axioms CBCL.StateLift.pick_eq_lift
#print axioms CBCL.StateLift.last_eq_lift
#print axioms CBCL.StateLift.latestPerKey_eq_lift
#print axioms CBCL.StateLift.current_eq_currentLift
#print axioms CBCL.StateLift.currentOwn_eq_currentOwnLift
#print axioms CBCL.StateLift.values_eq_lift
#print axioms CBCL.StateLift.valuesPerKey_eq_lift
#print axioms CBCL.StateLift.registerPerKey_eq_lift
#print axioms CBCL.StateLift.observedSet_eq_lift
#print axioms CBCL.StateLift.latestPerSigner_eq_lift
#print axioms CBCL.StateLift.isTop_eq_lift
#print axioms CBCL.StateLift.topCount_setEq
-- The thirteen heads and the domain filter, invariant from the lift theorem.
#print axioms CBCL.StateLift.fold_perm_invariant_lift
#print axioms CBCL.StateLift.initialCarrier_invariant
#print axioms CBCL.StateLift.initialAllowed_invariant
#print axioms CBCL.StateLift.initialDomain_invariant
#print axioms CBCL.StateLift.initialDomain_lift_invariant
#print axioms CBCL.StateLift.initialAllowed_fork
#print axioms CBCL.StateLift.HlcLift.carrier_eq
#print axioms CBCL.StateLift.HlcLift.candidates_consistent
#print axioms CBCL.StateLift.HlcLift.consistent_setEq
#print axioms CBCL.StateLift.HlcLift.readList_setEq
#print axioms CBCL.StateLift.HlcLift.merge_assoc
#print axioms CBCL.StateLift.HlcLift.merge_idem
#print axioms CBCL.StateLift.HlcLift.pick_cons
#print axioms CBCL.StateLift.HlcLift.pick_append
#print axioms CBCL.StateLift.HlcLift.display_union
#print axioms CBCL.StateLift.HlcLift.pick_eq_lift
#print axioms CBCL.StateLift.HlcLift.compressed_join
#print axioms CBCL.StateLift.HlcLift.display_invariant
#print axioms CBCL.StateLift.HlcLift.pick_invariant
#print axioms CBCL.StateLift.HlcLift.field_invariant
#print axioms CBCL.StateLift.HlcLift.unrecognized_is_bottom
#print axioms CBCL.StateLift.HlcLift.unrecognized_put_unchanged
#print axioms CBCL.StateLift.HlcLift.physical_precedes_address
#print axioms CBCL.StateLift.HlcLift.logical_precedes_address
#print axioms CBCL.StateLift.HlcLift.signer_precedes_address
#print axioms CBCL.StateLift.HlcLift.address_breaks_tie
#print axioms CBCL.StateLift.HlcLift.unrecognized_high_address_ignored
#print axioms CBCL.StateLift.HlcLift.all_unrecognized_have_no_winner
#print axioms CBCL.StateLift.hlc_register_invariant
#print axioms CBCL.StateLift.hlc_perSigner_invariant
#print axioms CBCL.StateLift.hlc_map_invariant
#print axioms CBCL.StateLift.domainActs_invariant
#print axioms CBCL.StateLift.domainActs_unique
#print axioms CBCL.StateLift.HlcFields.scalar_invariant
#print axioms CBCL.StateLift.HlcFields.group_invariant
#print axioms CBCL.StateLift.HlcFields.perSigner_invariant
#print axioms CBCL.StateLift.HlcFields.keyed_invariant
#print axioms CBCL.StateLift.HlcFields.domain_heads_invariant
#print axioms CBCL.StateLift.HlcFields.excluded_replacer_cannot_erase_value
#print axioms CBCL.StateLift.HlcFields.unrecognized_group_value_is_absent
#print axioms CBCL.StateLift.HlcFields.nonexistent_group_has_no_entry
#print axioms CBCL.StateLift.HlcFields.unrelated_delete_survives_domain
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

-- SPEC-035: typed HLC arbitration; clock honesty and Rust correspondence excluded.
#print axioms CBCL.HlcRegister.pick_correct
#print axioms CBCL.HlcRegister.pick_setEq
#print axioms CBCL.HlcRegister.register_correct
#print axioms CBCL.HlcRegister.own_correct
#print axioms CBCL.HlcRegister.keyed_correct
#print axioms CBCL.HlcRegister.own_candidate_scope
#print axioms CBCL.HlcRegister.keyed_candidate_scope

-- SPEC-036: typed whole-clause denotation; delegated resource classification excluded.
#print axioms CBCL.StateKernelSemantics.select_correct
#print axioms CBCL.StateKernelSemantics.allowed_correct
#print axioms CBCL.StateKernelSemantics.admitted_correct
#print axioms CBCL.StateKernelSemantics.data_selection_correct
#print axioms CBCL.StateKernelSemantics.pick_correct
#print axioms CBCL.StateKernelSemantics.cardinality_correct
#print axioms CBCL.StateKernelSemantics.total_correct
#print axioms CBCL.StateKernelSemantics.events_correct
#print axioms CBCL.StateKernelQueries.choose_correct
#print axioms CBCL.StateKernelQueries.cell_complete
#print axioms CBCL.StateKernelQueries.map_complete
#print axioms CBCL.StateKernelAggregates.histogram_correct
#print axioms CBCL.StateKernelAggregates.map_sum_correct
#print axioms CBCL.StateKernelAggregates.key_count_unique
#print axioms CBCL.StateKernelAggregates.key_total_unique
#print axioms CBCL.StateKernelExtensions.progress_correct
#print axioms CBCL.StateKernelExtensions.progress_unique
#print axioms CBCL.StateKernelExtensions.resource_correct
#print axioms CBCL.StateKernelExtensions.resource_unique
#print axioms CBCL.StateKernelExtensions.resource_floor
#print axioms CBCL.StateKernelExtensions.resource_ceiling
#print axioms CBCL.StateKernel.evaluate_correct
#print axioms CBCL.StateKernelClause.compile_clause_complete
#print axioms CBCL.StateKernelClause.whole_kernel_correct
#print axioms CBCL.StateKernelClause.well_formed_kernel_correct
#print axioms CBCL.StateKernel.values_by_complete
#print axioms CBCL.StateKernelAggregates.cell_number_correct

#print axioms CBCL.StateKernelAggregates.cell_number_complete
#print axioms CBCL.StateKernelAggregates.sum_meaning_unique
#print axioms CBCL.StateKernelAggregates.histogram_meaning_unique

-- SPEC-037: equal-set convergence, fair admission and finite-history SEC.
#print axioms CBCL.StateKernelSEC.admitted_setEq
#print axioms CBCL.StateKernelSEC.select_setEq
#print axioms CBCL.StateKernelSEC.choose_setEq
#print axioms CBCL.StateKernelSEC.map_setEq
#print axioms CBCL.StateKernelSEC.values_map_setEq
#print axioms CBCL.StateKernelSEC.histogram_equivalent
#print axioms CBCL.StateKernelSEC.sum_equivalent
#print axioms CBCL.StateKernelSEC.strong_convergence
#print axioms CBCL.StateKernelSEC.clause_strong_convergence
#print axioms CBCL.StateKernelDelivery.step_received
#print axioms CBCL.StateKernelDelivery.step_accepted
#print axioms CBCL.StateKernelDelivery.accepted_persistent
#print axioms CBCL.StateKernelDelivery.received_persistent
#print axioms CBCL.StateKernelDelivery.accepted_valid
#print axioms CBCL.StateKernelDelivery.pending_or_accepted
#print axioms CBCL.StateKernelDelivery.label_accepted
#print axioms CBCL.StateKernelDelivery.enabled_eventually_accepted
#print axioms CBCL.StateKernelDelivery.eventual_acceptance
#print axioms CBCL.StateKernelDelivery.finite_history_stabilizes
#print axioms CBCL.StateKernelDelivery.strong_eventual_consistency
#print axioms CBCL.StateKernelSECTests.run_behavior
#print axioms CBCL.StateKernelSECTests.child_eventually_accepted
#print axioms CBCL.StateKernelSECTests.starved_behavior
#print axioms CBCL.StateKernelSECTests.starved_no_acceptance
#print axioms CBCL.StateKernelSECTests.starved_not_fair
#print axioms CBCL.StateKernelSEC.merge_setEq
#print axioms CBCL.StateKernelSEC.merge_associative
#print axioms CBCL.StateKernelSEC.merge_commutative
#print axioms CBCL.StateKernelSEC.merge_idempotent
#print axioms CBCL.StateKernelSEC.duplicate_observation
#print axioms CBCL.StateKernelDelivery.eventual_dissemination
#print axioms CBCL.StateKernelSECTests.ticks_unique
#print axioms CBCL.StateKernelSECTests.ticks_count
#print axioms CBCL.StateKernelSECTests.ongoing_writes_need_not_stabilize

-- Version-4 sole initializer; no address-primary arbitration in the surface.
#print axioms CBCL.StateKernelSemantics.sole_some
#print axioms CBCL.StateKernelSemantics.sole_correct
#print axioms CBCL.StateKernelSemantics.sole_complete
#print axioms CBCL.StateKernelSemantics.sole_setEq
#print axioms CBCL.StateKernelSemantics.initialValues_setEq

-- Cached-state semantic continuation: no project-specific axioms.
#print axioms CBCL.CheckpointSummary.step_preserves
#print axioms CBCL.CheckpointSummary.checkpoint_continuation
#print axioms CBCL.CheckpointCompact.Initial.continuation
#print axioms CBCL.CheckpointCompact.LwwRegister.continuation
#print axioms CBCL.CheckpointKernel.rule_render_eq
#print axioms CBCL.CheckpointKernel.render_advance_checkpoint
#print axioms CBCL.CheckpointKernel.resume_valid_snapshot
#print axioms CBCL.CheckpointKernel.native_compile_fields
#print axioms CBCL.CheckpointKernel.fullFoldRaw_native

#print axioms CBCL.CheckpointKernel.native_compile_clause
#print axioms CBCL.CheckpointKernel.render_advance_native_clause

-- All sixteen native checkpoint heads and explicit evidence projections.
#print axioms CBCL.CheckpointAll.render_advance_checkpoint
#print axioms CBCL.CheckpointAll.resume_valid_snapshot
#print axioms CBCL.CheckpointAll.render_advance_native_clause
#print axioms CBCL.CheckpointAll.native_compile_clause
#print axioms CBCL.CheckpointAll.resolve_fields_complete
#print axioms CBCL.CheckpointAll.render_advance_wellformed_clause
#print axioms CBCL.CheckpointAll.position_advance_checkpoint
#print axioms CBCL.CheckpointAll.resource_facts_advance_checkpoint
#print axioms CBCL.CheckpointData.events_continuation
#print axioms CBCL.CheckpointEvidence.progress_checkpoint_tail_native
#print axioms CBCL.CheckpointEvidence.resource_checkpoint_tail_native

-- SPEC-038 fault-aware observations and actual replica dissemination.
#print axioms CBCL.StateLVar.below_trans
#print axioms CBCL.StateLVar.distinct_successes_force_conflict
#print axioms CBCL.StateLVar.threshold_quasi_determinism
#print axioms CBCL.StateLVar.success_persists
#print axioms CBCL.StateLVar.rawHistory_union
#print axioms CBCL.StateLVar.rawHistory_setEq
#print axioms CBCL.StateLVar.domainRead_setEq
#print axioms CBCL.StateLVar.display_rawHistory
#print axioms CBCL.StateLVar.opener_evidence
#print axioms CBCL.StateLVar.opener_fork_fault
#print axioms CBCL.StateLVar.domain_fork_fault
#print axioms CBCL.StateLVar.witness_dissemination
#print axioms CBCL.StateLVar.eventual_domain_fork
#print axioms CBCL.StateLVar.finite_observation_agreement
#print axioms CBCL.StateLVar.nonnegative_events_monotone
#print axioms CBCL.StateLVar.causalCut_agreement
#print axioms CBCL.StateLVar.freezer_in_cut
#print axioms CBCL.StateLVar.earliest_persists
#print axioms CBCL.StateLVar.frozen_value_agreement
#print axioms CBCL.StateLVar.freeze_evidence_sound
#print axioms CBCL.StateLVar.freeze_witness_transfer
#print axioms CBCL.StateLVar.eventual_freeze_conflict
#print axioms CBCL.StateLVar.below_refl
#print axioms CBCL.StateLVar.below_left
#print axioms CBCL.StateLVar.below_right
#print axioms CBCL.StateLVar.join_below
#print axioms CBCL.StateLVar.top_below
#print axioms CBCL.StateLVar.thresholdRead_fault_first
#print axioms CBCL.StateLVar.thresholdRead_sound
#print axioms CBCL.StateLVar.thresholdRead_agreement
#print axioms CBCL.StateLVar.rawHistory_eq
#print axioms CBCL.StateLVar.rawHistory_faithful
#print axioms CBCL.StateLVar.sole_evidence_join
#print axioms CBCL.StateLVar.nonnegative_sum_sublist
#print axioms CBCL.StateLVar.ancestor_accepted
#print axioms CBCL.StateLVar.earliest_transfer
#print axioms CBCL.StateLVar.freeze_witness_accepted
#print axioms CBCL.StateLVar.earliest_setEq
#print axioms CBCL.StateLVar.freezeConflict_setEq
#print axioms CBCL.StateLVar.freezeEvidence_setEq
#print axioms CBCL.StateLVar.causalCut_setEq
#print axioms CBCL.StateLVar.earliest_find_setEq
#print axioms CBCL.StateLVar.freezeRead_conflict
#print axioms CBCL.StateLVar.freezeRead_setEq
#print axioms CBCL.StateLVar.step_causal_closed
#print axioms CBCL.StateLVar.replica_causal_closed
#print axioms CBCL.StateLVar.eventual_freeze_fault
#print axioms CBCL.StateLVar.finite_freeze_agreement
#print axioms CBCL.StateLVar.finite_domain_agreement
#print axioms CBCL.StateLVar.resourceFailure_setEq
#print axioms CBCL.StateLVar.initializerConflict_setEq
#print axioms CBCL.StateLVar.initializerEvidence_setEq
#print axioms CBCL.StateLVar.evaluateField_fork
#print axioms CBCL.StateLVar.evaluateField_setEq
#print axioms CBCL.StateLVar.evaluateField_forget
#print axioms CBCL.StateLVar.compileTerms_union
#print axioms CBCL.StateLVar.compileTerms_put
#print axioms CBCL.StateLVar.compiled_clause_correspondence
#print axioms CBCL.StateLVar.legacy_strong_eventual_consistency
#print axioms CBCL.StateContext.carrier_union
#print axioms CBCL.StateContext.read_setEq
#print axioms CBCL.StateContext.display_quasi
#print axioms CBCL.StateContext.read_quasi
#print axioms CBCL.StateContext.invalid_root_faults
#print axioms CBCL.StateContext.recognized_root_value
#print axioms CBCL.StateContext.fault_evidence
#print axioms CBCL.StateContext.fault_join
#print axioms CBCL.StateContext.read_fault_persists
#print axioms CBCL.StateContext.eventual_context_fault

#print axioms CBCL.StateLVar.fault_aware_strong_eventual_consistency

#print axioms CBCL.StateResource.reaches_in_closed
#print axioms CBCL.StateResource.exact_cone_unique
#print axioms CBCL.StateResource.unsupported_fault
#print axioms CBCL.StateResource.fault_growth
#print axioms CBCL.StateResource.fault_setEq
#print axioms CBCL.StateResource.evidence_growth
#print axioms CBCL.StateResource.evidence_setEq
#print axioms CBCL.StateResource.faultRead_setEq
#print axioms CBCL.StateResource.faultRead_persists
#print axioms CBCL.StateResource.evidence_accepted
#print axioms CBCL.StateResource.eventual_resource_fault
#print axioms CBCL.StateObservation.unionError_grows
#print axioms CBCL.StateObservation.freezeEvidence_grows
#print axioms CBCL.StateObservation.freezeFault_grows
#print axioms CBCL.StateObservation.errors_persist
#print axioms CBCL.StateObservation.acceptedEvidence_setEq
#print axioms CBCL.StateObservation.errors_setEq
#print axioms CBCL.StateObservationPlan.freezeRead_setEq_unique
#print axioms CBCL.StateObservationPlan.data_setEq
#print axioms CBCL.StateObservationPlan.observe_setEq
#print axioms CBCL.StateObservationPlan.composed_strong_eventual_consistency
#print axioms CBCL.StateObservationPlan.eventual_composed_fault
#print axioms CBCL.StateObservationPlan.frozen_source_agreement
#print axioms CBCL.StateObservationPlan.threshold_read_of_success
#print axioms CBCL.StateObservationPlan.threshold_quasi_determinism
#print axioms CBCL.StateObservationPlan.derived_frozen_payload
#print axioms CBCL.StateObservationPlan.threshold_dependency_fault_first
#print axioms CBCL.StateResourceTests.checked_overflow
#print axioms CBCL.StateResourceTests.checked_underflow
#print axioms CBCL.StateResourceTests.insufficient_budget
#print axioms CBCL.StateResourceTests.valid_opener
#print axioms CBCL.StateResourceTests.valid_burn_shape
#print axioms CBCL.StateResourceTests.burn_cone
#print axioms CBCL.StateResourceTests.burn_budget_fault
#print axioms CBCL.StateResourceTests.concrete_budget_cause
#print axioms CBCL.StateResourceTests.no_opener_no_cause
#print axioms CBCL.StateResourceTests.concrete_fault
#print axioms CBCL.StateResource.aggregate_i128_bound
#print axioms CBCL.StateResource.sum_bounds
#print axioms CBCL.StateResource.owner_chains_comparable
#print axioms CBCL.StateResource.longer_owner_prefix
#print axioms CBCL.StateResource.merge_owner_tips_union
#print axioms CBCL.StateResource.ordered_of_perm
#print axioms CBCL.StateResource.localBudget_perm
#print axioms CBCL.StateResource.localBudget_cone_unique
#print axioms CBCL.StateResourceTests.reordered_headroom_valid
#print axioms CBCL.StateResourceNative.accountCheck_iff
#print axioms CBCL.StateResourceNative.amountCheck_iff
#print axioms CBCL.StateResourceNative.rowsCheck_iff
#print axioms CBCL.StateResourceNative.allocationsCheck_iff
#print axioms CBCL.StateResourceNative.checkedAdd_iff
#print axioms CBCL.StateResourceNative.checkedSub_iff
#print axioms CBCL.StateResourceNative.sum_nonnegative
#print axioms CBCL.StateResourceNative.checkedFold_nonnegative
#print axioms CBCL.StateResourceNative.checkedSum_nonnegative
#print axioms CBCL.StateResourceNative.allocationTotal_iff
#print axioms CBCL.StateResourceNative.empty_allocations_rejected
#print axioms CBCL.StateResourceNative.malformed_account_rejected
#print axioms CBCL.StateResourceNative.rootCheck_iff
#print axioms CBCL.StateResourceNative.kindCheck_iff
#print axioms CBCL.StateResourceNative.operationCheck_iff
#print axioms CBCL.StateResourceNative.initialValue_iff
#print axioms CBCL.StateResourceNative.mutual_keys_iff
#print axioms CBCL.StateResourceNative.headroomCheck_iff
#print axioms CBCL.StateResourceNative.initializationCheck_iff
#print axioms CBCL.StateResourceNative.initialization_rejection_iff
#print axioms CBCL.StateResourceNative.operation_rejection_iff
#print axioms CBCL.StateResourceNative.initialization_rejection_certificate
#print axioms CBCL.StateResourceNative.operation_rejection_certificate
#print axioms CBCL.StateResourceNative.addIncoming_eq
#print axioms CBCL.StateResourceNative.groupedIncoming_as_totals
#print axioms CBCL.StateResourceNative.groupedIncoming_refinement
#print axioms CBCL.StateResourceSummary.update_add
#print axioms CBCL.StateResourceSummary.record_refinement
#print axioms CBCL.StateResourceSummary.run_refinement
#print axioms CBCL.StateResourceSummary.effect_sequence
#print axioms CBCL.StateResourceSummary.native_sequence_is_prefix_length
#print axioms CBCL.StateResourceSummary.effect_credited
#print axioms CBCL.StateResourceSummary.effect_debited
#print axioms CBCL.StateResourceSummary.effect_sentRights
#print axioms CBCL.StateResourceSummary.effect_sentHeadroom
#print axioms CBCL.StateResourceSummary.native_counters_refinement
#print axioms CBCL.StateRuleRefinement.closure_threshold_refinement
#print axioms CBCL.StateRuleRefinement.domain_source_refinement
#print axioms CBCL.StateRuleRefinement.context_source_refinement
#print axioms CBCL.StateRuleRefinement.derived_source_refinement
#print axioms CBCL.StateRuleRefinement.source_error_refinement
#print axioms CBCL.StateRuleRefinement.cut_closed
#print axioms CBCL.StateRuleRefinement.clear_cut
#print axioms CBCL.StateRuleRefinement.freeze_source_refinement
#print axioms CBCL.StateCountRefinement.initial_absorbs
#print axioms CBCL.StateCountRefinement.selected_grows
#print axioms CBCL.StateCountRefinement.selected_unique
#print axioms CBCL.StateCountRefinement.count_display_refinement
#print axioms CBCL.StateCountRefinement.count_grows
#print axioms CBCL.StateCountRefinement.count_reached_iff
#print axioms CBCL.StateCountRefinement.installed_count_threshold_stable
#print axioms CBCL.StateNativeRefinementTests.native_initialization_accepts
#print axioms CBCL.StateNativeRefinementTests.native_operation_shape_accepts
#print axioms CBCL.StateNativeRefinementTests.empty_certificate_accounts_rejected
#print axioms CBCL.StateNativeRefinementTests.account_spelling_rejected
#print axioms CBCL.StateNativeRefinementTests.grouped_negative_budget
#print axioms CBCL.StateNativeRefinementTests.grouped_near_limit
#print axioms CBCL.StateNativeRefinementTests.source_linked_threshold_pending
#print axioms CBCL.StateNativeRefinementTests.source_linked_threshold_reached
#print axioms CBCL.StateNativeRefinementTests.frozen_closure_threshold
#print axioms CBCL.StateNativeRefinementTests.fault_closure_threshold
#print axioms CBCL.StateObservationPlan.thresholdOn_dependency_fault_first
