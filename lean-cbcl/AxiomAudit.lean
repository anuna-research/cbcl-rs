import LeanCbcl.StateAuthoredDataPreservationTests
import LeanCbcl.StateNativeDataPoliciesTests
import LeanCbcl.StateAuthoredFinitePreservationTests
import LeanCbcl.StateAuthoredFiniteStabilityTests
import LeanCbcl.StateAuthoredSourceProvenanceTests
import LeanCbcl.StateFiniteOutputStabilityTests
import LeanCbcl.StateFiniteFreezePolicyTests
import LeanCbcl.StateDomainSupportLocalityTests
import LeanCbcl.StateOpenerLocalityTests
import LeanCbcl.StateCausalCheckCompleteTests
import LeanCbcl.StateCausalRankIntegrationTests
import LeanCbcl.StateOutputCompilerTests
import LeanCbcl.StatePreparedOutputsTests
import LeanCbcl.StateThresholdDispatchTests
import LeanCbcl.StateCausalRank
import LeanCbcl.StateFrozenBodyEquationsTests
import LeanCbcl.StateCompiledFieldEquationsTests
import LeanCbcl.StateReaderReachabilityTests
import LeanCbcl.StateReaderValuesTests
import LeanCbcl.StateAuthoredDependencies
import LeanCbcl.StateReaderIndices
import LeanCbcl.StateMemoizedReaderTests
import LeanCbcl.StateMemoizedReader
import LeanCbcl.StateExecutableContext
import LeanCbcl.StateExecutableObservation
import LeanCbcl.StateExecutableFreeze
import LeanCbcl.StateAuthoredCompletion
import LeanCbcl.StateInstalledRecognition
import LeanCbcl.StateFinitePairLoop
import LeanCbcl.StateFiniteUpperCache
import LeanCbcl.StateNativeReader
import LeanCbcl.StateCompiledFreezeGrowth
import LeanCbcl.StateFreezeScopes
import LeanCbcl.StateFreezeGrowth
import LeanCbcl.StateAuthoredBindingsTests
import LeanCbcl.StateAuthoredBindings
import LeanCbcl.StateFiniteReadTests
import LeanCbcl.StateFiniteRead
import LeanCbcl.StateInstalledFinite
import LeanCbcl.StateFiniteProjectionTests
import LeanCbcl.StateFiniteProjection
import LeanCbcl.StateFiniteTable
import LeanCbcl.StateInstalledDomains
import LeanCbcl.StateInstalledContext
import LeanCbcl.StateContextEvidence
import LeanCbcl.StateInstalledTerm
import LeanCbcl.StateResourceCompletion
import LeanCbcl.StateResourceReadEquivalence
import LeanCbcl.StateInstalledLegacy
import LeanCbcl.StateInstalledResource
import LeanCbcl.StateInstalledLegacyTests
import LeanCbcl.StateInstalledLattice
import LeanCbcl.StateInstalledLowering
import LeanCbcl.StateInstalledLoweringTests
import LeanCbcl.StateResourceVerifierTests
import LeanCbcl.StateInstalledCompiler
import LeanCbcl.StateInstalledClause
import LeanCbcl.StateInstalledCompilerTests
import LeanCbcl.StateResourcePreflight
import LeanCbcl.StateResourceVerifier
import LeanCbcl.StateResourceAggregate
import LeanCbcl.StateResourceAccounting
import LeanCbcl.StateResourceSolvency
import LeanCbcl.StateResourceFinalize
import LeanCbcl.StateResourceValidated
import LeanCbcl.StateResourceAggregateTests
import LeanCbcl.StateResourceRecordBounds
import LeanCbcl.StateResourceGraph
import LeanCbcl.StateResourceCoupling
import LeanCbcl.StateResourceWorklist
import LeanCbcl.StateResourceAuthorization
import LeanCbcl.StateResourceCounters
import LeanCbcl.StateResourceWitness
import LeanCbcl.StateResourceMachine
import LeanCbcl.StateResourceDependency
import LeanCbcl.StateResourceOwnPrefix
import LeanCbcl.StateResourceOutgoing
import LeanCbcl.StateResourceLocalBudget
import LeanCbcl.StateResourceCones
import LeanCbcl.StateResourceFrontier
import LeanCbcl.StateResourcePartition
import LeanCbcl.StateResourceBudget
import LeanCbcl.StateResourceCacheTests
import LeanCbcl.StateResourceStructure
import LeanCbcl.StateResourceCache
import LeanCbcl.StateResourceKahnTests
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

#print axioms CBCL.StateResourceKahn.Reach

#print axioms CBCL.StateResourceKahn.Reach

#print axioms CBCL.StateResourceKahn.Reach

#print axioms CBCL.StateResourceKahn.Reach

#print axioms CBCL.StateResourceKahn.walk_length

#print axioms CBCL.StateResourceKahn.walk_inside

#print axioms CBCL.StateResourceKahn.walk_reaches

#print axioms CBCL.StateResourceKahn.walk_nodup_without_cycles

#print axioms CBCL.StateResourceKahn.closed_parent_cycle

#print axioms CBCL.StateResourceKahn.ready_cannot_reach

#print axioms CBCL.StateResourceKahn.reach_erase_ready

#print axioms CBCL.StateResourceKahn.cycle_erase_ready

#print axioms CBCL.StateResourceKahn.RemovalTrace

#print axioms CBCL.StateResourceKahn.saturated_cycle_iff_nonempty

#print axioms CBCL.StateResourceKahn.native_kahn_cycle_iff

#print axioms CBCL.StateResourceKahn.readyCheck_iff

#print axioms CBCL.StateResourceKahn.RemovalTrace

#print axioms CBCL.StateResourceKahn.reduce_trace

#print axioms CBCL.StateResourceKahn.reduce_saturated

#print axioms CBCL.StateResourceKahn.nativeKahn_cycle_iff

#print axioms CBCL.StateResourceKahn.closed_component_processed

#print axioms CBCL.StateResourceKahn.order_partition

#print axioms CBCL.StateResourceKahn.removalOrder_topological

#print axioms CBCL.StateResourceKahn.topological_rank

#print axioms CBCL.StateResourceKahn.nativeKahn_rank

#print axioms CBCL.StateResourceKahn.native_closed_component_processed

#print axioms CBCL.StateResourceKahn.budget_reduce_saturated

#print axioms CBCL.StateResourceKahn.native_budget_saturation

#print axioms CBCL.StateResourceKahn.native_no_hidden_closed_component

#print axioms CBCL.StateResourceCycle.operationVerbCheck_iff

#print axioms CBCL.StateResourceCycle.parent_iff

#print axioms CBCL.StateResourceCycle.reaches_mono

#print axioms CBCL.StateResourceCycle.native_reach_resource

#print axioms CBCL.StateResourceCycle.resource_reach_extend

#print axioms CBCL.StateResourceCycle.graph_cycle_iff_certificate

#print axioms CBCL.StateResourceCycle.native_cycle_certificate_iff

#print axioms CBCL.StateResourceCycle.native_cycle_rejection_cause

#print axioms CBCL.StateResourceKahnTests.acyclic_pass_removes_all

#print axioms CBCL.StateResourceKahnTests.cycle_pass_retains_nodes

#print axioms CBCL.StateResourceKahnTests.cycle_pass_has_witness

#print axioms CBCL.StateResourceKahnTests.missing_reference_is_not_a_cycle

#print axioms CBCL.StateResourceKahnTests.budget_pass_keeps_missing_reference

#print axioms CBCL.StateResourceKahnTests.budget_pass_processes_independent_component

#print axioms CBCL.StateResourceCache.empty_valid

#print axioms CBCL.StateResourceCache.tipId_append

#print axioms CBCL.StateResourceCache.ownerChain_append

#print axioms CBCL.StateResourceCache.run_append_one

#print axioms CBCL.StateResourceCache.previous_prefix

#print axioms CBCL.StateResourceCache.advance_valid

#print axioms CBCL.StateResourceCache.previous_owner

#print axioms CBCL.StateResourceCache.advance_inside

#print axioms CBCL.StateResourceCache.execute_valid

#print axioms CBCL.StateResourceCache.native_cached_prefix

#print axioms CBCL.StateResourceCache.cached_tip_union

#print axioms CBCL.StateResourceCacheTests.cached_owner_sequence_and_debit

#print axioms CBCL.StateResourceCacheTests.cached_other_owner_sequence_and_debit

#print axioms CBCL.StateResourceCacheTests.actual_cached_tip_chooses_longer_prefix

#print axioms CBCL.StateResourceCacheTests.absent_previous_prevents_cache_insertion

#print axioms CBCL.StateResourceStructure.previousOwnerCheck_iff

#print axioms CBCL.StateResourceStructure.forkCheck_iff

#print axioms CBCL.StateResourceStructure.checked_native_cached_prefix

#print axioms CBCL.StateResourceStructure.fork_rejection_iff

#print axioms CBCL.StateResourceStructure.foreign_owner_rejection_iff

#print axioms CBCL.StateResourceStructure.fork_rejection_cause

#print axioms CBCL.StateResourceStructure.foreign_owner_rejection_cause

#print axioms CBCL.StateResourceCones.unionCone_member

#print axioms CBCL.StateResourceCones.reaches_enlarge

#print axioms CBCL.StateResourceCones.unionCone_exact

#print axioms CBCL.StateResourceCones.gather_lookup

#print axioms CBCL.StateResourceCones.reconstruct_exact

#print axioms CBCL.StateResourceCones.insert_valid

#print axioms CBCL.StateResourceCones.execute_valid

#print axioms CBCL.StateResourceCones.executed_cone_exact

#print axioms CBCL.StateResourceFrontier.merge_represents

#print axioms CBCL.StateResourceFrontier.represented_chain

#print axioms CBCL.StateResourceFrontier.merge_prefix_members

#print axioms CBCL.StateResourceFrontier.merge_covers

#print axioms CBCL.StateResourceFrontier.dependency_own_prefix_before_current

#print axioms CBCL.StateResourcePartition.chain_owner

#print axioms CBCL.StateResourcePartition.chain_rank_after

#print axioms CBCL.StateResourcePartition.chain_ids_unique

#print axioms CBCL.StateResourcePartition.native_prefix_ids_unique

#print axioms CBCL.StateResourcePartition.grouped_prefixes_nodup

#print axioms CBCL.StateResourcePartition.frontier_partition

#print axioms CBCL.StateResourceBudget.chunks_flatten

#print axioms CBCL.StateResourceBudget.selected_sum_bound

#print axioms CBCL.StateResourceBudget.frontier_incoming_refinement

#print axioms CBCL.StateResourceBudget.amounts_sum

#print axioms CBCL.StateResourceBudget.readIncoming_refinement

#print axioms CBCL.StateResourceBudget.nativeIncoming_as_totals

#print axioms CBCL.StateResourceBudget.native_incoming_cone_refinement

#print axioms CBCL.StateResourceCache.same_cached_prefix

#print axioms CBCL.StateResourceFrontier.mergeAll_represents

#print axioms CBCL.StateResourceFrontier.mergeAll_members

#print axioms CBCL.StateResourceDependency.empty_represents

#print axioms CBCL.StateResourceDependency.parent_frontier_union

#print axioms CBCL.StateResourceDependency.unionCone_past

#print axioms CBCL.StateResourceDependency.pre_record_frontier_exact

#print axioms CBCL.StateResourceDependency.unique_ids_consistent

#print axioms CBCL.StateResourceDependency.dependency_incoming_exact_cone

#print axioms CBCL.StateResourceOwnPrefix.cached_parent_prefix

#print axioms CBCL.StateResourceOwnPrefix.prefix_eq_of_subset

#print axioms CBCL.StateResourceOwnPrefix.merged_previous_prefix

#print axioms CBCL.StateResourceOutgoing.sum_map_add

#print axioms CBCL.StateResourceOutgoing.sum_map_zero

#print axioms CBCL.StateResourceOutgoing.recipient_indicator

#print axioms CBCL.StateResourceOutgoing.recipient_partition_sum

#print axioms CBCL.StateResourceOutgoing.native_outgoing_refinement

#print axioms CBCL.StateResourceLocalBudget.owner_prefix_partition

#print axioms CBCL.StateResourceLocalBudget.ownTotal_prefix

#print axioms CBCL.StateResourceLocalBudget.own_credited_debited

#print axioms CBCL.StateResourceLocalBudget.native_local_budget_refinement

#print axioms CBCL.StateResourceLocalBudget.dependency_local_budgets_exact

#print axioms CBCL.StateResource.unsupported_empty_evidence

#print axioms CBCL.StateResourceCache.advance_preserves_old

#print axioms CBCL.StateResourceFrontier.represents_cache_extension

#print axioms CBCL.StateResourceFrontier.record_frontier_represents

#print axioms CBCL.StateResourceFrontier.record_frontier_covers

#print axioms CBCL.StateResourceBudget.checked_selected_present

#print axioms CBCL.StateResourceBudget.summaryFault_unreachable

#print axioms CBCL.StateResourceBudget.budgetFault_perm

#print axioms CBCL.StateResourceBudget.budgetFault_cone_unique

#print axioms CBCL.StateResourceLocalBudget.budgetDecision_false_iff

#print axioms CBCL.StateResourceLocalBudget.native_budget_rejection_iff

#print axioms CBCL.StateResourceWitness.native_budget_certificate_iff

#print axioms CBCL.StateResourceWitness.budget_witness_cause

#print axioms CBCL.StateResourceMachine.initial_invariant

#print axioms CBCL.StateResourceMachine.fresh_excludes_parent_cones

#print axioms CBCL.StateResourceMachine.recordStep_preserves_old

#print axioms CBCL.StateResourceMachine.recordResult_invariant

#print axioms CBCL.StateResourceMachine.recordStep_invariant

#print axioms CBCL.StateResourceMachine.recordStep_unchanged

#print axioms CBCL.StateResourceMachine.execute_invariant

#print axioms CBCL.StateResourceMachine.native_execution_invariant

#print axioms CBCL.StateResourceAuthorization.checkedStep_done_record

#print axioms CBCL.StateResourceAuthorization.checkedStep_budget_fault

#print axioms CBCL.StateResourceAuthorization.checkedStep_budget_certificate

#print axioms CBCL.StateResourceCounters.outstanding_cons

#print axioms CBCL.StateResourceCounters.outstanding_nil

#print axioms CBCL.StateResourceCounters.outstanding_positive

#print axioms CBCL.StateResourceCounters.outstanding_after_pop

#print axioms CBCL.StateResourceCounters.decrementAll_value

#print axioms CBCL.StateResourceCounters.count_unique

#print axioms CBCL.StateResourceCounters.waiting_pop_refinement

#print axioms CBCL.StateResourceCounters.waiting_after_pop

#print axioms CBCL.StateResourceCounters.zero_count_ready

#print axioms CBCL.StateResourceCounters.waiting_decrement_safe

#print axioms CBCL.StateResourceCounters.processed_closed_after_pop

#print axioms CBCL.StateResourceCounters.ready_pop_refinement

#print axioms CBCL.StateResourceCounters.initialize_invariant

#print axioms CBCL.StateResourceCounters.pop_invariant

#print axioms CBCL.StateResourceCounters.runFuel_invariant

#print axioms CBCL.StateResourceCounters.native_counters_invariant

#print axioms CBCL.StateResourceCounters.runFuel_saturated

#print axioms CBCL.StateResourceCounters.native_saturated

#print axioms CBCL.StateResourceCounters.saturated_processes_ready

#print axioms CBCL.StateResourceCounters.native_closed_component_processed

#print axioms CBCL.StateResourceWorklist.Environment.operations

#print axioms CBCL.StateResourceWorklist.Environment.initialValid

#print axioms CBCL.StateResourceWorklist.Environment.nonforking

#print axioms CBCL.StateResourceWorklist.Environment.uniqueParents

#print axioms CBCL.StateResourceWorklist.initial_joint

#print axioms CBCL.StateResourceWorklist.done_authorized

#print axioms CBCL.StateResourceWorklist.done_joint

#print axioms CBCL.StateResourceWorklist.runFuel_verified

#print axioms CBCL.StateResourceWorklist.native_worklist_verified

#print axioms CBCL.StateResourceWorklist.closed_cone_processed

#print axioms CBCL.StateResourceWorklist.native_budget_worklist_certificate_iff

#print axioms CBCL.StateResourceCoupling.initial_coupled

#print axioms CBCL.StateResourceCoupling.gather_available

#print axioms CBCL.StateResourceCoupling.ready_lookups

#print axioms CBCL.StateResourceCoupling.ready_fresh

#print axioms CBCL.StateResourceCoupling.coupled_after_record

#print axioms CBCL.StateResourceCoupling.ready_not_blocked

#print axioms CBCL.StateResourceGraph.lookup_known

#print axioms CBCL.StateResourceGraph.parents_known

#print axioms CBCL.StateResourceGraph.unknown_has_no_outgoing

#print axioms CBCL.StateResourceGraph.recognized_links_unique

#print axioms CBCL.StateResourceGraph.native_parent_lists_unique

#print axioms CBCL.StateResourceAuthorization.checkedStep_safe

#print axioms CBCL.StateResourceAuthorization.execute_safe

#print axioms CBCL.StateResourceAuthorization.native_budget_worklist_safe

#print axioms CBCL.StateResourceAuthorization.checkedStep_budget_identity

#print axioms CBCL.StateResourceRecordBounds.amounts_append_one

#print axioms CBCL.StateResourceRecordBounds.native_record_complete

#print axioms CBCL.StateResourceRecordBounds.machine_record_complete

#print axioms CBCL.StateResourceCounters.release_missing_invariant

#print axioms CBCL.StateResourceAggregate.configurationCheck_iff

#print axioms CBCL.StateResourceAggregate.allocation_natural64

#print axioms CBCL.StateResourceAggregate.delta_bound

#print axioms CBCL.StateResourceAggregate.account_balance_append

#print axioms CBCL.StateResourceAggregate.account_balance_i128

#print axioms CBCL.StateResourceAggregate.addAccount_success

#print axioms CBCL.StateResourceAggregate.transferAccounts_success

#print axioms CBCL.StateResourceAggregate.unary_effect

#print axioms CBCL.StateResourceAggregate.transfer_effect

#print axioms CBCL.StateResourceAggregate.active_transfer_complete

#print axioms CBCL.StateResourceAggregate.applySide_complete

#print axioms CBCL.StateResourceAggregate.applySideAll_prefix

#print axioms CBCL.StateResourceAggregate.native_account_fold_refinement

#print axioms CBCL.StateResourceAggregate.native_rights_fold

#print axioms CBCL.StateResourceAggregate.native_headroom_fold

#print axioms CBCL.StateResourceAggregate.total_delta

#print axioms CBCL.StateResourceAggregate.sum_swap

#print axioms CBCL.StateResourceAggregate.total_account_balance

#print axioms CBCL.StateResourceAggregate.global_total_refinement

#print axioms CBCL.StateResourceAggregate.net_delta_duality

#print axioms CBCL.StateResourceAggregate.allocation_row

#print axioms CBCL.StateResourceAggregate.initial_roster_total

#print axioms CBCL.StateResourceAggregate.aggregate_conservation

#print axioms CBCL.StateResourceAggregate.partial_delta_bound

#print axioms CBCL.StateResourceAggregate.partial_total_i128

#print axioms CBCL.StateResourceAggregate.checkedRosterFold_prefix

#print axioms CBCL.StateResourceAggregate.native_total_refinement

#print axioms CBCL.StateResourceAggregate.headroom_transfer_requires_active

#print axioms CBCL.StateResourceAccounting.delta_components

#print axioms CBCL.StateResourceAccounting.sum_map_sub

#print axioms CBCL.StateResourceAccounting.balance_components

#print axioms CBCL.StateResourceAccounting.checkedFold_value

#print axioms CBCL.StateResourceAccounting.ownTotal_value

#print axioms CBCL.StateResourceAccounting.localBudget_value

#print axioms CBCL.StateResourceAccounting.delta_other_nonnegative

#print axioms CBCL.StateResourceAccounting.sum_map_partition

#print axioms CBCL.StateResourceAccounting.account_balance_mono

#print axioms CBCL.StateResourceSolvency.cached_prefix

#print axioms CBCL.StateResourceSolvency.past_in_processed

#print axioms CBCL.StateResourceSolvency.processed_own_in_past

#print axioms CBCL.StateResourceSolvency.local_budget_le_processed

#print axioms CBCL.StateResourceSolvency.decision_spending

#print axioms CBCL.StateResourceSolvency.done_spending_covered

#print axioms CBCL.StateResourceSolvency.sender_spending_delta

#print axioms CBCL.StateResourceSolvency.sender_other_delta_nonnegative

#print axioms CBCL.StateResourceSolvency.processed_after_permutation

#print axioms CBCL.StateResourceSolvency.processed_balance_after

#print axioms CBCL.StateResourceSolvency.done_economic

#print axioms CBCL.StateResourceSolvency.initial_side_natural

#print axioms CBCL.StateResourceSolvency.initial_economic

#print axioms CBCL.StateResourceSolvency.runFuel_economic

#print axioms CBCL.StateResourceSolvency.native_worklist_solvency

#print axioms CBCL.StateResourceSolvency.completed_balances_nonnegative

#print axioms CBCL.StateResourceSolvency.all_processed_of_size

#print axioms CBCL.StateResourceSolvency.completed_size_balances_nonnegative

#print axioms CBCL.StateResourceFinalize.no_negative_check

#print axioms CBCL.StateResourceFinalize.signed64_i128

#print axioms CBCL.StateResourceFinalize.finishBalances_unbounded

#print axioms CBCL.StateResourceFinalize.finishBalances_bounded

#print axioms CBCL.StateResourceFinalize.native_aggregate_finishes

#print axioms CBCL.StateResourceValidated.native_validated_certificate_iff

#print axioms CBCL.StateResourceValidated.ready_aggregate_value

#print axioms CBCL.StateResourceAggregateTests.unbounded_mint_value

#print axioms CBCL.StateResourceAggregateTests.funded_address_order

#print axioms CBCL.StateResourceAggregateTests.negative_final_budget_rejected

#print axioms CBCL.StateResourceAggregateTests.bounded_burn_conservation

#print axioms CBCL.StateResourceAggregateTests.broken_conservation_rejected

#print axioms CBCL.StateResourcePreflight.operation_names

#print axioms CBCL.StateResourcePreflight.foreignCheck_iff

#print axioms CBCL.StateResourcePreflight.foreign_rejection_cause

#print axioms CBCL.StateResourcePreflight.foreign_implies_previous_check

#print axioms CBCL.StateResourcePreflight.unsupportedCheck_iff

#print axioms CBCL.StateResourcePreflight.Prepared.known_inside

#print axioms CBCL.StateResourcePreflight.Prepared.known_operation

#print axioms CBCL.StateResourcePreflight.Prepared.operation_known

#print axioms CBCL.StateResourcePreflight.Prepared.known_unique

#print axioms CBCL.StateResourcePreflight.Prepared.opener_excluded

#print axioms CBCL.StateResourcePreflight.Prepared.root_unique

#print axioms CBCL.StateResourcePreflight.prepared_cause_is_budget

#print axioms CBCL.StateResourcePreflight.prepared_native_certificate_iff

#print axioms CBCL.StateResourcePreflight.initial_member

#print axioms CBCL.StateResourcePreflight.check_false

#print axioms CBCL.StateResourcePreflight.rejected_item

#print axioms CBCL.StateResourcePreflight.no_opener_no_cause

#print axioms CBCL.StateResourcePreflight.missing_root_no_cause

#print axioms CBCL.StateResourceVerifier.native_verifier_certificate_iff

#print axioms CBCL.StateResourceVerifier.cause_mono

#print axioms CBCL.StateResourceVerifier.fault_iff_complete_cause

#print axioms CBCL.StateResourceVerifier.supported_iff

#print axioms CBCL.StateResourceVerifier.evidence_projection

#print axioms CBCL.StateResourceVerifier.native_certificate_read_refinement

#print axioms CBCL.StateResourceVerifier.native_fault_persists

#print axioms CBCL.StateResourceVerifierTests.absent_opener_pending

#print axioms CBCL.StateResourceVerifierTests.absent_root_pending

#print axioms CBCL.StateResourceVerifierTests.empty_resource_ready

#print axioms CBCL.StateResourceVerifierTests.unfunded_burn_fault

#print axioms CBCL.StateResourceVerifierTests.closed_funding_ready

#print axioms CBCL.StateInstalledCompiler.source_refinement

#print axioms CBCL.StateInstalledCompiler.pair_refinement

#print axioms CBCL.StateInstalledCompiler.nativeFreeze_congr

#print axioms CBCL.StateInstalledCompiler.compile_rule_refinement

#print axioms CBCL.StateInstalledCompiler.related_cons

#print axioms CBCL.StateInstalledCompiler.compile_fields_refinement

#print axioms CBCL.StateInstalledCompiler.installed_clause_refinement

#print axioms CBCL.StateInstalledCompiler.installed_rule_plan_refinement

#print axioms CBCL.StateInstalledCompiler.lookup_present

#print axioms CBCL.StateInstalledCompiler.compile_rule_complete

#print axioms CBCL.StateInstalledCompiler.compile_fields_complete

#print axioms CBCL.StateInstalledCompiler.installed_clause_complete

#print axioms CBCL.StateInstalledCompiler.installed_observations_setEq

#print axioms CBCL.StateInstalledClause.compile_field_refinement

#print axioms CBCL.StateInstalledClause.compile_fields_refinement

#print axioms CBCL.StateInstalledClause.installed_clause_refinement

#print axioms CBCL.StateInstalledClause.attached_freeze_compilation

#print axioms CBCL.StateInstalledClause.native_resource_source_refinement

#print axioms CBCL.StateInstalledCompilerTests.late_freeze_attaches_before_dependencies

#print axioms CBCL.StateInstalledCompilerTests.forward_reference_rejected

#print axioms CBCL.StateInstalledCompilerTests.duplicate_fields_rejected

#print axioms CBCL.StateInstalledCompilerTests.absent_freeze_target_rejected

#print axioms CBCL.StateInstalledCompilerTests.simultaneous_pair_faults

#print axioms CBCL.StateInstalledCompilerTests.compiled_derived_reads_frozen_payload

#print axioms CBCL.StateInstalledLattice.foldSet_history

#print axioms CBCL.StateInstalledLattice.source_data

#print axioms CBCL.StateInstalledLattice.pairCheck_iff

#print axioms CBCL.StateInstalledLattice.alternativesCheck_iff

#print axioms CBCL.StateInstalledLattice.query_source_coherence

#print axioms CBCL.StateInstalledLattice.query_refinement

#print axioms CBCL.StateInstalledLattice.query_quasi_determinism

#print axioms CBCL.StateInstalledLowering.lower_definition_refinement

#print axioms CBCL.StateInstalledLowering.lower_rule_refinement

#print axioms CBCL.StateInstalledLowering.interpret_attached_head

#print axioms CBCL.StateInstalledLowering.resolve_native_refinement

#print axioms CBCL.StateInstalledLowering.native_installed_compiler_refinement

#print axioms CBCL.StateInstalledLowering.recognized_complete

#print axioms CBCL.StateInstalledLowering.lowered_references

#print axioms CBCL.StateInstalledLowering.resolve_complete

#print axioms CBCL.StateInstalledLowering.native_installed_compiler_complete

#print axioms CBCL.StateInstalledLowering.native_installed_observations_refinement

#print axioms CBCL.StateInstalledLowering.native_installed_observations_setEq

#print axioms CBCL.StateInstalledLowering.native_installed_strong_eventual_consistency

#print axioms CBCL.StateInstalledLowering.aligned_reader

#print axioms CBCL.StateInstalledLowering.native_installed_eventual_fault

#print axioms CBCL.StateInstalledLoweringTests.empty_query_rejected

#print axioms CBCL.StateInstalledLoweringTests.duplicate_query_rejected

#print axioms CBCL.StateInstalledLoweringTests.conflict_top_query_rejected

#print axioms CBCL.StateInstalledLoweringTests.compatible_alternatives_rejected

#print axioms CBCL.StateInstalledLoweringTests.native_lattice_read_reached

#print axioms CBCL.StateInstalledLoweringTests.supersede_threshold_source_rejected

#print axioms CBCL.StateInstalledLoweringTests.fault_threshold_source_accepted_metadata

#print axioms CBCL.StateObservationPlan.contextAs_value

#print axioms CBCL.StateObservationPlan.guardThreshold_top_fault

#print axioms CBCL.StateObservationPlan.embed_preserves_reached

#print axioms CBCL.StateInstalledCompiler.lift_threshold_refinement

#print axioms CBCL.StateInstalledClause.attached_fields_complete

#print axioms CBCL.StateResourceCompletion.closed_known_processed

#print axioms CBCL.StateResourceCompletion.all_processed_closed

#print axioms CBCL.StateResourceCompletion.saturated_size_iff_closed

#print axioms CBCL.StateResourceCompletion.validated_ready_iff_closed

#print axioms CBCL.StateResourceCompletion.finishBalances_maps

#print axioms CBCL.StateResourceCompletion.validated_ready_finish

#print axioms CBCL.StateResourceCompletion.validated_ready_headroom

#print axioms CBCL.StateResourceCompletion.accountBalance_perm

#print axioms CBCL.StateResourceCompletion.closedKnown_equiv

#print axioms CBCL.StateResourceCompletion.budgetWitness_equiv

#print axioms CBCL.StateResourceCompletion.ready_snapshot_eq

#print axioms CBCL.StateResourceCompletion.validated_observe_perm

#print axioms CBCL.StateResourceReadEquivalence.accepted_root_prevents_pending

#print axioms CBCL.StateResourceReadEquivalence.checked_of_root_and_no_cause

#print axioms CBCL.StateResourceReadEquivalence.observe_fault_iff_cause

#print axioms CBCL.StateResourceReadEquivalence.native_observe_perm

#print axioms CBCL.StateInstalledLegacy.history_member

#print axioms CBCL.StateInstalledLegacy.history_setEq

#print axioms CBCL.StateInstalledLegacy.unique_of_consistent

#print axioms CBCL.StateInstalledLegacy.history_unique

#print axioms CBCL.StateInstalledLegacy.snapshot_value_refinement

#print axioms CBCL.StateInstalledLegacy.guardSources_clear

#print axioms CBCL.StateInstalledLegacy.kernel_source_value_refinement

#print axioms CBCL.StateInstalledLegacy.primitive_native_binding

#print axioms CBCL.StateInstalledLegacy.lower_rule_complete

#print axioms CBCL.StateInstalledLegacy.lower_fields_complete

#print axioms CBCL.StateInstalledLegacy.derived_frozen_sum_sound

#print axioms CBCL.StateInstalledLegacy.derived_frozen_histogram_sound

#print axioms CBCL.StateInstalledLegacy.lookup_name_member

#print axioms CBCL.StateInstalledLegacy.original_references_scoped

#print axioms CBCL.StateInstalledLegacy.lower_rule_references

#print axioms CBCL.StateInstalledLegacy.lower_fields_wellFormed

#print axioms CBCL.StateInstalledLegacy.concrete_installed_refinement

#print axioms CBCL.StateInstalledLegacy.lower_fields_metadata

#print axioms CBCL.StateInstalledLegacy.concrete_installed_complete

#print axioms CBCL.StateInstalledResource.makeInput_complete

#print axioms CBCL.StateInstalledResource.snapshot_native_refinement

#print axioms CBCL.StateInstalledResource.source_native_fault_refinement

#print axioms CBCL.StateInstalledResource.canonical_input

#print axioms CBCL.StateInstalledResource.snapshot_actual_history_refinement

#print axioms CBCL.StateInstalledResource.concrete_resource_read_refinement

#print axioms CBCL.StateInstalledLegacyTests.revisable_values_member_rejected

#print axioms CBCL.StateInstalledLegacyTests.observed_set_member_rejected

#print axioms CBCL.StateInstalledLegacyTests.arrival_member_accepted

#print axioms CBCL.StateInstalledLegacyTests.duplicate_count_alternatives_rejected

#print axioms CBCL.StateInstalledLegacyTests.structured_member_rejected

#print axioms CBCL.StateInstalledLegacyTests.signed_events_sum_rejected

#print axioms CBCL.StateInstalledLegacyTests.optional_nonnegative_sum_rejected

#print axioms CBCL.StateInstalledLegacyTests.mandatory_nonnegative_sum_accepted

#print axioms CBCL.StateInstalledLegacyTests.oversized_count_rejected

#print axioms CBCL.StateInstalledLegacyTests.negative_event_sum_bound_accepted

#print axioms CBCL.StateInstalledLegacyTests.empty_registry_clause_compiles

#print axioms CBCL.StateInstalledTerm.guard_data

#print axioms CBCL.StateInstalledTerm.source_state_coherence

#print axioms CBCL.StateInstalledTerm.accepted_history_merge

#print axioms CBCL.StateInstalledLegacy.kernelTerm_source

#print axioms CBCL.StateInstalledResource.source_unfold

#print axioms CBCL.StateContextEvidence.vacuous_closed

#print axioms CBCL.StateContextEvidence.mixedCheck_iff

#print axioms CBCL.StateContextEvidence.mixed_setEq

#print axioms CBCL.StateContextEvidence.soleError_grows

#print axioms CBCL.StateContextEvidence.hasRoot_iff

#print axioms CBCL.StateContextEvidence.normalization_eq_union

#print axioms CBCL.StateContextEvidence.native_context_witness_refinement

#print axioms CBCL.StateContextEvidence.native_context_fault_persists

#print axioms CBCL.StateContextEvidence.mixedCheck_first_root

#print axioms CBCL.StateInstalledContext.openerValue_setEq

#print axioms CBCL.StateInstalledContext.thread_setEq

#print axioms CBCL.StateInstalledContext.frontier_setEq

#print axioms CBCL.StateInstalledContext.observation_setEq

#print axioms CBCL.StateInstalledContext.value_setEq

#print axioms CBCL.StateInstalledContext.concrete_context_read_refinement

#print axioms CBCL.StateInstalledContext.roster_query_only

#print axioms CBCL.StateInstalledDomains.allowed_setEq

#print axioms CBCL.StateInstalledDomains.allowed_grows

#print axioms CBCL.StateInstalledDomains.eligible_setEq

#print axioms CBCL.StateInstalledDomains.eligible_grows

#print axioms CBCL.StateInstalledDomains.selected_setEq

#print axioms CBCL.StateInstalledDomains.selected_grows

#print axioms CBCL.StateInstalledDomains.roster_source_recognized

#print axioms CBCL.StateFiniteTable.all_indices

#print axioms CBCL.StateFiniteTable.lawCheck_iff

#print axioms CBCL.StateFiniteTable.check_iff

#print axioms CBCL.StateFiniteTable.compile_sound

#print axioms CBCL.StateFiniteTable.compile_complete

#print axioms CBCL.StateFiniteTable.empty_elements_rejected

#print axioms CBCL.StateFiniteProjection.check_iff

#print axioms CBCL.StateFiniteProjection.value_row

#print axioms CBCL.StateFiniteProjection.stable_value_order

#print axioms CBCL.StateFiniteProjection.contribution_lift

#print axioms CBCL.StateFiniteProjection.numeric_read_upward

#print axioms CBCL.StateFiniteProjection.compile_sound

#print axioms CBCL.StateFiniteProjection.compile_complete

#print axioms CBCL.StateFiniteProjection.boolean_read_upward

#print axioms CBCL.StateFiniteProjectionTests.native_table_checks

#print axioms CBCL.StateFiniteProjectionTests.numeric_projection_accepted

#print axioms CBCL.StateFiniteProjectionTests.boolean_projection_accepted

#print axioms CBCL.StateFiniteProjectionTests.decreasing_projection_rejected

#print axioms CBCL.StateFiniteProjectionTests.string_stable_projection_rejected

#print axioms CBCL.StateFiniteProjectionTests.mixed_stable_projection_rejected

#print axioms CBCL.StateFiniteProjectionTests.snapshot_string_projection_accepted

#print axioms CBCL.StateFiniteProjectionTests.top_row_required

#print axioms CBCL.StateFiniteProjectionTests.duplicate_row_rejected

#print axioms CBCL.StateFiniteProjectionTests.structured_projection_rejected

#print axioms CBCL.StateFiniteProjectionTests.oversized_literal_rejected

#print axioms CBCL.StateFiniteProjectionTests.unknown_contribution_rejected

#print axioms CBCL.StateFiniteProjectionTests.structured_contribution_rejected

#print axioms CBCL.StateFiniteProjectionTests.every_matching_row_contributes

#print axioms CBCL.StateFiniteProjectionTests.nonmatching_row_contributes_bottom

#print axioms CBCL.StateInstalledFinite.selected_setEq

#print axioms CBCL.StateInstalledFinite.selected_grows

#print axioms CBCL.StateInstalledFinite.selected_inside

#print axioms CBCL.StateInstalledFinite.state_setEq

#print axioms CBCL.StateInstalledFinite.state_grows

#print axioms CBCL.StateInstalledFinite.writers_setEq

#print axioms CBCL.StateInstalledFinite.writers_grows

#print axioms CBCL.StateInstalledFinite.native_error_refinement

#print axioms CBCL.StateInstalledFinite.concrete_finite_read_refinement

#print axioms CBCL.StateFiniteRead.pairCheck_iff

#print axioms CBCL.StateFiniteRead.reaches_upward

#print axioms CBCL.StateFiniteRead.distinct_reads_force_top

#print axioms CBCL.StateFiniteRead.policy_actual_history

#print axioms CBCL.StateFiniteRead.definition_guard_coherence

#print axioms CBCL.StateFiniteReadTests.named_bottom_accepted

#print axioms CBCL.StateFiniteReadTests.named_top_rejected

#print axioms CBCL.StateFiniteReadTests.numeric_projection_accepted

#print axioms CBCL.StateFiniteReadTests.mixed_query_common_upper_rejected

#print axioms CBCL.StateFiniteReadTests.duplicate_query_rejected

#print axioms CBCL.StateFiniteReadTests.empty_query_rejected

#print axioms CBCL.StateFiniteReadTests.boolean_query_on_numeric_projection_rejected

#print axioms CBCL.StateFiniteReadTests.unknown_named_query_rejected

#print axioms CBCL.StateFiniteReadTests.oversized_numeric_query_rejected

#print axioms CBCL.StateFiniteReadTests.invalid_literal_factory_rejected

#print axioms CBCL.StateFiniteReadTests.unknown_keyword_factory_rejected

#print axioms CBCL.StateFiniteReadTests.empty_contributions_factory_rejected

#print axioms CBCL.StateFiniteReadTests.valid_literal_factory_accepted

#print axioms CBCL.StateInstalledCompiler.raw_threshold_refinement

#print axioms CBCL.StateFiniteRead.test_top

#print axioms CBCL.StateFiniteRead.test_non_top

#print axioms CBCL.StateAuthoredBindings.authored_binding_refinement

#print axioms CBCL.StateAuthoredBindings.prepared_compiler_complete

#print axioms CBCL.StateAuthoredBindings.contributes_setEq

#print axioms CBCL.StateAuthoredBindings.contributes_grows

#print axioms CBCL.StateAuthoredBindings.freezes_setEq

#print axioms CBCL.StateAuthoredBindings.prepare_setEq

#print axioms CBCL.StateAuthoredBindings.compile_setEq

#print axioms CBCL.StateAuthoredBindings.authored_observations_setEq

#print axioms CBCL.StateAuthoredBindingsTests.rendered_bound_counts_thresholds

#print axioms CBCL.StateAuthoredBindingsTests.lattice_and_field_namespace_shared

#print axioms CBCL.StateAuthoredBindingsTests.unicode_field_name_rejected

#print axioms CBCL.StateAuthoredBindingsTests.upper_case_field_name_rejected

#print axioms CBCL.StateAuthoredBindingsTests.domain_can_reference_later_initializer

#print axioms CBCL.StateAuthoredBindingsTests.domain_unknown_role_rejected

#print axioms CBCL.StateAuthoredBindingsTests.review_prepares

#print axioms CBCL.StateAuthoredBindingsTests.review_compiles

#print axioms CBCL.StateAuthoredBindingsTests.whole_context_contributor

#print axioms CBCL.StateAuthoredBindingsTests.role_projection_has_no_write_contributors

#print axioms CBCL.StateAuthoredBindingsTests.progress_raw_contributor

#print axioms CBCL.StateAuthoredBindingsTests.forward_threshold_rejected

#print axioms CBCL.StateAuthoredBindingsTests.supersede_threshold_source_rejected

#print axioms CBCL.StateAuthoredBindingsTests.threshold_output_cannot_be_frozen

#print axioms CBCL.StateAuthoredBindingsTests.resource_operation_domain_rejected

#print axioms CBCL.StateFreezeGrowth.conflict_transfer

#print axioms CBCL.StateFreezeGrowth.evidence_grows

#print axioms CBCL.StateFreezeGrowth.fault_grows

#print axioms CBCL.StateFreezeGrowth.related_errors_grow

#print axioms CBCL.StateFreezeGrowth.authored_freeze_grows

#print axioms CBCL.StateFreezeScopes.causal_cut_closed

#print axioms CBCL.StateFreezeScopes.earliest_scope

#print axioms CBCL.StateFreezeScopes.scoped_conflict_global

#print axioms CBCL.StateFreezeScopes.global_cut_in_scope

#print axioms CBCL.StateFreezeScopes.absent_global_freezer_no_scoped_freezer

#print axioms CBCL.StateFreezeScopes.excluded_restriction

#print axioms CBCL.StateAuthoredBindingsTests.freeze_without_sender_role_rejected

#print axioms CBCL.StateFreezeScopes.selected_freezer_scope

#print axioms CBCL.StateFreezeScopes.cached_freeze_refinement

#print axioms CBCL.StateFreezeScopes.source_clear_in_scope

#print axioms CBCL.StateFreezeScopes.cached_plan_data_refinement

#print axioms CBCL.StateCompiledFreezeGrowth.lookup_paths

#print axioms CBCL.StateCompiledFreezeGrowth.compile_rule_path

#print axioms CBCL.StateCompiledFreezeGrowth.match_map

#print axioms CBCL.StateCompiledFreezeGrowth.match_join

#print axioms CBCL.StateCompiledFreezeGrowth.rule_path_related

#print axioms CBCL.StateCompiledFreezeGrowth.decorate_related

#print axioms CBCL.StateCompiledFreezeGrowth.extend_related

#print axioms CBCL.StateCompiledFreezeGrowth.fields_related

#print axioms CBCL.StateCompiledFreezeGrowth.compile_field_path

#print axioms CBCL.StateCompiledFreezeGrowth.compile_fields_path

#print axioms CBCL.StateCompiledFreezeGrowth.compiled_error_growth

#print axioms CBCL.StateAuthoredBindingsTests.materialized_progress_contributor

#print axioms CBCL.StateCompiledFreezeGrowth.authored_decorations

#print axioms CBCL.StateCompiledFreezeGrowth.authored_compiled_error_growth

#print axioms CBCL.StateCompiledFreezeGrowth.materialized_stable_source

#print axioms CBCL.StateCompiledFreezeGrowth.materialized_metadata

#print axioms CBCL.StateCompiledFreezeGrowth.authored_compiles_after_growth

#print axioms CBCL.StateCompiledFreezeGrowth.named_fault_transfer

#print axioms CBCL.StateCompiledFreezeGrowth.authored_fault_grows

#print axioms CBCL.StateCompiledFreezeGrowth.eventual_authored_fault

#print axioms CBCL.StateNativeReader.freeze_error_union
#print axioms CBCL.StateNativeReader.full_error_refinement
#print axioms CBCL.StateNativeReader.union_clear
#print axioms CBCL.StateNativeReader.freeze_clear
#print axioms CBCL.StateNativeReader.scoped_error_clear
#print axioms CBCL.StateNativeReader.cached_congr
#print axioms CBCL.StateNativeReader.scoped_value_refinement
#print axioms CBCL.StateNativeReader.native_reader_refinement

#print axioms CBCL.StateFiniteUpperCache.maximum_ge
#print axioms CBCL.StateFiniteUpperCache.upperMaximum_ge
#print axioms CBCL.StateFiniteUpperCache.optional_test
#print axioms CBCL.StateFiniteUpperCache.named_common
#print axioms CBCL.StateFiniteUpperCache.numeric_common
#print axioms CBCL.StateFiniteUpperCache.compatible_iff
#print axioms CBCL.StateFiniteUpperCache.value_kind
#print axioms CBCL.StateFiniteUpperCache.decode_reaches
#print axioms CBCL.StateFiniteUpperCache.cached_compatible_iff
#print axioms CBCL.StateFiniteUpperCache.cached_pair_refinement
#print axioms CBCL.StateFiniteUpperCache.cached_check_refinement

#print axioms CBCL.StateFinitePairLoop.projected_lookup
#print axioms CBCL.StateFinitePairLoop.maxima_lookup
#print axioms CBCL.StateFinitePairLoop.stored_compatible_refinement
#print axioms CBCL.StateFinitePairLoop.stored_scalar_refinement
#print axioms CBCL.StateFinitePairLoop.reason_clear
#print axioms CBCL.StateFinitePairLoop.row_clear
#print axioms CBCL.StateFinitePairLoop.pairs_clear
#print axioms CBCL.StateFinitePairLoop.pairwise_symmetric
#print axioms CBCL.StateFinitePairLoop.compatible_symmetric
#print axioms CBCL.StateFinitePairLoop.scalar_symmetric
#print axioms CBCL.StateFinitePairLoop.stored_pairs_refinement
#print axioms CBCL.StateFinitePairLoop.check_refinement
#print axioms CBCL.StateFinitePairLoop.row_reference
#print axioms CBCL.StateFinitePairLoop.pairs_reference
#print axioms CBCL.StateFinitePairLoop.first_diagnostic
#print axioms CBCL.StateFinitePairLoop.duplicate_precedence
#print axioms CBCL.StateFinitePairLoop.candidate_indices
#print axioms CBCL.StateFinitePairLoop.diagnostic_sound

#print axioms CBCL.StateInstalledRecognition.compile_rule_sound
#print axioms CBCL.StateInstalledRecognition.attached_fields_sound
#print axioms CBCL.StateInstalledRecognition.recognized_iff
#print axioms CBCL.StateInstalledRecognition.check_iff
#print axioms CBCL.StateInstalledRecognition.resolve_sound
#print axioms CBCL.StateInstalledRecognition.compile_sound
#print axioms CBCL.StateInstalledRecognition.compile_iff
#print axioms CBCL.StateAuthoredBindings.stable_source_history
#print axioms CBCL.StateAuthoredBindings.metadata_history
#print axioms CBCL.StateAuthoredBindings.static_preparation_sound
#print axioms CBCL.StateAuthoredBindings.preparation_compilation_iff
#print axioms CBCL.StateAuthoredBindings.preparation_preserves_compilation
#print axioms CBCL.StateAuthoredBindingsTests.forward_threshold_preparation_rejected
#print axioms CBCL.StateAuthoredBindingsTests.supersede_threshold_preparation_rejected
#print axioms CBCL.StateAuthoredBindingsTests.empty_threshold_preparation_rejected

#print axioms CBCL.StateAuthoredCompletion.prepared_readers_complete
#print axioms CBCL.StateAuthoredCompletion.cached_observations_setEq

#print axioms CBCL.StateExecutableFreeze.rankedCheck_sound
#print axioms CBCL.StateExecutableFreeze.ancestor_trans
#print axioms CBCL.StateExecutableFreeze.ancestor_last
#print axioms CBCL.StateExecutableFreeze.reachable_sound
#print axioms CBCL.StateExecutableFreeze.reachable_complete
#print axioms CBCL.StateExecutableFreeze.ancestor_iff
#print axioms CBCL.StateExecutableFreeze.cut_refinement
#print axioms CBCL.StateExecutableFreeze.earliest_iff
#print axioms CBCL.StateExecutableFreeze.conflict_iff
#print axioms CBCL.StateExecutableFreeze.conflicts_member
#print axioms CBCL.StateExecutableFreeze.evidence_member
#print axioms CBCL.StateExecutableFreeze.has_conflict
#print axioms CBCL.StateExecutableFreeze.evidence_set
#print axioms CBCL.StateExecutableFreeze.read_refinement

#print axioms CBCL.StateExecutableObservation.map_refinement
#print axioms CBCL.StateExecutableObservation.error_refinement
#print axioms CBCL.StateExecutableObservation.map_read
#print axioms CBCL.StateExecutableObservation.present_refinement
#print axioms CBCL.StateExecutableObservation.freeze_refinement

#print axioms CBCL.StateExecutableContext.identities_evidence
#print axioms CBCL.StateExecutableContext.root_error_refinement
#print axioms CBCL.StateExecutableContext.mixed_error_refinement
#print axioms CBCL.StateExecutableContext.opener_error_refinement
#print axioms CBCL.StateExecutableContext.join_refinement
#print axioms CBCL.StateExecutableContext.error_refinement
#print axioms CBCL.StateExecutableContext.frontier_refinement
#print axioms CBCL.StateExecutableContext.observation_refinement
#print axioms CBCL.StateExecutableContext.value_refinement
#print axioms CBCL.StateExecutableContext.read_refinement

#print axioms CBCL.StateMemoizedReader.below_meaning_eq
#print axioms CBCL.StateMemoizedReader.reference_equation
#print axioms CBCL.StateMemoizedReader.empty_valid
#print axioms CBCL.StateMemoizedReader.insert_valid
#print axioms CBCL.StateMemoizedReader.body_run_refinement
#print axioms CBCL.StateMemoizedReader.read_refinement
#print axioms CBCL.StateMemoizedReader.empty_read
#print axioms CBCL.StateMemoizedReader.operational_refinement
#print axioms CBCL.StateMemoizedReader.reads_refinement
#print axioms CBCL.StateMemoizedReader.redirect_rank
#print axioms CBCL.StateMemoizedReader.dependency_rank
#print axioms CBCL.StateMemoizedReader.finish_ranked
#print axioms CBCL.StateMemoizedReader.body_ranked
#print axioms CBCL.StateMemoizedReader.native_reads_refinement

#print axioms CBCL.StateMemoizedReaderTests.incomparable_cut_values
#print axioms CBCL.StateMemoizedReaderTests.different_request_order
#print axioms CBCL.StateMemoizedReaderTests.fault_shortcircuit

#print axioms CBCL.StateReaderIndices.reference_prefix
#print axioms CBCL.StateReaderIndices.reference_index
#print axioms CBCL.StateReaderIndices.compiled_scoping
#print axioms CBCL.StateReaderIndices.compiled_dependency_ordering
#print axioms CBCL.StateReaderIndices.compiled_native_cache


#print axioms CBCL.StateScopePool.normalize_setEq
#print axioms CBCL.StateScopePool.normalize_unique
#print axioms CBCL.StateScopePool.normalize_ranked
#print axioms CBCL.StateScopePool.initial_valid
#print axioms CBCL.StateScopePool.lookup_append
#print axioms CBCL.StateScopePool.intern_refinement
#print axioms CBCL.StateScopePool.intern_reuse
#print axioms CBCL.StateScopePool.intern_preserves_lookup
#print axioms CBCL.StateScopePool.allocate_preserves_lookup
#print axioms CBCL.StateScopePool.allocate_refinement
#print axioms CBCL.StateScopePool.cutAt_refinement
#print axioms CBCL.StateScopePool.native_cut_closed
#print axioms CBCL.StateScopePool.related_member
#print axioms CBCL.StateScopePool.native_scopes_refinement
#print axioms CBCL.StateScopePool.active_iff
#print axioms CBCL.StateScopePool.allocated_cut_complete
#print axioms CBCL.StateScopePool.uniqueRoot_accepted
#print axioms CBCL.StateScopePool.uniqueRoot_complete
#print axioms CBCL.StateScopePool.selectedRoots_accepted
#print axioms CBCL.StateScopePool.declared_scopes_refinement
#print axioms CBCL.StateScopePool.normalized_scopes_sound
#print axioms CBCL.StateScopePool.uniqueRoot_earliest
#print axioms CBCL.StateScopePool.shared_scope_witness
#print axioms CBCL.StateScopePool.causal_scope_witness
#print axioms CBCL.StateScopePool.duplicate_freezer_witness
#print axioms CBCL.StateAuthoredDependencies.primitive_references
#print axioms CBCL.StateAuthoredDependencies.bind_references
#print axioms CBCL.StateAuthoredDependencies.declaration_dependencies
#print axioms CBCL.StateAuthoredDependencies.resolve_field
#print axioms CBCL.StateAuthoredDependencies.static_dependencies
#print axioms CBCL.StateAuthoredDependencies.prepared_dependencies
#print axioms CBCL.StateAuthoredDependencies.extracted_reference
#print axioms CBCL.StateAuthoredDependencies.resolve_names
#print axioms CBCL.StateAuthoredDependencies.lowered_compiled_clause
#print axioms CBCL.StateAuthoredDependencies.prepared_native_cache
#print axioms CBCL.StateAuthoredDependencies.prepared_scoped_cache

#print axioms CBCL.StateReaderValues.derived_unfrozen
#print axioms CBCL.StateReaderValues.source_error
#print axioms CBCL.StateReaderValues.source_value
#print axioms CBCL.StateReaderValues.source_scoped_refinement
#print axioms CBCL.StateReaderValues.derived_scoped_refinement
#print axioms CBCL.StateReaderValues.combined_two_faults
#print axioms CBCL.StateReaderValues.combined_no_freeze
#print axioms CBCL.StateReaderValues.derived_frozen
#print axioms CBCL.StateReaderValues.frozen_unfrozen
#print axioms CBCL.StateReaderValues.frozen_nested
#print axioms CBCL.StateReaderValues.scoped_error
#print axioms CBCL.StateReaderValues.freeze_error_refinement
#print axioms CBCL.StateReaderValues.frozen_data_refinement
#print axioms CBCL.StateReaderValues.scoped_clear
#print axioms CBCL.StateReaderValues.cut_clear
#print axioms CBCL.StateReaderValues.cached_freeze_scoped
#print axioms CBCL.StateReaderValues.operations_fixed
#print axioms CBCL.StateReaderValues.normal_source
#print axioms CBCL.StateReaderValues.normal_derived
#print axioms CBCL.StateReaderValues.supported_definition
#print axioms CBCL.StateReaderValues.prepared_supported
#print axioms CBCL.StateReaderValues.prepared_fixed_cache
#print axioms CBCL.StateReaderValuesTests.cut_value_witness
#print axioms CBCL.StateReaderValuesTests.whole_value_witness
#print axioms CBCL.StateReaderValuesTests.unwrapped_value_witness
#print axioms CBCL.StateReaderValuesTests.outer_wrapper_witness
#print axioms CBCL.StateReaderValuesTests.fault_union_witness


#print axioms CBCL.StateReaderReachability.bind_dependency_known
#print axioms CBCL.StateReaderReachability.declarations_known
#print axioms CBCL.StateReaderReachability.static_known
#print axioms CBCL.StateReaderReachability.prepared_known
#print axioms CBCL.StateReaderReachability.cut_allocated
#print axioms CBCL.StateReaderReachability.finish_within
#print axioms CBCL.StateReaderReachability.body_within
#print axioms CBCL.StateReaderReachability.run_within
#print axioms CBCL.StateReaderReachability.read_within
#print axioms CBCL.StateReaderReachability.reads_within
#print axioms CBCL.StateReaderReachability.initial_admitted
#print axioms CBCL.StateReaderReachability.admitted_scope
#print axioms CBCL.StateReaderReachability.lookup_original
#print axioms CBCL.StateReaderReachability.admitted_rule
#print axioms CBCL.StateReaderReachability.declaration_shapes
#print axioms CBCL.StateReaderReachability.lowering_witness
#print axioms CBCL.StateReaderReachability.prepared_shapes
#print axioms CBCL.StateReaderReachability.resolved_threshold_source
#print axioms CBCL.StateReaderReachability.prepared_threshold_known
#print axioms CBCL.StateReaderReachability.initial_keys_admitted
#print axioms CBCL.StateReaderReachability.prepared_reachable_cache
#print axioms CBCL.StateReaderReachability.meaning_congr
#print axioms CBCL.StateReaderReachability.reference_on_domain
#print axioms CBCL.StateReaderReachabilityTests.review_request_keys
#print axioms CBCL.StateReaderReachabilityTests.review_requests_admitted


#print axioms CBCL.StateCompiledFieldEquations.compile_field_equation
#print axioms CBCL.StateCompiledFieldEquations.compile_rule_congr
#print axioms CBCL.StateCompiledFieldEquations.compile_rule_completed
#print axioms CBCL.StateCompiledFieldEquations.compile_fields_names
#print axioms CBCL.StateCompiledFieldEquations.fields_equations
#print axioms CBCL.StateCompiledFieldEquations.installed_equation
#print axioms CBCL.StateCompiledFieldEquations.source_equation
#print axioms CBCL.StateCompiledFieldEquations.derived_equation
#print axioms CBCL.StateCompiledFieldEquations.prepared_unique
#print axioms CBCL.StateCompiledFieldEquations.dependency_equation
#print axioms CBCL.StateCompiledFieldEquations.prepared_body_normal
#print axioms CBCL.StateCompiledFieldEquations.missing_freeze_root
#print axioms CBCL.StateCompiledFieldEquations.finish_without_freeze
#print axioms CBCL.StateCompiledFieldEquations.prepared_unfrozen_body
#print axioms CBCL.StateCompiledFieldEquations.prepared_no_freeze_reference
#print axioms CBCL.StateCompiledFieldEquations.prepared_no_freeze_cache
#print axioms CBCL.StateCompiledFieldEquations.finish_faulting
#print axioms CBCL.StateCompiledFieldEquations.prepared_fault_body
#print axioms CBCL.StateCompiledFieldEquationsTests.derived_keeps_frozen_source
#print axioms CBCL.StateCompiledFieldEquationsTests.counted_prepares
#print axioms CBCL.StateCompiledFieldEquationsTests.counted_freezes

#print axioms CBCL.StateScopeProperties.intern_property
#print axioms CBCL.StateScopeProperties.allocate_property
#print axioms CBCL.StateScopeProperties.scope_origin
#print axioms CBCL.StateScopeProperties.scope_properties
#print axioms CBCL.StateScopeProperties.root_lookup
#print axioms CBCL.StateScopeProperties.root_find
#print axioms CBCL.StateScopeProperties.compiled_freezes_unique
#print axioms CBCL.StateScopeProperties.admitted_properties
#print axioms CBCL.StateScopeProperties.absent_root_metadata
#print axioms CBCL.StateScopeProperties.selected_root_metadata
#print axioms CBCL.StateFrozenBodyEquations.freeze_selected_equation
#print axioms CBCL.StateFrozenBodyEquations.freeze_absent_equation
#print axioms CBCL.StateFrozenBodyEquations.finish_clear_refinement
#print axioms CBCL.StateFrozenBodyEquations.prepared_body_equation
#print axioms CBCL.StateFrozenBodyEquations.prepared_reference_equivalence
#print axioms CBCL.StateFrozenBodyEquations.prepared_cache_equivalence
#print axioms CBCL.StateFrozenBodyEquations.initial_meaning
#print axioms CBCL.StateFrozenBodyEquationsTests.incomparable_active_witness
#print axioms CBCL.StateFrozenBodyEquationsTests.allocated_cuts_witness
#print axioms CBCL.StateFrozenBodyEquationsTests.concrete_cache_transcript

#print axioms CBCL.StateCausalRank.reachable_complete_by
#print axioms CBCL.StateCausalRank.check_sound
#print axioms CBCL.StateCausalRank.ancestor_iff
#print axioms CBCL.StateCausalRank.cut_refinement
#print axioms CBCL.StateCausalRank.descending_check
#print axioms CBCL.StateCausalRank.descending_cut

#print axioms CBCL.StateThresholdDispatch.raw_scope_refinement
#print axioms CBCL.StateThresholdDispatch.dispatch_refinement
#print axioms CBCL.StateThresholdDispatch.prepared_threshold_reference
#print axioms CBCL.StateThresholdDispatchTests.allocated_raw_cut
#print axioms CBCL.StateThresholdDispatchTests.pending_source_reaches
#print axioms CBCL.StateThresholdDispatchTests.display_does_not_replace_raw

#print axioms CBCL.StateThresholdDispatch.installed_factored_rejects
#print axioms CBCL.StateThresholdDispatch.installed_scope_refinement

#print axioms CBCL.StatePreparedOutputs.threshold_available
#print axioms CBCL.StatePreparedOutputs.evaluate_complete
#print axioms CBCL.StatePreparedOutputs.evaluate_values_map
#print axioms CBCL.StatePreparedOutputs.evaluate_congr
#print axioms CBCL.StatePreparedOutputs.initial_keys_shapes
#print axioms CBCL.StatePreparedOutputs.prepared_output_admitted
#print axioms CBCL.StatePreparedOutputs.prepared_outputs
#print axioms CBCL.StatePreparedOutputs.prepared_cache_outputs
#print axioms CBCL.StatePreparedOutputsTests.concrete_cache_outputs

#print axioms CBCL.StateOutputCompiler.compile_query_refinement
#print axioms CBCL.StateOutputCompiler.compile_one_refinement
#print axioms CBCL.StateOutputCompiler.evaluate_cons_one
#print axioms CBCL.StateOutputCompiler.compile_outputs_refinement
#print axioms CBCL.StateOutputCompiler.prepared_sources_known
#print axioms CBCL.StateOutputCompiler.prepared_compiler_cache_refinement
#print axioms CBCL.StateOutputCompiler.authored_compiler_refinement
#print axioms CBCL.StateOutputCompilerTests.concrete_compiled_outputs

#print axioms CBCL.StateFiniteCausalRank.below_mono
#print axioms CBCL.StateFiniteCausalRank.below_strict
#print axioms CBCL.StateFiniteCausalRank.below_bound
#print axioms CBCL.StateCausalRank.ranked_from_order
#print axioms CBCL.StateCausalRank.causalCheck_sound
#print axioms CBCL.StateCausalRank.descending_reverse_checked
#print axioms CBCL.StateCausalRank.descending_integrated_cut
#print axioms CBCL.StateCausalRank.cycle_rejected
#print axioms CBCL.StateCausalRankIntegrationTests.descending_duplicate_compiled_outputs

#print axioms CBCL.StateCausalCheckComplete.minimum_rank
#print axioms CBCL.StateCausalCheckComplete.ready_exists
#print axioms CBCL.StateCausalCheckComplete.remove_shorter
#print axioms CBCL.StateCausalCheckComplete.order_prefix
#print axioms CBCL.StateCausalCheckComplete.check_of_positions
#print axioms CBCL.StateCausalCheckComplete.ready_no_parent
#print axioms CBCL.StateCausalCheckComplete.check_cons
#print axioms CBCL.StateCausalCheckComplete.order_complete
#print axioms CBCL.StateCausalCheckComplete.causalCheck_complete
#print axioms CBCL.StateCausalCheckComplete.causalCheck_iff
#print axioms CBCL.StateCausalCheckComplete.ranked_setEq
#print axioms CBCL.StateCausalCheckComplete.causalCheck_setEq
#print axioms CBCL.StateCausalCheckCompleteTests.duplicate_delivery_complete
#print axioms CBCL.StateCausalCheckCompleteTests.empty_complete

#print axioms CBCL.StateCausalCheckCompleteTests.closure_is_separate

#print axioms CBCL.StateFiniteProjection.row_literal_not_list
#print axioms CBCL.StateFiniteProjection.row_ignores_opaque

#print axioms CBCL.StateOpenerLocality.rooted_parent
#print axioms CBCL.StateOpenerLocality.opener_ancestor
#print axioms CBCL.StateOpenerLocality.initializer_unique
#print axioms CBCL.StateOpenerLocality.opener_cut_setEq
#print axioms CBCL.StateOpenerLocality.initializer_cut
#print axioms CBCL.StateOpenerLocality.domain_cut
#print axioms CBCL.StateOpenerLocality.fault_domain_cut
#print axioms CBCL.StateOpenerLocality.fault_domain_count
#print axioms CBCL.StateOpenerLocalityTests.metadata_root_permitted
#print axioms CBCL.StateOpenerLocalityTests.initializer_local
#print axioms CBCL.StateOpenerLocalityTests.unrooted_acyclic
#print axioms CBCL.StateOpenerLocalityTests.missing_business_parent_rejected
#print axioms CBCL.StateOpenerLocalityTests.unrooted_full_count
#print axioms CBCL.StateOpenerLocalityTests.unrooted_cut_count

#print axioms CBCL.StateOpenerLocalityTests.healthy_domain_count_local

#print axioms CBCL.StateOpenerLocality.count_success_at_fault_cut

#print axioms CBCL.StateInstalledDomains.support_setEq
#print axioms CBCL.StateInstalledDomains.support_grows

#print axioms CBCL.StateDomainSupportLocality.contribution_supported
#print axioms CBCL.StateDomainSupportLocality.allowed_support_locality
#print axioms CBCL.StateDomainSupportLocality.healthy_contributor_cut
#print axioms CBCL.StateDomainSupportLocality.domain_allowed_cut
#print axioms CBCL.StateDomainSupportLocality.selected_cut
#print axioms CBCL.StateDomainSupportLocality.selected_grows
#print axioms CBCL.StateDomainSupportLocality.count_grows
#print axioms CBCL.StateDomainSupportLocality.count_success_at_cut

#print axioms CBCL.StateDomainSupportLocalityTests.initializer_contributes
#print axioms CBCL.StateDomainSupportLocalityTests.roster_root_contributes
#print axioms CBCL.StateDomainSupportLocalityTests.healthy
#print axioms CBCL.StateDomainSupportLocalityTests.mixed_domain_count_local
#print axioms CBCL.StateDomainSupportLocalityTests.branch_faults

#print axioms CBCL.StateFiniteFreezePolicy.state_cut
#print axioms CBCL.StateFiniteFreezePolicy.compiled_singleton
#print axioms CBCL.StateFiniteFreezePolicy.compiled_alternatives
#print axioms CBCL.StateFiniteFreezePolicy.find_unique
#print axioms CBCL.StateFiniteFreezePolicy.compiled_success_or_fault
#print axioms CBCL.StateFiniteFreezePolicy.output_success_or_fault

#print axioms CBCL.StateFiniteFreezePolicyTests.prior_reached
#print axioms CBCL.StateFiniteFreezePolicyTests.policy_checked
#print axioms CBCL.StateFiniteFreezePolicyTests.compiled_mixed_domain_stability
#print axioms CBCL.StateFiniteFreezePolicyTests.bypass_source_faults

#print axioms CBCL.StateFiniteFreezePolicyTests.normalized_source_clear
#print axioms CBCL.StateFiniteFreezePolicyTests.compiled_mixed_domain_reached

#print axioms CBCL.StateFiniteOutputStability.source_clear
#print axioms CBCL.StateFiniteOutputStability.non_top
#print axioms CBCL.StateFiniteOutputStability.scope_state
#print axioms CBCL.StateFiniteOutputStability.run_reached
#print axioms CBCL.StateFiniteOutputStability.output_success_or_fault
#print axioms CBCL.StateFiniteOutputStability.output_reached

#print axioms CBCL.StateFiniteOutputStabilityTests.waiting_root_absent
#print axioms CBCL.StateFiniteOutputStabilityTests.before_clear
#print axioms CBCL.StateFiniteOutputStabilityTests.unfrozen_output_reached
#print axioms CBCL.StateFiniteOutputStabilityTests.waiting_output_reached
#print axioms CBCL.StateFiniteOutputStabilityTests.concurrent_root_absent
#print axioms CBCL.StateFiniteOutputStabilityTests.concurrent_output_faults

#print axioms CBCL.StateFiniteOutputStability.installed_threshold_success_or_fault
#print axioms CBCL.StateFiniteOutputStabilityTests.installed_dictionary_output

#print axioms CBCL.StateAuthoredSourceProvenance.declaration_origin
#print axioms CBCL.StateAuthoredSourceProvenance.bindings_origin
#print axioms CBCL.StateAuthoredSourceProvenance.raw_names_sublist
#print axioms CBCL.StateAuthoredSourceProvenance.static_trace
#print axioms CBCL.StateAuthoredSourceProvenance.finite_binding
#print axioms CBCL.StateAuthoredSourceProvenance.prepared_finite_source
#print axioms CBCL.StateAuthoredSourceProvenance.mapM_origin
#print axioms CBCL.StateAuthoredSourceProvenance.freeze_origin
#print axioms CBCL.StateAuthoredSourceProvenance.prepared_raw_unique
#print axioms CBCL.StateAuthoredSourceProvenance.prepared_finite_freeze
#print axioms CBCL.StateAuthoredSourceProvenance.finite_factory_identity
#print axioms CBCL.StateAuthoredSourceProvenance.prepared_finite_metadata
#print axioms CBCL.StateAuthoredSourceProvenance.declaration_threshold
#print axioms CBCL.StateAuthoredSourceProvenance.authored_finite_source
#print axioms CBCL.StateAuthoredSourceProvenance.authored_finite_plan

#print axioms CBCL.StateAuthoredSourceProvenanceTests.installation_succeeds
#print axioms CBCL.StateAuthoredSourceProvenanceTests.supersede_rejected
#print axioms CBCL.StateAuthoredSourceProvenanceTests.complete_source_lookup

#print axioms CBCL.StateAuthoredOutputProvenance.extend_origins
#print axioms CBCL.StateAuthoredOutputProvenance.unique_definition
#print axioms CBCL.StateAuthoredOutputProvenance.emitted_origin
#print axioms CBCL.StateAuthoredOutputProvenance.decode_queries
#print axioms CBCL.StateAuthoredOutputProvenance.finite_emitted

#print axioms CBCL.StateAuthoredFiniteStability.freeze_spec_setEq
#print axioms CBCL.StateAuthoredFiniteStability.source_setEq
#print axioms CBCL.StateAuthoredFiniteStability.authored_program_stability

#print axioms CBCL.StateAuthoredFiniteStabilityTests.actual_authored_program
#print axioms CBCL.StateAuthoredFiniteStabilityTests.prefix_query_actually_reaches

#print axioms CBCL.StateCompiledFiniteInversion.compile_one_name
#print axioms CBCL.StateCompiledFiniteInversion.compiled_names
#print axioms CBCL.StateCompiledFiniteInversion.observed_names
#print axioms CBCL.StateCompiledFiniteInversion.raw_success
#print axioms CBCL.StateCompiledFiniteInversion.scope_inside
#print axioms CBCL.StateCompiledFiniteInversion.output_native_success
#print axioms CBCL.StateCompiledFiniteInversion.definition_tests

#print axioms CBCL.StateAuthoredFinitePreservation.authored_reached_native
#print axioms CBCL.StateAuthoredFinitePreservation.successive_compiled

#print axioms CBCL.StateAuthoredFinitePreservationTests.waiting_output_inverts
#print axioms CBCL.StateAuthoredFinitePreservationTests.constructed_successive_programs

#print axioms CBCL.StateAuthoredFinitePreservation.authored_output_names_unique
#print axioms CBCL.StateAuthoredFinitePreservation.quasi_determinism

#print axioms CBCL.StateNativeDataPolicies.selected_setEq
#print axioms CBCL.StateNativeDataPolicies.count_grows
#print axioms CBCL.StateNativeDataPolicies.canonical_count
#print axioms CBCL.StateNativeDataPolicies.admitted_nil
#print axioms CBCL.StateNativeDataPolicies.count_value
#print axioms CBCL.StateNativeDataPolicies.exists_value
#print axioms CBCL.StateNativeDataPolicies.compiled_count
#print axioms CBCL.StateNativeDataPolicies.compiled_exists

#print axioms CBCL.StateNativeDataFreeze.query_fault
#print axioms CBCL.StateNativeDataFreeze.selected_scope
#print axioms CBCL.StateNativeDataFreeze.count_success_or_fault
#print axioms CBCL.StateNativeDataFreeze.exists_success_or_fault

#print axioms CBCL.StateNativeDataPoliciesTests.duplicate_count
#print axioms CBCL.StateNativeDataPoliciesTests.duplicate_exists
#print axioms CBCL.StateNativeDataPoliciesTests.count_pending_payload
#print axioms CBCL.StateNativeDataPoliciesTests.exists_pending_payload
#print axioms CBCL.StateNativeDataPoliciesTests.oversized_count_rejected
#print axioms CBCL.StateNativeDataPoliciesTests.count_freeze_constructed

#print axioms CBCL.StateAuthoredDataProvenance.binding
#print axioms CBCL.StateAuthoredDataProvenance.lower_definition
#print axioms CBCL.StateAuthoredDataProvenance.prepared_source
#print axioms CBCL.StateAuthoredDataProvenance.prepared_footprint
#print axioms CBCL.StateAuthoredDataProvenance.prepared_metadata
#print axioms CBCL.StateAuthoredDataProvenance.authored_plan
#print axioms CBCL.StateAuthoredDataProvenance.emitted_policy

#print axioms CBCL.StateAuthoredDataOutputs.authored_emitted
#print axioms CBCL.StateAuthoredDataOutputs.spec_setEq
#print axioms CBCL.StateAuthoredDataOutputs.decorate_setEq
#print axioms CBCL.StateAuthoredDataOutputs.dispatch_member
#print axioms CBCL.StateAuthoredDataOutputs.count_program_stability
#print axioms CBCL.StateAuthoredDataOutputs.exists_program_stability

#print axioms CBCL.StateAuthoredDataPreservation.authored_reached
#print axioms CBCL.StateAuthoredDataPreservation.raw_inside
#print axioms CBCL.StateAuthoredDataPreservation.count_admitted
#print axioms CBCL.StateAuthoredDataPreservation.count_native
#print axioms CBCL.StateAuthoredDataPreservation.exists_native
#print axioms CBCL.StateAuthoredDataPreservation.count_successive
#print axioms CBCL.StateAuthoredDataPreservation.exists_successive

#print axioms CBCL.StateAuthoredDataPreservationTests.installation_succeeds
#print axioms CBCL.StateAuthoredDataPreservationTests.supersede_rejected
#print axioms CBCL.StateAuthoredDataPreservationTests.constructed_programs_preserve_both
