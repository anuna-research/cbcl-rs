import LeanCbcl.ConsensusFree.CollectiveProtocol
open CBCL.ConsensusFree.CollectiveActors
#print axioms execute_erases
#print axioms run_erases
#print axioms control_step
#print axioms admitted_run
#print axioms infinite_refinement
#print axioms cancel_quorum_has_original_request
#print axioms checkpoint_quorum_has_eligible_request
#print axioms operation_quorum_has_authorized_actor
#print axioms finality_has_authorized_actor
#print axioms minted_finality_checks_issuer
#print axioms declared_cap_bound
#print axioms declared_ceiling
#print axioms released_cannot_finalize
#print axioms receipt_run_mono
#print axioms honest_successor_choice_persists
#print axioms recover_control
