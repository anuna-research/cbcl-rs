# Availability investigation independent review

Research: [[counter-availability-investigation]]. Review performed by `/root/counter_liveness_review` in fresh context with a different model, under anuna-dev's adversarial-review requirement. Source read and Lean kernel checks only; no edits, installations or theory membership changes by reviewer.

Both current-model audits passed independent kernel checks. Reviewer found no proof defect and required precise limits: residual initial-unit instance is not a spend-down trace; finite static DAG and fixed catalogue; target-action fairness is not arbitrary global scheduling fairness; cancellation authorization is an ideal boolean policy, not a concrete caller/packet history; cancellation witness has no future versions and does not prove all recovery extensions impossible.

Literature review confirmed the honest-owner envelope and residual conversion in Stingray, large-request Error branch, FastPay sender sequence discipline, Astro representative correctness premise, CryptoConcurrency all-correct-account assumption and consensus-backed recovery. No paper was credited with the unproved CBCL dual-resource conversion.

Report review required freezing owner issuance BEFORE draining a finite submitted set, and fair selection so new small requests cannot starve an outside-envelope request. Applied. Clarifications also applied: reserve accepted request funding in both coordinates and do not assume the existence of target/handoff/cancellation certificates in the evidence-delivery premise.

The proposed continuation remains explicitly unimplemented and unproved. Approval of this investigation does not approve a production protocol change, certify arbitrary shared-pool recovery, or establish Rust/network equivalence.

Final follow-up: reviewer approved the revised research report and model-specific counterexamples, confirmed source hashes and negative-control failures, and reported no remaining blocking findings. The proposed continuation protocol is not covered by that approval.
