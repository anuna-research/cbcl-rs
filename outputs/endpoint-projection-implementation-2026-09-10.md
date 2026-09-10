Endpoint projection recommendations — implemented 2026-09-10

Scope: follow-up to [[endpoint-projection-review-2026-09-10]]. The user authorized implementation of the review recommendations. The patch adds the missing finite-support temporal result and corrects theorem names and model-scope claims. It does not implement the separately identified concrete projection or authentication refinements.

Changes:

- `Bridge.FinitePredecessors` states finite citation support using a covering list, without requiring decidable message equality or a finite global store.
- `Bridge.Schedule.eventually_holds_list` combines exhaustion with append-only delivery and a maximum arrival time.
- `Bridge.eventually_present_valid` proves that a relevant message is eventually present and Valid at every later time, assuming a safe closed run and finite predecessor support.
- `Bridge.InfinitePredecessorsExample` gives a safe closed infinite run with finite delivery prefixes and a dependent message present but Unknown at every finite time. Its checked theorem demonstrates the missing finiteness condition cannot simply be omitted.
- The theorem names `projectability_iff_local_verifiability`, `causal_locality_necessary`, and `weakest_sound_condition` become `projectability_sufficiency_and_counterexample`, `nonlocal_protocol_counterexample`, and `decidesAll_iff_predsLocal`. Active references and the axiom audit are updated. These are Lean API renames, without compatibility aliases; historical review text records the old names explicitly.
- EPP, protocol agreement, and splicing prose now distinguishes abstract statements from concrete clause projection, cryptographic authentication, and optimal communication claims. README, manuscript, and related specifications carry the same qualifications.
- [[../specs/SPEC-016-splicing-boundary]] version 0.2.0 preserves the static routing policy but distinguishes it from necessity for realized citations. [[../specs/SPEC-017-typed-content-addresses]] version 0.1.1 separates abstract injectivity from concrete Merkle refinement.

Validation:

- `lake build`: passed, 77 jobs; output `/private/tmp/epp-build-final.log`.
- `lake exe runLinter LeanCbcl`: passed.
- `scripts/check-axioms.sh`: passed, 52 audited theorems. The new temporal theorem and infinite-predecessor counterexample use only standard Lean axioms; `always_unknown` has no axiom dependencies.
- `scripts/check-verified-by.sh`: passed.
- `git diff --check`: passed.
- A source comparison removing comments and whitespace verified that EPP, Projectability, ProtocolProjection, and Splice proof statements and terms are unchanged modulo the declared renames.
- Fresh-context reviewer `/root/review_epp_amendment` first read only the revised Orientation and correctly predicted bare-hash rejection and the outstanding authentication boundary. The subsequent adversarial review found no invalid Lean proof or weakened theorem. Its static-route necessity and residual documentation findings were corrected and the reviewer confirmed resolution.
- `zetl check --dead-links --fail-on error`: fails on existing vault debt. A comparison with the pre-change specification snapshot found no new unresolved source/target pairs after resolving the new endpoint-projection reference to the existing role-layer specification. Evidence: `/private/tmp/epp-vault-baseline.json` and `/private/tmp/epp-vault-current.json`. Remaining vault-link maintenance belongs to the specification maintainers.

Remaining model boundaries: concrete erasure/splice agreement, branch/cast/seal obligation construction, authenticated-opening interpretation, and a refinement to deployed eager verifier semantics are still separate proof obligations. They are now explicitly described as such. No Rust behavior changed.
