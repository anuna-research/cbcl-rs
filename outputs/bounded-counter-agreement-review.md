---
title: Bounded-counter agreement comparison evidence
mode: explanation
---

# Agreement comparison evidence

Decision and next actor: [[SPEC-020-resource-certification#ADR-2001]] selects an
invariant-aware account-local model as the prerequisite to richer-profile runtime.
The CBCL maintainer owns [[SPEC-020-resource-certification#TEST-2006]].
No certification runtime, grammar, library API or dependency changed in this work.
The fixed-slot draft API is a candidate, not an implemented export.

`python3 proofs/bounded-counter-certification/compare_agreement.py` reproduces
`outputs/bounded-counter-agreement-comparison.json`. Its finite assertions cover
non-join-closed rights and headroom, three-way contention, individual-signature
quorum insufficiency, monotonic whole-set signatures, receipt retraction by hash
filtering, both budget dimensions and unfunded net-zero cycles. The whole-set
example assumes fixed capacity and limited signature histories; it does not model
incoming funding, COD, Byzantine reliable broadcast, recovery or asynchronous progress.

`cargo test -p cbcl-parser --test bounded_counter funding_evidence_pending_replay_and_forks`
passes; the command output is `outputs/bounded-counter-agreement-runtime-check.log`.
The test constructs different individually valid treasury payments from the same
opener. Their sum fits the treasury allocation, but the combined history reports
`owner fork`. This corroborates the stated implementation compatibility boundary.

The original quorum research harness also runs unchanged. The comparison makes no
new claim about deployed fault tolerance or model/runtime correspondence.

Independent comprehension and adversarial review results follow. Human security review remains a release requirement; this comparison is
not a deployed payment protocol assessment.


## Independent review

The fresh-context orientation-only reader `agreement_orientation_v3` correctly
predicted the overspending evidence example, current compatible-sibling rejection,
the competing compatible-set and validator-budget designs, and the [[SPEC-020-resource-certification#TEST-2006]] gate.
It received only the Orientation text and used no tools or other artefacts.
An earlier full reviewer disclosed accidentally reading beyond the Orientation;
that reading is not counted as a blinded comprehension gate.

Cross-model reviewer `agreement_design_review` inspected the full specification,
finite models, current fork semantics and primary papers. It identified missing
owner-independent next-epoch notarization, a mistaken universal unique-version
rule, imprecise update-certificate wording and missing effects-finality evidence.
The specification now scopes notarization to COD, preserves Stingray's divergent
version merges, describes owner-signed updates referencing certified operations,
and requires candidate-specific finality and recovery-race cases. Follow-up review
verified those fixes with no substantive blocker; its final wording correction is
also applied. This validates the design comparison's scope, not a runtime protocol.

## Additional literature checks

`python3 proofs/bounded-counter-certification/check_signing_budgets.py` reproduces
`outputs/bounded-counter-signing-budget-checks.json`. The safe budget guard was
mutated in an isolated temporary copy to give each witness the full balance. The
run exited with an assertion failure on the safety property, as recorded in
`outputs/bounded-counter-signing-budget-mutation.log`. The working model was not
modified by this mutation. Independent review also reproduced the failure.

[[byzantine-resource-literature]] records findings and distinguishes source results
from CBCL inferences. `outputs/resource-literature/crawl-manifest.json` records
ar-crawl source provenance and local raw evidence paths. Elephant theory
`spec-020-resource-agreement` stores sourced comparison, literature and next-model
work; the prior runtime promise was retracted after the user redirected to this
comparison. No runtime task is reported completed by this research evidence.

The descriptive literature prose checker reports no errors or warnings in
`outputs/resource-literature/prose-lint.json`. Repository target/named-anchor
recognition for the new comparison artefacts passes in
`outputs/resource-literature/traceability-check.json`. The zetl check succeeds at
its error threshold but reports unresolved links across the existing vault
boundaries; its complete report remains in `outputs/resource-literature/vault-check.json`.
This is not represented as a link-clean vault.

Elephant's derived next task is `agreement-model`, sourced from
[[SPEC-020-resource-certification#TEST-2006]]. The completed comparison/literature
premises, provenance, fulfilled commitments and closure fingerprint are exported
under `outputs/resource-literature/elephant-*`. Model completion remains unclaimed.
