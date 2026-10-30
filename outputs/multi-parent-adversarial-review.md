# Multi-parent independent adversarial review

Review target: [[SPEC-029-multi-parent-counter-model]], its Lean numeric protocol,
and the executable audit and isolated mutation harness. Reviewer: fresh-context
`gpt-6-astra` agent `multi_parent_adversarial`, separate from the implementing
coordinator. The reviewer ran the Lean audit and mutation checker independently.
This records that review; it does not attribute Elephant assertions to the reviewer.

## Findings and resolutions

- The specification omitted the disjoint debit/credit restriction required by
  funded refinement. The contract now states `Config.disjoint` explicitly.
- Infinite refinement is over infinite steps in one fixed finite catalogue. The
  contract now excludes an unbounded fresh-identifier extension theorem.
- The interpreter uses proof-only honest membership and aggregate certificate
  evidence. The contract now describes it as a safety overapproximation of packet
  delivery, with no claim of executable Rust/network equivalence.
- An overspending rejection originally failed on the active-version check. The
  corrected test first demonstrates successful adoption of a valid merge, then
  attempts scaled charge 240 against local allowance 200. Removing the budget
  guard now fails the executable assertion.

Final reviewer conclusion: accepted within the documented model scope; no
remaining material defects or hidden consensus assumption found. The numeric proof
preserves invariants from local guards and derives ancestry, late-certificate
coverage, nonnegative resources and funded refinement. The maximal finalized
version is used only in the proof. Genuine A/B joining and cancellation-assisted
joining execute. Progress remains conditional.

The independent rerun confirmed that unmodified executable control passes and
weakened history, books, direct-parent, cancellation-release and budget guards fail
real `decide` assertions. Measured outputs are [[multi-parent-mutations]].
No source files or coordination status were edited by the reviewer.

Packet-level refinement, Rust integration, growing-catalogue refinement and
production domain review remain outside this acceptance.
