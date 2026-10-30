# Rust DAG independent review

Target: [[SPEC-030-rust-multi-parent-refinement]], the changed quorum runtime,
`MultiParentRustOracle.lean`, the shared fixture and production-API tests.
Fresh-context reviewer: `gpt-6-astra` agent `rust_dag_review`, separate from the
implementing coordinator, under the anuna-dev adversarial review requirement.
The reviewer did not edit source or assert coordination status.

## Findings resolved

- Lean tuple JSON initially encoded commands as nested pairs. Explicit flat JSON
  arrays now match the trace schema.
- The immutable Lean transaction catalogue permits abstract actions without Rust's
  candidate/source-metadata registration prerequisite. The checked API adapter
  now requires known source metadata for honest actions and held/credited inputs.
  It leaves Byzantine actions unrestricted and does not modify abstract `perform`.
- The correspondence contract now names source-metadata admission, signed-only
  release and durable retry stuttering. It distinguishes synchronized shared
  traces from delayed-delivery boundary tests.
- Requested boundary coverage includes same-rank siblings, delayed local proofs,
  zero-cost signatures and unsafe replay. Those tests now execute successfully.

The reviewer independently ran the multi-parent suite successfully. It exercises
real runtime methods, actual test signatures/QCs, per-step shared oracle comparison
and durable recovery, plus authorization/domain/rank/limit and delayed-evidence
boundaries. Deduplication, cancellation-assisted crowded joins and the old partial
renewal pattern were checked against actual production guards.

The reviewer inspected the mutation report: control passed; history, books, parent,
release, budget, domain and durability mutants fail actual test assertions.
The reviewer did not independently run those long mutation builds. Workspace,
no-std and Clippy outcomes are coordinator execution evidence.

Final scoped acceptance: no unresolved production-runtime safety finding. This is
tested transition correspondence, not universal Rust source equivalence.
Human domain review is required before production deployment; none is requested.

## Orientation comprehension

Fresh reader `rust_dag_orientation_final` received only the updated Orientation,
without tools/file access. It predicted a shared debit10 against genesis100 leaves
allocation90 after A/B joining; distinct debit IDs would leave80. It identified
active-parent and complete-history adoption, preserved journals, protocol isolation,
external signing and explicit non-universal proof scope. It named the correct
contract/projection/acceptance artefacts and found no material transmission defect.
