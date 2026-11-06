# State-kernel correctness verification

Implements [[SPEC-036-state-kernel-correctness]] through
[[IMPL-023-state-kernel-correctness]]. Worktree branch:
`draft/state-register-semantics`, building on implementation commit `3cd7b65`.
Date: 2026-11-06. Steward: Codex `/root`.

## Established result

`StateKernelClause.well_formed_kernel_correct` quantifies over every finite typed
clause satisfying independent backward-reference/domain well-formedness and unique
field names, and every accepted history with unique addresses. It establishes
successful elaboration and the independently specified ordered clause observations.
`compile_clause_complete` rules out rejection of all inputs as a vacuous proof.
`whole_kernel_correct` also establishes meaning for every successful compilation.

All 19 runtime rule heads have typed constructors, independent surface meanings
and lowering cases. Two multi-value aliases normalize before that AST. The coverage
script checks this inventory against Rust names; this is not semantic equivalence.
Derived histogram/sum sources match R7's primitive-map inventory. They cannot read
a preceding histogram. Maps distinguish key support from payload presence; events
omit missing payloads, histograms skip absence, and sums unwrap event values.

Component results independently specify raw-opener domains, replacement evidence,
maximal choice, finite enumeration, exact cardinality/sums, map support and reads.
Map and multi-value-map completeness use extensional equality. Independent numeric
cell graphs prevent a constant-zero implementation from redefining the sum spec.
Progress composes `Repeat.At` resolver soundness and completeness using raw evidence.

Resource adapter results are explicitly relative to supplied typed verifier outcomes.
They compute ready budgets and retain pending/fault tags without numeric balances.
They do not establish classification, dependency-DAG validation, allocation validity,
or certified-history finalization. Ceiling arithmetic retains the allocation equation
as an explicit premise. Parsing, installation recognition, clock honesty, rendering,
Rust correspondence, universal business refinement and liveness are outside this result.

## Executed verification

- `cd lean-cbcl && lake build`: passed, 127 jobs including regression examples.
- `cd lean-cbcl && lake exe runLinter LeanCbcl`: passed.
- `scripts/check-axioms.sh`: passed, 362 audited theorems. New theorem dependencies
  use only standard Lean axioms; no new custom axioms or `sorry` introduced.
- `python3 scripts/check-state-kernel.py --output proofs/state-kernel/mutations.json`:
  checks 19 heads and two aliases, baseline compilation, then isolated mutations.
  Full diagnostics are archived in `mutations.json`.
- Regression examples cover domain-excluded replacers, lower-address observed edits,
  two signer groups and aggregate values, missing map/event payloads, event numeric
  projection, nonnumeric pending/fault tags, duplicate field rejection, bad domain
  initializers, forward/incompatible references and aliases.
- `git diff --check`: passed.

Mutation failures must include proof/type/tactic diagnostics, with no missing-module,
file, or parser errors. A changed selector can produce follow-on local tactic binder
errors; these are recorded alongside the unsatisfied semantic goals. Mutants compile
from temporary files and never overwrite the working tree or shared compiled modules.

## Independent review

Reviewer `/root/whole_kernel_spec_review` read all new modules, SPEC-036 and relevant
Rust evaluation/R7 restrictions. Initial findings and repairs:

1. Added independent well-formed-clause acceptance completeness and unique names.
2. Made exact support, missing payloads and event projection explicit.
3. Added independently enumerated surface meanings and full head inventory.
4. Replaced shared numeric sum projection with `CellNumberMeaning` plus correctness.
5. Added `ValueMapEquivalent` and `values_by_complete`.
6. Clarified sibling histogram/sum references. Runtime R7 rejects sum(histogram).
7. Retained the delegated resource-verifier classification boundary.

The reviewer initially questioned event sums, then checked Rust `Value::as_int` and
withdrew that finding: it recursively unwraps pairs. Read-only re-review reported
no remaining design blockers, conditional on passing checks.

Reviewer `/root/hlc_orientation_check` read only SPEC-036 Orientation and recovered
the deliverable, named failure, six controls and all material boundaries. It noted
that “whole kernel” requires the stated typed-model/resource-port qualification.
These are independent tool sessions under one steward, not distinct cryptographic
Elephant peer identities. Reviews performed no edits or builds.

## Planning and repository checks

Elephant theory `spec-036`:
`6992feb382ca028722376ef69c028cd526fcda05debf0e9c56d978b154d8d71b`.
The theory records component, composition and verification task completion.
The local store is ephemeral; this plan and evidence preserve the durable outcome.

`NO_COLOR=true zetl check` retains the pre-existing 23 dead links and three SPL
errors from older plans. No new dead link or SPL error originates in this work.
The installed checker does not validate wikilink anchors; new requirement/test
anchors and paths were checked directly. Runtime code is unchanged, so the prior
Rust/WASM validation remains separate evidence rather than a new Rust proof.
