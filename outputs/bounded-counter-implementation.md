---
title: Bounded counter implementation evidence
mode: reference
---

# Bounded counter implementation evidence

Scope: [[SPEC-019-state-rules#CON-1908]] and [[SPEC-019-state-rules#CON-1909]].
The runtime implementation supports lower bounds, optional ceilings, account
rights and headroom transfers, empty issuance authority, and tagged observations.
It preserves protocol admission as a separate stage.

## Implementation plan

The executable plan is `plans/IMPL-021-bounded-counter.spl`, imported into local
Elephant theory `spec-019-bounded-counter`. The local steward records independent
review sessions as evidence; those sessions are not distinct P2P signers.
The grammar task precedes runtime integration, which precedes evidence review.
Their acceptance traces to [[SPEC-019-state-rules#TEST-1960]] through
[[SPEC-019-state-rules#TEST-1969]]. Optional ceiling work follows the user's
explicit amendment during implementation.

The next depth tasks remain owned by the CBCL maintainer: prove resource-DAG
compatible-union safety and Rust/model correspondence, and run a process-crash
host adapter rig. They are not implied complete by passing pure-core tests.

## Runtime surface

- Grammar recognition, role/shape installation checks, canonical dialect identity,
  structured initializer allocations, and compiler-owned resource references.
- Pure resource-DAG verification with account chains, fork faults, missing-evidence
  pending results, per-account rights and optional headroom budgets.
- Context-pinned `fold_instance` and binding exports. The lower-level `observe`
  retains the premise of authenticated, accepted, already pinned input history.
- `intend` bookkeeping and advisory resource checks; `issue` requires an explicit
  `IssuanceGate` that persists the complete candidate using one shared account lane.
- Shared `resource-check` exports for parser, WASM, C FFI, and Erlang. The JSON
  authoring compiler accepts `boundedCounter` with canonical option arrays.
- Lower-only and capped example dialects and corpus vectors under suite version 2.0.0.

The verifier uses a Kahn traversal and per-owner causal frontiers with cumulative
transfer totals. Installed profiles bound accounts and dependency lists by
`max-list`; summaries do not materialize quadratic ancestor sets.

## Verification commands

| Check | Command | Evidence |
|---|---|---|
| Workspace tests | `cargo test --workspace` | `outputs/bounded-counter-rust-tests.log` |
| no_std | `cargo check -p cbcl-core -p cbcl-parser --no-default-features` | `outputs/bounded-counter-no-std.log` |
| Clippy | `cargo clippy --workspace --all-targets` | `outputs/bounded-counter-clippy.log` |
| Lean build | `lake build` in `lean-cbcl` | `outputs/bounded-counter-lean-build.log` |
| Lean linter | `lake exe runLinter LeanCbcl` | `outputs/bounded-counter-lean-lint.log` |
| Arithmetic/axioms | `lean LeanCbcl/BoundedCounter.lean` under pinned toolchain | `outputs/bounded-counter-model.log` |
| Budget mutation | Remove the local budget guard and run the lower/headroom causal-evidence cases | `outputs/bounded-counter-mutations.log` and corresponding mutation logs |
| Erlang loader | `erlc -o /private/tmp crates/cbcl-erl/erlang/cbcl_erl.erl` | Successful compiler exit |
| Vault | `NO_COLOR=true zetl -d . check --dead-links --fail-on error` | `outputs/bounded-counter-vault.json` |

Workspace tests, no_std, Clippy compilation, Lean build/linter, Erlang loader
compilation, and whitespace checks pass. Clippy still reports existing repository
warnings; warnings-as-errors is not a clean repository gate. New large-variant,
parser item-order, and needless-borrow findings were corrected.
The vault retains unresolved pre-existing references, so its global gate does
not pass. New implementation references resolve.

The integration tests cover the worked coin arithmetic, budget refusals, exact
replay, out-of-order funding, observed forks, canonical binding, conflicting root
casts, foreign dialect/thread histories, fixed supply, dual-budget operations,
and randomized comparison with an independent arithmetic machine.
The existing admission-stratification twin generator now changes the counter
floor and ceiling together, preserving its message footprint while changing its
observation. This tests that protocol admission still ignores arithmetic state.

The binding tests use the same checked-in lower/capped resource-check frames and
compare each wrapper to the shared parser implementation. The corpus runner
checks forward, reverse and duplicate delivery against fixed expected balances.
The corpus authoring test is ignored by default and was run explicitly to write
canonical message/hash fixtures; arithmetic expectations are separately stated constants.

Removing the local budget guard makes both causal-evidence tests fail while they
actually execute: locally visible funding/headroom cannot replace evidence in an
operation's own resource history. The source is restored exactly after mutation.

## Independent review

Fresh-context reviewer `escrow_contract_review` checked the orientation, wire
contract, optional ceiling model, and the standalone Lean proofs. Review found
and implementation corrected the canonical option order, empty issuance contract,
reserved-field rules, sorted dependency requirement, and status/claim boundaries.

Fresh-context reviewer `escrow_code_review` found foreign-instance histories and
conflicting cast wrappers were insufficiently checked. Context-pinned entrypoints
and explicit conflicting-cast detection now reject those cases, with regression tests.
Re-review found no remaining concrete defect. The reviewer separately inspected
the summary-based traversal and found no missed transfer or forged-frontier path
under the enforced nonforking account-chain conditions.

## Claim boundary and remaining depth

The Lean model proves guarded local arithmetic conservation and floor/ceiling
bounds from nonnegative budgets and the capacity allocation equation.
Its reported axioms are standard Lean axioms; no `sorry` or custom axiom occurs.
The existing Lean state-rule datatype still models the ordinary rules; the new
wire recognizer is exercised by Rust grammar and corpus tests.
It does not establish resource-DAG merge safety, Rust correspondence, deployed
signature correctness, or durable host correctness.

The file-backed test gate exercises racing account writers and reopening a
persisted complete candidate. It does not simulate every process-crash point or
prove exactly-once external effects. Production hosts supply durable shared
serialization, authentication, protocol admission, missing-evidence retrieval,
and idempotent effect sinks. A self-asserted signed wrapper supplies none of those.
A ready result cannot exclude an undisclosed remote fork.


## Certification investigation

The follow-up research at [[SPEC-019-state-rules#ADR-1915]] compares AT2, Astro,
source/account-ordered secure broadcast, VRF eligibility, and Pastro with the existing runtime.
No runtime or accepted grammar change accompanies that investigation.
The proposed profile keeps raw evidence, certified delivery and application
finalization distinct. It requires complete certified dependency closures before
reusing the resource verifier or exposing spendable state.

Run `python3 proofs/bounded-counter-certification/check_quorums.py` to reproduce
`outputs/bounded-counter-certification-checks.json`. Replay matches the saved JSON.
The harness enumerates small static-roster quorum intersections and constructs
negative examples for threshold, persistence, slot binding, and roster changes.
Signer labels represent authenticated keys; no cryptography, ledger or network
implementation is provided by this harness.
The existing raw-fork behavior was rerun with the named integration test;
`outputs/bounded-counter-certification-existing-fork.log` records its passing result.

Fresh-context cross-model reviewer `certification_research_review` first read
only the research orientation, then reviewed the full investigation, finite
harness, source papers and relevant runtime interfaces. The orientation correctly
transmitted the honest-quorum safety premise and the absence of malicious-source
progress guarantees. Full review reported no substantive blocker to the research
prototype. The suggested acceptance extension—merging independently finalized
histories while preserving bounds and final receipts—is included in the note.
Human security review, protocol proofs and production implementation remain
future work; this review does not certify a deployed payment protocol.

Follow-up independent review found no substantive defects in the Astro and VRF
comparison. The extracted research prose lint reports zero errors and two sentence
length warnings. `git diff --check` passes.
