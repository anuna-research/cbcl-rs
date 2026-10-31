# Rust multi-parent implementation and correspondence

Contract: [[SPEC-030-rust-multi-parent-refinement]]. Abstract protocol:
[[SPEC-029-multi-parent-counter-model]]. The Rust collective DAG implementation is
opt-in through `Context::from_instance_multi_parent`; existing contexts retain
single-parent behavior. No consensus is introduced. Transaction and metadata
signing remain external host responsibilities.

## Runtime and interface

`cbcl_core::quorum` now supplies `Handoff`, `VersionManifest`, `DagVersion` and
`VersionSnapshot`. `Replica::draft_version` recomputes cumulative unique-ID books;
`receive_version` validates actual actor authorization, parent/rank structure,
inherited sets and refund/credit QCs. `adopt_version` requires the active direct
parent and every historical signature ID, including released and zero-cost IDs.
`version` and `version_snapshot` expose retained relay/projection data.

The new context domain isolates roots, signatures and journal namespaces from
legacy checkpoint execution. Opposite-mode events reject during ordinary execution
and recovery. Seals, checkpoint votes and one-successor choices are not used by
DAG adoption. Tentative apply, atomic compare-and-append, rollback on failure and
replay use the existing implementation. Evidence never resets across adoption.

```text
    collective runtime                 Lean numeric model
    ------------------                 ------------------
    authenticated candidates     -->   immutable bound catalogue (stutter)
    verified version receipt     -->   record
    local DAG adoption           -->   adopt
    durable reservation vote     -->   sign
    durable effects vote         -->   effect
    authenticated cancel fence   -->   fence
    cancellation-backed release  -->   release
    existing durable retries     -->   replay/stutter
```

Version rank is a well-founded label. Parents and held source epochs have lower
rank; siblings can share rank. Finite `(rank, semantic-ID)` ordering gives a
compatible Lean topological naming. This correspondence is documented and tested
with equal-rank siblings, not proved as a Rust-source extraction theorem.

## Checked reference and shared executions

`lean-cbcl/MultiParentRustOracle.lean` proves `apiPerform_sound`, `oracle_run` and
`oracle_safe`. Every accepted API-adapted command generates an abstract step, and
arbitrary adapted scripts preserve the proved resource safety invariant. The
adapter explicitly adds source-metadata registration for honest commands and
held/credited inputs, requires an own signature for release, and treats previously
durable signing/adoption retries as stuttering. It does not weaken abstract guards.
Byzantine test participant actions remain unrestricted; the Rust validator does
not gain a Byzantine bypass.

The shared fixture is `test-vectors/quorum/multi-parent-lean.json`. The checker
regenerates it with the actual Lean interpreter and compares structural JSON.
The Rust test invokes production context/act/authentication/journal APIs, compares
admission and all projected fields after each command, then recovers every honest
validator and compares recovered state and finalized views. Model Byzantine votes
are emitted by an adversarial external test signer, not an honest Replica API.

Shared schedules synchronize metadata and deliver QCs at formation. Independent
Rust tests delay operation and effects QCs and verify refusal until local receipt,
including refusal of a credit-importing version. Thus shared equality is not
mistaken for complete network equivalence or global client knowledge.

## Validation

Executed from repository root:

```sh
python3 proofs/validator-budget/check_rust_multi_parent.py
CARGO_PROFILE_TEST_DEBUG=0 CARGO_INCREMENTAL=0 CARGO_BUILD_JOBS=4 cargo test --workspace
cargo check -p cbcl-core --no-default-features
python3 proofs/validator-budget/check_rust_multi_parent_mutations.py
CARGO_PROFILE_DEV_DEBUG=0 CARGO_INCREMENTAL=0 cargo clippy -p cbcl-core -p cbcl-parser --all-targets --message-format=json
```

Executed from `lean-cbcl`:

```sh
lake build
lake env lean MultiParentRustOracle.lean
```

Workspace tests, no-std, reference regeneration, Lean kernel checks and all mutation
expectations pass. Clippy exits successfully in diagnostic mode and reports no
primary findings in changed runtime/test files. Strict `-D warnings` remains red
in unchanged baseline modules; those diagnostics were retained rather than fixed
outside scope. Formatting/diff checks pass.

The runtime suite covers actual branch joining/spending, late certificates,
shared debit/credit deduplication, crowded joins requiring cancellation, optional
ceiling resources, zero-cost historical mint signatures and the partial-renewal
counterexample after real reservation quorums. It checks authentication, payload
binding, protocol domains, missing metadata, rank/inheritance/books, local budget,
limits/rank overflow, append failure/CAS, retry stability and unsafe recovery.

Production source guard mutants run in a temporary archived checkout, with
separate Cargo target directories. Control passes; weakening history, books,
direct-parent, cancellation release, scaled budget, domain isolation or durable
append causes actual running test assertions to fail. Compilation errors do not
count as kills. Scratch target removal and disabled debug/incremental output keep
disk use bounded. The initial disk-full attempt was discarded and retried.
The fixture was moved out of the state-fold corpus after its different schema
exposed an integration failure; the final workspace run uses the dedicated path.

Independent review and Orientation comprehension accepted this scope:
[[rust-multi-parent-review]]. Measured commands, trace totals, test outcomes and
mutation details are retained in the retained mutation/scoped-check JSON summaries.

## Claim boundaries

There is no universal theorem equating the compiled Rust source to Lean. The
formal theorem is for the checked reference adapter; actual Rust correspondence
is differential and adversarial execution evidence. Rust adds authenticated
candidate admission, positive CBCL amounts, bounded machine integers, object/log
limits and local proof receipt. Those restrictions reject outside the supported
projection rather than silently granting capacity.

The proof remains a finite-catalogue safety result with disjoint per-coordinate
cost/credit. It does not establish an unbounded fresh-ID extension, guaranteed
progress, complete/latest balance queries, parser/crypto correctness or physical
journal durability. DAG account transfers and journal migration are unsupported.
Human domain/security review remains a production-release gate.

The specs-only vault scan still has unrelated dead links and output-page references
outside its root. Vault integration is coordinator-owned backlog; no clean-vault or
strict-global-lint claim is made. The existing default API is retained to avoid
silently changing live protocol identities.

Raw diagnostic transcripts are archived as described in this directory's README;
reproduction commands and concise outcome records remain versioned.
