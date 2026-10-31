# One quorum-budget DAG runtime

Contract: [[SPEC-031-unified-quorum-dag]]. User authorization removes compatibility
for the former single-parent checkpoint handoff. `(certification quorum-budget ...)`
now always denotes multi-parent DAG adoption, for both ownership modes.
`Context::from_instance` is the sole constructor. Hosts supply cryptography,
transport and durable storage rather than selecting a handoff protocol.

## Changes

Removed the host Handoff enum/selector, alternate constructor, legacy Manifest,
Proposal, Checkpoint and SealReport types, seal/checkpoint vote kinds, serialized
legacy events, sealed journals, successor choices and their APIs. The DAG manifest
is the direct internal resource representation. `Limits::versions` bounds retained
DAG versions. Legacy serialized variants reject as unknown; old logs are not
migrated or reinterpreted.

Account and collective execution share DAG receipt/adoption, independent local
budgets, QCs and atomic journal replay. Account parents and held operations must
match the resource account. Incoming credits may come from another account only
when an actual effects QC targets this account. Adoption checks complete historical
signatures originating in the target account. Other accounts' signatures do not
block it, and no journals are cleared. `version_snapshot(account)` projects each
scope. Collective actors all resolve to the same pool scope.

The API reference, bounded-counter concept page, module and root READMEs now
present a single language-selected DAG protocol. SPEC-030 is marked superseded;
earlier runtime specifications direct current handoff readers to SPEC-031.
Historical single-parent Lean/Python research models remain evidence and reusable
arithmetic, not runtime compatibility paths.

## Executed validation

```sh
CARGO_PROFILE_TEST_DEBUG=0 CARGO_INCREMENTAL=0 CARGO_BUILD_JOBS=4 cargo test --workspace
cargo check -p cbcl-core --no-default-features
python3 proofs/validator-budget/check_rust_multi_parent.py
python3 proofs/validator-budget/check_rust_multi_parent_mutations.py
CARGO_PROFILE_DEV_DEBUG=0 CARGO_INCREMENTAL=0 cargo clippy -p cbcl-core -p cbcl-parser --all-targets --message-format=json
```

All workspace tests and no-std pass. The existing collective shared oracle still
matches runtime execution/recovery. Scoped Clippy reports no primary diagnostics
in modified runtime/test files; unrelated baseline warnings remain. Formatting and
diff checks pass. Source search confirms removed protocol APIs/types are absent
from the runtime. Legacy names appear only in explicit deserialization rejections
or historical evidence.

Account execution covers ordinary and headroom transfers, incoming credit reuse,
independent per-account histories, foreign parent/debit and wrong-actor rejection,
real A/B branch joining with shared incoming credits counted once, new joined
spending followed by an old transfer QC, cancellation/refund and durable recovery.
Collective tests retain shared budgets, optional ceiling, zero-cost signatures,
late certificates, refund-backed crowded joining and unsafe partial-renewal refusal.

Mutations run in an isolated archived checkout with unique Cargo target directories
removed after each case. Control passes. Parent scope, held scope, global-vs-scoped
history, history omission, books, direct parenthood, release certificate, scaled
budget, context domain and durable append mutants fail actual test assertions.
Compiler/import failures cannot satisfy the checker. The new scope rejection cases
isolate the intended guard rather than failing on authorization or books first.

Independent review accepted source, actual account tests, mutation outcomes and
revised docs: [[unified-quorum-review]]. Measured command output is retained in
`outputs/unified-quorum-*.log/json`.

## Scope

The existing Lean numeric model and checked oracle cover the collective pool.
This change does not manufacture a new formal account-DAG refinement theorem.
Account safety has concrete transfer/isolation/late-certificate execution evidence
and independent adversarial review; the account formal extension remains owned by
the coordinator. Universal Rust source equivalence via an extraction toolchain is
also separate work. Cryptographic authentication and physical nonforking durable
journals remain host assumptions. Progress under contention, old-log migration and
production deployment are not supplied.

The specs-only vault still has existing dead links and evidence references outside
its scan root. Those remain a coordinator-owned vault integration backlog; no
clean-vault or strict-global-lint claim is made.
