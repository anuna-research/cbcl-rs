# Cached checkpoint validation

SPEC-035-cached-state-checkpoints implements opt-in member-certified checkpoints
for all 16 native kernel rule heads. Runtime usage and exact wire formats are in
[the crate guide](../../crates/cbcl-checkpoint/README.md) and
[WIRE.md](../../crates/cbcl-checkpoint/WIRE.md). The all-head law and ordered native
clause bridge are in
[CheckpointAll.lean](../../lean-cbcl/LeanCbcl/CheckpointAll.lean).

## Recorded acceptance

Implementation commit `f1729a088c572a3ab6502980ee064a7f924a4447` passed the following local checks before
PR artifact cleanup. The workspace count included the subsequently removed
research-only prototype; it is a historical count, not the cleaned workspace's
current test inventory.

| Check | Recorded result |
|---|---|
| Rust workspace | 1,739 passed, 0 failed; 36 ignored |
| Strict workspace Clippy, formatting, no-std WASM | Passed |
| Lean library build and linter | Passed |
| Repository axiom audit | 423 theorem reports allowlisted |
| Critical all-head declarations | 41 audited; only standard Lean foundational axioms |
| Semantic Lean mutations | All 4 rejected inside proofs |
| Compiled runtime / summary mutations | All 17 / 8 caught by their tests |
| Rust/Lean all-head correspondence | 7,392 field comparisons across 231 prefix/cut records |
| Projection controls | 3 compiled/executed controls caused semantic divergence |
| Legacy collective/quorum policy correspondence | 20 prefix/cut records matched |
| Existing seven-head correspondence | 1,330 observations matched |

The 2,000-event selected-projection test recorded 10,296,890 signed-body bytes
versus a 184,942-byte summary (55.68x). It verifies native-fold equivalence and
restored-summary rendering. It excludes certificate, tail, frontier, coverage
proofs and retained archives; it is neither a drawing benchmark nor an end-to-end
latency result.

Local same-model reviews covered all-head proof composition, native progress
continuation, resource projections and the bounded correspondence bridge. They
reported no remaining actionable findings and disclosed dependency-authorship
overlap. They do not constitute human or independent security approval.

## Cleanup revalidation

After removing the prototype and generated artifacts, `cargo test --workspace
--locked` passed **1,692 tests** with zero failures and 36 ignored. Strict workspace
Clippy and formatting passed. The refactored proof checker passed all six
trust-zero baselines and rejected all four semantic mutations. Canonical wire
vector source hashes still match. Runtime code, formal theorem sources and
checkpoint test cases are unchanged by this cleanup.

## Reproduction

Run Rust checks from the repository root:

```sh
cargo test --workspace --locked
cargo clippy --workspace --all-targets --locked -- -D warnings
cargo fmt --all -- --check
cargo check -p cbcl-checkpoint --no-default-features --target wasm32-unknown-unknown --locked
cargo run -p cbcl-checkpoint --example cached_checkpoint
```

Build the pinned Lean library before running correspondence checks:

```sh
cd lean-cbcl
lake build LeanCbcl
lake exe runLinter LeanCbcl
cd ..
scripts/check-axioms.sh
python3 scripts/check-checkpoint-all16.py
```

Compile the external-tool oracle and run the explicitly ignored parity tests:

```sh
cd lean-cbcl
lake env lean -D linter.missingDocs=true -D warningAsError=true -o .lake/build/lib/lean/CheckpointAllRustOracle.olean CheckpointAllRustOracle.lean
cd ..
cargo test -p cbcl-checkpoint --test lean_all16_parity -- --ignored --nocapture
cargo test -p cbcl-checkpoint --test lean_checkpoint_parity -- --ignored --nocapture
```

Mutation and legacy resource-policy checks use the current compiled native graph:

```sh
cargo build -p cbcl-checkpoint --locked
python3 scripts/check-checkpoint-mutations.py
python3 crates/cbcl-checkpoint/src/summary_mutations.py
python3 scripts/check-checkpoint-resource-ports.py
```

Detailed JSON reports and raw logs are generated locally and gitignored. The
canonical [v2 wire vectors](../../test-vectors/checkpoints/v2-wire-vectors.json)
remain checked in for interoperability; the parity tests generate their own input
corpora rather than reading committed copies of their output.

## Acceptance scope

The Lean law covers the existing typed native kernel over accepted-ID-normalized
history. Wire extraction, clock/signer interpretation, cryptography and general
native resource classification/finalization remain explicit boundaries. The
7,392-comparison fixture uses one recognized repeat-chain mapping and an
independent bootstrap-account classifier. Separate policy-port checks preserve
the two constant legacy collective/quorum fault modes; none proves arbitrary
resource authority or general native-admission refinement.

Actual installed-dialect certificate/repeat-tail/durable-recovery tests live in
`all_heads_tests.rs`; the surrounding lifecycle, host, coverage, evidence, summary,
progress and resource tests preserve their native fold/admission oracles. The
runtime continues to retain original signed evidence.

Checkpointing defaults to `Off`. Events, protocol metadata and resource facts can
grow; resource graph verification is not constant-time. Domains and global
all-occupant fan-in remain separate unsupported features. The current certificate
still has a 4,096-head ceiling; resumable verification of arbitrarily wide
frontiers and `cbcl-bus` integration are follow-up work. Checkpoints do not grant
resource issuance or garbage-collection authority.
