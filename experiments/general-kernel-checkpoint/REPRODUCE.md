# Reproduce the governed experiment

Use a separate worktree. The nested Cargo workspace intentionally does not change
the production workspace. Pin RISC Zero SDK/cargo-risczero/r0vm to 3.0.6 and the
RISC Zero Rust toolchain to the recorded 1.97.0. `cargo build` embeds the guest;
its image changes when kernel/wrapper source or dependencies change. Lockfiles
are retained for both workspaces. Tooling installation details are in environment
metadata; no shell profile was modified. Install/download/build costs are not
proof-call times. Do not rerun over retained evidence without backing it up.

From this directory, fixture generation uses a read-only sibling cbcl-bus:

```sh
node make-fixtures.mjs
cargo run --release -p checkpoint-common --example canonicalize_fixtures
cargo run --release -p checkpoint-common --example make_native
cargo run --release -p checkpoint-common --example make_role
python3 make-ancestor-fixture.py
cargo test --release -p checkpoint-common
python3 run-managed.py host-build cargo build --release -p checkpoint-host
python3 run-managed.py execution-matrix python3 run-execution-matrix.py
target/release/checkpoint-host native fixtures/drawing-1.json evidence/independent-drawing-1
python3 run-managed.py prove-drawing-1 target/release/checkpoint-host prove fixtures/drawing-1.json evidence/proved-drawing-1-tuned
python3 run-managed.py compress-drawing-1 target/release/checkpoint-host compress evidence/proved-drawing-1-tuned/receipt.bin evidence/succinct-drawing-1
python3 run-managed.py standalone-verification target/release/checkpoint-host verify evidence/succinct-drawing-1/receipt.bin evidence/independent-drawing-1/expected.json evidence/independent-drawing-1/state.json
python3 run-managed.py negative-guest target/release/guest-negative
python3 verify-negative.py
python3 mutation-check.py
```

The first recorded proof used segment exponent 16. Subsequent runs default to 18;
set CBCL_SEGMENT_PO2 explicitly (16..20 accepted) to reproduce the segmentation.
The guest program image is independent of this executor setting. Compare recorded
image IDs before combining evidence. `run-managed.py` forces real IPC proving,
disables dev mode and sets one Cargo worker and a bounded Rayon pool (initial1, tuned4), recording sampled aggregate
process-tree RSS. Short-lived spikes between two-second samples can be missed;
recorded peak is observed, not an OS-enforced memory limit. The time/disk envelope
is conservative and includes setup/review. Paid remote proving is not configured.

A native expected journal is deliberately captured before proof generation and
used from a separate path during verification. For a real deployment, a client
must authenticate the expected program/dialect/thread/message-set commitment
independently. A provider's self-declared expected.json is insufficient. The
snapshot is current native fold output, not a resumable admission checkpoint.

Jolt/SP1/Nexus findings are documented separately in
[[experiments/general-kernel-checkpoint/BACKENDS]]. They have not been benchmarked
for CBCL here. SIGINT/SIGTERM trigger managed cleanup; SIGKILL cannot be handled.

Final receipt-negative checks run for each retained proof kind:

```sh
python3 verify-negative.py drawing-1 composite
python3 verify-negative.py drawing-1 succinct
python3 verify-negative.py status-8 composite
python3 verify-negative.py status-8 succinct
python3 cli-artifact-check.py
python3 manager-selftest.py
node measure-bandwidth.mjs
python3 capture-environment.py
python3 summarize-results.py
```

In-place compression is rejected before touching its input; use a separate output
directory. The managed runner removes an older ledger before starting. Bandwidth
rows require the matching successful ledger, so a failed/partial rerun cannot
silently count an old receipt as newly produced.
