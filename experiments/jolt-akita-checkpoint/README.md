# Jolt/Akita CBCL checkpoint experiment

The `experiment/jolt-akita-1000` scaling branch raises the profile limits and
adds an execution-only counting mode. See [[SCALE-1000]] for the failed full-proof
attempt and measured VM result. The smaller successful proofs in [[RESULTS]]
are from baseline commit5b55d0e and its original guest image.

This runs the existing bounded general CBCL consumer in a Jolt no_std guest.
Inputs are untrusted advice. The public journal binds the complete supplied
source registry, dialect, thread, canonical message/signer set, count and native
folded state. The kernel's authentication and freshness limitations are inherited
from `../general-kernel-checkpoint/BRIEF.md`; this does not certify Ed25519
signatures, transport identity or global completeness.

## Reproduce

Use Rust 1.95.0 and its `riscv64imac-unknown-none-elf` target. Clone Jolt at
`beebf45d829f5aecc5d330f78879cd914e47541e` into a dedicated checkout. From this
directory run `python3 prepare-source.py /path/to/jolt`. The script stages only
owned overlay packages and workspace membership. It does not modify upstream
cryptographic checks or catalogs. `evidence/Jolt.Cargo.lock` records resolution.
The core/parser dependency paths are resolved to this CBCL worktree.

Run all Cargo commands sequentially. Build packages `jolt` (binary `jolt`) and
`cbcl-akita-host` with `--profile build-fast --target-dir "$PWD/target"` and the
Jolt root manifest, using `run-managed.py LABEL COMMAND...`. Run native tests
with `cargo nextest run --cargo-profile build-fast -p checkpoint-common` under
the same target directory. Set `CBCL_JOLT_SOURCE` if using a different checkout.
`run-from-jolt.py` supplies the scoped CLI/guest target paths.

The host's `run INPUT EXPECTED OUT PINS` mode checks the native and traced
journal against an independently supplied expected journal, creates trusted
preprocessing, proves, verifies and exports proof/public I/O. `verify SETUP
PROOF IO EXPECTED STATE TRUSTED_PIN no-history` is the separate-process receiver;
it reads no history. The setup digest must be acquired from a trusted build.
Its ELF digest is provenance, not a separately verified program binding.

The dense catalogs require producer profile W8R2; this is distinct from the
one-hot trace geometry, which remains default W1R0. Advice capacities and other
memory layout parameters must match between guest attributes and host. The
guest explicitly sets trusted-advice capacity to zero.

## Measurement boundaries

Keep build, tracing, setup, proof and verification timings separate. The CPU
build uses upstream `build-fast`, not the authors' Metal configuration. Count
verifier preprocessing in cold transfer; proof-only transfer assumes the exact
trusted preprocessing is already installed. Public I/O and snapshot must also be
transferred. A successful trace is not a proof.

The managed runner enforces a sampled 4 GiB process-tree RSS ceiling, 1 GiB free
disk reserve, 30 minutes per invocation and 90 minutes from the worktree epoch.
It records failures as well as successes. The monitor samples every two seconds,
so its RSS figure is an observed peak rather than an exact maximum.
