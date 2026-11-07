# Browser private vote export experiment

This is the actual browser prototype of the fixed authenticated voting experiment
in [[../README]], governed by [[BRIEF]]. [[RESULTS]] records executed outcomes and
failures; build success alone is not browser proving evidence. The prototype uses
experimental signed envelopes and a fixed vote source, not native R4 v2 or the
future general dialect/profile/export API in
[[../../../specs/SPEC-038-optional-thread-proof-export]]. Full expected-Journal
fixtures are test oracles here, not a production requirement to trust the tally
before verifying it. Synthetic fixture keys are public and must never be reused
for real discussions.

The Rust module runs native admission/fold and the guest tracer/prover inside a
Web Worker. The native helper only produces pinned preprocessing before the
browser run; the loopback server does not prove. Browser cancellation terminates
the worker and requires native-proof verification in a fresh worker. Only public
proof/IO artifacts are uploaded to the local server. No remote prover is used.

## Prepare sources and fixtures

Run commands from the CBCL repository root. Use a dedicated clean Jolt checkout
at `beebf45d829f5aecc5d330f78879cd914e47541e`, Rust 1.95.0 with
`wasm32-unknown-unknown` and `riscv64imac-unknown-none-elf`, Node 25 or newer, a local
64-bit Chromium/headless-shell binary, and wasm-bindgen CLI **0.2.126**, matching
the crate. No npm packages or browser download are performed by the runner.

```sh
export CBCL_JOLT_SOURCE=/absolute/path/to/pinned-jolt
export CBCL_JOLT_TARGET=/absolute/path/to/build-cache
export CBCL_VOTE_FIXTURES=/absolute/path/to/native-vote-output
export CBCL_VOTE_OUTPUT="$PWD/outputs/jolt-dory-browser-reproduction"
export CHROME=/absolute/path/to/chrome-headless-shell
mkdir -p "$CBCL_JOLT_TARGET" "$CBCL_VOTE_OUTPUT"
python3 experiments/private-vote-export/browser/prepare.py "$CBCL_JOLT_SOURCE"
```

`prepare.py` stages the owned native packages and browser adapter into
`.vote-overlay/`, adjusts workspace membership and applies
`jolt-browser-lock.patch` to the exact upstream lock. The native preparation
preserves the vendor manifest/lock in `.vote-backup`; restore them after all
builds finish. The
browser lock delta includes the exact wasm-bindgen version and is separate from
the parent experiment's lock delta. Do not run the parent preparation again
between browser staging and its locked builds, because it resets the lock.

When `jolt-wasm-portability.patch` is present, preparation applies it after lock staging,
or recognises the exact already-applied patch; conflicting source is an error.
This small upstream portability patch widens the intermediate multiplication in
sparse register partitioning from host `usize` to `u128` before dividing and
converting the bounded result back to `usize`. The mathematical partition remains
`floor(block * len / block_count)`; the patch prevents 32-bit intermediate overflow.
It does not change the guest ELF, field arithmetic, proof constraints, transcript,
ZK mode or authentication checks. The source/build pin must include the patch;
record patched and unpatched outcomes separately. Its presence is optional in the
staging script, but reproducing a patched-browser measurement requires it. Restore
that upstream file after builds if returning the vendor checkout to its original
state; restoring only `.vote-backup` manifest/lock does not undo this source patch.

First reproduce the native fixtures using [[../README]] and its receiver checks.
The browser expects both clear and ZK proofs, independently copied ZK operator
pins, guest ELF, negative witnesses and receiver-tampering fixtures. Produce the
valid over-budget fixture using the `make_scale OUTPUTDIR 16` example under
`private-vote-common`; its directory must be `scale-16` under the fixture root.
Generate negative witnesses with `make_negatives OUTPUTDIR`, using
`negative-fixtures` as that directory. The parent `verify-cases.py zk` creates the
advice/coherent-output fixtures. Native prove/count operations remain separate
from the browser runs. Do not generate fixtures from real private histories.

`CBCL_VOTE_FIXTURES` selects the read-only synthetic fixture root. Its default
preserves the original workstation path:
`/Users/anuna-02/Code/cbcl-rs-private-vote/outputs/private-vote-export`.
`CBCL_VOTE_OUTPUT` selects the outer manager's ledger directory; the runner's
second positional argument selects its runtime artifact directory. For managed
runs that directory must be inside `CBCL_VOTE_OUTPUT`, so the supervisor can safely
register and clean its public artifact paths. Use absolute paths for both.

## Build the helper and browser package

Run builds sequentially through the browser manager. It sets native
`RAYON_NUM_THREADS=4`, `CARGO_BUILD_JOBS=1`, `CARGO_INCREMENTAL=0` and
`RUSTUP_TOOLCHAIN=1.95.0`. Four native Rayon threads **do not** configure WASM
threading; this browser adapter uses one compute worker and browser-provided
entropy, not a four-worker Rayon pool.

```sh
python3 experiments/private-vote-export/browser/manage.py native-build \
  cargo build --manifest-path "$CBCL_JOLT_SOURCE/Cargo.toml" --locked \
  -p cbcl-vote-browser --bin browser-profile --profile build-fast \
  --target-dir "$CBCL_JOLT_TARGET"

python3 experiments/private-vote-export/browser/manage.py profile \
  "$CBCL_JOLT_TARGET/build-fast/browser-profile" \
  "$CBCL_VOTE_FIXTURES/guest-target/cbcl-vote-guest-export_vote/riscv64imac-unknown-none-elf/release/cbcl-vote-guest" \
  "$CBCL_VOTE_FIXTURES/operator-pins/zk/trusted.json" \
  "$CBCL_VOTE_OUTPUT/profile"
```

The helper's exact arguments are `browser-profile ELF EXISTING_TRUST_JSON OUTPUT`.
It checks the Jolt commit, ZK mode and guest hash, generates Dory prover setup,
checks that the verifier setup hash equals the existing independently supplied
operator pin, then writes `prover-setup.bin`, `setup.bin` and `profile.json`.
The profile is explicitly `experimental-private-vote-v0`, with a `2^24` padded
trace bound. These are experiment choices, not protocol limits. The browser still
reads the old verifier setup from the fixed fixture map below.

The current WASM build uses a 128 MiB WASM stack and a 4 GiB maximum linear memory
address space. These linker parameters are not browser RSS limits or measured
memory usage. A smaller 3 GiB build is a distinct artifact; do not mix its results
or package hashes with the 4 GiB build.

```sh
CARGO_PROFILE_BUILD_FAST_DEBUG=0 \
RUSTFLAGS='--cfg getrandom_backend="wasm_js" -C link-arg=-z -C link-arg=stack-size=134217728 -C link-arg=--max-memory=4294967296' \
  python3 experiments/private-vote-export/browser/manage.py wasm-build \
  cargo build --manifest-path "$CBCL_JOLT_SOURCE/Cargo.toml" --locked \
  -p cbcl-vote-browser --lib --target wasm32-unknown-unknown \
  --profile build-fast --target-dir "$CBCL_JOLT_TARGET"

python3 experiments/private-vote-export/browser/manage.py bindgen \
  wasm-bindgen \
  "$CBCL_JOLT_TARGET/wasm32-unknown-unknown/build-fast/cbcl_vote_browser.wasm" \
  --target web --out-dir "$CBCL_VOTE_OUTPUT/pkg" --out-name cbcl_vote_browser
```

Add `--offline` to Cargo commands only if the pinned dependencies are already
cached. Compile and bindgen are preparatory evidence; neither passes a runtime
trace/prove/export/verify gate.

## Run the browser modes

Set `CHROME` explicitly to the binary being measured. A fresh profile is created
inside the run output directory and deleted during cleanup; no installed user's
Chrome profile is touched. The runner otherwise defaults to an existing system
Chrome/Chromium. An engine startup failure is a harness/engine result, not a
cryptographic rejection. Record the actual CDP-reported version with each run.

```sh
mkdir -p "$CBCL_VOTE_OUTPUT/run-1"
ln -s "$CBCL_VOTE_OUTPUT/pkg" "$CBCL_VOTE_OUTPUT/run-1/pkg"
ln -s "$CBCL_VOTE_OUTPUT/profile" "$CBCL_VOTE_OUTPUT/run-1/profile"

for mode in verify count cancel-trace cancel-prove prove; do
  python3 experiments/private-vote-export/browser/manage.py "runtime-$mode" \
    python3 experiments/private-vote-export/browser/run-browser.py \
    "$mode" "$CBCL_VOTE_OUTPUT/run-1" || exit $?
done
```

The modes run sequentially. `verify` checks an honest native proof and targeted
context/setup/mode/output/advice negatives. `count` executes the guest and checks
invalid signatures, missing closure, trace-budget rejection and recovery.
`cancel-trace` and `cancel-prove` require explicit cancellation plus successful
fresh-worker native-artifact verification. `prove` traces/proves inside the
browser, verifies the generated proof in a fresh browser worker, then publishes
`browser-proof.bin` and `browser-io.bin`. A failed mode exits nonzero; a random
nonzero exit does not count as an expected negative. Error messages must match
the check being exercised.

Each mode requires fresh per-mode ledgers and a fresh `MODE-supervisor.json`. The sequence deliberately puts prove
last: cancellation cannot inherit or publish proof files. For a retry or rebuilt
WASM package create a new run directory with new `pkg`/`profile` symlinks and use
unique outer labels. The runner refuses stale ledgers/artifacts instead of
silently overwriting them. Keep failed attempt logs and source/package pins. Files alone are not a successful
export: require `MODE-supervisor.json` with `ok:true` and `status:"complete"`, its
referenced manager ledger with `ok:true`, and the successful runner/proof
verification records. The marker starts with `ok:false` before work is allowed.
Do not rebuild or edit app/worker/driver code during a measured run.

After checking those supervisor/runner verdicts, independently verify any
browser-produced proof with the native ZK receiver and no history argument, as a
separate managed operation:

```sh
python3 experiments/private-vote-export/browser/manage.py native-receiver \
  "$CBCL_VOTE_FIXTURES/cbcl-vote-zk" verify \
  "$CBCL_VOTE_FIXTURES/zk-proof/setup.bin" \
  "$CBCL_VOTE_OUTPUT/run-1/browser-proof.bin" \
  "$CBCL_VOTE_OUTPUT/run-1/browser-io.bin" \
  "$CBCL_VOTE_FIXTURES/operator-pins/zk/expected.json" \
  "$CBCL_VOTE_FIXTURES/operator-pins/zk/trusted.json" no-history
```

This uses the existing trusted native binary, expected experimental statement and
setup pin. The receiver does not need a private history or accept a pin chosen by
the browser package. A new deployment must independently authenticate its pins;
the local synthetic fixture arrangement is not a production distribution policy.

## HTTP, assets and public artifacts

The runner binds only `127.0.0.1`, checks Host/Origin, and constructs the complete
GET allowlist before serving. Request paths never become filesystem joins.
`/`, `/index.html`, `/app.js` and `/worker.js` map to this source directory;
`/pkg/…` maps to the snapshot of actual generated package files, including any
wasm-bindgen snippets. Package files must resolve inside the selected `pkg` root.
Exact `/favicon.ico` returns 204 without an asset read. Unknown paths, queries and
traversal aliases reject. MIME types cover HTML/JS/JSON/WASM; COOP/COEP and CSP
allow same-origin workers and WASM compilation, but no remote connection.

Every `/assets/` entry has a fixed source; paths below are relative to
`CBCL_VOTE_FIXTURES`, except the final profile entries:

| URL under `/assets/` | Fixed file |
|---|---|
| `setup.bin` | `zk-proof/setup.bin` |
| `proof.bin` | `zk-proof/proof.bin` |
| `io.bin` | `zk-proof/io.bin` |
| `expected.json` | `fixture/expected.json` |
| `trusted.json` | `operator-pins/zk/trusted.json` |
| `clear-proof.bin` | `clear-proof/proof.bin` |
| `witness.json` | `fixture/input.json` |
| `missing-closure.json` | `negative-fixtures/cases/missingclosure.json` |
| `bad-signature.json` | `negative-fixtures/cases/invalidmsgsig.json` |
| `over-cap.json` | `scale-16/input.json` |
| `over-cap-expected.json` | `scale-16/expected.json` |
| `advice-io.bin` | `zk-receiver-cases/advice-io.bin` |
| `coherent-io.bin` | `zk-receiver-cases/changed-io.bin` |
| `coherent-expected.json` | `zk-receiver-cases/coherent-tally.json` |
| `guest.elf` | `guest-target/cbcl-vote-guest-export_vote/riscv64imac-unknown-none-elf/release/cbcl-vote-guest` |
| `prover-setup.bin` | runner OUTPUT_DIR `/profile/prover-setup.bin` |
| `profile.json` | runner OUTPUT_DIR `/profile/profile.json` |

Only these POST endpoints exist:

| Endpoint | Bound | Output |
|---|---|---|
| `/artifact/proof` | 1 MiB | `browser-proof.bin`, prove mode only |
| `/artifact/io` | 16 KiB | `browser-io.bin`, prove mode only |
| `/phase` | 16 KiB ordinary JSON | `MODE-phases.jsonl`; immediately flushed phase lines on stdout |
| `/result` | 1 MiB ordinary JSON | `MODE-result.json` |

There is no witness POST endpoint. Metrics/results must not contain private input,
ballots, salt or signatures. The JSON boundary rejects duplicate/nonfinite values,
excessive nesting and explicitly private field names; that guard is not a claim
that arbitrary strings can be automatically certified private-data-free. The app
owns the public metrics projection. The posted final result must equal the CDP
return value and pass mode-specific checks. Failures/cancellation leave no proof
or IO artifact files.

## Monitoring and cleanup

Node's built-in WebSocket sends CDP commands and awaits
`window.runExperiment(MODE)`. The driver captures target identities, console
output, runtime exceptions, network request/response/failure events and performance
metrics in `MODE-cdp.json`; unexpected runtime/network errors fail the run. Service
workers are prohibited. Pages have Fetch interception. Worker targets have Runtime
and Network monitoring plus their same-origin response CSP; the worker Fetch
domain is not supported by the measured engine and is not silently ignored.
Capabilities are recorded per target. Engine-internal background activity is not
claimed to be exhaustively measured by renderer CDP; background networking,
components, sync and extensions are disabled by launch flags.

`MODE-harness.log`, `MODE-chrome.log` and `MODE-runner.json` retain diagnostics and
cleanup errors/warnings. The driver has a 25-minute runtime deadline, and the
outer browser manager applies a 30-minute limit, sampled 4 GiB aggregate process
RSS cap and 1 GiB disk reserve. A 4 GiB WASM address-space ceiling can still exceed
the aggregate RSS budget. Worker-reported `linear_memory_bytes` means memory
capacity, not process RSS or live allocation. Native Rayon settings are not WASM
parallelism measurements.

For managed runs a private inherited socket registers the run mode and artifact
output paths before the manager acknowledges launch. Each detached Chrome/CDP
process first enters a small Python bootstrap, registers its own PID/process
group, and waits for a matching supervisor ACK before executing Chrome/Node. The
manager records the group before acknowledging it. If the runner dies in the
spawn/registration window, socket closure or timeout ends the bootstrap without
releasing browser work. Browser/Node do not inherit the management descriptor.
Registration is separate from the two-second resource samples; the controlled
Chrome/CDP groups do not rely on a lucky sampling interval for cleanup.

The runner stops its child groups and server on completion/failure. The manager
also stops registered and sampled descendant groups. After a failed/capped run it
removes final and pending public proof/IO files, then records a failed supervisor
marker and ledger, even if the runner was killed before its own cleanup. A clean
exit and successful runner ledger are required before the manager can issue a
success marker. A lower time budget can be set with
`CBCL_BROWSER_TIME_LIMIT_SECONDS`; it cannot exceed 1800 seconds.

Sampling is still not an OS-enforced memory ceiling, and this handshake does not
claim supervision of arbitrary uncooperative descendants that detach outside the
controlled launcher. Nor can it promise cleanup if the manager itself is killed
with SIGKILL: the pre-existing `ok:false` marker still prevents treating an
unfinished export as accepted. Post-exit process-group permission errors are
explicit cleanup warnings; live-group permission errors are fatal and recorded.
Never interpret a cap, startup failure or crash as successful proving or a
cryptographic negative.

`python3 experiments/private-vote-export/browser/check-manager.py` exercises real
SIGTERM interruption and cleanup of a managed child and a detached-session child.
It records its own PID/ledger evidence under a fresh outputs subdirectory and
must observe all groups gone before its fallback cleanup can run. It is a
manager smoke test, not proof or browser performance evidence.

`python3 experiments/private-vote-export/browser/check-supervisor.py` tests the
actual pre-exec handshake with runner death before registration, runner death
after publication, and a real lowered time cap during publication, plus a clean
positive control. It requires no unregistered work, no surviving process groups
before fallback cleanup, failed supervisor verdicts and removal of public artifact
names after failures. Its public fixture bytes explicitly are not proofs; these
process tests do not establish browser proving or cryptographic validity.

The portability patch also widens the lookup-table saturation comparison before
squaring its length. `check-partitions.py JOLT_DIR NEW_OUTPUT_DIR` executes both
patched expressions on real wasm32 and compares them with BigInt arithmetic. It
requires the Rust WASM target and Node; it does not run or prove the guest.
