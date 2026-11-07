# Optional private vote export

The contract and measurement boundaries are in [[BRIEF]]. This experiment lives
on `experiment/private-vote-export`; it changes no production kernel or API.
[[RESULTS]] records actual outcomes, including unsuccessful attempts.

The shared consumer deliberately pins one vote dialect and the current native
kernel. Keys are public synthetic fixtures, not identities for real use. The
export includes participants and tally; individual ballots and discussion remain
witness data. Abstention means no current ballot, not a retraction verb. Every
participant must endorse the same exact closing set; an offline participant can
therefore prevent this experimental closure policy from completing.

## Browser scope

The measured harness is native. A WASM library-compatibility probe is recorded
separately in [[RESULTS]]; it is not an in-browser vote proof. A browser port
would preload the compiled guest/program and preprocessing, replace file/process
interfaces with browser inputs, supply browser randomness and execution workers,
and measure memory and proving time on the actual client.

## Reproduction

Use the Jolt checkout pinned in [[BRIEF]], Rust 1.95.0 with
`riscv64imac-unknown-none-elf`, and the matching Jolt CLI. `prepare.py JOLT_DIR`
stages owned packages, substituting absolute current-kernel dependency paths.
It temporarily removes the older checkpoint overlay from workspace membership
because Cargo cannot lock two path copies of the same CBCL package/version.
The recorded `jolt-lock.patch` reproduces dependency resolution from the pinned
upstream lock without tracking a duplicate full lockfile. Original vendor
manifest and lock are saved in `.vote-backup`; restore both after
finishing. Upstream cryptographic sources and previous experiment evidence stay
unchanged.

`manage.py LABEL COMMAND...` saves logs/resource ledgers to ignored
`outputs/private-vote-export/` by default. Set `CBCL_VOTE_OUTPUT` to override.
Labels must be unique. Run all Cargo and proof operations sequentially. Build
`cbcl-vote-host` with the upstream `build-fast` profile, once without extra
features and once with `--features zk`. Copy each executable into the output
folder as `cbcl-vote-clear` and `cbcl-vote-zk` before the next build replaces it.

Run native tests for `private-vote-common` using nextest. Its `make_vote` example
writes a signed two-participant fixture and public expected statement; add
`--replacement` for the revision case. `make_negatives` writes malformed synthetic
witnesses and their expected native rejection reasons.

`run-host.py MODE count INPUT EXPECTED OUTPUT` executes the guest without keeping
the complete trace. `run-host.py MODE run INPUT EXPECTED OUTPUT` repeats that count,
refuses an oversized trace, then proves, verifies and serializes. `MODE` is
`clear` or `zk`; only the latter is suitable for private export. Both modes use
the same guest-target directory, ELF and fixture. Set `CBCL_JOLT_SOURCE` and
`CBCL_JOLT_TARGET` for different checkout/cache locations.

`guest-cases.py` tests malformed witnesses inside the VM without a host native
precheck. `verify-cases.py MODE` verifies saved public artifacts from a fresh
process, including coherent output tampering and cross-mode proofs (both modes required).
It uses independently copied operator pins, not a pin selected by an untrusted
proof package. Production distribution/authentication of those pins is outside
this local experiment.

No substring scan or successful clear proof establishes privacy. The zero-
knowledge claim relies on the pinned upstream BlindFold protocol and explicit
proof-mode verification. Counts, roster, tally, execution shape and timing still
have disclosure implications. This experiment is not a cryptographic audit.

A minimal sequence from the CBCL repository root (all paths below are explicit
local directories; use a fresh output directory):

```sh
export CBCL_JOLT_SOURCE=/path/to/pinned/jolt
export CBCL_JOLT_TARGET=/path/to/build-cache
export CBCL_VOTE_OUTPUT=/path/to/new-run
mkdir -p "$CBCL_VOTE_OUTPUT" "$CBCL_JOLT_TARGET"
python3 experiments/private-vote-export/prepare.py "$CBCL_JOLT_SOURCE"
python3 experiments/private-vote-export/manage.py cli cargo build --manifest-path "$CBCL_JOLT_SOURCE/Cargo.toml" --locked -p jolt --bin jolt --profile build-fast --target-dir "$CBCL_JOLT_TARGET"
python3 experiments/private-vote-export/manage.py build-clear cargo build --manifest-path "$CBCL_JOLT_SOURCE/Cargo.toml" --locked -p cbcl-vote-host --profile build-fast --target-dir "$CBCL_JOLT_TARGET"
cp "$CBCL_JOLT_TARGET/build-fast/cbcl-vote-host" "$CBCL_VOTE_OUTPUT/cbcl-vote-clear"
python3 experiments/private-vote-export/manage.py build-zk cargo build --manifest-path "$CBCL_JOLT_SOURCE/Cargo.toml" --locked -p cbcl-vote-host --features zk --profile build-fast --target-dir "$CBCL_JOLT_TARGET"
cp "$CBCL_JOLT_TARGET/build-fast/cbcl-vote-host" "$CBCL_VOTE_OUTPUT/cbcl-vote-zk"
python3 experiments/private-vote-export/manage.py fixture cargo run --manifest-path "$CBCL_JOLT_SOURCE/Cargo.toml" --locked -p private-vote-common --example make_vote --profile build-fast --target-dir "$CBCL_JOLT_TARGET" -- "$CBCL_VOTE_OUTPUT/fixture"
python3 experiments/private-vote-export/manage.py clear-proof python3 experiments/private-vote-export/run-host.py clear run "$CBCL_VOTE_OUTPUT/fixture/input.json" "$CBCL_VOTE_OUTPUT/fixture/expected.json" "$CBCL_VOTE_OUTPUT/clear-proof"
python3 experiments/private-vote-export/manage.py zk-proof python3 experiments/private-vote-export/run-host.py zk run "$CBCL_VOTE_OUTPUT/fixture/input.json" "$CBCL_VOTE_OUTPUT/fixture/expected.json" "$CBCL_VOTE_OUTPUT/zk-proof"
```

As the trusted local operator, copy each mode's `trusted.json` and the fixture's
`expected.json` into `operator-pins/MODE/` under the output directory. Then run
`verify-cases.py clear`, `verify-cases.py zk` and `summarize.py`, under the managed
runner. This local pin-copy step represents an operator build decision; it is not
a production mechanism for authenticating third-party packages. `make_scale`
accepts an output directory and total message count, 4–32. Only attempt proving
when the count reports the selected profile bound is satisfied.

The final lint command uses `-D warnings -A clippy::unused_unit` for the frozen
measured consumer; [[RESULTS]] explains that narrow style exception. Run the named
native tests before `mutations.py`; the script requires their successful
`native-tests-2-run.json` baseline ledger. Preserve that label when reproducing
that gate. Restore `.vote-backup/Cargo.toml` and `.vote-backup/Cargo.lock` in the
Jolt checkout after all Cargo and guest-build operations finish.
