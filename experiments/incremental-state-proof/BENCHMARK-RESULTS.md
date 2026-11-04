---
mode: explanation
status: experimental-evidence
---
# Drawing state versus replay, and proof generation cost

The app-format experiment shows why a proof does not eliminate drawing state:
unique stroke chunks carry the geometry that must still be delivered. Ordinary
compression removes much of the repeated native-message syntax already.

## Dataset and measurements

These are deterministic synthetic traces generated through cbcl-bus's actual
shared-drawing contract and SDK, not a captured user drawing. Four signer labels,
eight operations per stroke, and periodic erasure of one in five strokes. Small
chunks have four coordinate pairs; maximum chunks have thirty. Each row also
contains one drawing opener. No signatures are counted; signer authentication is
assumed. Actual native fresh admission and fold must equal independently accumulated
expected title, chunks and erased markers. No circuit was changed.

All sizes are bytes. Replay includes canonical messages and signer labels. Full
view is the complete native fold output including erased chunks and tombstones.
Savings compare Brotli full view to Brotli replay, not raw replay to compressed state.

| Operations | Points/chunk | Replay raw | Replay gzip9 | Full view gzip9 | Replay Brotli5 | Full view Brotli5 | View saving | Native fresh replay |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 128 | 4 | 53,157 | 3,390 | 2,811 | 2,861 | 2,451 | 14.3% | 0.247 s |
| 128 | 30 | 79,076 | 14,795 | 13,996 | 10,865 | 10,500 | 3.4% | 0.390 s |
| 1,024 | 4 | 425,496 | 24,751 | 22,193 | 20,072 | 18,195 | 9.4% | 12.384 s |
| 1,024 | 30 | 631,106 | 113,231 | 106,560 | 82,893 | 78,270 | 5.6% | 19.473 s |
| 4,096 | 4 | 1,701,540 | 97,745 | 88,828 | 79,212 | 73,680 | 7.0% | 192.775 s |
| 4,096 | 30 | 2,524,451 | 447,243 | 427,042 | 315,006 | 311,968 | 1.0% | 294.212 s |

The view is **not a resumable checkpoint**: the existing native admission path
still requires history. Visible-only previews are measured separately in the
JSON evidence, but discard erased chunks and cannot substitute for full native
state. These views have no drawing proof. Therefore no measured proof-plus-drawing
checkpoint bundle or continuation speedup is claimed. A usable replacement needs
a specified drawing transition kernel, authenticated state and available future
witnesses, including concurrency and late delivery semantics.

Compression round trips were byte-exact. Decode/parse validation timing fields
include assertions and are labelled accordingly; they are not pure client decode
latencies. Measurements are single samples on an Apple M2 with 8 GiB RAM; native
runs and proving overlapped on a shared workstation. Source and WASM hashes are
recorded with each row. Early WASM/compiler metadata added after the run is
explicitly marked retrospective, so it is weaker than hashes captured during a
measurement. The SDK fresh admission loop serializes the growing accepted history
for each individual admission, so these replay times include that repeated work;
they are not a lower bound for an optimized native batch/incremental API.
Structured, smooth synthetic strokes may compress better
than an actual user's drawing. A real history location/export is still requested.

## Recursive proof calibration

The unchanged numeric-register circuit produced and verified one proof covering
all **256 writes from empty genesis**. Its binary proof is
24,381 bytes (compact JSON 33,069 bytes).
Cumulative actual genesis and batch proof calls took **2241.266 seconds
(37.35 minutes)**, summed across the original
128-write run and the resumed extension. The additional 128 writes took
1114.933 seconds of completed proof calls. This is not a fresh uninterrupted
wall time. Final in-process verification took 2.162 seconds.
Cached setup for the resumed worker was 7.962 seconds;
setup, witnesses, serialization and interrupted work are excluded from the proof-call sum.
The original cold source setup was recorded separately in
[[experiments/incremental-state-proof/RECURSION-RESULTS]].

This is calibration for sequential UInt32 registers. **It does not prove a drawing,
and drawing proof-generation time remains unmeasured.** Extrapolating these timings
would not establish drawing circuit performance or proof size.

## Reproduction and next action

From this experiment directory, set `CBCL_BUS_REPO` to the sibling app repository
and run `python3 run-drawing-benchmark.py`, then `python3 summarize-benchmark.py`.
Each drawing process has a five-minute limit. Proof calibration uses
`python3 run-benchmark-proof.py --control-only` with the original recursive prefix
artifacts and native oracle configured as in the earlier experiment; add
`--resume-control` only with a consistent saved latest proof/timing ledger.
The runner overwrites its new benchmark output files, so preserve evidence before
rerunning. No app network traffic or production changes occur.

Next: the maintainer supplies an actual history location for an aggregate-only
measurement and decides whether avoiding replay CPU warrants a drawing-specific
checkpoint successor. Recursive numeric proofs are demonstrated; general drawing
proofs and production cryptographic review remain open. Scope and acceptance are
recorded in [[experiments/incremental-state-proof/BENCHMARK-BRIEF]].
