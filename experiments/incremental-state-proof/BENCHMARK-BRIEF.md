---
mode: explanation
status: experiment
owner: CBCL maintainer
---
# Drawing compression and recursive proof calibration

The user requests realistic histories and proof-generation timing, and identifies
`../cbcl-bus` shared drawings with potentially thousands of messages as the
relevant workload. The failure under investigation is confusing a constant-size
proof with constant-size usable drawing state, and attributing ordinary structural
or transport compression to cryptography. This is a Tier 2 benchmark around the
existing Tier 1 experimental recursive circuit; no production enablement occurs.

## Workload and acceptance

Use the actual drawing contract, canonical intent generation, native WASM admission
and fold from the sibling repository, read-only. Until a real drawing history is
located, generate deterministic app-format traces and label them synthetic.
Measure 128, 1024 and 4096 operations with four-point and maximum thirty-point
chunks, four signer labels, chunks grouped into strokes and periodic erasures.
Signer authentication is assumed and signatures are absent. Record source hashes.
A complete fold must equal independently accumulated expected chunks and erasures.
Measure fresh native admission plus fold separately from generation.

Compare compact JSON replay records (signer plus canonical message), full native
fold output, and visible-only preview. Apply gzip 9 and Brotli 5 symmetrically,
record encoding/decoding time and check byte-exact round trips. The full native
output includes erased chunks and tombstones. It is a view, not a resumable
checkpoint: native continuation still needs admission history. The visible-only
preview discards erased chunks and cannot replace the native output. Neither
snapshot is authenticated by the numeric-register proof. Do not advertise their
sizes as measured proof-plus-drawing-checkpoint bundles.

Keep one full-history numeric-register proof as a timing calibration: extend the
existing verified 128-write proof to 256 after checking key, object and prefix
roots. Report actual extension time and cumulative genesis-to-256 proof-call time
from recorded calls across runs separately. Stop the planned telemetry/status
proof runs because they do not cover the user's drawing semantics. No drawing
proof is implemented, so its generation time remains unmeasured. Any throughput
extrapolation is explicitly a projection for the current numeric circuit.

## Evidence, resource envelope and exit

Preserve previous recursive evidence. New evidence lives in `evidence/benchmark`.
One proof worker, 4 GiB sampled process-tree RSS, 1 GiB disk reserve, 60-minute
managed run, 65-minute total active proof-run envelope. Record interrupted stages
and resumes. Native drawing replay is bounded to 4096 operations per case and
five minutes per process. Record concurrent workstation activity: this is not a
dedicated performance machine. No changes to cbcl-bus, app traffic or production
configuration. Actual private histories, if supplied, produce aggregate results
only; no raw drawing payload is committed. Obtain fresh-context adversarial review
of the harness and conclusions. Human cryptographic review remains open.

The maintainer acts next on whether reduced replay CPU justifies a drawing-specific
checkpoint design, which requires drawing semantics and resumable witness/state
availability beyond the current circuit. Missing real history is recorded as an
open dataset request, not silently substituted with production claims.

Producer: Codex, GPT-6 family; experiment follows
[[experiments/incremental-state-proof/RECURSION-RESULTS]]. The initial numeric-only
brief is retained as BENCHMARK-BRIEF.md.initial for provenance; user steering
supersedes its snapshot and additional proof-case plans.
