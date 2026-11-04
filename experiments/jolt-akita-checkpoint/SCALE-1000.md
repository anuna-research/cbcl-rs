# 1,000-message drawing checkpoint experiment

Follow-up request: try a checkpoint with 1,000 messages. Hypothesis: the same
Jolt/Akita general consumer can prove one drawing opener and 999 distinct chunks.
The synthetic workload uses the existing cbcl-bus drawing dialect, two writers,
valid canvas coordinates, native intent serialization and distinct chunk keys.
An independently constructed map of all 999 payloads checks the native result.
No production app or private drawing is accessed.

Limits raised only for this scaling branch: message ceiling 1024 (from 256),
guest heap 64 MiB (from 8), padded trace 2^30 (from2^22). Other recognition,
commitments, admission and folding are unchanged. This changes the guest image;
previous image/setup pins must not be reused. Proof acceptance still requires
separate receiver and tampering checks. Successful VM execution is not a proof.

First use upstream checkpointed execution to measure actual trace rows without
retaining a whole trace, then attempt the same full optimized Akita proof. Keep
4 GiB observed process-tree RSS,1 GiB disk reserve,30 minutes per process,90 minutes
for this explicitly authorized follow-up session (`CBCL_RUN_SESSION=scale1000`).
A resource cap is a measured failure to prove locally, not an inferred proof
latency or proof size. No paid remote compute or upstream crypto changes.

Tier 3 benchmark harness changes; inherited Tier 1 cryptography remains unmodified.
Fresh-context review required for changed limits/harness and final claims.
Human cryptographic review and cross-model review diversity remain open as before.
Producer model exact variant/settings unavailable. Next maintainer action: use
measured cycles/resources to choose local optimization, streaming proving, or a
larger host, then feed the result into general checkpoint protocol design.

## Reproduction

From this experiment directory, stage with `python3 prepare-source.py
/tmp/cbcl-jolt-akita-source`. Reuse the pinned toolchain/dependencies from
[[README]]. Use `CBCL_RUN_SESSION=scale1000` on every managed invocation so the
same immutable follow-up session epoch applies to builds, execution and proving.

Generate the fixture with the common example `make_drawing_1000`, passing the
existing drawing-1.json seed and `evidence/scale1000-fixture` output directory.
It uses the native intent API against the opener, then checks the complete
native folded state against an independently constructed keyed payload map.
The pre-existing native nextest suite is the regression gate.

Build `cbcl-akita-host` with the pinned vendor manifest and build-fast profile.
Call the host using `run-from-jolt.py run INPUT EXPECTED OUT PINS`. The count pass
uses `CBCL_COUNT_ONLY=1`, `evidence/scale1000-count` and
`evidence/independent-scale1000-count`. The proof attempt omits COUNT_ONLY and
uses separate `evidence/scale1000-proof` and
`evidence/independent-scale1000-proof` directories. Both use the same fixture and
expected journal from the native generator; the guest output must match them.
A successful count pass records trace eligibility but leaves proof_generated
false. If a real proof succeeds, run `verify-negative.py scale1000-proof` for
independent serialized receiver checks.

## Build incident

An initial no-incremental build failed with LLVM no-space-left-on-device before
any VM execution. Its supervisor then received PermissionError in final process
group cleanup after the child exited, so no timed run ledger was emitted. Exact
runtime/peak memory for that failed build are unknown; the error log is retained.
The supervisor now tolerates that cleanup error only after leader exit and records
a warning; it still raises if the leader is running. A true-process smoke run
completed with a ledger. Removed only standalone .rcgu.o compiler objects from
this experiment's target/build-fast/deps, retaining complete libraries, binaries,
source and proof evidence; the cleanup manifest records bytes. The retry uses
the original incremental profile and reuses complete compiled libraries.

## Measured result

The requested attempt completed, with **no proof generated**. The full 1,000
messages execute correctly in the VM, but the retained-trace proof path stopped
before setup/proving. All measurements are single observations on the same 8 GB
M2 and pinned CPU backend as the smaller experiments.

| Measurement | Observed result |
|---|---:|
| Messages / distinct drawing chunks | 1,000 / 999 |
| Input JSON / canonical folded state | 350,003 B / 61,339 B |
| Input Brotli9 / state Brotli9 | 7,706 B / 5,514 B |
| Native consumer computation | 278 ms |
| Checkpointed VM execution | 134.447 s |
| VM output matches expected journal | yes |
| Actual trace rows | 5,024,762,651 |
| Required padded trace rows | 8,589,934,592 (2^33) |
| Configured padded trace ceiling | 1,073,741,824 (2^30) |
| Checkpointed execution sampled peak RSS | 459,177,984 B |
| Full proof attempt elapsed before stop | 35.233 s |
| Full attempt sampled peak process-tree RSS | 1,026,097,152 B |
| Full attempt observed minimum free disk | 509,186,048 B |
| Full attempt stop reason | disk reserve below 1 GiB |
| Last phase | trace collection |
| Proof size / proving time / verification | unavailable |

The 134.447s is execution-only, not proof generation. The whole count invocation
was 147.435s, including 8.122s guest compilation and other host work. The subsequent
35.233s is an aborted tracing invocation, not a measured proving time. The memory
cap was not reached; do not describe this as a 4 GiB RSS failure or infer swap
causation from the disk-pressure observation. The monitor samples every 2 s and
therefore can overshoot its stop thresholds. Its recorded minimum fell below the
1 GiB reserve before termination. No setup, proving or cryptographic verification
was reached in the full attempt. No serialized receiver acceptance is claimed.

Two separate constraints apply: the full trace attempt exhausted the monitored
local disk budget, AND its correctly measured complete trace exceeds the trial's
configured maximum by 8x in padded capacity. More disk alone cannot make this
configuration accept it. The packaged upstream catalogs document support through
2^31 cycles, below this measured 2^33 shape; no catalog setup was attempted and no
missing-catalog error is claimed as an observed failure. Supporting this shape
would require legitimate configuration/catalog provisioning as well as resources.

After the process exited, disk availability recovered. Disposable standalone
compiler objects and the owned incremental cache were removed, leaving about
8.16 GB free at cleanup measurement. Complete libraries, executables, guest ELF,
fixtures and all proof evidence remain. No experiment process was left running.

### Interpretation and next action

The small-fixture speedup does not establish 1,000-message feasibility for this
unchanged replay algorithm. A concrete source-level scaling mechanism exists:
`state_exports::admit` calls `Instance::store` for each admission, and that method
clones every accepted message into a new store. Repeating it over a growing
accepted set creates quadratic copying work. This was identified by source
inspection; no instruction profile quantifies its fraction of the 5.02 billion
rows. Parser, allocation, hashing and other work may also matter.

Next maintainer task: profile and reuse an indexed admission store while
preserving the same dialect/shape/causal rules and public commitments, verify
against the native kernel, then rerun this frozen 1,000-message fixture. A prover
that does not retain the whole trace and a legitimately provisioned larger
shape may also be needed. No automatic extrapolated proving time or proof size
is presented. This failure does not establish that Jolt cannot prove 1,000 CBCL
messages using a different implementation or machine.

Fresh-context adversarial review checked the workload, count-vs-proof distinction,
limits, final ledgers and claims. Two findings were repaired: stale execution
metrics are cleared before runs; count results explicitly record padded trace
eligibility. Exact cross-model diversity is unestablished and human cryptographic
review remains open. The fixture is synthetic and retains the authentication,
set anchoring and freshness assumptions from [[BRIEF]].

Evidence: [[evidence/scale1000-fixture/fixture-metrics]],
[[evidence/scale1000-count/execution-metrics]],
[[evidence/scale1000-vm-count-run]], [[evidence/scale1000-proof-attempt-run]],
[[evidence/scale1000-input-provenance]], [[evidence/scale1000-post-run-cleanup]].
