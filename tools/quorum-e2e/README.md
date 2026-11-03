# Quorum end-to-end finality benchmark

This opt-in harness starts four separate validator processes and one client on
loopback TCP. It runs the Rust quorum-budget protocol against one shared
`collective-tickets` pool (four validators, quorum three). Fresh OS-random
Ed25519 keys authenticate actors and protocol votes. Validators apply the
ordinary CBCL role/causal verifier against the fixed genesis history; independent
sales all reference the opener. This is a benchmark host adapter for that fixture.

Build and run from the repository root:

```sh
CARGO_PROFILE_RELEASE_OPT_LEVEL=3 CARGO_PROFILE_RELEASE_LTO=false \
  cargo build --release -p cbcl-quorum-e2e

target/release/cbcl-quorum-e2e \
  --transactions 1000 --rate 100 --delay-ms 20 \
  --timeout-ms 5000 --max-inflight 1024 --out /tmp/cbcl-finality-run
```

`--out` must name a new directory. The default creates a unique temporary
directory. `--rate` controls open-loop offered transactions per second;
`--max-inflight` bounds client outstanding work. `--delay-ms` adds fixed one-way
latency to every frame in both directions, without serializing frames by sleeping
once per request. Two quorum rounds therefore have an approximate `4 × delay`
network floor. TCP, serialization, scheduling and queueing add further time.
`--silent-validators 1` exercises quorum progress with one silent validator;
`--silent-validators 2` exercises stalls. Silent validators still answer shutdown.
`--byzantine-mode withhold|equivocate|invalid-flood` makes `@v0` actively faulty:

- `withhold` returns valid operation votes, then withholds every other effects
  vote. The three honest validators must supply quorum when it withholds.
- `equivocate` signs both cancellation and effects votes for the same transaction,
  sending cancellation first. Both signatures are genuine; one signer cannot
  supply a cancellation quorum. The client ignores cancellation votes rather
  than adding them to an operation/effects certificate.
- `invalid-flood` sends eight identical invalid-signature votes for each
  operation/effects request, with no valid vote. This is a bounded,
  request-proportional flood, not an unrestricted traffic attack.

These modes cannot be combined with silent-validator settings. They use a
benchmark-only handler outside `Replica`: a compromised signer can bypass its
local journal/signing rules. Honest validators retain normal verification and
sync-before-vote behavior. The faulty node ignores final certificates and
retains only its initialized ledger. Recovery checks its actual state; it does
not require a compromised node to agree with the honest ledger. Reports expose
fault request/reply/withholding/conflicting-pair counters in validator zero's
profile, plus client invalid-vote and verified-but-ignored cancellation counts.
Client rejection counts cover votes processed while a transaction is pending;
late frames drained after completion are not included in those counts.

The harness connects validators to one client; it does not simulate divergent
gossip views, partitions, adaptive attackers, malformed-frame attacks or
unbounded denial of service. A faulty node also frees shared CPU/storage by
skipping honest work, so honest and faulty runs on this single host cannot be
interpreted as isolated physical-machine costs.

Timeouts must be at least one second. Debug builds require `--allow-debug` and
are useful for tests only.

For higher-load runs on the measured local host, use
`--journal-batch-size 128 --journal-batch-wait-ms 1`. This uses the existing
durable group-commit path; the default remains 64 requests / 1 ms. See the
batch-tuning results below before interpreting offered rate as capacity.

The clock starts immediately before the signed transaction is enqueued for
transmission. It stops after the client receives and strictly verifies an effects
certificate containing three distinct committee signatures bound to the context,
kind and transaction. Transaction generation and initial actor signing precede
the clock. Both network rounds, transport queues, validator admission and
signature work, journal syncing and client certificate verification are included.
The client broadcasts the final certificate afterward; that delivery is outside
the finality timer. No validator ordering/consensus service is introduced.

Each validator has an exclusively locked append-only JSONL journal. By default,
up to 64 requests share one write and `sync_all`; all records for a vote are
durable before it can be returned. Creation also
syncs the parent directory on Unix. Actor signatures are persisted for replay.
An ambiguous write/sync error aborts the signer; recovery refuses torn records
instead of truncating them. Durability relies on the filesystem/device honoring
`sync_all`. After the timed run, fresh processes replay all four journals and
compare recovered final counts, values and event counts with shutdown observations.
This recovery audit is outside the timed interval.

`report.json` and stdout contain:

- Conditional finality latency p50/p95/p99 for completed transactions.
- All-submitted p50/p95/p99 including stalls. A quantile beyond observed
  completions is `right_censored: true`, with a timeout lower bound and no
  invented latency value.
- Finalized throughput over the measurement window, including timeout drain.
- Fraction finalized within one second, using both submitted and all offered
  transactions as denominators. Stalls and client overload cannot disappear.
- Offered/submitted/finalized/stalled/overload counts, scheduler lateness,
  errors, process IDs, build/host metadata and recovery results.

`transactions.jsonl` records each outcome and actual effects certificate;
`public-setup.json` allows independent signature verification. Validator
subdirectories contain journals, logs and **secret key configurations**. The run
directory is private (0700) and config files are 0600 on Unix. Do not publish raw
run directories. Aggregate reports contain no private keys.

These are measurements on one host with fixed artificial delay: there is no
packet-loss, jitter, bandwidth, geographic deployment or storage-failure model.
The workload has one hot collective pool and no warmup exclusion. Journal groups
combine storage I/O; transactions still have individual quorum certificates.
Record repeated runs before comparing changes. Subsecond success in one run is
an observation, not an asynchronous progress bound. No-quorum transactions may
finalize after the observation timeout; they are reported as censored stalls.

Validation:

```sh
cargo test -p cbcl-quorum-e2e
cargo clippy -p cbcl-quorum-e2e --all-targets --no-deps -- -D warnings
```

Tests include four-process finality, independent certificate verification,
recovery, one silent validator, quorum loss with client overload, signature
mutation, invalid signed protocol evidence, journal fencing/CAS/torn logs and
censored percentile accounting.

Historical per-event baseline smoke measurements (`--journal-batch-size 1`,
100 transactions each; one-way delay
20 ms, timeout 5 s; no silent validators):

| Offered TPS | Finalized TPS | p50 | p95 | p99 | Within 1 second |
|---:|---:|---:|---:|---:|---:|
| 20 | 19.69 | 129.66 ms | 138.66 ms | 140.32 ms | 100% |
| 100 | 26.34 | 2265.94 ms | 2760.85 ms | 2804.12 ms | 18% |

A separate two-silent-validator run finalized 0/10 by its 1500 ms deadline;
all population percentiles were censored. All journals recovered successfully.
Other build/test activity was present on the host. These single runs establish that the harness observes load-dependent queueing
and quorum stalls; they are not a capacity estimate. Aggregate evidence and build
metadata are in [quorum-e2e-evidence.json](https://git.anuna.io/anuna-research/cbcl-rs/src/commit/96d5858d427fb1e371e0a8f13ddf0b23c6c6c8f2/outputs/quorum-e2e-evidence.json).

## Validator service-cost measurements

Every shutdown observation includes a `profile` object with count, total, mean
and p50/p95/p99 wall-clock timings. `request_service` encloses handler work,
including response serialization/enqueue, but excludes socket reads and startup.
Its nested components are journal encoding, `write_all`, `sync_all`, ordinary
role/causal admission, strict Ed25519 verification, and vote signing (including
preimage construction). Verification preimage construction and remaining runtime
work belong to the residual. Initial journal creation and directory syncing are
outside these samples. Final-certificate handlers are included even though they
run after the client's finality timer stops. Timers also observe scheduler delays;
they are not CPU instruction profiles. Sample collection adds instrumentation cost.
Do not add the parent service time to its nested component totals.

Historical per-event baseline measurements (`--journal-batch-size 1`): three
sequential release repetitions at each load (100 transactions/run,
20 ms one-way delay, syncing unchanged) produced these medians:

| Offered TPS | Finalized TPS | Journal sync | Journal write | Signature verification | Vote signing | Admission |
|---:|---:|---:|---:|---:|---:|---:|
| 20 | 19.64 | 78.13% | 17.16% | 3.31% | 0.38% | 0.12% |
| 100 | 26.05 | 73.52% | 22.58% | 2.82% | 0.29% | 0.11% |

Percentages use service time summed across all four validators in each run;
medians of components need not sum exactly to 100%. At 100 offered TPS, the
median run's mean sync cost was 6.43 ms/event and mean write cost 1.95 ms/event.
There are five journal events per completed transaction per validator. All six
runs finalized every transaction and passed recovery. This identifies journal I/O
as the primary service cost on this host; it does not apportion end-to-end latency
or predict throughput after batching. All validators share the same host/storage,
and other development activity was present. Evidence with per-validator timings,
latency distributions and build metadata is in
[quorum-e2e-service-costs.json](https://git.anuna.io/anuna-research/cbcl-rs/src/commit/96d5858d427fb1e371e0a8f13ddf0b23c6c6c8f2/outputs/quorum-e2e-service-costs.json).


## Durable group commit

The default `--journal-batch-size 64 --journal-batch-wait-ms 1` collects at most
64 requests, waiting up to 1 ms after the first request. Already queued work is
drained within that bound. Size 1 selects the original per-event sync path for
comparisons; the maximum size is 128 and the maximum wait is 10 ms.

`Replica::commit_group` validates at most 256 ordered events with the ordinary
protocol guards. It privately stages touched-entry updates under an exclusive
mutable borrow and undoes them before persistence, including on rejection or
unwinding. It never clones retained history. The host serializes the whole group
before any write, performs one `write_all` and `sync_all`, then the engine applies
the validated updates and returns signing requests. No vote is signed or sent
before that barrier. Invalid groups restore state before serial fallback isolates
the bad request. All other protocol APIs retain per-event durability.

The optional `BatchJournal` trait requires complete-group durability on success
and no append on a returned error. Ambiguous I/O stops the signer. An interrupted,
unacknowledged group may recover as a complete prefix; torn records fail closed.
This adds a storage optimization, not consensus or a stronger progress promise.
Its preservation contract and tests are recorded in
[SPEC-032](../../specs/SPEC-032-quorum-local-update-cost.md#con-3201-private-staging-and-durable-publication).

Three paired release runs, each 100 transactions at 100 offered TPS, 20 ms
one-way delay and a 5-second deadline, produced these medians:

| Durability mode | Finalized TPS | p50 | p95 | p99 | Within 1 s | Total syncs |
|---|---:|---:|---:|---:|---:|---:|
| Per event | 26.27 | 2273.01 ms | 2745.39 ms | 2785.73 ms | 16% | 2004 |
| Group commit | 90.64 | 115.00 ms | 124.75 ms | 130.90 ms | 100% | 461 |

Sync counts include initialization and all four validators. All 600 transactions
finalized and all journals recovered. These short runs on shared host/storage
show improvement for the same offered workload, not maximum sustainable TPS.
[Aggregate evidence](https://git.anuna.io/anuna-research/cbcl-rs/src/commit/96d5858d427fb1e371e0a8f13ddf0b23c6c6c8f2/outputs/quorum-e2e-group-commit.json) includes per-run
latency distributions, service profiles, sync counts and build metadata.


## Above-100-TPS load sweep

An unchanged release build was exercised at 250, 500, 1000, 1250, 1500 and
2000 offered TPS. Each offered window lasted five seconds, with four validator
processes and one client sharing an 8-logical-CPU macOS AArch64 host. Settings
were 20 ms one-way delay, 64-request/1 ms group commit, a five-second transaction
deadline and 16384 maximum in-flight transactions. No concurrent builds/tests
ran during measurements. The 1000 and 1500 TPS points have three repetitions;
other points are single runs. Throughput includes transaction drain time.

| Offered TPS | Runs | Median finalized TPS | p99 finality (median across runs) | Within 1 s | Timed out |
|---:|---:|---:|---:|---:|---:|
| 250 | 1 | 244.53 | 138.42 ms | 100.0% | 0 |
| 500 | 1 | 488.05 | 135.36 ms | 100.0% | 0 |
| 1000 | 3 | 976.93 | 123.42 ms | 100.0% | 0 |
| 1250 | 1 | 1222.09 | 153.90 ms | 100.0% | 0 |
| 1500 | 3 | 1464.49 | 125.91 ms | 100.0% | 0 |
| 2000 | 1 | 807.28 | censored ≥5000 ms | 29.1% | 2222 |

The p99 at 2000 offered TPS uses the all-submitted population and is censored;
completed-only p99 is available in the raw report. Timeout counts sum across
repetitions, and within-one-second fractions use all offered transactions.
All 22500 transactions at 1500 offered TPS finalized within one second;
per-run p99 ranged from 125.35 to 130.64 ms. Every journal recovered, with zero
invalid votes, transport errors or client-overload drops across the sweep.
At 2000 offered TPS, 2222 of 10000 transactions missed the five-second deadline.
The drop in finalized throughput at overload includes this timeout drain and
excludes transactions without a verified certificate by their deadline; it is
not the validators' raw event-processing rate.

The earlier ~1300 TPS serial CPU estimate extrapolated low-load wall-clock
service costs and was not a hard ceiling. Larger batches amortize I/O better;
the measured higher-load results supersede that capacity estimate.
These short runs establish a repeatable 1500 offered TPS point with subsecond
finality, not maximum sustainable capacity. A representative long-duration
multi-host run remains necessary for deployment-level claims.

Reproduce an individual 1500 TPS run with a new output directory:

```sh
target/release/cbcl-quorum-e2e --transactions 7500 --rate 1500 \
  --delay-ms 20 --timeout-ms 5000 --max-inflight 16384 \
  --journal-batch-size 64 --journal-batch-wait-ms 1 \
  --out /tmp/cbcl-finality-1500
```

[Full sweep evidence](https://git.anuna.io/anuna-research/cbcl-rs/src/commit/96d5858d427fb1e371e0a8f13ddf0b23c6c6c8f2/outputs/quorum-e2e-load-sweep.json) includes all ten
reports, build/host metadata, service timings and recovery checks. Raw run
folders remain private because they contain validator signing keys.

## Memory diagnostic

Diagnostic reruns sampled client/validator RSS with `ps` approximately every
100 ms and captured system-wide `vm_stat` counters before/after each full run
(including recovery). At 1500 offered TPS, peak combined client/four-validator
RSS was 378.88 MiB; at 2000 offered TPS it was 465.95 MiB. Peak individual
validator RSS was 87.58 and 105.17 MiB respectively. The host has 8 GiB RAM.
Neither run recorded any system swap-ins or swap-outs. System memory compression
and small pageout counts did occur; RSS excludes compressed memory and kernel
filesystem cache, and system counters also include unrelated host activity.

The 2000 TPS diagnostic still overloaded despite the modest resident footprint,
while 1500 TPS finalized everything within one second. This does not support
RAM capacity exhaustion as the cause of the overload cliff. The earlier
uninstrumented 2000 TPS run spent approximately 47% of validator service time in
journal syncing, 16% writing, and 27% signature verification. Profiling memory
bandwidth/cache behavior and long-lived history growth are separate questions.
`ps` sampling adds overhead, so diagnostic throughput is not substituted for the
uninstrumented sweep. Both diagnostic runs passed journal recovery.

[Memory evidence](https://git.anuna.io/anuna-research/cbcl-rs/src/commit/96d5858d427fb1e371e0a8f13ddf0b23c6c6c8f2/outputs/quorum-e2e-memory-probe.json) includes RSS
samples, paging/compression deltas, timing reports and measurement limitations.

## CPU diagnostic

A separate diagnostic sampled cumulative per-process CPU `TIME` with `ps` at
approximately 100 ms intervals. CPU-time deltas during roughly seconds 1–4 after
launch (inside the offered-load window, excluding drain) gave:

| Offered TPS | Client CPU equivalents | Each validator CPU equivalents | Combined CPU equivalents |
|---:|---:|---:|---:|
| 1500 | 1.15 | 0.63 | 3.67 |
| 2000 | 1.27 | 0.55 | 3.48 |

One CPU equivalent means one second of process CPU time per elapsed second;
process totals include all threads. The host has eight logical CPUs. During the
2000 TPS diagnostic, journal writes/syncs accounted for approximately 66% of
validator service wall time. These results do not show benchmark-wide CPU
exhaustion and support synchronous journal waits as a major limiting factor.
They do not rule out a hot client thread, per-thread limits, unrelated host load,
or memory/cache stalls. Thread affinity and per-thread CPU were not measured.
The full evidence also records a longer middle-80% live-validator window, which
can include drain and should not be compared as steady offered-load utilization.
Both runs passed recovery. Sampling adds overhead; diagnostic finality/throughput
is not substituted for the uninstrumented load sweep.

[CPU evidence](https://git.anuna.io/anuna-research/cbcl-rs/src/commit/96d5858d427fb1e371e0a8f13ddf0b23c6c6c8f2/outputs/quorum-e2e-cpu-probe.json) includes CPU-time samples,
window definitions, service profiles and end-to-end results.



## Recheck after removing preverification

The restored inline-verification/group-commit implementation was rebuilt in
release mode and run three times each at 1500 and 2000 offered TPS. Each run
used five seconds of offered load, 20 ms one-way delay, a five-second transaction
deadline, 64-request/1 ms group commit and 16384 maximum in-flight transactions.
Four validators and one client shared the same eight-logical-CPU macOS host.
Original input-queue behavior was restored. No deliberate concurrent builds,
tests or profiling were launched during these measurements.

| Offered TPS | Median finalized TPS | p50 | p95 | p99 | Within 1 s | Timeouts / offered |
|---:|---:|---:|---:|---:|---:|---:|
| 1500 | 1463.35 | 120.75 ms | 127.85 ms | 154.47 ms | 100.00% | 0 / 22500 |
| 2000 | 744.36 | 4113.65 ms | ≥5000 ms (censored) | ≥5000 ms (censored) | 27.22% | 8360 / 30000 |

Quantiles and throughput are medians of three per-run results. Quantiles include
all submitted transactions, with censored deadlines where indicated. One-second
fractions and timeout counts aggregate all three runs. At 1500 offered TPS all
22500 transactions finalized within one second, but per-run p99 varied from
125.92 to 798.61 ms; the median must not obscure that variation. At 2000 offered
TPS, 8360 of 30000 transactions missed their observation deadline. There were no
client-overload drops, invalid votes or transport errors. All six runs passed
recovery, and all four validators' final counts and pool values matched the
client-observed completions. These are short local tests, not sustained capacity
or deployment-level finality guarantees.

[Restored implementation results](https://git.anuna.io/anuna-research/cbcl-rs/src/commit/96d5858d427fb1e371e0a8f13ddf0b23c6c6c8f2/outputs/quorum-e2e-restored-inline.json)
contain every report, build/host metadata, service profiles and recovery results.


## Saturation between 1500 and 2000 offered TPS

Two five-second offered-load runs at each intermediate rate (ascending then
descending order) used the restored inline implementation and the same settings:
four validators and one client on the eight-logical-CPU macOS host, 20 ms
one-way delay, 64-request/1 ms durable group commit, a five-second deadline and
16384 maximum in-flight transactions. No deliberate concurrent builds/tests or
profiling ran during these measurements.

| Offered TPS | Finalized TPS (median of two) | p99 range | Within 1 s (all offered) | Peak client outstanding range |
|---:|---:|---:|---:|---:|
| 1600 | 1561.76 | 128–136 ms | 100.00% | 208–224 |
| 1700 | 1635.91 | 277–298 ms | 100.00% | 474–507 |
| 1800 | 1313.90 | 2236–2306 ms | 58.30% | 2817–2876 |
| 1900 | 1043.44 | 4446–4722 ms | 34.32% | 4625–4850 |

The one-second-finality knee in these short runs falls between 1700 and 1800
offered TPS. Queue growth is already visible at 1700: first-second submission
cohorts had median finality around 124–126 ms, while last-second cohorts rose to
236–268 ms. At 1600, cohort medians stayed approximately flat. Both 1700 TPS
runs finalized all 17000 transactions within one second. At 1800 and 1900 TPS, every transaction still finalized before its
five-second deadline, but substantial queued work extended the drain interval.
The finalized-TPS metric divides completions by the entire measurement window,
including drain; it is not raw journal event throughput. All eight runs passed
recovery, with zero invalid votes, transport errors, client-overload drops or
observation timeouts.

Peak outstanding work and per-second submission-cohort latencies were
reconstructed from client submission and certificate-verification timestamps.
They describe work across the full pipeline, not a measured individual validator
queue. The evidence includes those traces in aggregate to expose growing delay
rather than treating low whole-run throughput as a protocol safety failure.
These short local results do not establish a long-duration safe operating limit.

[Intermediate-rate evidence](https://git.anuna.io/anuna-research/cbcl-rs/src/commit/96d5858d427fb1e371e0a8f13ddf0b23c6c6c8f2/outputs/quorum-e2e-saturation-knee.json)
contains all eight reports, recovery/state checks, service profiles and cohort
summaries. Full raw traces remain in private run directories.


The saturation profiles point to the serialized validator service loop, with
journal I/O becoming the largest service component. At 1700 offered TPS, journal
write/sync consumed 40–41% and signature verification about 45% of service wall
time; at 1900 these were 61–62% and 29–30%. Events per sync fell from 92–95 to
56–57, while mean write-plus-sync wall time rose from 4.1–4.4 to 5.7–6.2 ms.
Operation, Effects and Final requests share one FIFO state worker; blocking
journal I/O prevents it from processing any phase. These observations support
queueing and reduced I/O amortization, but do not establish which is cause versus
consequence. Per-queue residence and per-round client processing delays have not
been measured, so exact end-to-end attribution remains open.


## Queue and phase diagnosis: client timeout scanning

Detailed queue diagnostics are opt-in so normal measurements do not pay for
extra per-frame timers, metric locks and phase samples:

```sh
CARGO_PROFILE_RELEASE_OPT_LEVEL=3 CARGO_PROFILE_RELEASE_LTO=false \
  cargo build --release -p cbcl-quorum-e2e --features queue-diagnostics
```

Rebuild without that feature for ordinary throughput runs. Reports explicitly
mark `queue_diagnostics_enabled`. The diagnostic build measures local
JSON-decode-to-channel-dequeue time, group collection holds, request/response
transport lateness beyond the configured artificial delay, socket writes,
client handler time, client timeout scans, observed quorum-round completion
latency, and group composition/service by operation-only/effects-only/final-only/
mixed batches. All timestamps are local monotonic clocks. No cross-process clock
subtraction is used. Per-round samples describe observed phase completions only;
the existing end-to-end metrics still include censored stalls.

The diagnostic 1900 offered TPS run showed client response-queue p99 of 3.41 s,
while maximum per-validator/per-phase receive-queue p99 was 26.5 ms. Outgoing
transport excess-delay p99 stayed below about 3.4 ms. The client spent 4.59 s
scanning all pending transactions for timeouts and 4.60 s handling responses.
This corrects the earlier journal-focused attribution: the benchmark client's
linear pending-map scan on every processing iteration creates substantial
feedback as backlog grows. Validator service-cost percentages alone do not
identify the transaction's critical-path wait.

A controlled, temporary client-only variant scanned at most once per millisecond,
retaining every diagnostic timer and the existing per-response timeout guard.
Two runs at 1900 offered TPS, 9500 transactions and unchanged validators produced:

| Client scan policy | Finalized TPS | Client queue p99 | Total scan time |
|---|---:|---:|---:|
| Temporary once/ms, run 1 | 1615.94 | 55.98 ms | 127.18 ms |
| Temporary once/ms, run 2 | 1618.95 | 132.36 ms | 144.30 ms |
| Original every-iteration scan, restored | 802.78 | 3454.77 ms | 4631.95 ms |

Both temporary runs finalized all transactions before their five-second deadline;
88.6–91.9% finalized within one second. The restored run timed out 1794/9500.
Every run passed recovery. Reducing the client bottleneck exposed more validator
queueing (roughly 402–484 ms maximum per-phase p99), so this is not evidence of
unlimited validator capacity. The probe was reverted byte-for-byte before adding
the diagnostic feature gate. The temporary throttling variant was never adopted. The deadline-ordered queue
implemented below subsequently replaced the original full scan.

Profiling shifts saturation and these are single diagnostic runs, not replacement
capacity figures. Validator response-transport snapshots precede Stop enqueue
and can omit a few outstanding writes. Group composition timing covers grouped
attempts; serial mode retains the existing aggregate service profiles. Quantiles
from different queues cannot be added to decompose one transaction.

[Queue evidence](https://git.anuna.io/anuna-research/cbcl-rs/src/commit/96d5858d427fb1e371e0a8f13ddf0b23c6c6c8f2/outputs/quorum-e2e-queue-diagnostics.json) includes four
instrumented load points. [Controlled scan probe](https://git.anuna.io/anuna-research/cbcl-rs/src/commit/96d5858d427fb1e371e0a8f13ddf0b23c6c6c8f2/outputs/quorum-e2e-timeout-scan-probe.json)
includes the temporary variants and restored baseline. Tests check phase counts,
group event/sync accounting, recovery, and absence of diagnostic samples in the
normal build. Core protocol and journal semantics are unchanged.


## Deadline-ordered client expiration

The client now enqueues `(deadline, transaction ID, submission sequence)` once
per submitted transaction. Fixed timeouts and monotonic submission times keep
those entries in FIFO deadline order. Each processing iteration checks only the
front and pops entries that are due. Completed submissions leave stale entries
that are ignored when popped. A sequence match prevents an older timer from
expiring a newer request with the same ID. Client-overload drops get no timer.

Submission timestamps, configured timeout, pre-vote expiry check and the
post-verification finality deadline check are unchanged. Timer expiration still
only records a censored client observation; it never cancels a protocol operation
or releases rights. There is no periodic scan interval or weakened deadline.

An idle expiration check is O(1); each timer is inserted and removed once. Due
entries still require O(log pending) map lookup/removal. Timer storage includes
completed submissions until their deadlines, is approximately bounded by the
submission volume within the timeout window, and is capped by the run's total
transaction limit. Diagnostic timing is now named `timeout_collection_ms`;
historical evidence retains the earlier `timeout_scan_ms` field.

Deterministic tests compare expiration against the original full-map scan with
completion and ID reuse, and check exact deadline boundaries, stale timer entries
and no duplicate stalled outcomes. Normal and diagnostic-mode process tests,
scoped Clippy, release build and independent semantics/complexity review pass.

Three new uninstrumented release runs at each load, each five seconds of offered
transactions, retained four validators, real Ed25519, durable 64-request/1 ms
group commit, 20 ms one-way delay, a five-second deadline and max in-flight 16384:

| Offered TPS | Median finalized TPS | Median p50 | Median p95 | Median p99 | Within 1 s |
|---:|---:|---:|---:|---:|---:|
| 1900 | 1781.26 | 293.66 ms | 467.60 ms | 469.96 ms | 100.00% |
| 2000 | 1749.70 | 597.46 ms | 954.59 ms | 965.24 ms | 92.59% |

All 58500 transactions finalized before the five-second deadline, with zero
client-overload drops, invalid votes or transport errors; all journals recovered.
At 1900 offered TPS, all 28500 finalized within one second and per-run p99 was
462–531 ms. At 2000, aggregate one-second success was 92.59%; per-run p99 varied
from 892 to 1161 ms, so this is not uniformly subsecond. Throughput includes drain.
These five-second local runs do not establish long-duration capacity. Queue
instrumentation was disabled and no concurrent builds/tests/profiling were
intentionally run during the measurements.

[Deadline FIFO results](https://git.anuna.io/anuna-research/cbcl-rs/src/commit/96d5858d427fb1e371e0a8f13ddf0b23c6c6c8f2/outputs/quorum-e2e-deadline-fifo.json) include all
six reports, client-source digest, build/host metadata and recovery checks. Earlier
full-scan and throttled-probe results remain historical evidence; the temporary
throttling variant is not present in the implementation.


## Canonical signing-byte reuse experiment (removed)

A host-only prototype stored immutable actor snapshots plus their signing bytes
and immutable prepared votes plus canonical vote bytes. Actor reuse required full
Act equality; certificate reuse required full vote equality. Every signature was
still verified using current keys and strict Ed25519. Wire formats, core protocol
APIs, content hashing and core object-size encoding were unchanged. Tests checked
stale envelope/address attacks, signature/context mutation, duplicate signers,
key rotation and signature-verification counts; independent guard review accepted
these boundaries. The prototype eliminated six client vote encodings per finalized
transaction (seven preparations versus thirteen uses in this workload).

Three paired release repetitions per load alternated baseline/candidate order,
with five-second offered windows, 20 ms one-way delay, five-second deadlines,
16384 maximum in-flight, and durable 64-request/1 ms group commit. Detailed queue
diagnostics were disabled. Actual saved baseline and candidate binaries were
used; no concurrent builds/tests/profilers were deliberately launched.

| Offered TPS | Implementation | Median finalized TPS | Median per-run p99 | Within 1 s (all offered) |
|---:|---|---:|---:|---:|
| 1900 | baseline | 1644.96 | 1072.08 ms | 88.86% |
| 1900 | candidate | 1708.26 | 642.17 ms | 100.00% |
| 2000 | baseline | 1731.75 | 1007.93 ms | 97.76% |
| 2000 | candidate | 1719.04 | 1069.18 ms | 86.52% |

At 1900 TPS the candidate improved median throughput by approximately 3.85% and
tail latency, but at 2000 TPS throughput declined approximately 0.73% and the
one-second completion fraction fell from 97.76% to 86.52%. All 117000 transactions
finalized before their deadlines and all twelve recovery audits passed. These
are shared-host short runs, not a universal conclusion about prepared canonical
representations. Actor snapshots added retained memory and construction work;
most actor envelopes were encoded only once in the baseline's normal path anyway.

Decision: remove this prototype because it did not consistently improve the tested
end-to-end workload enough to justify the additional representation/cache code.
The deadline FIFO fix remains. Earlier performance evidence is historical; the
new paired numbers should not be mixed with earlier isolated runs.
[Experiment evidence](https://git.anuna.io/anuna-research/cbcl-rs/src/commit/96d5858d427fb1e371e0a8f13ddf0b23c6c6c8f2/outputs/quorum-e2e-canonical-bytes.json) retains all
public reports, source/binary digests, counters and review scope. Private run
fixtures were deleted only after recovery/report capture to bound disk use;
prototype source snapshots remain outside the repository in the comparison folder.


## Local certificates from verified immutable votes

The client now verifies each incoming vote strictly once and stores a private,
non-serializable `VerifiedVote` holding the owned immutable vote and the exact
public-key bytes used to verify it. The type can only be created by the checked
constructor; its vote accessor is immutable. A local certificate builder requires
a quorum of tokens and rechecks context, payload, vote kind, committee membership,
map-key/signer consistency, distinct signers and current public-key bindings.
If the key mapping changes, stale tokens are rejected. It then constructs the
same raw certificate without repeating the same curve operations. This removes
six redundant client signature checks per completed transaction in the benchmark.

Full verification remains mandatory for raw/external certificates. Validators
and journal recovery use those unchanged paths. No wire `verified` flags, actor
signature-result cache, worker pool, weaker threshold, prehash signature scheme
or changed deadline rule is introduced. A received certificate cannot acquire
trusted-token status by deserialization. Finality timing includes strict checks
of all constituent votes and the local quorum/domain/current-key proof checks.
The output still contains ordinary certificates that independent parties fully
verify; existing process tests do that on the saved transaction outcomes.

Tests verify that three token constructions perform exactly three signature
checks, repeated local construction adds none, and independent raw-certificate
verification adds three. Invalid signatures, wrong payload/kind, insufficient
quorum, duplicate/mis-keyed signers, a different genuine instance, and key rotation
are rejected. Static independent guard review accepted these boundaries. Default
parallel tests and diagnostic serial tests passed, as did scoped all-feature
Clippy. An initial parallel diagnostic test run hit a transient reopening failure
in the existing journal owner-lock test during concurrent process tests; the
serial rerun passed without a production journal change.

Three paired release repetitions per offered load alternated baseline/candidate
order by trial. The saved baseline binary retained duplicate verification; the
candidate used tokens. Each run offered traffic for five seconds with four
validators and one client on the shared eight-logical-CPU macOS host, real
Ed25519, durable 64-request/1 ms group commit, 20 ms one-way delay, a five-second
deadline and max in-flight 16384. Detailed queue diagnostics were off.

| Offered TPS | Implementation | Median finalized TPS | Median p99 | Within 1 s (all offered) | Median OS user + system CPU |
|---:|---|---:|---:|---:|---:|
| 1900 | Duplicate verification | 1701.40 | 798.88 ms | 95.91% | 35.87 s |
| 1900 | Verified-vote builder | 1715.68 | 604.93 ms | 100.00% | 32.78 s |
| 2000 | Duplicate verification | 1705.74 | 1169.11 ms | 72.78% | 37.92 s |
| 2000 | Verified-vote builder | 1756.47 | 758.86 ms | 100.00% | 34.57 s |

CPU is the external `/usr/bin/time -l` user/system usage for the whole invocation,
including startup and recovery outside the benchmark interval; it is not an
isolated client CPU measurement. Both modes use the same external accounting.
At 2000 offered TPS, median finalized throughput improved approximately 2.97%,
p99 improved approximately 35.1%, and reported whole-run CPU declined 8.83%.
All 117000 transactions across the twelve runs finalized before their deadline,
with zero invalid votes, transport errors or client-overload drops. Every recovery
audit passed. All 58500 candidate transactions finalized within one second;
candidate per-run p99 ranged from 587–656 ms at 1900 TPS and 750–846 ms at 2000.
These are five-second local runs, not long-duration or geographically distributed
capacity guarantees. Throughput includes drain, and quantiles are medians of
per-run quantiles; one-second fractions aggregate all offered transactions.

Decision: retain this small client-only change. [Paired results](https://git.anuna.io/anuna-research/cbcl-rs/src/commit/96d5858d427fb1e371e0a8f13ddf0b23c6c6c8f2/outputs/quorum-e2e-verified-votes.json)
include reports, signature counts, OS accounting, source/binary digests and review
scope. Private fixtures were deleted only after recovery/report capture to bound
disk use. Public reports and baseline binaries remain in the comparison folder.

## Journal batch tuning

Increasing the existing request batch cap from 64 to 128 improves high-load
throughput without changing signatures, quorum thresholds or durability. Each
vote still waits for its journal records to sync. This is a host configuration
change using the same binary, with no protocol change. The recommended measured
high-load preset is `--journal-batch-size 128 --journal-batch-wait-ms 1`.

Three repetitions per setting offered 2500 TPS for five seconds with four
validators and one client, real Ed25519, 20 ms fixed one-way delay, a five-second
deadline and max-inflight 16384 on the shared eight-logical-CPU macOS host.
Diagnostics were disabled. Actual offering rates were 2499.9–2500.0 TPS.

| Request cap / wait | Median finalized TPS | Median p50 | Median p95 | Median p99 | Within 1 s (all offered) |
|---|---:|---:|---:|---:|---:|
| 64 / 1 ms | 1806 | 1194 ms | 1991 ms | 2009 ms | 40.27% |
| 128 / 1 ms | 2172 | 509 ms | 825 ms | 846 ms | 100% |
| 128 / 2 ms | 2171 | 486 ms | 830 ms | 851 ms | 100% |

The 128 / 1 ms preset improved median finalized throughput by 20.25% and reduced
median p99 by 57.89%. Mean journal sync count per validator fell from 592.58 to
304 for the same 12500 transactions. Extending collection to 2 ms showed no
clear additional gain, so retain the 1 ms window. All 112500 transactions in
the repeated comparison finalized before their deadline, with no overload,
invalid votes or transport errors. Every fresh-process recovery audit passed.

The initial single-run sweep reached 2113 finalized TPS with p99 249 ms at
2200 offered TPS using 128 / 1 ms. At 3000 offered TPS it reached 2181 finalized
TPS, but p99 grew to 1926 ms and only 44.43% finalized within one second.
Increasing offered load beyond the service rate therefore builds a backlog.
These five-second tests demonstrate a local tuning gain, not sustained capacity
or a geographically distributed subsecond guarantee. TPS includes drain;
table quantiles are medians of per-run quantiles, while one-second fractions
aggregate all offered transactions. Repetitions followed the initial sweep
and were not randomized. The ordinary default remains 64 / 1 ms.

[Full batch-tuning reports](https://git.anuna.io/anuna-research/cbcl-rs/src/commit/96d5858d427fb1e371e0a8f13ddf0b23c6c6c8f2/outputs/quorum-e2e-batch-tuning.json) retain
build metadata, binary digest, all run metrics and recovery results. Private
fixtures were deleted only after successful recovery and report capture.

## Active Byzantine measurements

One validator (`@v0`) was faulty, leaving three honest validators and a quorum
of three. Three repetitions per setting used the same release binary, 128-request
/ 1 ms durable batching, 20 ms fixed one-way delay, a five-second offered-load
window, a five-second deadline and max-inflight 16384. Queue diagnostics were off.
The second repetition reversed the order of the five 2000 TPS modes. The
1500 TPS flood followup was selected after the 2000 TPS flood showed backlog.

| Scenario | Offered TPS | Median finalized TPS | Median p50 | Median p95 | Median p99 | Within 1 s (all offered) |
|---|---:|---:|---:|---:|---:|---:|
| All honest | 2000 | 1946 | 144 ms | 167 ms | 177 ms | 100.00% |
| One silent | 2000 | 1946 | 143 ms | 162 ms | 169 ms | 100.00% |
| Selective withholding | 2000 | 1950 | 132 ms | 145 ms | 152 ms | 100.00% |
| Signed effects/cancel equivocation | 2000 | 1952 | 131 ms | 141 ms | 145 ms | 100.00% |
| 8 invalid replies / request | 2000 | 1626 | 965 ms | 1454 ms | 1487 ms | 51.41% |
| 8 invalid replies / request | 1500 | 1463 | 124 ms | 142 ms | 150 ms | 100.00% |

All 172500 offered transactions across 18 runs finalized before their deadline;
there were no stalls, client-overload drops or transport errors. Every honest
validator's final count/value matched client finalizations, and all four journal
recovery audits passed in every run (including the faulty node's initialized
state). The client observed/rejected 840000 invalid signatures and verified/ignored
30000 cancellation votes; the faulty node emitted 30000 conflicting signed pairs.
Process tests independently verify the resulting raw effects certificates.

Withholding and equivocation stayed subsecond in these runs. The fixed invalid
signature flood caused verification backlog at 2000 offered TPS: only 51.41%
finalized within one second, despite no five-second timeouts. In its first run,
client signature verification took 5399 ms of the 6152 ms measurement interval
(about 88%, wall timers rather than isolated CPU time). At 1500 offered TPS the
same flood stayed subsecond in all three runs. This is an observed operating
point, not a measurement of the maximum sustainable adversarial load.

These are bounded scripted attacks on shared hardware. A compromised node skips
honest validation and durable writes, freeing resources on this host; small
throughput improvements over the honest control do not imply faults improve a
deployed network. No divergent gossip, conflicting client-spend workload,
partitions or unbounded/adaptive DoS was simulated. Five-second local results
are not sustained capacity or a geographic finality guarantee. TPS includes
drain; quantiles are medians of per-run quantiles, and fractions aggregate all
offered transactions. The first honest run had p99 531 ms versus 175–177 ms for
the later two; no warmup was excluded.

Reproduce a flood run (use a fresh output directory):

```sh
target/release/cbcl-quorum-e2e \
  --transactions 10000 --rate 2000 --delay-ms 20 \
  --timeout-ms 5000 --max-inflight 16384 \
  --journal-batch-size 128 --journal-batch-wait-ms 1 \
  --byzantine-mode invalid-flood --out /tmp/cbcl-byzantine-example
```

[Full Byzantine reports](https://git.anuna.io/anuna-research/cbcl-rs/src/commit/96d5858d427fb1e371e0a8f13ddf0b23c6c6c8f2/outputs/quorum-e2e-byzantine.json) include each
run, attack counters, build/host metadata, source/binary digests and recovery
evidence. Private fixtures were removed only after successful recovery, honest
state checks and report capture.
