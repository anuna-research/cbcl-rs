# Local quorum execution cost

Contract: [[SPEC-032-quorum-local-update-cost]]. The protocol, public APIs,
quorums, authority checks, history retention, journal format and proof limits of
[[SPEC-031-unified-quorum-dag]] are unchanged.

## Implemented changes

- Validate typed events into small owned updates without mutating state. Validated
  retries return no update. Check limits, atomically append the original event,
  then apply without additional fallible protocol guards. Remove whole-state
  cloning/equality and rollback copies. Replay uses the same preparation/application.
- Maintain per-version charge from immutable operation costs. First signature adds
  once; first cancellation-backed release subtracts once. Other transitions and
  retries do not change charge. Adoption never resets old charges. There is no
  serialized cache input or new source of capacity.
- Independently recompute the original signed/unreleased history expression after
  every debug update, including replay. Zero-cost and all-released buckets remain
  represented. Optimized builds use the derived totals without the diagnostic scan.
- Borrow stored manifests during read-only checks instead of cloning parent/held/
  refund/credit sets. Drafting still constructs its own validated cumulative sets.

The cache is an implementation optimization, not a new protocol premise. This
adds no universal Rust-source refinement theorem. Private update application can
allocate memory, but performs no further fallible protocol validation. Recovery
remains the way to reconstruct state after a crash following durable append.

## Local probe

The ignored `multi_parent::in_memory_throughput_probe` performs 1,000 one-unit
collective decrements against ample initial rights, including authoring, candidate
registration, operation certificates and effects finality. Four validators execute
serially on one Apple M2 with memory journals and test authentication. It excludes
network, real signatures, disk durability, version merges and adversarial contention.

The baseline engine is commit `83b6741`; the probe was added before changing the
engine. One baseline and three optimized runs use the same workload and build flags:

```sh
CARGO_PROFILE_RELEASE_OPT_LEVEL=3 CARGO_PROFILE_RELEASE_LTO=false CARGO_PROFILE_RELEASE_DEBUG=0 \
  cargo test --release -p cbcl-parser --test quorum_runtime \
  multi_parent::in_memory_throughput_probe -- --ignored --exact --nocapture
```

The workspace's normal release default is size optimization; the overrides above
make this a native speed-oriented comparison. It is an illustrative local sample,
not a statistically characterized or production throughput claim. Exact measured
rows, run counts, source hash and aggregate calculation are
[[quorum-local-cost-performance]]. No raw build/test transcript is vendored.

| Retained history during batch | Baseline TPS | Optimized median TPS |
|---|---:|---:|
| 0–50 | 536.8 | 3359.4 |
| 50–100 | 347.5 | 3481.6 |
| 100–250 | 156.5 | 3501.2 |
| 250–500 | 68.2 | 3587.7 |
| 500–1000 | 26.2 | 3607.8 |

Overall: 41.75 TPS before and 3565.86 median TPS after, a 85.4× local improvement.

Default retained-candidate/event limits and the absence of safe pruning are
unchanged. These measurements do not establish indefinite operation or maximum
network throughput. Durable storage and actual cryptography can dominate a deployed
system; those providers have not been benchmarked here.

## Verification

Workspace tests, no-std, all runtime checks and collective oracle regeneration
passed. The opt-in probe stays ignored during ordinary CI with no timing threshold.
The new failure test proves that failed signature append does not consume capacity,
failed release does not grant capacity, duplicate sign/release does not create
capacity and recovery reconstructs the same admission decisions. Existing shared
traces compare projected state and recovery at every step. Debug tests also execute
the independent historical charge check at every applied transition.

The real production-source mutation runner detects cache-sign/cache-release errors
with debug assertions disabled, in addition to the existing scope, history, books,
parent, release, budget, domain and persistence failures. Its durability mutant
applies adoption without appending, rather than merely skipping the update.
Compiler/import failures do not count. Compact results are
[[quorum-local-cost-mutations]] and [[quorum-local-cost-checks]].

Independent review accepted source and inspected final execution evidence:
[[quorum-local-cost-review]]. Scoped Clippy reports no primary diagnostics in the
modified engine/test files; unrelated existing warnings remain. This does not
claim a clean global Lean/Rust lint or specs-only vault. Output-page vault
integration remains coordinator-owned backlog.
