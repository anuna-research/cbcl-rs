---
id: SPEC-032
title: Local quorum transition cost
version: 0.1.0
status: implemented
last-updated: 2026-10-31
---

# Local quorum transition cost

## Orientation

Reduce avoidable copying and history scans in the existing DAG runtime without
changing its admission rules or public protocol. Validate an event into an owned
local update without mutating state. Append the original event atomically, then
apply the validated update without further fallible guards. A rejected event or
failed append leaves all state and signing requests unchanged; retries still
stutter. Recovery uses the same validation/update path.

Per-version charge totals are derived caches, never serialized authority. Signing
adds immutable operation cost once; first release subtracts it once. Adoption does
not reset totals. Debug executions independently compare caches with the original
history sum. Stored version manifests are borrowed during read-only checks.

The protocol and proof boundaries remain [[SPEC-031-unified-quorum-dag]].
[[SPEC-032-quorum-local-update-cost#CON-3200]] governs persistence/cache invariants;
[[SPEC-032-quorum-local-update-cost#TEST-3200]] defines acceptance.

## Amendment Channels

The user requests easy performance improvements. This Tier 1 implementation
optimization changes no authority, quorum, numeric budget, history retention or
liveness contract. Independent review applies. Host cryptography and physical
journal assumptions remain; no source-extraction proof is introduced.

## REQ-3200: Local updates preserve protocol behavior

All observable admission, rejection, retry and recovery behavior MUST remain
consistent with [[SPEC-031-unified-quorum-dag]]. Routine transitions MUST NOT clone
or compare the whole state to detect changes. Read-only version lookup SHOULD
borrow stored metadata. Overflow MUST continue to reject before persistence.
Validates: [[SPEC-032-quorum-local-update-cost#TEST-3200]].

## CON-3200: Preparation, persistence and derived charge

Preparation MUST recognize the complete typed event using existing guards, return
no update for a validated retry, and otherwise return an owned update. It MUST NOT
mutate any state. Commit MUST check the event limit and atomic journal append
before applying the update. Applying a prepared update MUST introduce no fallible
validation or exposed signing request before durable append. Replay MUST validate
and apply each event, reconstructing every cache from original journal evidence.

For each version, cached charge MUST equal the sum of immutable costs of all own
signed operations in that version whose released marker is false. First signing
adds cost once; first release subtracts cost once. Retries and all other steps
MUST preserve charge. Account/collective scope and per-version scaled inequalities
remain unchanged. Caches MUST NOT be accepted from a serialized snapshot. Debug
checks MUST recompute the independent historical expression after updates.

## TEST-3200: Preservation and measured cost

Shared Lean/Rust traces, all runtime tests, recovery, failed append/CAS and real
production guard mutations MUST pass. Explicit tests MUST check that failed
sign/release append leaves cached capacity unchanged. Duplicate releases MUST NOT
create capacity; replay MUST restore the same signing decisions. Debug historical
charge checks MUST run throughout normal execution/recovery tests. Workspace,
no-std, formatting and changed-file lint checks MUST pass.

An opt-in optimized-build probe MUST report batch throughput against growing
retained history. It MUST use the baseline's four serial validators, test
authentication and memory journal. It MUST clearly exclude network/real crypto/
durable-write claims and carry no timing threshold in CI. Do not claim production
TPS from this measurement. Independent review MUST inspect guards and write order.
Validates: [[SPEC-032-quorum-local-update-cost#REQ-3200]].

## Implementation and evidence

The runtime uses immutable preparation, durable append and owned update application.
Stored manifests are borrowed; charges are derived from signed/released evidence.
Runtime/recovery tests, shared traces, workspace/no-std and changed-file lint pass.
Guard mutations include cache errors with debug assertions disabled. Independent
review accepted the code and inspected execution evidence. The opt-in probe has
no timing gate; exact measurements and limits are [quorum-local-cost-evidence](https://git.anuna.io/anuna-research/cbcl-rs/src/commit/96d5858d427fb1e371e0a8f13ddf0b23c6c6c8f2/outputs/quorum-local-cost-evidence.md),
[quorum-local-cost-performance](https://git.anuna.io/anuna-research/cbcl-rs/src/commit/96d5858d427fb1e371e0a8f13ddf0b23c6c6c8f2/outputs/quorum-local-cost-performance.json) and [quorum-local-cost-review](https://git.anuna.io/anuna-research/cbcl-rs/src/commit/96d5858d427fb1e371e0a8f13ddf0b23c6c6c8f2/outputs/quorum-local-cost-review.md). Output-page
integration into the specs-only vault remains coordinator-owned backlog.

## REQ-3201: Bounded durable group commit

Trace: [[#REQ-3200]], [[#CON-3200]], [[#TEST-3201]].

Measured end-to-end service cost is dominated by journal writes and syncing.
An optional group path MUST amortize that I/O without weakening durable-before-
signing semantics or changing the accepted protocol events. The serial path
MUST remain available for comparison. The host MAY wait up to a configured short
batch window; no new async progress guarantee follows.

## CON-3201: Private staging and durable publication

Trace: [[#REQ-3201]], [[#TEST-3201]].

The batch extension MUST accept at most 256 candidate/certificate/sign/effect
events. Ordinary event guards MUST validate the ordered group. Private staging
under an exclusive mutable borrow MAY apply reversible touched-entry updates;
it MUST restore exact state and sequence before calling the durable journal and
on rejection or unwinding. This bounded staging is an explicit extension to
[[#CON-3200]]; the serial preparation path remains immutable. No retained-history
clone, external callback with state access, or signing request may escape staging.

A batch journal success MUST mean the complete ordered group is durable at the
expected sequence. A returned error MUST mean no append. Ambiguous write/sync
failures MUST stop the signer. Only after success may the engine apply prepared
updates and return signing requests. Retries MUST remain journal stutters.
An interrupted unacknowledged batch may recover as a complete prefix; torn
records MUST fail closed. Recovery MUST use ordinary event replay, never caches
or serialized staging state. The host MUST fence competing journal owners.

The benchmark host defaults to at most 64 requests and a 1 ms collection window;
size 1 selects the unchanged per-event durability path. Invalid groups MUST
restore staging before per-request fallback. Final certificate observation MUST
also be durable before shutdown statistics are acknowledged.

## TEST-3201: Group safety and measured benefit

Trace: [[#REQ-3201]], [[#CON-3201]].

Tests MUST cover dependent candidate/sign events, duplicate groups, invalid
suffix rollback, event limits, failed CAS/append, unwinding, and exact serial/
group event-log and recovered-state equivalence. Rejected groups MUST expose no
signing requests and consume no cached capacity. Journal tests MUST verify one
sync per group, pre-write envelope rejection, contiguous records, owner fencing,
and refusal of torn suffixes. Process tests MUST retain real signatures,
certificate verification, quorum stalls and restart recovery. Paired release
runs MUST report throughput, latency, one-second fractions, sync counts and
recovery with identical offered load/delay; report sample sizes and host scope.
Independent review MUST inspect rollback, durability order and vote publication.

### Group implementation and evidence

Synthesis: measured I/O saturation motivated group commit; the synchronous
journal contract ruled out returning success before sync. Reversible touched-
entry staging preserves the serial guards without copying retained history.
Independent review identified a grouped response-delivery behavior mismatch and
missing exact-capacity/certificate rollback coverage; both were corrected.

The host/core group tests pass, including exact-capacity rollback, unwind,
failed append/CAS, certificate/effect undo, envelope rejection before writing,
serial equivalence and recovery. Workspace tests (1,537 passed, 30 ignored),
shared Lean-derived transition traces, native no-std and actual WASM no-std
builds pass. Changed-file formatting and scoped Clippy pass; core Clippy allows
only the five existing lint categories recorded by the baseline run.
Independent safety/preservation review accepted the implementation.

Three paired 100-transaction release runs at 100 offered TPS and 20 ms one-way
delay changed median completed throughput from 26.27 to 90.64 TPS and median
p99 from 2785.73 to 130.90 ms. Median sync count across four validators fell
from 2004 to 461. All 600 transactions finalized; every journal recovered.
The grouped path uses the default 64-request bound and 1 ms collection window.
Evidence: [archived quorum-e2e-group-commit.json](https://git.anuna.io/anuna-research/cbcl-rs/src/commit/96d5858d427fb1e371e0a8f13ddf0b23c6c6c8f2/outputs/quorum-e2e-group-commit.json). This is a same-workload
comparison on shared host/storage, not a maximum capacity or async liveness claim.

## Retired experiment IDs: REQ-3202, CON-3202, TEST-3202

Signature preverification ahead of journal I/O showed no throughput benefit on
the benchmark host and worsened overload results. The experiment, configuration,
cache and worker pipeline were removed; these IDs remain reserved.
