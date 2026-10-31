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
no timing gate; exact measurements and limits are [[quorum-local-cost-evidence]],
[[quorum-local-cost-performance]] and [[quorum-local-cost-review]]. Output-page
integration into the specs-only vault remains coordinator-owned backlog.
