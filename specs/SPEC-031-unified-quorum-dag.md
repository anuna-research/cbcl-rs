---
id: SPEC-031
title: One DAG protocol for quorum counters
version: 0.2.0
status: implemented
last-updated: 2026-11-01
---

# One DAG protocol for quorum counters

## Orientation

`(certification quorum-budget ...)` selects the consensus-free multi-parent DAG
protocol. The host supplies authentication, storage and transport, not a handoff
algorithm. `Context::from_instance` constructs that protocol directly. No protocol
selector or backward-compatible single-parent runtime remains.

Account-owned counters retain separate resource scopes and transfer semantics.
Collective counters share one scope across actors. Adoption requires the current
scope's active version among the parents and every historical signature for that
scope in held. Other accounts' signatures do not become held obligations for this
account. Parent sets cannot cross scopes; incoming finalized transfer credits can.
Unique-ID genesis-based books, actual refund/credit certificates and durable
journal guards remain. Signatures, fences and releases are never reset.

This replaces the runtime selection contract in
[[SPEC-030-rust-multi-parent-refinement]]. Its collective Lean adapter and shared
traces still apply after constructor simplification. Account DAG execution is
covered by concrete transfer, resource-isolation and adversarial tests plus review;
it is not newly claimed as formally refined to the single-pool Lean model.
No old journal migration or consensus fallback is supplied.
[[SPEC-033-owned-counter-lifecycle]] adds the permanent account-owned completion
lifecycle and its conditional progress contract. It amends this specification's
earlier prohibition on all seals; collective DAG contention remains unchanged.

[[SPEC-031-unified-quorum-dag#CON-3100]] defines the sole protocol and scoped
adoption. [[SPEC-031-unified-quorum-dag#TEST-3100]] defines acceptance.

## Amendment Channels

The user explicitly rejects backward compatibility for the single-parent protocol.
This Tier 1 change removes runtime APIs and serialized variants rather than
retaining a host switch. Existing business syntax and account balances remain.
Independent cross-model review and Orientation comprehension apply. The coordinator
owns the implementation and account-model formalization backlog. Deployment and
migration are outside this change.

## REQ-3100: Language-selected DAG semantics

Every quorum-budget context MUST use multi-parent adoption. There MUST be no host
handoff selector, legacy checkpoint quorum, consensus-selected successor or legacy
install API. Account-owned permanent seals and full-capacity continuation are
governed exclusively by [[SPEC-033-owned-counter-lifecycle#REQ-3300]] and
[[SPEC-033-owned-counter-lifecycle#REQ-3301]]; they do not restore the removed
checkpoint protocol. Unknown legacy serialized events and vote variants MUST reject.
Validates: [[SPEC-031-unified-quorum-dag#TEST-3100]].

## REQ-3101: Account and collective resource isolation

Account-owned counters MUST retain authorized transfers and independent budgets.
Version parents and held debits MUST belong to the target resource scope. Adoption
MUST cover every historical signature from that scope, including released and
zero-cost signatures. Certified incoming credits MUST be counted once. Collective
actors MUST continue to share one scope. Durability and certificate checks MUST
remain enforced.
Validates: [[SPEC-031-unified-quorum-dag#TEST-3100]].

## CON-3100: Construction, graph and scoped state

`Context::from_instance` recognizes the existing certification and ownership
clauses. Concurrent quorum updates use DAG adoption; account completion follows
[[SPEC-033-owned-counter-lifecycle#CON-3300]]. Metadata input uses the typed
VersionManifest/DagVersion grammar from
[[SPEC-030-rust-multi-parent-refinement#CON-3000]], with `account` ranging over
pinned accounts or the collective pool. Hash-bound lifecycle phase and DAG identity
v2 are defined by [[SPEC-033-owned-counter-lifecycle#CON-3300]].
Legacy Event/VoteKind variants MUST NOT be recognized by serde. No automatic
conversion of old logs is performed.

A version MUST have known same-scope parents, increasing rank, cumulative sets,
verified authority and exact nonnegative books. Held operations MUST originate in
that scope and have lower source rank. Credits MAY originate in another account,
but MUST target this scope and have actual effects certificates. Refunds MUST have
cancellation certificates and refer to held IDs.

`draft_version` derives its scope from its parents. `version_snapshot(account)`
projects the requested scope's active/visited/known metadata and own-origin journals.
Adoption MUST retain the whole machine state and require inclusion of all own-origin
signatures for the target scope. Other-scope signatures MUST NOT block adoption.
Account authority requires that account's actual actor; collective authority uses
eligible actual cast actors. Counter act signing and certificate quorums retain
the existing verification and atomic persistence discipline.

## TEST-3100: Unified runtime acceptance

Existing account and collective language/runtime tests MUST use DAG versions.
Tests MUST cover account/headroom transfers, incoming credits, shared budgets,
delayed certificates, cancellation/release and cross-scope rejection. Missing own
history, harmless other-scope history, branch joins and durable recovery MUST also
be covered.
Legacy variant deserialization MUST reject. Removed public API/type names MUST be
absent from runtime source. Collective Lean/Rust shared traces and weakened-guard
mutations MUST still detect unsafe transitions. Workspace tests, no-std, formatting
and changed-file Clippy checks MUST pass. Scope changes MUST receive independent
adversarial review. Historical Lean single-parent modules remain research artifacts,
not a runtime compatibility path.
Validates: [[SPEC-031-unified-quorum-dag#REQ-3100]],
[[SPEC-031-unified-quorum-dag#REQ-3101]].

## Implementation and evidence

Runtime source contains one DAG handoff, with no legacy types, methods, event
variants or host selector. Both ownership modes use `Context::from_instance`.
Runtime and concept documentation describe that API; SPEC-030 is superseded for
runtime selection. Earlier specifications link to this current handoff contract.

Workspace tests, no-std, collective oracle regeneration and production guard
mutations pass. Changed-file Clippy diagnostics are empty; unrelated baseline
warnings remain elsewhere. Independent review accepted source, account-specific
execution tests and actual scope-guard mutation failures. Orientation comprehension
correctly distinguishes account scope from a collective pool. Detailed evidence and
claim boundaries are [[unified-quorum-evidence]], with review in
[[unified-quorum-review]]. Output-page vault integration remains coordinator-owned
backlog outside the specs-only scan.
