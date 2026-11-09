---
id: BUG-017
title: Native admission trusts cached Act identity before storing a candidate
severity: S2
priority: P1
status: resolved
reported-date: 2026-11-09
assigned-to: SPEC-038 implementer
component: crates/cbcl-parser/src/state_exports.rs
---

# BUG-017: Native candidate admission skips identity validation

Before the repair, the public `admit` function checked the candidate message's shape, then appends it
under the caller-supplied `Act.address`. It did not run the existing derived
identity check on that candidate. A caller can therefore present a valid sealed
root with its old simple-message address cached in the public Act structure,
and receive `Accepted` after the wrapper-commitment migration.

The regression `sealed_root_identity_validation_rejects_cached_simple_address`
actually executed and failed with `Accepted`, after the new construction and
existing identity-validator hashing policy had been updated. This is an
admission-boundary cache-validation defect, not evidence that ordinary message
parsing generates forged Acts or that host authentication was bypassed.

The fix reuses the existing Act identity validator before candidate admission.
It checks message-derived address, verb, predecessors, recipients and fields;
authenticated signer provenance remains the host's responsibility. No state
fold, domain membership or resource balance is consulted. This preserves the
admission/state stratification required by [[SPEC-019-state-rules#REQ-1914]].
It enforces the consistent identity policy of
[[SPEC-038-lvar-state-kernel#REQ-3807]] and
[[SPEC-038-lvar-state-kernel#TEST-3814]].

Acceptance: the stale cached root is rejected, valid roots remain admitted,
state-independent admission tests pass, and a mutation skipping the identity
check makes the executed regression fail. Construction/validation and historical
migration checks remain separate obligations.

## Resolution — 2026-11-09

Implemented and independently reviewed under
[[SPEC-038-lvar-state-kernel#TEST-3814]]. Native library and state integration
suites pass, including transport-wrapped root admission and progress. The
explicit migration manifest preserves the immutable historical snapshot and
checks exact original state bytes. Live Lean oracle and progress comparisons
pass. Executed semantic mutants reject cast omission, the wrong root predicate,
stale candidate identity, transport-stopping discovery, legacy progress pinning,
and raw-render whitespace drift. Compiler or disk-space failures were not
counted as mutation rejection; the final isolated gate passed after regenerable
build caches were removed.

This resolves the root identity/discovery implementation defect; authored
condition thresholds and the full v0.4 acceptance audit remain separate work.
