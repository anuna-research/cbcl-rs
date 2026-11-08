---
id: BUG-014
title: Parsed resource oracle comparisons can round i128 aggregates
severity: S3
priority: P1
status: resolved
reported-date: 2026-11-09
assigned-to: SPEC-038 implementer
component: crates/cbcl-parser/tests/state_kernel_oracle/resource_facts.rs
---

# BUG-014: Resource-ready comparison can hide a one-unit difference

The differential evidence for [[SPEC-038-lvar-state-kernel#TEST-3806]] compared
ready resource values and balances after parsing their JSON into the current
Rust `serde_json::Value` representation. Wire amounts fit signed 64-bit integers,
but accumulated kernel values use signed 128-bit integers. Parsed comparisons
alone can lose the distinction between different large aggregates and therefore
cannot establish the output agreement required by
[[SPEC-038-lvar-state-kernel#REQ-3806]]. This is a verification-harness defect;
no incorrect native resource aggregate has been demonstrated.

## Reproduction

A temporary example using the repository's current dependencies parsed the two
decimal JSON numbers `73786976294838207456` and `73786976294838207457`. Comparing
the resulting `serde_json::Value` instances returned true. The temporary example
was removed after the observation. The former number is the valid fixture value
from initial rights 1000 plus eight maximum signed-64-bit mints.

## Correction and regression evidence

The typed resource profile now compares `ready_bytes` in addition to parsed
fields. Native bytes come directly from the actual resource `Value::render`;
Lean emits the complete checked snapshot in native key order. This retains exact
value, rights and optional headroom numbers without passing them through floating
point parsing before equality. The request contains no expected bytes or result.

The directed large-mint chain executes the complete native verifier and complete
Lean verifier. The `resource-large-ready-unit-error` mutant changes only native
rendered totals above the unsigned-64-bit range by one unit. The corrected live
comparison rejects it with an executed assertion. All oracle suites pass on the
unmodified implementation. This closes the precision gap in the typed resource
campaign; it does not change public JSON or prove full native AST extraction.
