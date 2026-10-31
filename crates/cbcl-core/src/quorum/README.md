---
title: Quorum budget module
mode: reference
---

# Quorum budget module

`(certification quorum-budget ...)` selects the multi-parent DAG protocol for both
account and collective counters. `Context::from_instance` pins instance, rules and
committee; there is no host handoff selector or single-parent compatibility path.
The host supplies signing, authentication, transport and durable journal storage.

`VersionManifest` and `DagVersion` bind verified metadata. Receipt checks scope,
parents/ranks, cumulative books and real credit/refund QCs. Local adoption checks
the active parent and the complete signing history for that resource scope.
Evidence never resets; atomic append and semantic recovery guard every mutation.

See [runtime API reference](../../../../docs/reference/quorum-runtime.md) and
[[SPEC-031-unified-quorum-dag]]. Collective Lean/Rust correspondence is checked
against `MultiParentRustOracle.lean`. Account DAG has additional scope/transfer
execution evidence, not a new single-pool Lean refinement claim. Universal Rust
source equivalence remains separate work.
