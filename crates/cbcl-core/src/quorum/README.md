---
title: Quorum budget module
mode: reference
---

# Quorum budget module

`Context` binds the authenticated instance and committee. `Replica` implements one
validator's independent budget, effects/fence and checkpoint state machine. Public
proof and journal types are in `types.rs`. Declaration defaults are in the sibling
`certification` module. Host signers, authentication, networking and durable storage
remain separate integrations.

See the [runtime API reference](../../../../docs/reference/quorum-runtime.md) for
method contracts, defaults, persistence requirements, query semantics and limits.
The executable integration trace is
[quorum_runtime.rs](../../../cbcl-parser/tests/quorum_runtime.rs).


Collective hosts can select `Context::from_instance_multi_parent` for the separate
SPEC-030 DAG protocol. Its context domain excludes legacy signatures/journals.
`VersionManifest` and `DagVersion` describe authenticated metadata; receipt verifies
cumulative unique-ID books, parents, ranks and real credit/refund QCs. Adoption
checks the local active parent and all historical signatures without seal votes or
a successor choice. The engine retains evidence and reuses atomic journal replay.
Source correspondence is checked against `MultiParentRustOracle.lean`; this is not
formal Rust extraction. Public authoring, API and proof boundaries are documented
in `docs/reference/quorum-runtime.md` and [[SPEC-030-rust-multi-parent-refinement]].
