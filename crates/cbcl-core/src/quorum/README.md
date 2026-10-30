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
