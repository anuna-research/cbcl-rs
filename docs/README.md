# CBCL documentation

[Open a lunch poll and count a vote](tutorials/lunch-vote.md) walks through editing a dialect, verifying it, admitting a vote and inspecting the tally.

| I want to… | Start here |
|---|---|
| Author a dialect | Use the [language grammar](cbcl-grammar.ebnf) for syntax and the [state language reference](reference/state-language.md) for rule arguments and results. The [example dialects](../dialects/) are executable inputs. |
| Use CBCL from an application | The [JS/TypeScript guide](../js/README.md) covers authoring, file round trips, intents and state. Other hosts have [WASM](../crates/cbcl-wasm/README.md), [C](../crates/cbcl-ffi/README.md) and [Erlang](../crates/cbcl-erl/README.md) binding guides. |
| Understand how a message becomes state | Follow the [protocol model](concepts/protocol-model.md) from recognition through admission to derived state. Use [roles and casts](concepts/role-cast.md) for sender authority and [HLC registers](concepts/hlc-registers.md) for competing writes. |
| Implement a resource-aware host | The [worked coin example](concepts/example-coin.md) traces rights, transfers and rejection. Consult the [quorum runtime reference](reference/quorum-runtime.md) and [checkpoint guide](../crates/cbcl-checkpoint/README.md) for host operations. |
| Check a guarantee | The [Lean proof guide](../lean-cbcl/README.md) identifies the theorem, its assumptions and its scope. The [state-kernel oracle guide](state-kernel-oracle.md) shows how to compare model and implementation. |
| Build or contribute | The [development instructions](../README.md#development) cover local checks and releases. The [changelog](../CHANGELOG.md) records shipped changes and migrations. |

## Which source answers which question?

For behavior in a released version, consult that version’s reference, examples and [conformance vectors](../test-vectors/). For a feature’s intended contract, read its [specification](../specs/) and check the status and version at the top. The [IETF draft guide](../IETF/README.md) identifies historical examples and the draft’s relationship to the current implementation.

Two specification documents carry the identifier SPEC-035. Cite [SPEC-035 register semantics](../specs/SPEC-035-register-semantics.md) for HLC arbitration, and [SPEC-035 cached state checkpoints](../specs/SPEC-035-cached-state-checkpoints.md) for certified continuation.
