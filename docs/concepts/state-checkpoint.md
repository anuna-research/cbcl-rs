---
title: State checkpoint
mode: explanation
---

# State checkpoint

A checkpoint names one accepted set of a CBCL thread by two commitments: the set root and the state root of its native fold.
A checkpoint proof lets a party that trusts one checkpoint accept a later one without replaying the messages between them.
The proof states that the accepted set grew by exactly the committed batch, that every added message was admitted against the previous set under the installed dialect, and that the new state is the native fold of the new set.

The relation is compiled by the verifier, not proved in gates.
For a public vocabulary of at most eight candidate messages, the verifier runs the native kernel over every subset and every monotone pair of subsets and records which are valid and admitted, with their roots.
The circuit then proves only exact membership: Boolean selection of a before set and an after set, equality of the public roots with the selected table constants, grow-only membership, the exact batch difference, and that the pair is an admitted transition.
The native kernel of SPEC-019 stays the single definition of admission and fold; the circuit is a bounded specialisation of it, not a second implementation.

The verifier owns the expectation.
A single proof is checked against a statement the receiver chose, never against the statement inside the package.
A chain is checked link by link from a receiver-pinned start, each link's before checkpoint matched to the running checkpoint, so two valid proofs that do not meet cannot be accepted as one history.

The proof is silent on authorship.
A candidate enters the vocabulary either attested, through its R4 v2 attestation header, or unauthenticated, as a host precondition; both give the same profile identity.
A host that skips authentication gets a proof that says nothing about who wrote each message, and the proof looks the same either way.

The ceiling is the enumeration.
Rows grow as 2^n and transitions as 3^n, so the vocabulary is capped at eight and a new vocabulary needs a new profile and new keys.
Commitments are flat set roots with no membership paths, so the whole vocabulary is needed to compile a profile and history is retained in the root rather than purged.
Removing the ceiling needs an incremental constrained kernel over authenticated state paths, and shortening long chains needs recursive composition; both remain open.
The artefact is experimental and not independently audited.

Requirement: [REQ-3500](../../specs/SPEC-035-halo2-state-checkpoints.md#req-3500-verifier-compiled-relation).
Contracts: [CON-3500](../../specs/SPEC-035-halo2-state-checkpoints.md#con-3500-profile-compiler), [CON-3501](../../specs/SPEC-035-halo2-state-checkpoints.md#con-3501-circuit-statement), [CON-3503](../../specs/SPEC-035-halo2-state-checkpoints.md#con-3503-verifier-and-chain).
Decisions: [ADR-3500](../../specs/SPEC-035-halo2-state-checkpoints.md#adr-3500-verifier-derived-finite-relation), [ADR-3505](../../specs/SPEC-035-halo2-state-checkpoints.md#adr-3505-chains-compose-by-sequential-verification-from-a-pinned-start).
Kernel: [SPEC-019 state rules](../../specs/SPEC-019-state-rules.md).
