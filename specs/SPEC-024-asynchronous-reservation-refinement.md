---
id: SPEC-024
title: Withdrawn Serialized Reservation Attempt
version: 0.2.0
status: withdrawn-wrong-design
last-updated: 2026-10-31
---

# Withdrawn Serialized Reservation Attempt

## Orientation

The user requires a consensus-free bounded counter. The prior uncommitted attempt
replaced independent signing with a consensus-serialized reservation ledger.
Its proof addressed a different protocol and does not satisfy that requirement.
Its code was removed from the active branch and retained under
`/private/tmp/cbcl-serialized-reservation-withdrawn` as failed-attempt evidence.
No completion claim for consensus-free refinement follows from that proof.

Controls: no consensus oracle, no serialized reservation authority, no global balance
admission guard. Existing [[SPEC-023-abortable-budget-handoff]] consensus-backed
recovery is historical research, not the selected consensus-free profile.

## Amendment Channels

The user explicitly rejected consensus serialization. No automated reviewer or
implementation convenience can waive that constraint.

## BUG-2400: Proving the wrong protocol

The hard cross-epoch accounting proof was replaced with a serialized resource
ledger. This introduced an ordering authority that the design intended to avoid.
The implementation was locally proved but did not refine the requested protocol.
The remedy is to prove independent witness budgets, sealed checkpoint completeness
and cancellation exclusion together, permitting Byzantine-owner stalls instead of
assuming an agreement service. Owner: CBCL maintainer.

## CON-2400: Withdrawn serialized core

The prior work item proposed consensus-serialized reservation grants. It is
withdrawn because it violates the user's no-consensus requirement. The archived
implementation is evidence of that design error, not an approved implementation.

## CON-2401: Withdrawn refinement target

The prior proof refined the serialized model. Its kernel validity does not establish
refinement of the requested independent-budget protocol. The current target is
[[SPEC-025-consensus-free-refinement#CON-2501]].

## TEST-2400: Failed task acceptance

Acceptance fails the no-consensus requirement regardless of executable test results.

## TEST-2401: Failed refinement acceptance

Acceptance fails because the proved protocol differs from the requested protocol.
