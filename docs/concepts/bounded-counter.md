---
title: Bounded counter
mode: explanation
---

# Bounded counter

A bounded counter preserves a numeric floor by giving each owner exclusive spending rights.
Owners spend their own rights and can transfer rights to others.
Independent owners can operate concurrently without consulting a global balance.
An owner with insufficient rights waits for a transfer even when rights exist elsewhere.

CBCL’s draft lower-bound escrow contract is in [[SPEC-019-state-rules#CON-1907]].
It defines a resource verdict separately from protocol admission.
The accepted message set remains the replicated object; resource observations derive from its evidence.
The existing `counter` rule remains unrestricted integer arithmetic.

For a floor of zero and initial allocations Alice 6, Bob 4, concurrent spending of 6 and 4 is safe.
Alice cannot spend 7 against her allocation.
A transfer of 2 from Alice to Bob changes allocations to 4 and 6 without changing global value.
Bob must have causal evidence of that transfer before using its rights.

The bound assumes each owner issues one durable operation chain.
Two devices sharing one signing key therefore need shared serialization or distinct allocations and owner identities.
Signatures authenticate competing spends but do not prevent them.
An observed fork faults the resource instance; choosing the greatest hash cannot undo an external effect.

This is a draft specification, not runtime support or a completed proof.
The arithmetic counter theorem does not establish these stronger guarantees.
Implementation and release obligations are in [[SPEC-019-state-rules#Implementation handoff]].

The construction follows [Balegas et al., Extending Eventually Consistent Cloud Databases for Enforcing Numeric Invariants](https://arxiv.org/abs/1503.09052).
