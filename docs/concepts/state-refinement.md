---
title: State refinement
mode: explanation
---

# State refinement

A refinement mapping interprets detailed execution state as business state.
For a fixed CBCL dialect, the mapping reads the accepted acts through its state rules.
Receipt, buffering, rejection, and retries change execution bookkeeping without changing that observation.
These are stuttering steps.

The proof obligation connects acceptance to an independently defined business operation.
Every fresh acceptance needs an operation proof, even when its observed value remains unchanged.
Only internal work and reapplication of an already accepted act can use stuttering without an operation proof.
Equal accepted sets producing equal observations establishes set invariance; legal changes require an additional transition argument.
The counter instance interprets accepted increments and decrements as integer addition and subtraction, once per address.
Its business specification carries no received-message queue or fold definition.

The generic theorem maps complete behaviors pointwise, retaining stuttering, even when an execution makes no further business progress.
No fairness or liveness conclusion follows from this safety theorem.
The typed authentication premise does not prove a deployed signature verifier.
Rust/model equivalence and other business instances remain separate obligations.

Contract: [CON-1906](../../specs/SPEC-019-state-rules.md#con-1906-execution-to-business-simulation).
Decision: [ADR-1913](../../specs/SPEC-019-state-rules.md#adr-1913-compose-an-execution-model-with-an-independent-counter-specification).
