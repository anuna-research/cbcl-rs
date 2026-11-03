---
id: SPEC-028
title: Collective actor protocol refinement
version: 0.1.0
status: implemented-proof
last-updated: 2026-10-31
---

# Collective actor protocol refinement

## Orientation

Formalize collective lifecycle policy before further Rust protocol changes. The
existing [[SPEC-027-collective-bounded-counters]] adapter proves resource safety
with abstract actor predicates, but omits explicit cancellation and checkpoint
request admission. The new executable Lean layer recognizes signed requests,
checks concrete cast/role tables, and retains per-validator authorization receipts.

```text
raw request: instance + payload kind/id + actor-or-pool identity
                         |
               ideal signature verification
               exact actor and role checks
                         |
          persistent local authorization receipts
                         |
        shared-pool sign / fence / checkpoint votes
                         |
       erase receipt-only steps to generic stuttering
                         |
          funded asynchronous business refinement
```

Only the original transaction signer can authorize its cancellation. Checkpoint
proposers occupy an increment or decrement role in the pinned cast. Reserved pool
identities, wrong instances and wrong payload kinds cannot authorize those actions.
All actors use the same resource account and shared validator budget. Genesis
checks signature, initializer role, nonnegative stock and optional ceiling binding.

Prove receipt and honest-vote provenance, quorum authorization, nonnegativity,
funded refinement, and cancellation-safe reclamation for arbitrary schedules.
Network delivery may reorder, duplicate or omit requests. Byzantine validators
retain the generic unrestricted-vote overapproximation; safety assumes at most f
faults in 3f+1 validators. No consensus, multi-parent merge or liveness theorem is
introduced. Receipts and rejected events have the empty business label and erase
to stuttering. A certificate requires 2f+1 distinct validators. Receipts are indexed
by validator, payload kind/id and actor within the pinned instance; replay retains
accepted evidence. A configured ceiling admits genesis only when floor plus initial
rights does not exceed the cap; headroom is their nonnegative difference. Floors and
caps are signed integers and may be negative. Initial rights are nonnegative;
the displayed value is floor plus rights. For floor -10, initial rights 5 and cap
-2, genesis is valid with headroom 3. The signed
genesis identity commits the fixed declaration, cast and initial values.
Ideal signature validity and identifier-to-payload binding are inputs;
cryptographic algorithms, parsers, physical storage and Rust extraction are outside
this proof. [[SPEC-028-collective-actor-refinement#CON-2800]] defines the typed
request grammar, [[SPEC-028-collective-actor-refinement#CON-2801]] defines execution,
and [[SPEC-028-collective-actor-refinement#TEST-2800]] governs kernel acceptance.

## Amendment Channels

The user requests Lean-first formalization. Rust implementation stays unchanged
until the formal model and review are complete. Existing consensus-free assumptions
remain binding. This Tier 1 model requires fresh adversarial and Orientation
review; human security review remains a production-release obligation. BCP 14
keywords state measurable requirements.

## REQ-2800: Explicit actor and payload authorization

The model MUST derive operation, cancellation and checkpoint authorization from
verified instance/payload/signer identities and concrete role tables. Honest votes
MUST have persistent local authorization evidence. Pool identifiers MUST NOT act
as signing identities. Genesis MUST bind the declared floor and optional ceiling.
Validates: [[SPEC-028-collective-actor-refinement#TEST-2800]].

## REQ-2801: Asynchronous safety and refinement

Every executable actor-layer step MUST erase to a generic consensus-free step,
including stuttering for receipt-only and rejected events. Reachable states MUST
preserve authorization provenance and numeric safety. Cancellation-backed release
MUST exclude later finality. These results MUST cover arbitrary finite schedules
and infinite executions under the stated assumptions.
Validates: [[SPEC-028-collective-actor-refinement#TEST-2800]].

## CON-2800: Fixed typed context and raw request grammar

```text
Identity K := actor(Fin K) | pool
Payload T P := genesis | operation(Fin T) | cancellation(Fin T) | checkpoint(Fin P)
Packet K T P := { instance: Nat, signer: Identity K, payload: Payload T P }
```

The immutable context contains manifest/transaction data, actual actors, cast/role
membership and initializer/increment/decrement roles. It also contains an optional
issuer role, scalar initial rights, floor and optional ceiling.
An ideal signature relation indexes actual actor, instance and complete payload.
Identifiers denote fixed complete payloads; hashing/injectivity and cryptographic
unforgeability are external assumptions. Raw packets confer no authority merely
by naming an actor. The recognizer checks the ideal relation and all policy fields.

Receipt tables retain canonical authenticated request identities per validator,
payload and actor. Complete payload data is fixed in the context; signature bytes
are abstracted by the ideal verification relation. The pool identity
has no signature key. Checkpoint manifest authorization is derived from an actual
eligible authenticated proposer, not supplied as a free authorized boolean.

## CON-2801: Layered execution and proof boundary

The actor layer adds request receipt and authorization guards to the existing
shared-resource engine. It preserves local signing charges, effects/fence exclusion,
sealed full journals, cumulative checkpoint accounting and one-successor choices.
Only honest validators require correct receipt evidence; Byzantine votes retain
the existing adversarial freedom. Receipt replay preserves prior evidence.

Initialization returns no state for invalid genesis. Initial headroom is calculated
from ceiling minus floor minus rights and admitted only when nonnegative. Without
a ceiling, headroom is zero and inactive. Prove the
resulting resource sum equals the declared cap. Refine arbitrary actor execution
to the existing generic transition relation, then to funded business steps. Derive
quorum authorization from honest quorum intersection and vote provenance.

The executable event log includes attempted deliveries and protocol actions;
rejected events stutter. It is an abstract execution log, not the Rust journal
serialization. Rust recovery rejects corrupt acknowledged records, which is a
stronger implementation restriction. Persistent abstract journals mean acknowledged
decisions are not lost. Replaying
an identical complete event log reconstructs the same state. This is not a proof
of physical durability. Local observations retain unknown completeness. Finite
identifier universes model a fixed run/configuration, not a storage pruning theorem.

## TEST-2800: Runnable proof core and adversaries

Kernel-check the general preservation, erasure/refinement, authorization, bounds
and reclamation theorems. Execute valid concurrent sellers, wrong-signer cancel,
wrong context/kind, pool-identity forgery, unauthorized/alternate checkpoint actors,
replay, invalid genesis/cap and late-finality/refund traces. Mutations removing
critical authorization guards MUST fail theorem or executable checks. Accept no
sorry, custom axioms or native_decide. Record standard axiom output.

Compare the completed formal guards with Rust read-only before any further
implementation changes. State abstraction gaps rather than claiming extraction.
Validates: [[SPEC-028-collective-actor-refinement#REQ-2800]],
[[SPEC-028-collective-actor-refinement#REQ-2801]].

## Evidence and reading paths

[collective-actor-formalization](https://git.anuna.io/anuna-research/cbcl-rs/src/commit/96d5858d427fb1e371e0a8f13ddf0b23c6c6c8f2/outputs/collective-actor-formalization.md) links kernel builds, executable adversaries,
mutation results and independent review. Reviewers follow request grammar to
control invariants and quorum provenance, then erasure/refinement and numeric bounds.
Implementers follow the read-only Rust mapping and its stated abstraction gaps.
Stakeholders start with Orientation and the audit's shared-pool and reclamation
traces. No Rust implementation is modified in this formalization pass.

## Open scope

The maintainer owns physical signatures/storage, codec correspondence, Rust
extraction, complete-history reads and any future multi-parent version protocol.
