---
title: Bounded counter
mode: explanation
---

# Bounded counter

A bounded counter gives each account exclusive rights to decrement a shared integer.
Accounts can transfer those rights without changing the total value.
Different accounts operate concurrently within their allocations.
An account with insufficient rights needs a transfer, even when another account has unused rights.

CBCL declares this meaning in a state rule over ordinary authored acts:

```lisp
(state
  (coins
    (bounded-counter
      (floor 0)
      (initial-rights open :allocations)
      (issuers issuer)
      (increment mint :amount)
      (decrement burn :amount)
      (transfer pay :recipient :amount))))
```

`extend` defines `mint`, `burn`, and `pay` as business messages.
The state declaration associates them with fixed escrow operations.
The source account is the authenticated signer, not a caller-supplied field.
The opener fixes the account allocations, for example `((@treasury 1000) (@alice 0) (@bob 0))`.
Accounts must belong to its authenticated cast; issuer-role keys must have allocation entries.
All operation amounts are positive integer base units.
`(issuers ())` disables minting for fixed initial supply.

The complete lower-bound example is in `dialects/example-coin.cbcl`.
Its allocation trace ends at treasury 1150, Alice 75, Bob 20: total 1245.
Payments conserve supply, burning decreases it, and authorized minting increases it.
The unrestricted `counter` rule remains plain integer arithmetic and can become negative.

## Optional ceiling

A ceiling adds a second escrow budget: headroom to increment.
Add these options to the same rule:

```lisp
(ceiling 10)
(initial-headroom open :space)
(transfer-headroom share-space :recipient :amount)
```

`ceiling` and `initial-headroom` must appear together; headroom transfer is optional.
The opener supplies `:space` as allocation pairs for exactly the same accounts.
Initial rights plus initial headroom equal ceiling minus floor.
Increment consumes the signer's headroom and creates its decrement rights.
Decrement consumes rights and restores the signer's headroom.
A normal transfer moves rights only; `share-space` moves headroom only.
Both transfer kinds preserve total value.
Minting still requires issuer authority, even with available headroom.

The invariant is:

```text
value = floor + sum(rights)
      = ceiling - sum(headroom)    when a ceiling is configured

rights(account) >= 0
headroom(account) >= 0
```

`dialects/example-capped-coin.cbcl` demonstrates the ceiling profile.
A global observed-value check cannot substitute for account headroom under concurrency.

## Host-gated observation and authorization

A bounded field returns a tagged value through the existing fold exports:

```json
{"status":"ready","value":1245,"rights":{"@alice":75,"@bob":20,"@treasury":1150}}
```

Capped observations also contain `headroom` by account.
Missing resource dependencies return `pending` with missing addresses.
An invalid history or observed account fork returns `fault` with reason and evidence.
Neither outcome exposes a partial spendable balance.

The binder fills compiler-owned `:escrow-prev` and `:escrow-deps` fields.
They describe resource causality separately from protocol `:caused-by` links.
`intend` checks the candidate but remains a pure, advisory operation.
The `(resource-check dialect thread (acts ...) (signer message))` export checks resource authorization.
Protocol `admit` remains a separate check; both are required before resource effects.
Bindings trust the signers supplied by the authenticated host; a `signed` wrapper alone is not authentication.

The Rust `escrow::issue` helper requires a host implementation of `IssuanceGate`.
Its atomic compare-and-append persists the complete candidate before returning it for signing and publication.
All operation kinds share a lane identified by canonical dialect, thread, opener, field, and signer.
Two devices sharing an account therefore need shared durable serialization.
Separate account allocations permit independent devices to operate concurrently.
External effect sinks deduplicate by operation address.

Signatures do not prevent competing spends.
A later observed fork faults the instance; choosing the greatest hash cannot undo an external effect.
Hard-bound use therefore requires authenticated, protocol-accepted histories and a correct durable issuance gate.
The library supplies the verifier and gate interface, not a production distributed storage service.

## Evidence and scope

[[SPEC-019-state-rules#CON-1908]] defines the wire contract; [[SPEC-019-state-rules#CON-1909]] defines dual budgets.
[[bounded-counter-implementation]] records tests, mutations, binding agreement, and remaining proof obligations.
The independent Lean model proves guarded local conservation and arithmetic bounds.
It does not prove resource-DAG merge safety, Rust correspondence, or deployed host correctness.

The construction follows [Balegas et al., Extending Eventually Consistent Cloud Databases for Enforcing Numeric Invariants](https://arxiv.org/abs/1503.09052).

## Consensus-free quorum certification

Add this option to select the Rust certificate runtime:

```lisp
(certification quorum-budget)
```

The host supplies an authenticated, pinned validator roster when binding the
instance. A static roster can instead be part of the dialect:

```lisp
(certification quorum-budget
  (validators @v0 @v1 @v2 @v3)
  (faults 1))
```

Omitting `faults` derives it from the committee size, which must equal `3f+1`.
Certificates require `2f+1` distinct authenticated validators; safety assumes at
most `f` Byzantine validators. Omitting the entire certification option preserves
the existing host-gated semantics. Explicit quorum mode never falls back to that gate.
Compiler evidence and committee configuration are bound into signed identities.

```text
business fields -> runtime.intend(instance, owner, verb, fields, nonce)
                                  |
                         complete unsigned act
                                  |
                         external owner signer
                                  |
                         authenticate + register
                                  |
                 durable independent operation votes
                                  |
                         operation certificate
                                  |
                   durable effects votes -> effects certificate
                                                    |
                                           known-final balance view
```

Transaction signing and validator signing remain separate host layers. The core
returns domain-separated `SigningRequest` bytes; it stores no private keys.
An operation certificate reserves capacity but does not make the transfer final.
Only a verified effects certificate contributes to the runtime balance.

In the concurrent phase, each validator has its own scaled signing budget per
resource scope and epoch. The guard is
`quorum * signed_cost <= (f+1) * epoch_allocation`, independently for rights and
headroom. It does not consult a shared available-balance ledger. This conservative
rule can reject a payment even when the displayed balance covers it, including a
full-balance or final-unit payment. An account's `OwnerDriver` responds by entering
the completion lifecycle below; it does not keep retrying the same insufficient
fractional budget. Collective pools retain the concurrent guard and its contention
limits.

For concurrent operations, an owner's signed cancellation request allows validators
that have not signed effects to fence the operation. A cancellation quorum permits
local release and DAG-version refunds. Released and zero-cost signatures stay in
every covering version. A validator adopts only from its current active parent and
requires its complete signing history for that resource scope. Two branches can
join by unioning obligations and accounting for each ID once. Collective DAG updates
need no seal or successor votes. Raw concurrent use can stall through contention
or split execution/cancellation votes; the correct-owner driver avoids that race
by finishing issued work without cancellation. Timeouts never unlock reservations.

`Replica::finalized_view()` reports `status: finalized-view`, verified known-final
IDs, pending operation IDs, rights, optional headroom, and total value. Its
`completeness: unknown` label means other finalized transactions may exist. Its
evidence digest identifies the local final set; it is not a quorum-signed latest
balance snapshot. `Replica::fold_instance()` overlays this view on the ordinary
state fold. Plain stateless fold/authoring bindings reject quorum counters without
an explicit runtime and certificate evidence.

The Rust API and host contracts are documented in
[the quorum runtime reference](../reference/quorum-runtime.md). The executable
worked trace is `crates/cbcl-parser/tests/quorum_runtime.rs`.
[[SPEC-031-unified-quorum-dag]] defines this runtime;
[[SPEC-029-multi-parent-counter-model]] supplies the collective DAG safety model.
Account transfers have runtime scope/isolation and asynchronous execution tests;
a formal account-DAG extension remains separate.
Rust/model correspondence has executable tests and independent review; it is not
formal extraction. The earlier [[SPEC-023-abortable-budget-handoff]] consensus
fallback is historical research.

## Collective ownership

`(ownership collective)` lets distinct authorized signers consume one shared pool.
The default `(ownership account)` retains per-signer allocations and existing hashes.
For tickets, sellers authorize their own sales while charging the same inventory:

```lisp
(state
  (tickets
    (bounded-counter
      (ownership collective)
      (certification quorum-budget)
      (floor 0)
      (initial open :available)
      (issuers organizer)
      (increment restock :amount)
      (decrement sell :amount))))
```

Every bound verb, including the opener, declares its `:from` role in `extend`.
For example, `sell` is from `seller`, while `open` and `restock` are from `organizer`.
The complete dialect is `dialects/example-collective-tickets.cbcl`.
The opener supplies scalar `:available 100`, rather than account allocation pairs.
Concurrent effects-final sales of three and two tickets leave one pool with 95.
Changing the seller does not create another validator budget.

Collective counters require quorum-budget certification. They support increments
and decrements; account allocation and transfer options reject. With a ceiling,
initial headroom is derived as ceiling minus floor minus initial rights. Restocking
requires both issuer authority and available signing capacity. All existing
conservative capacity and conditional-progress limits continue to apply.

An owner cancellation request must be signed by the transaction's original actor.
Another seller may subsequently propose a pool version using that cancellation proof,
without gaining permission to cancel the transaction itself. Version proposers
must occupy an operation's from role. A cast member with only an opener or read role
cannot authorize versions. The reserved internal pool identity is never an actor key.

Collective views render scalar `rights` and optional `headroom`, alongside
`ownership: collective`, `status: finalized-view` and `completeness: unknown`.
The Rust map holds one reserved pool entry; it does not represent seller balances.
Use `Context::pool()` to obtain that resource scope.

Both account and collective quorum counters use multi-parent DAG adoption through
`Context::from_instance`. The language declaration determines the protocol; hosts
provide storage, signing and transport. [[SPEC-031-unified-quorum-dag]] replaces
the earlier single-parent runtime. Collective Lean safety/refinement and shared
Rust traces remain applicable; universal Rust source equivalence is not claimed.


## Spending the whole account balance

For account ownership, the durable owner driver batches requests inside the
concurrent signing envelope. If the FIFO head does not fit, it freezes issuance,
drains its finite published batch to effects, and proposes one permanently sealed
Owned root. A quorum authorizes the cutover. Each following Owned version permits
one distinct operation using its full rights/headroom allocation, including the
last unit. Later versions carry complete books and real effects credits.

This remains consensus-free: no account or validator selects a global transaction
order. The correct logical owner sequences its own continuation; other accounts
progress independently. The existing `quorum-budget` declaration needs no added
language option. Signing and durable storage remain host layers. Collective pools
retain their contention limits.

Use `quorum::OwnerDriver`, with a separate nonforking `OwnerJournal` initialized
before first publication. Raw validator APIs provide safety guards but do not
implement that client's freeze/drain/retry policy. Availability assumes a correct
coherent owner, fair honest service, eventual reliable delivery, at most f Byzantine
validators in 3f+1, and available configured catalogue/storage capacity. There is no
timeout refund or fixed finality deadline. See [[SPEC-033-owned-counter-lifecycle]],
[[quorum-runtime]] and [[owned-lifecycle-evidence]] for API, proof scope and evidence.


### Protocol stalls and the progress claim

The account lifecycle addresses two protocol-level traps: insufficient fractional
budget for an otherwise funded request, and a split between execution and
cancellation votes. A funded request outside the envelope triggers freeze, drain
and a permanent seal. Draining finishes the finite already-issued batch; it needs
no fresh spending allowance. The sealed continuation then uses the full remaining
allocation. The driver never cancels its issued operations, so its recovery path
does not depend on collecting a competing cancellation quorum.

Under the stated correct-owner, honest-quorum, delivery, fair-service and capacity
conditions, the intended contract is that each funded FIFO request eventually
obtains an observed effects certificate, including a full-balance or final-unit
request. Waiting for messages or certificates during this lifecycle is an
asynchronous pending state; the model supplies no fixed completion deadline.
Collective pools and conflicting owner behavior have no corresponding progress
claim.

The current Lean results establish abstract safety and conditional progress under
explicit batch, history, funding and prerequisite-availability premises. Tests
exercise the Rust driver's establishment of those conditions. A universal proof
that every Rust driver execution establishes the model's progress premises remains
open. Consequently, the implemented escape from the identified protocol traps
must be distinguished from a proved absence of every possible implementation
protocol deadlock. See [[owned-lifecycle-evidence]] for the precise boundary.


### Closing the progress proof

[[SPEC-034-owned-progress-closure]] tracks the remaining proof work. Publications
now retain transitive counter prerequisites. Receivers retry them to a fixed point
and catch up along verified ancestry before signing; failed out-of-order adoptions
need not be resent as separate old jobs. Seal requests carry the drained batch's
actual certificates too. Effects responses relay their enabling operation QC, and
completed responses carry the proof chain, so the owner can verify observed finality.

The new Lean components derive dependency readiness from an acyclic catalogue and
an executable retry queue, permit retirement only on owner-observed evidence, and
derive full-allocation head funding from checked admission/reservation invariants.
They are components of the proof. The theorem composing the complete executable
owner, dependency relay, validators and completion journal remains open; a blanket
protocol deadlock-freedom claim is still premature.
