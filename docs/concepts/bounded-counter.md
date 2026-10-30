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

## Observation and authorization

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
