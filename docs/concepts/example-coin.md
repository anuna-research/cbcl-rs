---
title: Example coin
mode: how-to
---

# Example: a coin with a bounded counter

`dialects/example-coin.cbcl` declares a coin. `open` fixes each account's allocation, `mint` and `burn` change the value, and `pay` moves spending rights between accounts without changing the value:

```lisp
; Bounded-counter example. Amounts are integer base units, not decimals.
; Hosts authenticate acts and serialize issuance per account before publication.
(define example-coin (cbcl) @coin-author
  (:resource-requirements ((max-depth 16) (max-expansion-size 4096) (verification-time 1000)))
  (:roles (issuer (* holder)))
  (extend open (to name allocations) :from issuer :to (issuer holder)
    (tell to :name name :allocations allocations))
  (extend mint (to amount) :from issuer :to (issuer holder)
    (tell to :amount amount))
  (extend burn (to amount) :from holder :to (issuer holder)
    (tell to :amount amount))
  (extend pay (to recipient amount) :from holder :to (issuer holder)
    (tell to :recipient recipient :amount amount))
  (shape open (require :name string) (require :allocations list))
  (shape mint (require :amount number))
  (shape burn (require :amount number))
  (shape pay (require :recipient symbol) (require :amount number))
  (protocol (then begin open) (then open mint) (then open burn) (then open pay))
  (state
    (name (initial open :name))
    (coins (bounded-counter
      (floor 0)
      (initial-rights open :allocations)
      (issuers issuer)
      (increment mint :amount)
      (decrement burn :amount)
      (transfer pay :recipient :amount)))))
```

The `issuer` role may mint; any `holder` may burn or pay. The source account of every operation is the authenticated signer, never a caller-supplied field. Verify the dialect with:

```bash
cargo run -p cbcl-cli -- verify < dialects/example-coin.cbcl
```

## Sending messages in the dialect

A thread starts with a root act that fixes the cast, binding each role to agent keys:

```lisp
(with-roles ((issuer @treasury) (holder @treasury @alice @bob))
  (signed @treasury
    (hello () :thread "coin-1" :caused-by begin)))
```

Every later act names the dialect with `(lang example-coin …)`. A performative takes the recipient list, a content slot (empty here), the keyword fields its `shape` requires, and the routing fields `:from`, `:thread` and `:caused-by`. The opening act cites the root's content address:

```lisp
(signed @treasury
  (lang example-coin
    (open (@alice @bob @treasury) ()
      :name "Example Coin"
      :allocations ((@treasury 1000) (@alice 0) (@bob 0))
      :from @treasury
      :thread "coin-1"
      :caused-by sha256-6655c6fbcd385dd84414cad93d6cad9a1ed650f4c2834790d9043f543051d407)))
```

A payment cites the opening act. The binder adds `:escrow-prev` and `:escrow-deps`, which record resource causality separately from the protocol's `:caused-by`:

```lisp
(signed @treasury
  (lang example-coin
    (pay (@alice @bob @treasury) ()
      :recipient @alice
      :amount 100
      :escrow-prev sha256-a9d6de157c34d0473ad88f651a6701c40415978732593f22bf77b4fb0a448ca5
      :escrow-deps ()
      :from @treasury
      :thread "coin-1"
      :caused-by sha256-a9d6de157c34d0473ad88f651a6701c40415978732593f22bf77b4fb0a448ca5)))
```

Hosts do not write these by hand. `intend` completes a verb and its business fields into the canonical act above, ready for the host to sign and publish:

```rust
let inst = Instance::new(&dialect, ThreadId("coin-1".into()), &accepted_acts)?;
let fields = BTreeMap::from([
    ("recipient".to_string(), SExpr::Atom(Atom::Symbol("@alice".into()))),
    ("amount".to_string(), SExpr::Atom(Atom::Num(100))),
]);
let act = intend(&inst, &AgentKey("@treasury".into()), "pay", fields)?;
```

The `signed` wrapper names the signer; the host's authentication, not the wrapper, establishes it. The complete message sequence for this example is in `test-vectors/state/bounded-coin.json`.

## How identities, roles and allocations connect

`@treasury` is a key identity, short for `@ed25519:treasury`. The core never holds public keys: the host maps each identity to real key material, verifies the signature over the act's header, and only then passes the signer to the core. The root act's `with-roles` cast binds identities to roles and is immutable for the thread. The opener's `:allocations` binds the same identities to rights; every account must be in the cast, and each operation debits the authenticated signer. One host-side signature check therefore anchors role, account and rights.

The trace from `crates/cbcl-parser/tests/bounded_counter.rs` opens the coin with allocations `((@treasury 1000) (@alice 0) (@bob 0))` and then applies four acts:

| Act | Signer | Rights afterwards | Value |
|-----|--------|-------------------|-------|
| `pay :recipient @alice :amount 100` | `@treasury` | treasury 900, alice 100 | 1000 |
| `pay :recipient @bob :amount 25` | `@alice` | alice 75, bob 25 | 1000 |
| `burn :amount 5` | `@bob` | bob 20 | 995 |
| `mint :amount 250` | `@treasury` | treasury 1150 | 1245 |

`fold` over the accepted acts renders the state as:

```json
{"name":"Example Coin","coins":{"status":"ready","value":1245,"rights":{"@treasury":1150,"@alice":75,"@bob":20}}}
```

A `pay` or `burn` that exceeds the signer's rights is refused with the reason `insufficient rights`, even when another account has unused rights; the signer needs a transfer first. When a cited resource predecessor has not arrived, the field reports `pending` rather than a partial balance. Replicas that merge the same acts in different orders derive the same rights table.

The default certification profile requires a durable host issuance gate. `(certification quorum-budget)` selects the Rust validator runtime with authenticated quorums, multi-parent DAG adoption, durable journals, and cancellation-backed refunds. Signing, authentication, persistence, and external-effect deduplication remain host responsibilities. Quorum balance queries report known-final local views, with completeness unknown. See [quorum runtime API](docs/reference/quorum-runtime.md).

