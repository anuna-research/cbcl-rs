# Accepted-history admission

`admission::AdmissionMonitor` implements an opt-in execution discipline aligned
with the paper's `LeanCbcl.Execution.Trace`. It freezes one protocol, cast, root,
thread, and endpoint. It keeps received candidates separate from accepted history.
Only the monitor can promote a candidate into its private accepted store.

## Host integration

1. Install the dialect using the existing installation pipeline. Supply its
   complete role annotations, including inherited/unrolled runtime steps.
2. Implement `AdmissionGate` using the authenticated transport's verification
   facilities. Authenticate the entire semantic message and return its verified
   content address. In particular, bind the outer cast/dialect/thread envelope
   and the signer used by role conformance. Check immutable parser/shape
   requirements here too. A parsed `signed` form alone is insufficient.
3. Construct `AdmissionMonitor::new(dialect, endpoint, root_message, gate)`.
   Construction receives but does not accept the root. It requires a computed
   matching dialect pin, R5/R6, unique annotations and roles, a valid root cast,
   and occupant-instantiated causal locality. Context is immutable afterward.
4. Feed both incoming messages and the endpoint's own outgoing submissions to
   `receive`. The returned hash identifies a candidate, **not an accepted act**.
5. Call `drain_ready` after receipt, or interleave `receive` with `step` under
   continuous traffic. Consume application messages only from new `Accepted`
   events. Retrieve their data through `accepted().lookup(&event.hash)`.

```rust,ignore
let hash = monitor.receive(authenticated_input)?;
for event in monitor.drain_ready() {
    match event.state {
        AdmissionState::Accepted => {
            let message = monitor.accepted().lookup(&event.hash).unwrap();
            // Dispatch the admitted message through the host's application layer.
            // Protocol acceptance does not itself make external effects idempotent.
            deliver_to_application(message);
        }
        AdmissionState::Rejected(reason) => report_rejection(event.hash, reason),
        AdmissionState::Pending => unreachable!("drain_ready omits pending visits"),
    }
}
// Querying state(&hash) distinguishes a still-pending candidate from acceptance.
```

Authentication remains an explicit trusted interface, as in the Lean `gate`
parameter. There is no default accepting gate, built-in key registry, or newly
invented signing discipline. Its verdicts must be immutable for this context;
changing revocation or deadline policies require separate temporal semantics.

## Correspondence to the execution model

| Lean component | Rust behavior |
|---|---|
| Received store `D` grows | Successfully gated candidates are retained in `received`; failed decoding/gate input can be represented as receipt-only stuttering outside this API |
| Accepted store initially empty | The authenticated root starts pending |
| Immutable gate and endpoint relevance | Required gate, private pinned context, explicit thread, declared step, signed role/key relevance; indexed sends checked per occupant |
| Predecessors already accepted | `resolved` checks all raw hash references in the private full-message accepted store before invoking the verifier |
| Acceptance against the previous store | `step` verifies first, then appends; self/cyclic references cannot bootstrap admission |
| Accepted history only grows | No mutable store accessor, restore/merge shortcut, removal, or overwrite API |
| Fair reconsideration | A FIFO queue rotates pending candidates to its tail; new candidates append at the tail; duplicate receipts do not reorder it |
| Eventual acceptance | Conditional on delivery, a correct gate/verifier, and continued host calls to the scheduler; finite queued input drains to a fixed point |

Each queue visit is an abstract transition. A receive is a stuttering transition
for accepted history; each acceptance is a separate transition even within
`drain_ready`. Unlike the abstract model's possibly infinite batches, each Rust
visit considers one candidate. The scheduler still depends on the host giving it
execution time; enqueueing indefinitely without calling it is not fair.

The root's wire `:caused-by begin` denotes a predecessor-free nomination. All
non-root messages must use explicit predecessor hashes. This avoids interpreting
a bare `begin` as an unanchored second root. Raw references to the pinned root
are resolved against accepted history before the existing verifier rewrites the
reference to the protocol's `begin` type.

## Scope and compatibility

- Full-message strict locality is required. Envelope-derived admission is a
  separate refinement; no opened/redacted evidence enters this monitor's store.
- Duplicate performative definitions are refused, even when their annotations
  happen to agree, avoiding first/last-lookup divergence. All protocol steps
  need direct annotations; callers should materialize inherited/unrolled ones.
- Messages must explicitly name their thread. This is stricter than legacy
  call sites that supply a default thread externally.
- Pending candidates do not expire and are not evicted. This realizes retention
  but does not give a fixed memory bound. Backpressure before receipt is the
  appropriate integration point; discarded candidates require reliable retry.
- Accepted/rejected duplicates do not emit new completion events. Exactly-once
  external effects, crash recovery, and durable delivery remain host concerns.
- The existing `Agent`, parser pipeline, low-level store, and role verifier remain
  available for compatibility. They do not automatically acquire this monitor's
  admission guarantees. A host claiming accepted-history safety must migrate its
  receive-to-application path to this API and avoid direct-store bypasses.
- The causal verifier now calls `causal_kernel`, whose actual Rust source is
  extracted by Charon/Aeneas and whose acceptance rules are checked in Lean.
  The paper workspace contains `proofs/refinement/kernel`: a conditional bridge
  derives EPP validity under explicit lookup, coverage and protocol/role contracts.
  Those Rust adapters and this monitor's state machine are not yet refined.
  Authentication, byte-level hashing and occupant-counted fan-in also remain
  separate obligations; this is not a whole-monitor refinement theorem.

## Validation

`cargo test -p cbcl-core --test admission_tests` exercises all 24 delivery orders
of a four-step three-role fan-in at all three endpoints; it checks accepted
closure and validity along the way. Additional tests cover received-but-invalid
predecessors, missing roots, mixed wrong/missing fan-in evidence, duplicate
receipts, ongoing arrivals, context and authentication failures, hash conflicts,
asynchronous union safety without coverage, and indexed-occupant fan-in.

The test gate is deliberately a fixture, not a deployable authenticator.
