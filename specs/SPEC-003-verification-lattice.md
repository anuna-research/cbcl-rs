---
id: SPEC-003
title: Verification Lattice — Algebraic Foundations for Causal Protocol Checking
status: draft
version: 0.1.0
date: 2026-03-24
author: Anuna Research (https://anuna.io)
depends-on: SPEC-002 (structural contracts — causal protocols and shapes)
prior-art:
  - Conway et al. 2012 (logic and lattices for distributed programming, BloomL)
  - Kuper 2015 (LVars — lattice-based deterministic parallelism, threshold reads)
  - Ameloot/Neven/Van den Bussche 2011 (CALM theorem — monotonic = coordination-free)
  - Shapiro et al. 2011 (CRDTs — conflict-free replicated data types, state-based merge)
  - Sanjuan/Poyhtari/Teixeira/Psaras 2020 (Merkle-CRDTs — Merkle-DAGs meet CRDTs)
  - Davey & Priestley 2002 (Introduction to Lattices and Order — reference text)
  - Lamport 1978 (happened-before, causal ordering)
  - Birman/Joseph 1987 (reliable communication in the presence of failures)
  - Bailis et al. 2015 (coordination avoidance, invariant confluence)
repository: https://codeberg.org/anuna/cbcl-rs
---

# SPEC-003: Verification Lattice — Algebraic Foundations for Causal Protocol Checking

## Overview

SPEC-002 introduces causal protocol verification and proves it monotonic by case analysis: single-predecessor checks are stable, fan-in checks are conjunctions of stable checks, and the message store is append-only. These arguments are correct but ad hoc — each new verification feature requires a new monotonicity proof.

This specification provides the **algebraic foundation** underneath SPEC-002. It identifies the lattice structures implicit in the message store, the verification result, and the `:caused-by` Merkle DAG, and formalises the relationships between them. The payoff is threefold:

1. **Monotonicity becomes structural, not per-feature.** If the verification function is a lattice homomorphism, every composition of it is automatically monotone. No case analysis needed per requirement.
2. **Three-valued verification.** The current two-valued result (`Ok` / `Err`) conflates "predecessor not yet received" with "predecessor has wrong type." The lattice gives a principled three-valued result: `Unknown` (⊥), `Valid`, `Violation`. This is the correct distinction for unordered transports.
3. **The Merkle DAG IS the lattice.** The message store's `:caused-by` links are not an ad-hoc parameter — they are the covers relation of a join-semilattice. Content hashes are lattice element identities. Fan-in via `(all ...)` is lattice join. Causal closure is the principal ideal. This unification means the data structure, the protocol semantics, and the verification algebra are the same object viewed from three angles.

### Design Provenance

**Lattices for distributed programming.** Conway, Marczak, Alvaro, Hellerstein & Maier (2012, [*Logic and Lattices for Distributed Programming*](https://dl.acm.org/doi/10.1145/2391229.2391230)) extended Bloom with lattice-typed variables, showing that monotonic programs over lattices are automatically eventually consistent. SPEC-003 applies this framework to protocol verification: the message store is a lattice, verification is a monotone function, and eventual consistency of the verification result follows algebraically.

**Threshold reads.** Kuper (2015, [*Lattice-Based Data Structures for Deterministic Parallel and Distributed Programming*](https://users.soe.ucsc.edu/~lkuper/papers/lindsey-kuper-dissertation.pdf)) introduced LVars with threshold reads — a query that blocks until the lattice state reaches a specified threshold. The three-valued verification result maps directly: `Unknown` is the state below the threshold `{Valid, Violation}`; verification resolves when the threshold is crossed. The choice of whether to block (buffer the message) or reject immediately (fail-fast) is a policy decision on a threshold read.

**Merkle-CRDTs.** Sanjuan, Poyhtari, Teixeira & Psaras (2020, [*Merkle-CRDTs: Merkle-DAGs meet CRDTs*](https://research.protocol.ai/publications/merkle-crdts-merkle-dags-meet-crdts/psaras2020.pdf)) observe that "Merkle-Clocks already embed ordering and causality information." SPEC-003 formalises this observation: the `:caused-by` Merkle DAG is a join-semilattice where each message's hash commits to its entire causal history (principal ideal).

### Scope

This specification covers:

- The lattice structure of the message store, the verification result, and the `:caused-by` DAG
- The three-valued verification result (`Unknown`, `Valid`, `Violation`)
- The agent policy for handling `Unknown` results (reject vs buffer)
- The lattice homomorphism property relating message store growth to verification result stability
- Lean 4 formalisation targets

This specification does **not** cover:

- Protocol or shape declaration syntax (SPEC-002)
- Blame attribution (SPEC-002)
- Runtime pipeline integration (SPEC-002)
- Counted sequences or non-monotonic extensions

---

## User Profiles

### User: Protocol Implementor

**Role:** Developer implementing the causal verification engine in `cbcl-rs`.

**Goals:** Understand the algebraic structure well enough to implement verification correctly and to write the Lean 4 proofs. Know which invariants the implementation must preserve. Understand why `Unknown` is not an error.

**Constraints:** Must implement in `no_std` Rust with `alloc` only. Must preserve the O(1) / O(k) verification latency from SPEC-002.

**Daily workflow:** Implements `VerificationResult`, updates `verify_causal()` to return three-valued results, writes lattice property tests, begins Lean formalisation.

### User: Dialect Author (via SPEC-002)

**Role:** Developer defining protocols. Not expected to understand lattice theory.

**Goals:** Understand that messages arriving out of order are not errors — they are "not yet decidable." Understand that the system will eventually verify correctly regardless of message arrival order.

**Constraints:** Interacts with the lattice only through SPEC-002's protocol declarations. The lattice is invisible infrastructure.

---

## Happy Paths

### Happy Path: Message Arrives Before Predecessor

**Preconditions:** Dialect with protocol installed. Transport delivers messages out of order.

**Steps:**
1. Agent receives `pause-ack` with `:caused-by "sha256:abc..."` → Looks up hash → Not in store.
2. Verification returns `Unknown` (⊥) — not a violation.
3. Agent policy is `Reject` → Returns error `CausalPending { caused_by: "sha256:abc..." }` to sender.
   - OR: Agent policy is `Buffer { max_pending: 100, ttl: 30s }` → Buffers message.
4. (Buffer path) Agent later receives `pause` → Appends to store → Re-evaluates buffered `pause-ack` → `Valid`.

**Postconditions:** Message verified. No false positive. Policy determines operational behaviour.

**Failure modes:**
- Buffer policy, predecessor never arrives → TTL expires, message dropped with `CausalTimeout`.
- Buffer policy, buffer full → Oldest pending message evicted with `CausalBufferFull`.
- Predecessor arrives but has wrong type → `Violation` (permanent).

### Happy Path: Fan-In With Partial Predecessors

**Preconditions:** Scatter-gather protocol. Three search results expected before merge.

**Steps:**
1. Agent receives `merge-results` with `:caused-by (hash-a hash-b hash-c)`.
2. Store contains `result-a` (hash-a) and `result-b` (hash-b) but not `result-c` (hash-c).
3. Sub-checks: `result-a` → `Valid`, `result-b` → `Valid`, hash-c → `Unknown`.
4. Conjunction: `Valid ⊓ Valid ⊓ Unknown = Unknown`.
5. Agent policy determines response (reject or buffer).
6. (Buffer path) `result-c` arrives → Re-evaluate → `Valid ⊓ Valid ⊓ Valid = Valid`.

**Postconditions:** Fan-in resolved correctly. No false `IncompleteFanIn` error for timing.

---

## Requirements

### REQ-300: Message Store Lattice

The message store SHALL be formalised as a **join-semilattice** (S, ⊆, ∪) where:

- **Elements**: Sets of messages. Each agent's store is an element.
- **Ordering**: Set inclusion (⊆). If store₁ ⊆ store₂, then store₂ has observed everything store₁ has.
- **Join**: Set union (∪). Merging two agents' stores produces a store containing everything either has observed.
- **Bottom**: The empty set (∅). An agent that has observed nothing.

Messages are immutable. The store is append-only — the only operation is `store ∪ {new_msg}`. This is a grow-only set (G-Set) CRDT (Shapiro et al. 2011). The join operation (set union) is commutative, associative, and idempotent, satisfying the semilattice axioms.

Each message is identified by the SHA-256 hash of its canonical serialisation (SPEC-002 REQ-202). The hash is the lattice element identity — two messages with the same hash are the same message.

**Rationale:** Making the lattice structure explicit enables algebraic reasoning about verification. The G-Set CRDT structure guarantees convergence without coordination (Shapiro et al. 2011). BloomL (Conway et al. 2012) shows that monotonic functions over lattices are automatically eventually consistent — this is the property we exploit.

Trace:
- TEST-300
- CON-300

### REQ-301: Causal Ordering as Join-Semilattice

The `:caused-by` Merkle DAG within each thread SHALL be formalised as a **join-semilattice** (M, ≤, ⊔) where:

- **Elements**: Messages within the thread, plus a distinguished bottom element `begin`.
- **Ordering**: Causal precedence. Message A ≤ message B if A is in B's causal closure (reachable by following `:caused-by` links from B back to A).
- **Join**: For two messages A and B, their join A ⊔ B is the earliest message that has both A and B in its causal closure. If no such message exists yet, the join is **undefined** (the messages are on incomparable branches — the lattice is a partial order, not total).
- **Bottom**: `begin` — causally precedes everything.

The `:caused-by` links are the **covers relation** of this semilattice:
- Single `:caused-by` hash = M covers its predecessor (M is an immediate successor).
- List-valued `:caused-by` = M is the **join** of its predecessors. Fan-in via `(all ...)` IS lattice join — the merge message is the least upper bound of its predecessors in the causal order.

Fan-out (multiple messages referencing the same predecessor) produces incomparable elements — branches that have not yet been joined.

**Content hashing as identity.** Each message's hash commits to its content, which includes its `:caused-by` hashes, recursively. Therefore M's hash is a cryptographic commitment to its entire **principal ideal** ↓M = {x ∈ M | x ≤ M} — the set of all messages in M's causal closure. Two agents holding the same hash have, by construction, observed at least the same causal history for that message.

**Rationale:** This is not a new data structure — it is the algebraic name for the Merkle DAG that SPEC-002 already defines. Identifying it as a join-semilattice makes three facts obvious: (1) fan-in is join, (2) causal closure is the principal ideal, (3) the hash is a commitment to lattice position. These are exactly the properties SPEC-002 proves ad hoc in REQ-203, REQ-211, and REQ-212.

Trace:
- TEST-301

### REQ-302: Three-Valued Verification Result

The system SHALL use a three-valued verification result lattice:

```
     Valid          Violation
       \              /
        \            /
         ⊥ (Unknown)
```

Where:

- **Unknown** (⊥) — The predecessor hash is not in the message store. The check is undecidable with the current store state. This is NOT a protocol violation — it is missing information.
- **Valid** — The predecessor hash resolves to a message with the correct performative type per the protocol declaration.
- **Violation** — The predecessor hash resolves to a message with an incorrect performative type, or the hash is malformed, or the protocol declaration forbids this causal link.

The lattice ordering is: `Unknown < Valid` and `Unknown < Violation`. `Valid` and `Violation` are incomparable (a check cannot be both valid and a violation). This is a **flat lattice** (also called a discrete order with bottom): ⊥ is below everything, all other elements are incomparable.

**Stability property.** Both `Valid` and `Violation` are **stable** (permanent) under store growth:

- If `check(msg, store) = Valid`, then `check(msg, store ∪ S) = Valid` for all S. The predecessor hash exists and has the correct type; adding messages cannot remove a hash or change its type.
- If `check(msg, store) = Violation`, then `check(msg, store ∪ S) = Violation` for all S. Same reasoning — the predecessor exists with the wrong type, and that fact is immutable.
- If `check(msg, store) = Unknown`, then `check(msg, store ∪ S)` may be `Unknown`, `Valid`, or `Violation`. The result can only move **up** in the lattice (away from ⊥).

This is exactly the definition of a **monotone function** from the store lattice (REQ-300) to the result lattice: if store₁ ⊆ store₂, then `check(msg, store₁) ≤ check(msg, store₂)`.

Trace:
- TEST-302
- CON-301

### REQ-303: Conjunction and Disjunction on the Result Lattice

For fan-in verification with `(all ...)`, the overall result SHALL be the **meet** (greatest lower bound) of sub-results:

| ⊓ | Unknown | Valid | Violation |
|---|---------|-------|-----------|
| **Unknown** | Unknown | Unknown | Violation |
| **Valid** | Unknown | Valid | Violation |
| **Violation** | Violation | Violation | Violation |

Rules:
- `Unknown ⊓ Unknown = Unknown` — still can't decide.
- `Valid ⊓ Valid = Valid` — all predecessors verified.
- `Violation ⊓ anything = Violation` — one bad predecessor poisons the conjunction (Violation is absorbing for meet).
- `Unknown ⊓ Valid = Unknown` — can't confirm the conjunction until all sub-checks resolve.

For disjunctive predecessors with `(any ...)`, the overall result SHALL be the **join** (least upper bound) of sub-results:

| ⊔ | Unknown | Valid | Violation |
|---|---------|-------|-----------|
| **Unknown** | Unknown | Valid | Violation |
| **Valid** | Valid | Valid | Valid |
| **Violation** | Violation | Valid | Violation |

Rules:
- `Unknown ⊔ Unknown = Unknown` — no alternative has resolved.
- `Valid ⊔ anything = Valid` — one valid predecessor suffices (Valid is absorbing for join).
- `Unknown ⊔ Violation = Violation` — the one resolved alternative is invalid. (But note: if more alternatives arrive later, the result may change to Valid. This is only stable once ALL alternatives in the `(any ...)` set have resolved.)

**Disjunction stability caveat.** For `(any ...)`, the result is stable (permanent) once any sub-check returns `Valid` — a single valid alternative suffices and cannot be invalidated. However, a `Violation` result for `(any ...)` is NOT stable until all alternatives have been checked — a later alternative may turn out `Valid`. The implementation MUST NOT emit a final `Violation` for `(any ...)` until all alternatives in the disjunction are known.

In practice, for `(any ...)` on the predecessor side, the agent has a single `:caused-by` hash. The disjunction is over the valid predecessor *types*, not over multiple hashes. The check is: "is the predecessor's type in the set {a, b, c}?" This resolves immediately when the predecessor is in the store (the type is known) and is `Unknown` when the predecessor is not in the store. There is no partial-disjunction case for single-predecessor `(any ...)` — the result is atomic.

The partial-disjunction caveat applies only if a future extension allows disjunctive `:caused-by` (multiple hashes where any one suffices). This is not part of SPEC-002 or SPEC-003 but the algebra is recorded here for completeness.

**Rationale:** Meet for conjunction and join for disjunction are the standard lattice operations. The absorbing elements (Violation for meet, Valid for join) correspond to short-circuit evaluation — a known bad predecessor fails the conjunction immediately, a known good predecessor passes the disjunction immediately.

Trace:
- TEST-303

### REQ-304: Verification as Lattice Homomorphism

The causal verification function SHALL be a **monotone function** (order-preserving map) from the message store lattice (REQ-300) to the verification result lattice (REQ-302):

```
verify: (Message × Store) → VerificationResult
```

Such that: if `store₁ ⊆ store₂`, then `verify(msg, store₁) ≤ verify(msg, store₂)`.

This property SHALL hold for all verification modes:

1. **Single predecessor.** `verify(msg, store)` looks up the `:caused-by` hash in the store. If absent → `Unknown`. If present and correct type → `Valid`. If present and wrong type → `Violation`. Monotone because: adding messages to the store can cause `Unknown → Valid` or `Unknown → Violation` but never `Valid → anything_else` or `Violation → anything_else`.

2. **Conjunctive fan-in `(all ...)`.** `verify(msg, store) = ⊓ᵢ verify_sub(hashᵢ, store)`. Each `verify_sub` is monotone (case 1). Meet of monotone functions is monotone: if each sub-result can only increase, their meet can only increase (Violation is absorbing downward, Unknown can only move up).

3. **Disjunctive predecessor `(any ...)`.** `verify(msg, store) = ⊔ⱼ verify_sub(hashⱼ, store)`. Each `verify_sub` is monotone. Join of monotone functions is monotone (Valid is absorbing upward).

**Consequence.** Any composition of verification checks — nested `(all ...)` within `(any ...)`, multiple shape checks, shape + causal — preserves monotonicity automatically. No per-feature monotonicity proof is needed beyond establishing the base case (single-predecessor lookup is monotone) and the compositional closure (meet and join of monotone functions are monotone).

This is the **structural monotonicity guarantee** that replaces SPEC-002's ad-hoc case analysis in REQ-211.

Trace:
- TEST-304

### REQ-305: Unknown Predecessor Policy

When causal verification returns `Unknown`, the agent SHALL apply a configurable policy:

**Policy: Reject (default).** Treat `Unknown` as a non-fatal refusal. Return a `CausalPending` response to the sender indicating that the predecessor is not yet available. The sender MAY retransmit after a delay. No message is buffered. No mutable state is created.

```scheme
(error @sender "causal-pending"
  :detail "predecessor-not-yet-available"
  :caused-by "sha256:7d3e...a1f0"
  :performative "pause-ack"
  :retry-after 5)
```

`CausalPending` is distinct from `CausalViolation` — it carries `:retry-after` instead of `:blamed`, signalling that retransmission may succeed. The sender is NOT blamed.

**Policy: Buffer.** Hold the message in a bounded pending queue and re-evaluate when the store grows.

```rust
Buffer {
    max_pending: usize,   // maximum messages in the pending queue (DoS protection)
    ttl: Duration,        // time-to-live for pending messages
}
```

Constraints:
- The pending queue is per-thread, bounded by `max_pending`. When full, the oldest pending message is evicted with `CausalBufferFull`.
- Pending messages expire after `ttl` with `CausalTimeout`.
- When a new message is appended to the store, the agent re-evaluates all pending messages in the affected thread. Re-evaluation is O(pending × k) where k is the maximum fan-in degree.
- The pending queue is **mutable state**. Agents using the Buffer policy do not satisfy NFR-204 (zero mutable protocol state) from SPEC-002. This trade-off is explicit and documented.

**Policy selection.** The choice between Reject and Buffer depends on the transport and the use case:

| Transport | Recommended policy | Rationale |
|---|---|---|
| Ordered (TCP, WebSocket) | Reject | Messages arrive in order; Unknown indicates a genuine problem, not timing. |
| Unordered (Nostr relays, UDP, gossip) | Buffer (bounded) | Out-of-order delivery is normal; Unknown is a timing artifact. |
| Third-party audit (Tier 3 verification) | Reject | Auditor has the full message set; Unknown means the set is incomplete. |

**Rationale:** The lattice formalization reveals that SPEC-002's `UnknownPredecessor` error conflated two distinct situations: "the predecessor doesn't exist" (timing) and "the predecessor has the wrong type" (violation). Separating them lets agents operating over unordered transports avoid false positives without compromising the detection of genuine violations. The Buffer policy is opt-in and bounded to prevent DoS; the Reject policy preserves SPEC-002's zero-state guarantee.

Trace:
- TEST-305
- CON-302

### REQ-306: Merkle DAG as Lattice Position Certificate

Each message's content hash SHALL serve as a **lattice position certificate** — a cryptographic commitment to the message's position in the causal semilattice (REQ-301).

**Prerequisite: deterministic sort.** For the lattice position certificate to be well-defined, the canonical serialisation of list-valued `:caused-by` must be deterministic. SPEC-002 REQ-202 requires that `:caused-by` hashes are sorted in lexicographic (byte-wise ascending) order before computing the content hash. Without this sort, two agents constructing the same logical join (same set of predecessors) would produce different hashes — the lattice identity property (same element → same hash) would break. The sort ensures that `:caused-by` lists are **set-like** in the canonical form: order-independent, determined solely by membership.

Specifically, because a message's hash is computed over its canonical serialisation which includes its sorted `:caused-by` hashes (SPEC-002 REQ-202), and those hashes in turn commit to their predecessors' content recursively:

1. **M's hash commits to ↓M.** The principal ideal ↓M (all messages causally preceding M) is cryptographically fixed by M's hash. Any alteration to any message in ↓M changes that message's hash, which changes its successor's `:caused-by` hash, which propagates up to M.

2. **Two agents holding the same hash agree on causal history.** If agent A and agent B both hold a message with hash H, they necessarily agree on the entire causal closure of that message. They may disagree on messages *outside* the causal closure (different branches of the DAG), but they agree on everything that causally precedes H.

3. **Fan-in joins commit to the union of predecessors' histories.** A merge message M with `:caused-by (H₁ H₂ H₃)` (sorted) commits to ↓M = ↓H₁ ∪ ↓H₂ ∪ ↓H₃ ∪ {M}. The hash of M is a compact certificate that the sender has observed the union of all three causal histories. Because the hash list is canonically sorted, two agents who observed {H₁, H₂, H₃} in any order produce the same merge message hash.

4. **Verification of lattice position is recursive and local.** To verify that M is at the lattice position it claims, verify: (a) M's hash matches its content (including sorted `:caused-by`), (b) each `:caused-by` hash resolves to a message in the store, (c) each predecessor's hash matches its content (recursively). This is the Tier 3 (full audit) verification from SPEC-002 REQ-212, now understood as lattice position verification.

**No separate certificate format is needed.** The message itself IS the certificate. The Merkle DAG IS the lattice. The hash IS the position. The deterministic sort makes the position unique.

Trace:
- TEST-306

### REQ-307: Eventual Verification

For agents using the Buffer policy (REQ-305), the system SHALL guarantee **eventual verification**: if all messages in a protocol interaction are eventually delivered (possibly out of order), every message will eventually be verified as `Valid` or `Violation`.

Formally: for a message M with `verify(M, store_t) = Unknown` at time t, if all messages in M's causal closure are eventually appended to the store, then there exists a time t' > t such that `verify(M, store_t') ∈ {Valid, Violation}`.

This follows from:
1. The store grows monotonically (append-only).
2. The verification function is monotone (REQ-304).
3. `Unknown` is the only non-stable result — it resolves when the predecessor appears.
4. By assumption, the predecessor eventually appears.

**Liveness assumption.** Eventual verification requires eventual delivery — all messages are eventually received. This is a liveness assumption on the transport, not a property of the verification system. If a message is permanently lost, pending messages that depend on it will remain `Unknown` until TTL expiry.

**Convergence.** Two agents that eventually receive the same set of messages will reach the same verification results for every message, regardless of the order of arrival. This is eventual consistency of the verification function, following from its monotonicity and the confluence of the store lattice (Conway et al. 2012).

Trace:
- TEST-307

### REQ-308: DCFL Preservation

The verification lattice introduces no new parsing capability. `VerificationResult` is an in-memory enum. The three-valued result and the `Unknown` policy are runtime decisions, not grammar extensions. `CausalPending` error messages use the existing CBCL `(error ...)` grammar. DCFL preservation is maintained trivially.

Trace:
- TEST-308

---

### REQ-309: Hash Index (O(1) Lookup)

The message store SHALL maintain a hash index providing O(1) amortised lookup from content hash to message. The index is per-thread: `HashMap<ContentHash, &Message>` scoped to a single `:thread`.

SPEC-002 ADR-006 describes hash lookup as O(n) with an optional auxiliary index. This is insufficient. SPEC-002 NFR-201 requires ≤ 100 ns causal verification latency. A linear scan over a thread with thousands of messages cannot meet this bound. The hash index is a MUST, not a MAY.

The index SHALL be updated on every append. It SHALL NOT be updated on any other operation (no deletions, no mutations). The index is a derived structure — it can be reconstructed from the message store by a full scan. Crash recovery MAY reconstruct the index by replaying the store.

**Thread scoping.** The hash index SHALL enforce thread isolation (SPEC-002 ADR-008). A lookup for hash H in thread T SHALL NOT return a message from thread T'. This prevents cross-thread `:caused-by` references from passing verification. Implementations MAY use a global index with thread-membership validation, or per-thread indexes — the observable behaviour is the same.

Trace:
- TEST-309
- CON-303

### REQ-310: Deduplication (G-Set Idempotence)

The message store SHALL be idempotent under append: appending a message whose content hash already exists in the store SHALL be a no-op. The store SHALL NOT contain two messages with the same content hash.

This is a direct consequence of G-Set CRDT semantics (REQ-300): the join operation is set union, which is idempotent (A ∪ A = A). Without deduplication, the `Vec<Message>` representation would contain duplicates, violating the set abstraction, wasting memory, and producing incorrect results for operations that iterate over the store (e.g., frontier computation, causal closure).

**Deduplication check.** On append, the implementation SHALL check the hash index (REQ-309) for the incoming message's content hash. If present, the append is skipped. This is O(1) amortised.

**Duplicate delivery is normal.** Over gossip transports (Nostr relays, epidemic dissemination), the same message may be delivered multiple times via different paths. Deduplication ensures that the store's logical state is independent of delivery multiplicity.

Trace:
- TEST-310

### REQ-311: Causal Closure Transfer

The system SHALL support a `(meta (causal-closure ...))` message format for transferring a verifiable subset of the message store. A causal closure bundle contains the minimal set of messages needed to independently verify a target message.

```scheme
(meta (causal-closure
  :target "sha256:e4f5...6789"
  :thread "thread-42"
  :messages (
    (lang compaction (pause "context full" :caused-by "begin"
      :thread "thread-42" :sender "@agent-a"))
    (lang compaction (pause-ack :caused-by "sha256:7d3e...a1f0"
      :thread "thread-42" :sender "@agent-b"))
    ;; ... all messages in ↓target
  )))
```

**Completeness.** The bundle SHALL include every message in the principal ideal ↓target — all messages reachable by following `:caused-by` links from the target back to root(s). A complete bundle is self-verifying: every `:caused-by` hash in the bundle resolves to another message in the bundle (or `"begin"`).

**Verification by recipient.** On receiving a causal closure bundle, the recipient SHALL:

1. Parse each message in the bundle (R1–R4 via existing pipeline).
2. Recompute the content hash of each message. The computed hash must match the hash used in downstream `:caused-by` references.
3. Verify completeness: every `:caused-by` hash resolves within the bundle.
4. Verify causal validity: every message passes causal verification (SPEC-002 REQ-203 / SPEC-003 REQ-304) against the bundle as the message store.
5. If all checks pass, merge the bundle into the agent's store (set union — REQ-300). Deduplication (REQ-310) handles messages already present.

**Use cases:**
- **Late joiner.** An agent joining a thread mid-conversation requests the causal closure of the current frontier. The sender constructs the bundle from their store.
- **Tier 2 verification.** A partial verifier needs only the causal closure of the messages it cares about, not the entire thread.
- **Escrow / audit.** A third party receives a bundle and verifies the entire interaction history without having participated.

**Bundle authenticity.** The bundle is as trustworthy as the Merkle DAG itself: any alteration to any message changes its hash, invalidating downstream references. No additional signatures on the bundle are needed — the content addressing provides tamper-evidence. However, the bundle does NOT prove that the included messages are the ONLY messages — an adversary could omit branches. Completeness is verifiable within the bundle (no dangling `:caused-by` references) but not across the full thread without access to other sources.

**Monotonicity.** Merging a causal closure bundle into the store is set union — a monotone operation on the store lattice (REQ-300). Verification results can only improve (Unknown → Valid or Unknown → Violation), never regress.

Trace:
- TEST-311
- CON-304

### REQ-312: Store Reconciliation (Anti-Entropy)

The system SHALL support a reconciliation protocol for two agents on the same thread to discover and repair discrepancies in their message stores. The protocol uses the Merkle DAG structure for efficient set difference computation.

**Reconciliation procedure:**

1. **Frontier exchange.** Agent A sends its frontier (set of leaf message hashes) to Agent B. Agent B compares with its own frontier.

2. **Divergence detection.** If the frontiers match, the stores agree on the causal structure up to the frontier. If they differ, the agents identify the divergence:
   - Hashes in A's frontier but not in B's store → A has messages B lacks.
   - Hashes in B's frontier but not in A's store → B has messages A lacks.
   - Hashes in both frontiers → agreement on that branch.

3. **Causal closure request.** For each hash that one agent has and the other lacks, the agent with the hash sends the causal closure of that hash (REQ-311). The recipient merges it into their store.

4. **Convergence.** After exchanging causal closures for all frontier discrepancies, both agents have the same store state (set union). By the G-Set CRDT merge property (REQ-300), the merged state is the least upper bound.

**Efficiency.** The reconciliation protocol is proportional to the size of the difference, not the size of the store. If agents agree on most of the DAG and differ on a few branches, only the differing branches are transferred. The Merkle structure enables this: agreement on a hash implies agreement on the entire sub-DAG below it.

**Reconciliation message format:**

```scheme
;; Step 1: frontier exchange
(meta (frontier-exchange
  :thread "thread-42"
  :frontier ("sha256:a1b2...c3d4" "sha256:e5f6...7890")))

;; Step 3: respond with causal closures for missing hashes
(meta (causal-closure
  :target "sha256:a1b2...c3d4"
  :thread "thread-42"
  :messages (...)))
```

**Not a consensus protocol.** Reconciliation produces the union of both agents' stores — it does not resolve conflicts or establish agreement on which messages are "correct." There are no conflicts to resolve: the store is a G-Set (grow-only), and union is the unique merge. Two agents that reconcile will have identical stores and identical verification results for every message (eventual consistency — REQ-307).

Trace:
- TEST-312
- CON-305

### REQ-313: Frontier Compaction (Pruning)

The system SHALL support optional compaction of the message store below a **checkpoint** — a signed agreement that a region of the DAG is fully verified and will not be referenced by future messages.

**Checkpoint creation.** A checkpoint is a message declaring that all messages below a specified cut (set of message hashes) are fully verified:

```scheme
(meta (checkpoint
  :thread "thread-42"
  :cut ("sha256:a1b2...c3d4" "sha256:e5f6...7890")
  :verified-by ("@agent-a" "@agent-b")
  :digest "sha256:ffee...1122"))
```

Where:
- `:cut` is the set of message hashes at the compaction boundary (an antichain in the DAG — no message in the cut is an ancestor of another).
- `:verified-by` lists the agents agreeing to the checkpoint.
- `:digest` is the SHA-256 hash of the sorted concatenation of all message hashes below the cut (a commitment to the compacted region).

**Compaction procedure.** After a checkpoint is accepted:

1. Messages strictly below the cut (ancestors of cut messages, excluding the cut messages themselves) MAY be removed from the store.
2. The checkpoint message is retained in the store as a summary.
3. The `:digest` field enables verification that a reconstructed sub-DAG matches the compacted region.
4. Causal verification of messages above the cut continues normally — their `:caused-by` references point to cut messages or later messages, all of which are retained.

**Coordination requirement.** Compaction is inherently non-monotonic: deleting messages from a grow-only set is a retraction. By CALM, this requires coordination. The coordination point is the checkpoint agreement: all parties listed in `:verified-by` must agree before compaction. This is an explicit, bounded coordination event — not a protocol-wide coordination requirement.

**Compaction is optional.** Agents MAY retain the full store indefinitely. The checkpoint mechanism exists for operational reasons (memory, storage) and does not affect correctness — any agent that retains the full store can reconstruct the compacted region and verify the `:digest`.

**Safety property.** Compaction SHALL NOT be performed if any pending message (Buffer policy, REQ-305) has a `:caused-by` reference to a message below the cut. Pending messages must resolve before their predecessors can be compacted.

Trace:
- TEST-313

### REQ-314: Persistence and Crash Recovery

The message store SHALL support durable persistence via a write-ahead log (WAL). The WAL records every append operation. On crash recovery, the store is reconstructed by replaying the WAL.

**WAL format.** Each WAL entry is a serialised message in canonical form (the same serialisation used for content hashing). The WAL is an append-only file — entries are never modified or deleted.

**Recovery procedure:**

1. Open the WAL file.
2. Replay each entry: parse the message, compute its content hash, append to the in-memory store with deduplication (REQ-310).
3. Reconstruct the hash index (REQ-309) from the replayed store.
4. Reconstruct the frontier by identifying leaf messages (unreferenced by any `:caused-by`).
5. If the Buffer policy is active, pending messages are lost on crash — they are not persisted in the WAL (they were never accepted into the store). The sender will retransmit or timeout.

**Integrity verification.** On recovery, the implementation SHOULD verify the Merkle DAG integrity: for each message, recompute the content hash and check that all `:caused-by` references resolve. This detects WAL corruption (bit flips, truncation). A message with a hash mismatch is discarded; its absence will cause downstream messages to produce `Unknown` results, which is correct (the message is effectively lost).

**WAL compaction.** After a frontier checkpoint (REQ-313), WAL entries for compacted messages MAY be removed by rewriting the WAL with only retained messages. This is equivalent to log compaction in event sourcing systems.

**Persistence is optional.** In-memory-only operation (no WAL) is valid for ephemeral agents or testing. The monotonicity and correctness guarantees hold regardless of persistence — they depend on the store lattice, not on durability.

Trace:
- TEST-314

---

## Non-Functional Requirements

### NFR-300: Verification Latency (Unchanged)

The three-valued verification result SHALL NOT increase verification latency beyond SPEC-002's bounds: ≤ 100 ns per message for single-predecessor, O(k) for fan-in.

**Rationale:** The only change is the return type (`VerificationResult` instead of `Result<(), CausalViolation>`). The lookup and comparison operations are identical. The O(1) hash index (REQ-309) is required to meet this bound.

Trace:
- TEST-350

### NFR-301: Buffer Memory Bound

Agents using the Buffer policy SHALL bound pending queue memory to `max_pending × max_message_size` per thread. The default `max_pending` SHALL be 64 messages.

Trace:
- TEST-351

### NFR-302: No Mutable State Under Reject Policy

Agents using the Reject policy (default) SHALL maintain zero bytes of mutable per-thread protocol state, satisfying SPEC-002 NFR-204.

Trace:
- TEST-352

### NFR-303: Hash Index Memory

The hash index (REQ-309) SHALL use no more than 64 bytes per message entry (hash + pointer). For a thread with N messages, the index overhead is ≤ 64N bytes.

Trace:
- TEST-353

### NFR-304: Deduplication Overhead

Deduplication (REQ-310) SHALL add ≤ 50 ns to the append operation (one hash index lookup).

Trace:
- TEST-354

---

## Architecture Decisions

### ADR-300: Three-Valued Result vs Two-Valued

**Context:** SPEC-002 uses `Result<(), CausalViolation>` — two values. `UnknownPredecessor` and `InvalidPredecessor` are both `Err` variants. Over unordered transports, legitimate messages arriving before their predecessors are false-positived as violations.

**Decision:** Replace with `VerificationResult { Unknown, Valid, Violation }`.

**Trade-offs:**

| Factor | Two-valued (SPEC-002) | Three-valued (this spec) |
|---|---|---|
| Simplicity | Simpler — one code path for rejection | One extra case to handle |
| False positives on unordered transports | Yes — timing errors look like violations | No — timing produces `Unknown`, violations produce `Violation` |
| Zero mutable state | Always | Only under Reject policy |
| Blame correctness | May blame sender for timing | Only blames sender for genuine violations |
| Lean proof structure | Ad-hoc per-requirement | Lattice homomorphism — compositional |

**Rationale:** The false positive problem is real. CBCL operates over Nostr relays where message ordering is not guaranteed. Blaming a sender for a timing artifact violates the blame correctness requirement (SPEC-002 REQ-230). The three-valued result is the minimal fix: one new value (`Unknown`) that correctly represents the epistemic state.

### ADR-301: Reject as Default Policy

**Context:** The Buffer policy is more useful over unordered transports. But it introduces mutable state and a DoS surface.

**Decision:** Reject is the default. Buffer is opt-in.

**Rationale:** SPEC-002's zero-state guarantee (NFR-204) is valuable — it means the verification system has no resource to exhaust. The Buffer policy breaks this deliberately. Making it opt-in means agents that don't need it don't pay for it.

### ADR-302: Lattice Formalisation as Separate Spec

**Context:** The lattice structure could be folded into SPEC-002 or written as a separate spec.

**Decision:** Separate spec (SPEC-003).

**Rationale:** SPEC-002 is an engineering specification — it defines syntax, verification procedures, blame, and the pipeline. SPEC-003 is a mathematical specification — it identifies algebraic structure and proves properties compositionally. Different audiences: SPEC-002 is for implementors; SPEC-003 is for the Lean proof and for researchers evaluating the monotonicity claims. Separation keeps SPEC-002 readable for dialect authors who don't need lattice theory.

### ADR-303: Hash Index as Mandatory

**Context:** SPEC-002 ADR-006 describes O(n) hash lookup with an optional hash map index. SPEC-002 NFR-201 requires ≤ 100 ns verification latency.

**Decision:** The hash index is mandatory (REQ-309). O(n) lookup is not sufficient.

**Trade-offs:**

| Factor | O(n) scan | O(1) hash index |
|---|---|---|
| Memory | Zero overhead | ~64 bytes per message |
| Lookup latency | O(n) — grows with thread length | O(1) amortised |
| 100 ns bound at 1000 messages | Impossible (~10 µs) | Achievable (~20 ns) |
| Append cost | O(1) | O(1) amortised (hash insert) |
| Crash recovery | Nothing to rebuild | Rebuild from store (O(n) one-time) |

**Rationale:** 64 bytes per message is negligible (a thread with 10,000 messages uses ~640 KB of index). The verification latency bound is non-negotiable — it is the only way causal checking stays in the noise relative to parsing.

### ADR-304: Compaction Requires Coordination

**Context:** The message store is a G-Set CRDT (grow-only). Pruning messages is a retraction — a non-monotonic operation. By CALM, non-monotonic operations require coordination.

**Decision:** Compaction (REQ-313) requires explicit coordination: a signed checkpoint agreed by all participating agents. This is an honest acknowledgment that pruning is outside the coordination-free envelope.

**Rationale:** The alternative is unbounded growth, which is operationally unacceptable for long-running agents. The checkpoint mechanism makes the coordination point explicit, bounded, and auditable — rather than hiding it in an implicit garbage collection scheme. Agents that never compact are correct; agents that compact with agreement are correct; agents that compact unilaterally risk breaking downstream verification for others.

### ADR-305: Reconciliation via Frontier Exchange

**Context:** Two agents on the same thread may have different store states due to network partitions, relay failures, or different gossip paths. They need a way to discover and repair discrepancies.

**Decision:** Reconciliation via frontier exchange and causal closure transfer (REQ-312).

**Trade-offs:**

| Factor | Full store exchange | Frontier-based reconciliation |
|---|---|---|
| Bandwidth | O(store size) | O(difference size) |
| Latency | Proportional to full store | Proportional to difference |
| Privacy | Reveals entire history | Reveals only differing branches |
| Complexity | Simple | Requires frontier computation and DAG traversal |

**Rationale:** Frontier-based reconciliation is efficient because agreement on a hash implies agreement on the entire sub-DAG below it. This is the same principle Git uses for fetch/push negotiation. The common case (small divergence after a brief partition) transfers very little data.

---

## Contracts

### CON-300: Store Lattice

```
Interface: cbcl_core::lattice::StoreLattice

Trait (conceptual — the store lattice is the mathematical structure,
not necessarily a Rust trait):

  The message store satisfies:
    - Associativity: (A ∪ B) ∪ C = A ∪ (B ∪ C)
    - Commutativity: A ∪ B = B ∪ A
    - Idempotence: A ∪ A = A
    - Bottom: ∅ ∪ A = A

  These are the G-Set CRDT axioms. The existing
  conversation_threads: BTreeMap<String, Vec<Message>>
  satisfies them by construction (append-only, deduplication
  by content hash).

Implements:
  REQ-300

Verified by:
  TEST-300
```

### CON-301: VerificationResult API

```
Interface: cbcl_core::protocol::VerificationResult

Types:
  enum VerificationResult {
      Unknown,                           // ⊥ — predecessor not in store
      Valid,                             // predecessor found, type matches
      Violation(CausalViolation),        // predecessor found, type mismatch
                                         // or malformed hash
  }

Methods:
  fn meet(self, other: VerificationResult) -> VerificationResult
    Post-conditions:
      - Violation ⊓ _ = Violation
      - _ ⊓ Violation = Violation
      - Unknown ⊓ _ = Unknown  (when other ≠ Violation)
      - Valid ⊓ Valid = Valid
    Implements: conjunction for (all ...) fan-in

  fn join(self, other: VerificationResult) -> VerificationResult
    Post-conditions:
      - Valid ⊔ _ = Valid
      - _ ⊔ Valid = Valid
      - Violation ⊔ Unknown = Violation
      - Unknown ⊔ Unknown = Unknown
    Implements: disjunction for (any ...) predecessor check

  fn is_resolved(&self) -> bool
    Post-conditions: true iff self ∈ {Valid, Violation}
    Implements: Kuper's threshold test — has the lattice crossed {Valid, Violation}?

  fn is_stable(&self) -> bool
    Post-conditions: true iff self ∈ {Valid, Violation}
    Note: identical to is_resolved() — once resolved, the result
    is permanent under store growth (monotonicity).

Implements:
  REQ-302, REQ-303

Verified by:
  TEST-302, TEST-303
```

### CON-302: CausalVerifier (Updated from SPEC-002 CON-202)

```
Interface: cbcl_core::protocol::CausalVerifier (replaces SPEC-002 CON-202)

Types:
  enum CausedBy {
      Begin,
      Single(String),                    // single predecessor hash
      Multiple(Vec<String>),             // fan-in: list of predecessor hashes
  }

  enum UnknownPredecessorPolicy {
      Reject,
      Buffer {
          max_pending: usize,
          ttl: Duration,
      },
  }

Functions:
  fn verify_causal(
      msg_performative: &str,
      caused_by: &CausedBy,
      message_store: &dyn MessageStore,
      protocol: &CausalProtocol,
  ) -> VerificationResult
    Pre-conditions: protocol installed, message parsed
    Post-conditions:
      - Unknown: predecessor(s) not in store — undecidable
      - Valid: all predecessor(s) exist and have valid types
      - Violation: predecessor(s) exist with invalid types,
        or hash malformed, or protocol forbids this link
    Mutates: nothing
    Monotonicity: if store₁ ⊆ store₂ then
      verify_causal(m, cb, store₁, p) ≤ verify_causal(m, cb, store₂, p)
    Complexity:
      - Single predecessor: O(1) amortised
      - Multiple predecessors: O(k)

  fn apply_policy(
      result: VerificationResult,
      policy: &UnknownPredecessorPolicy,
      msg: &Message,
      pending_queue: &mut Option<PendingQueue>,
  ) -> PolicyOutcome
    Post-conditions:
      - Valid → PolicyOutcome::Accept
      - Violation → PolicyOutcome::Reject(CausalViolation)
      - Unknown + Reject policy → PolicyOutcome::Pending(CausalPending)
      - Unknown + Buffer policy → PolicyOutcome::Buffered
    Mutates: pending_queue (Buffer policy only)

  enum PolicyOutcome {
      Accept,
      Reject(CausalViolation),
      Pending(CausalPending),           // Unknown + Reject policy
      Buffered,                          // Unknown + Buffer policy
  }

trait MessageStore {
    fn lookup(&self, msg_id: &str) -> Option<&Message>;
    fn lookup_in_thread(&self, msg_id: &str, thread: &str) -> Option<&Message>;
    fn contains(&self, msg_id: &str) -> bool;
    fn append(&mut self, msg: Message) -> bool;
        // returns false if already present (deduplication)
    fn frontier(&self, thread: &str) -> Vec<&Message>;
        // leaf messages — unreferenced by any :caused-by
    fn causal_closure(&self, msg_id: &str) -> Option<Vec<&Message>>;
        // ↓M — all messages reachable by following :caused-by from M
}

Implements:
  REQ-302, REQ-303, REQ-304, REQ-305

Verified by:
  TEST-302, TEST-303, TEST-304, TEST-305
```

### CON-303: Hash Index API

```
Interface: cbcl_core::store::HashIndex

Types:
  struct HashIndex {
      index: HashMap<ContentHash, (ThreadId, usize)>,
      // hash → (thread, position in thread's message vec)
  }

Methods:
  fn insert(&mut self, hash: ContentHash, thread: &str, pos: usize)
    Post-conditions: index contains mapping for hash
    Complexity: O(1) amortised
    Idempotence: inserting the same hash twice is a no-op

  fn lookup(&self, hash: &ContentHash) -> Option<(ThreadId, usize)>
    Post-conditions: returns thread and position if present
    Complexity: O(1) amortised

  fn contains(&self, hash: &ContentHash) -> bool
    Post-conditions: true iff hash is in index
    Complexity: O(1) amortised

  fn rebuild(store: &MessageStore) -> HashIndex
    Post-conditions: index contains all hashes in store
    Complexity: O(N) where N = total messages across all threads
    Note: used for crash recovery (REQ-314)

Implements:
  REQ-309

Verified by:
  TEST-309
```

### CON-304: Causal Closure Transfer API

```
Interface: cbcl_core::store::CausalClosureBundle

Types:
  struct CausalClosureBundle {
      target: ContentHash,
      thread: String,
      messages: Vec<Message>,       // all messages in ↓target, topologically sorted
  }

Functions:
  fn extract(
      target: &ContentHash,
      store: &dyn MessageStore,
  ) -> Result<CausalClosureBundle, ClosureError>
    Pre-conditions: target exists in store
    Post-conditions:
      - messages contains every message in ↓target
      - messages is topologically sorted (predecessors before successors)
      - every :caused-by hash in the bundle resolves within the bundle
    Error model:
      ClosureError::TargetNotFound
      ClosureError::IncompleteStore { missing_hashes }

  fn verify(bundle: &CausalClosureBundle) -> Result<(), BundleVerificationError>
    Post-conditions:
      - Every message's content hash matches its canonical serialisation
      - Every :caused-by hash resolves within the bundle
      - Every causal link is valid per the protocol declaration
    Error model:
      BundleVerificationError::HashMismatch { message, expected, computed }
      BundleVerificationError::DanglingReference { caused_by }
      BundleVerificationError::CausalViolation(CausalViolation)

  fn merge(
      bundle: &CausalClosureBundle,
      store: &mut dyn MessageStore,
  ) -> MergeResult
    Post-conditions:
      - All messages in bundle are in store (set union)
      - Deduplication applied (REQ-310)
    Returns:
      MergeResult { added: usize, deduplicated: usize }

  fn to_sexpr(&self) -> SExpr
    Post-conditions: output is a valid (meta (causal-closure ...)) message

Implements:
  REQ-311

Verified by:
  TEST-311
```

### CON-305: Reconciliation API

```
Interface: cbcl_core::store::Reconciliation

Types:
  struct FrontierExchange {
      thread: String,
      frontier: Vec<ContentHash>,     // leaf message hashes, sorted
  }

  struct ReconciliationDiff {
      i_have_you_lack: Vec<ContentHash>,
      you_have_i_lack: Vec<ContentHash>,
  }

Functions:
  fn compute_frontier(
      store: &dyn MessageStore,
      thread: &str,
  ) -> FrontierExchange
    Post-conditions:
      - frontier contains all leaf message hashes in thread
      - frontier is lexicographically sorted (deterministic)
    Complexity: O(N) where N = messages in thread

  fn diff_frontiers(
      local: &FrontierExchange,
      remote: &FrontierExchange,
      store: &dyn MessageStore,
  ) -> ReconciliationDiff
    Post-conditions:
      - i_have_you_lack: hashes in local frontier not in remote
      - you_have_i_lack: hashes in remote frontier not in local store
    Note: this is an approximation — frontier-level diff, not full
    store diff. Deeper divergence requires recursive DAG comparison.

  fn reconcile(
      diff: &ReconciliationDiff,
      store: &dyn MessageStore,
  ) -> Vec<CausalClosureBundle>
    Post-conditions:
      - One bundle per hash in i_have_you_lack
      - Each bundle is a causal closure (REQ-311)
    Note: bundles may overlap (shared ancestors). Recipient
    handles deduplication on merge (REQ-310).

Implements:
  REQ-312

Verified by:
  TEST-312
```

---

## Purity Boundary Map

### Pure Core (no I/O, no shared state, deterministic)

- `VerificationResult::meet()` — lattice meet, returns result
- `VerificationResult::join()` — lattice join, returns result
- `VerificationResult::is_resolved()` — threshold test, returns bool
- `verify_causal()` — lookup(s) + set membership, returns VerificationResult (reads message store but does not mutate)

### Effectful Shell (orchestrates I/O, calls pure core)

- `apply_policy()` — may mutate pending queue (Buffer policy)
- `PendingQueue::re_evaluate()` — triggered on store growth, calls verify_causal for each pending message
- `PendingQueue::expire()` — triggered by timer, removes expired messages

### Boundary Contracts

- `VerificationResult` — pure core → shell (returned to caller)
- `PolicyOutcome` — shell → pipeline (determines message fate)
- `PendingQueue` — shell only (mutable state, Buffer policy)

### Dependency Rule

Dependencies point inward. `VerificationResult` and `verify_causal` depend only on `alloc` and `core`. `PendingQueue` depends on the pure core but not vice versa.

---

## Test Specifications

### TEST-300: Store Lattice Properties

Verify G-Set axioms on the message store: associativity, commutativity, idempotence of append. Property-based: for random stores A, B, C, `(A ∪ B) ∪ C = A ∪ (B ∪ C)` etc.

Trace: REQ-300

### TEST-301: Causal Semilattice Structure

Verify that `:caused-by` links define a partial order. Property-based: for random message DAGs, verify reflexivity (M ≤ M via trivial path), antisymmetry (if M ≤ N and N ≤ M then M = N — but the DAG is acyclic so this is vacuous for distinct messages), and transitivity (if A ≤ B and B ≤ C then A ≤ C). Verify that fan-in messages are joins: for merge message M with `:caused-by (H₁ H₂)`, verify ↓M = ↓H₁ ∪ ↓H₂ ∪ {M}.

Trace: REQ-301

### TEST-302: Three-Valued Result Construction

Verify VerificationResult construction and ordering. Cover: Unknown < Valid, Unknown < Violation, Valid and Violation are incomparable.

Trace: REQ-302

### TEST-303: Meet and Join Tables

Exhaustively verify the 3×3 meet table and 3×3 join table from REQ-303. 18 cases total.

Trace: REQ-303

### TEST-304: Monotonicity Property

Property-based: for random (message, store) pairs, verify that `verify_causal(msg, store) ≤ verify_causal(msg, store ∪ {random_msg})`. Generate random stores, random additional messages, and check that the result never decreases. Cover: single predecessor, `(all ...)` fan-in, `(any ...)` disjunction.

Trace: REQ-304

### TEST-305: Unknown Predecessor Policy

Scenario 1 (Reject): Predecessor missing, policy = Reject → `PolicyOutcome::Pending` with `CausalPending` error containing `:retry-after`.

Scenario 2 (Buffer): Predecessor missing, policy = Buffer → `PolicyOutcome::Buffered`, message in pending queue.

Scenario 3 (Buffer resolution): Predecessor arrives → pending message re-evaluated → `PolicyOutcome::Accept`.

Scenario 4 (Buffer TTL): Predecessor never arrives, TTL expires → `CausalTimeout`.

Scenario 5 (Buffer overflow): `max_pending` reached → oldest evicted with `CausalBufferFull`.

Scenario 6 (Violation not buffered): Predecessor present but wrong type → `PolicyOutcome::Reject(CausalViolation)` regardless of policy. Violations are never buffered.

Trace: REQ-305

### TEST-306: Lattice Position Certificate

Verify that modifying any message in a causal closure invalidates the root message's hash. Property-based: construct a chain of 5 messages, alter message 2's content, recompute hashes — message 5's hash changes. Verify that two agents computing the hash of the same message independently get the same result.

Trace: REQ-306

### TEST-307: Eventual Verification

Integration test: deliver a protocol's messages in random order to an agent with Buffer policy. Verify that all messages eventually reach `Valid` or `Violation` regardless of arrival order. Property-based: for random permutations of a valid protocol trace, all messages verify as `Valid` after full delivery.

Trace: REQ-307

### TEST-308: DCFL Preservation

Verify that `CausalPending` error messages parse correctly via the existing DCFL parser. Verify that no new grammar productions are introduced.

Trace: REQ-308

### TEST-309: Hash Index

Verify O(1) hash lookup. Insert 10,000 messages across 10 threads, verify all lookups return correct results. Verify thread isolation: lookup for hash H in thread T1 does not return a message from thread T2 even if H exists in T2. Verify rebuild from store produces identical index. Benchmark: lookup latency ≤ 50 ns.

Trace: REQ-309

### TEST-310: Deduplication

Append the same message twice. Verify store contains exactly one copy. Verify `append()` returns `false` on duplicate. Property-based: for random message sequences with duplicates, store size equals number of unique messages. Verify deduplication works across crash recovery (replay WAL with duplicates).

Trace: REQ-310

### TEST-311: Causal Closure Transfer

Scenario 1 (extract): Build a DAG of 10 messages with fan-out and fan-in. Extract causal closure of a leaf. Verify all ancestors included. Verify topological order (predecessors before successors).

Scenario 2 (verify): Receive a valid bundle. Verify passes. Tamper with one message's content (without updating hash). Verify fails with `HashMismatch`. Remove one message from bundle. Verify fails with `DanglingReference`.

Scenario 3 (merge): Merge bundle into a store that already contains some of the messages. Verify deduplication. Verify new messages appear. Verify verification results improve (Unknown → Valid) for previously pending messages.

Scenario 4 (round-trip): Extract closure, serialise to S-expression, parse, verify, merge into empty store. Verify resulting store matches the original closure.

Trace: REQ-311

### TEST-312: Store Reconciliation

Scenario 1 (identical stores): Two agents with identical stores. Frontier exchange produces empty diff.

Scenario 2 (one-sided divergence): Agent A has messages Agent B lacks. Frontier diff identifies them. Causal closure bundles transferred. After merge, stores are identical.

Scenario 3 (mutual divergence): Both agents have messages the other lacks (different branches). Reconciliation produces bundles in both directions. After mutual merge, stores are identical.

Scenario 4 (deep divergence): Agents diverged many messages ago. Verify that only differing branches are transferred, not the common prefix.

Property-based: for two random subsets of a message DAG, reconciliation produces the union.

Trace: REQ-312

### TEST-313: Frontier Compaction

Scenario 1 (basic compaction): Create checkpoint at a cut. Compact messages below cut. Verify messages above cut still verify correctly. Verify causal closure of messages above cut returns the cut as the "floor."

Scenario 2 (digest verification): Compact, then reconstruct the compacted region from an external source. Verify digest matches.

Scenario 3 (safety): Attempt to compact while pending messages reference messages below the cut. Verify compaction is refused.

Scenario 4 (no compaction): Verify that agents that never compact function identically to agents with the full store.

Trace: REQ-313

### TEST-314: Persistence and Crash Recovery

Scenario 1 (basic recovery): Append 100 messages, write WAL, simulate crash (drop in-memory state), recover from WAL. Verify store matches pre-crash state. Verify hash index is correct. Verify frontier is correct.

Scenario 2 (integrity check): Corrupt one byte in the WAL. Recover. Verify the corrupted message is discarded. Verify downstream messages produce `Unknown` results.

Scenario 3 (WAL compaction): Append 100 messages, compact below a checkpoint, rewrite WAL. Recover from compacted WAL. Verify retained messages are correct.

Scenario 4 (no WAL): Run without persistence. Verify all in-memory operations work correctly. Verify crash loses all state (expected).

Trace: REQ-314

### TEST-353: Hash Index Memory

Verify hash index memory usage ≤ 64 bytes per entry. Insert 10,000 messages, measure total index allocation.

Trace: NFR-303

### TEST-354: Deduplication Overhead

Benchmark append with and without deduplication check. Verify overhead ≤ 50 ns per append.

Trace: NFR-304

### TEST-350: Verification Latency Unchanged

Benchmark `verify_causal` returning `VerificationResult` vs the previous `Result<(), CausalViolation>`. Median ≤ 100 ns (SPEC-002 NFR-201).

Trace: NFR-300

### TEST-351: Buffer Memory Bound

Under Buffer policy, fill pending queue to `max_pending`, verify eviction occurs and memory does not exceed `max_pending × max_message_size`.

Trace: NFR-301

### TEST-352: Zero State Under Reject

Under Reject policy, process 1000 messages (some with unknown predecessors), verify zero bytes of mutable per-thread protocol state.

Trace: NFR-302

---

## Lean 4 Formalisation Targets

The lattice formalization is designed to support a Lean 4 mechanised proof. The proof structure:

1. **Define the lattice types.** `StoreLattice` as `Finset Message` with `⊆` and `∪`. `VerificationResult` as an inductive type with an `Ord` instance.

2. **Prove the base case.** A single-predecessor lookup is monotone: `store₁ ⊆ store₂ → verify_single(h, store₁) ≤ verify_single(h, store₂)`. This is the core lemma — everything else composes from it.

3. **Prove compositional closure.** Meet of monotone functions is monotone. Join of monotone functions is monotone. These are standard lattice theory lemmas.

4. **Derive SPEC-002 REQ-211 as a corollary.** The existing monotonicity guarantee is a special case: `verify_causal` is a composition of monotone functions, therefore monotone. QED — no case analysis.

5. **Prove eventual verification.** Under the liveness assumption (eventual delivery), the verification function reaches a fixpoint ∈ {Valid, Violation} for every message. This follows from the lattice being finite (each message resolves independently) and the function being monotone on a lattice with finite height (height 1: Unknown → {Valid, Violation}).

The Lean proof targets the pure core only — `VerificationResult`, `meet`, `join`, `verify_causal`. The effectful shell (Buffer policy, pending queue) is outside the proof scope.

---

## Implementation Plan

### Phase 1: VerificationResult Type (cbcl-core)

1. `src/verification_result.rs` — `VerificationResult` enum, `meet()`, `join()`, `is_resolved()`.
2. Tests (TEST-302, TEST-303).

### Phase 2: Updated CausalVerifier (cbcl-core)

3. Update `src/protocol.rs` — `verify_causal()` returns `VerificationResult` instead of `Result<(), CausalViolation>`.
4. `src/policy.rs` — `UnknownPredecessorPolicy`, `apply_policy()`, `PolicyOutcome`.
5. Tests (TEST-304, TEST-305).

### Phase 3: Message Store Infrastructure (cbcl-core)

6. `src/store/hash_index.rs` — `HashIndex`, per-thread O(1) lookup, `rebuild()`.
7. Update `src/store/mod.rs` — `MessageStore` trait with `append()` (deduplication), `lookup_in_thread()`, `frontier()`, `causal_closure()`.
8. Tests (TEST-309, TEST-310).

### Phase 4: Pipeline Integration

9. Update `run_pipeline()` to use `VerificationResult` and `apply_policy()`.
10. `CausalPending` error message format.
11. Tests (TEST-308).

### Phase 5: Causal Closure Transfer and Reconciliation

12. `src/store/closure.rs` — `CausalClosureBundle`, `extract()`, `verify()`, `merge()`, `to_sexpr()`.
13. `src/store/reconciliation.rs` — `FrontierExchange`, `diff_frontiers()`, `reconcile()`.
14. Tests (TEST-311, TEST-312).

### Phase 6: Compaction and Persistence

15. `src/store/checkpoint.rs` — `Checkpoint`, compaction below cut, digest computation.
16. `src/store/wal.rs` — WAL append, recovery, compaction.
17. Tests (TEST-313, TEST-314).

### Phase 7: Properties and Benchmarks

18. Property-based tests (TEST-300, TEST-301, TEST-304, TEST-307).
19. Benchmarks (TEST-350, TEST-353, TEST-354).

### Phase 8: Lean 4 Proof

20. Lean 4 definitions and base case lemma.
21. Compositional closure lemmas.
22. Eventual verification theorem.
