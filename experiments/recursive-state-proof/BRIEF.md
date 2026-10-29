---
mode: explanation
status: experiment
owner: CBCL maintainer
---
# Recursive proof-carrying state experiment

Hypothesis: recursive proofs can certify append and exact union of concurrent
accepted-operation sets, including shared ancestors, without the receiver
replaying historical messages. This follows the proof-carrying CRDT approach
of Marx, Jacob and Hartenstein (PaPoC 2025), implemented with o1js 2.2.0.
The user explicitly requested this experiment after reviewing that work.

The isolated experiment remains on `prototype/halo2-state-checkpoints`. It uses
synthetic public data and experimental Schnorr keys; no production service,
CBCL wire format, authentication component or state rule is changed.
OpenAI Codex generated this experiment; the session identifies GPT-6 without a
more specific model version. It is a Tier 1 cryptographic experiment and carries
no production approval or independent cryptographic audit.

## Approach and acceptance

A fixed circuit accepts arbitrary positive UInt32 contributions with a UInt32
nonce and one of two signers. It commits to a canonical, sorted set of at most
four records and publishes its count and sum. SHA-256 CBCL message identities
and experimental Poseidon record identities are separate; their general byte
encoding equivalence is not proved. A native Rust oracle constructs the matching
CBCL contributions and checks admission and folding for the executed fixtures.
The fixed bound limits materialised sets, not a predeclared candidate vocabulary.

- R1: actual base, append and merge proofs verify after JSON serialization.
- R2: append and merge verify predecessor proofs *inside* the new proof.
  Public context binds the exact expected object, operation kind, parent roots
  and appended operation identity. A receiver supplies its expected context.
- R3: a fork/merge counts a shared ancestor once; self-merge and duplicate append
  preserve the same set root, count and total.
- R4: forged projection, unrelated-object proofs, tampered snapshots, invalid
  signatures and additions omitted from a union fail constraints or verification.
- R5: native CBCL admission/folding matches the positive fixtures, with duplicate
  message identities deduplicated. No general compiler equivalence is claimed.
- R6: one compiled program and verification key support different payloads and
  histories; no subset table or per-history key generation is permitted.

## Resources and exit

Use one proof worker and sequential proving. Measure compile/prove/verify time,
serialized proof size and peak observed memory. Stop the managed run if available
disk falls below 1 GiB or child RSS exceeds 6 GiB. Cap the real-proof run at
20 minutes; record a terminal limit result rather than treating it as success.
Only one real compilation/proof run is required. Constraint-only tests do not
count as cryptographic proof evidence.

The prover materialises bounded current sets and checks exact union; it does not
implement Merkle-path state updates or unbounded garbage collection. A scalable
CBCL integration and formal kernel parity would be the next specification step.
The maintainer owns that decision; retain this experiment as evidence meanwhile.

## Completeness boundary

Exact union is relative to the parent heads in the receiver-owned public context.
It does not establish that those heads are latest or cover all messages anyone
has sent or observed. Members must separately authenticate and agree which heads
are to be covered. Verification of an arbitrary valid history for the same object
is insufficient. Review identified that missing public binding in the initial
version; its compilation was stopped and recorded before the corrected run.
