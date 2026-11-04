---
mode: explanation
status: experiment-complete
---
# Incremental register proofs over authenticated paths

This experiment proves one actual register update using authenticated state
paths, without enumerating candidate messages or possible histories. Real
serialized proofs for updates after 8 and 256 prior writes verify under one key.
The circuit has 2178 rows and 76 private witness fields in either case.
Measured costs, adversarial review and limitations are in [[experiments/incremental-state-proof/RESULTS]].

It supports a deliberately narrow CBCL subset: sequential writes per signer,
with interleaved independent signers. Each write replaces exactly that signer's
current head. General concurrent replacements, deletion and branch merge are
not implemented. This is a standalone o1js experiment, not a change to the
Halo2 crate or a production protocol.

## Run

Node 22+ and Rust are needed. From this directory:

```sh
npm ci --ignore-scripts --no-audit --no-fund
npm run oracle
npm run check
npm test
python3 oracle-checks.py
python3 mutate.py
npm run prove
npm run verify
```

`npm test` executes witnessed arithmetic constraints and native CBCL comparisons;
it does not establish cryptographic proof validity. `npm run prove` compiles one
program and creates/verifies real proofs under resource limits. `npm run verify`
reverifies serialized artifacts against fresh native expectations and saves the
public verification key. One proof worker is used. `CBCL_INCREMENTAL_ORACLE` may
name an already built oracle binary when a custom Cargo target directory is used.

## What changes on an update

A checkpoint carries a head-tree root, history-log root and write count. The
prover supplies the previous signer head and two depth-16 authentication paths.
The circuit authenticates the old head, checks the signer/path index and exact
replacement/sequence, checks the next history slot is empty at the expected
index, and computes both new roots and the incremented count. The same circuit
and key accept new message identities as the log grows.

The prover still retains tree nodes and history. These are ordinary growing
structures, not a list of all possible histories. The current depth supports
65536 writes and 65536 signer positions; increasing depth changes the circuit
and key. Exhaustion rejects. There is no claim of unbounded or constant storage.

## Trust and scope

The previous checkpoint, expected object and circuit key are receiver-owned.
The proof verifies one transition, not the validity of its entire prior history.
It is nonrecursive; a succession of these proofs still costs one verification
per step until composition is added.

Mapping CBCL bytes, native SHA-256 addresses and authenticated signer labels to
experimental tuples remains a host obligation. The circuit hashes those tuples
with Poseidon; it does not parse CBCL, hash its native wire bytes or check
Ed25519. Native admission and fold are independently exercised by the Rust oracle.
Fixture agreement covers this sequential subset, not general kernel equivalence.

The history log is order-dependent. Its root is not SPEC-035's canonical
accepted-set root and cannot be merged by simply combining two roots. All prior
records remain committed. Compaction, available history and complete member-head
coverage remain separate questions.

Two sibling updates can each prove from one previous checkpoint. A receiver
that wants one linear successor must serialize acceptance against its current
checkpoint. There is no global latest-head guarantee.

[[experiments/incremental-state-proof/BRIEF]] records the hypothesis, bounded language, acceptance criteria and cost
caps. This isolated experiment is not cryptographically audited or authorized
for production. The CBCL maintainer owns the successor specification decision.
