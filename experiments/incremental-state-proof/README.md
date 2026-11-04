---
mode: explanation
status: experiment-complete
---
# Register proofs over authenticated paths

This experiment proves one actual register update using authenticated state
paths, without enumerating candidate messages or possible histories. Real
serialized proofs for updates after 8 and 256 prior writes verify under one key.
The circuit has 2178 rows and 76 private witness fields in either case.
Measured costs, adversarial review and limitations are in [[experiments/incremental-state-proof/RESULTS]].

A separate recursive program now composes that same transition kernel from a
fixed empty write checkpoint. Its final proof establishes the complete supported
history, rather than just the last update. See
[[experiments/incremental-state-proof/RECURSION-RESULTS]] for executed whole-history
measurements and [[experiments/incremental-state-proof/RECURSION-BRIEF]] for its
contract. The original nonrecursive program and evidence remain available.

Both support a deliberately narrow CBCL subset: sequential writes per signer,
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

## Run recursive composition

After installing dependencies and building the oracle as above:

```sh
npm run recursive:test
python3 recursive-mutate.py
npm run recursive:prove -- --target=128
python3 recursive-recovery-check.py
npm run recursive:verify -- --trusted-key=evidence/recursive/verification-key.json
python3 recursive-proof-mutation.py
```

The managed recursive run uses one worker with a 30-minute run limit, 4 GiB
sampled RSS cap and 1 GiB disk reserve. It saves progress after each fixed-eight
batch. `--resume --target=128` recovers an interrupted run; `--resume --target=256`
extends the same full-history proof if a longer measurement is wanted. Only
actually proved lengths are reported. The isolated proof-verification mutation
uses an intentionally unsafe temporary program and key, with a separate 15-minute
cap and no persistent proving-key cache.

A minimal receiver needs only the final proof plus its independently trusted key
and selected expected head:

```sh
node --import tsx recursive-one-proof.ts \
  evidence/recursive/history-128.json \
  evidence/recursive/verification-key.json \
  evidence/recursive/expected-head-128.json
```

The key and expected head are receiver trust inputs. Accepting arbitrary values
for them from the prover establishes no selected object/history claim. The audit
verifier can also compile the key from source when `--trusted-key` is omitted;
that setup is separate from cached proof-verification timing. The measured
receiver works without an oracle or predecessor-proof files.

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
The original program verifies one transition from a trusted prior checkpoint.
The recursive program fixes the empty origin and cryptographically verifies every
predecessor, establishing the complete supported write history in one final proof.
The opener remains a trusted host input in either experiment.

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
