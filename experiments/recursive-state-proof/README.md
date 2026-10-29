---
mode: explanation
status: experiment
---
# Recursive proof-carrying CBCL state experiment

This experiment applies the recursive-proof approach from
[Proof-Carrying CRDTs](https://github.com/kit-dsn/proof-carrying-crdts) to a small
signed contribution set. It uses real o1js 2.2.0 recursive proofs, not the earlier
Halo2 prototype's pre-enumerated candidate relation. One compiled program accepts
new nonces and amounts without regenerating keys for each message history.

Run from this directory with Node 22+ and Rust available:

```sh
npm ci --ignore-scripts --no-audit --no-fund
npm run check
npm test
python3 mutate.py
npm run prove
```

`npm test` runs arithmetic constraints and a native CBCL fixture comparison;
it does not establish cryptographic proof validity. `npm run prove` additionally
compiles the recursive program, creates real proofs and verifies serialized
proofs. It uses one worker and explicit memory, disk and duration caps.

## What the proof says

The public input names the expected object, operation kind, parent set roots
and appended operation identity. The public output contains the resulting set
root, contribution count and total. A receiver compares the public input with
its own expected context before cryptographic verification.

- `base` proves the empty set for that object.
- `append` verifies its predecessor proof inside the circuit, checks a signature,
  and proves exact union with the specified operation. Duplicate delivery has
  no effect on the committed set or its count/total.
- `merge` verifies both predecessor proofs inside the circuit and proves exact
  union of their sets. Every input record is preserved, every output record
  comes from an input, and shared records occur once.

Records contain a positive UInt32 amount, a UInt32 nonce and one of two signers.
Their Poseidon identities include those fields, the object and a domain tag.
Snapshots are sorted unique sets, with a constrained empty padding encoding.
The current circuit checks whole materialised sets of at most four records.
It does not use Merkle paths and does not support an unbounded materialised set.
Capacity overflow must reject; it cannot silently discard an input record.

The executed fork has this shape:

```text
empty -- add Alice:5 --> shared ancestor
                             |       |
                       add Bob:7   add Alice:3
                             |       |
                          total12  total8
                             \       /
                            exact union
                       count3, total15
```

The shared contribution of 5 is counted once. Self-merge and appending an
already included operation preserve the same set root, count and total.
The public parent roots make the claim checkable against specified checkpoints;
a proof for another branch is not a receipt for those checkpoints.

## Admission, completeness and authentication boundaries

The circuit enforces this fixed experimental admission relation: matching
object, valid experimental signature, positive bounded contribution, canonical
set growth and exact union. It is not a general circuit compiler for CBCL
admission or state rules.

`recursive_oracle.rs` constructs a matching native CBCL dialect and messages,
checks native admission, deduplicates native message identities, and folds the
count and total. The fixtures compare these with the circuit model. This is
fixture-level agreement, not a formal equivalence proof. Experimental Poseidon
record IDs are not native CBCL SHA-256 wire IDs; the mapping from full CBCL bytes
is outside the circuit. Signatures are o1js Schnorr signatures, not CBCL Ed25519.
The exposed test secrets 1 and 2 are synthetic fixtures, never real identities.

An exact-union proof establishes preservation of the **specified** parent heads.
It does not establish that those heads are latest or that every member disclosed
all messages they sent or observed. Members must authenticate and agree the
heads to cover. A verifier that checks only the object and accepts any valid
proof can accept an old branch or an empty base: this experiment's receiver also
checks its caller-owned parent/operation context.

## Evidence and limits

The run records separate compile, prove and verify times, proof sizes, sampled
process-tree RSS and available disk. The receiver verifies the final proof using
its expected public statement and trusted verification key, without predecessor
proofs or operation snapshots. The prover still needs the materialised bounded
sets and immediate predecessor proofs.

The real negative test changes a predecessor's output to a locally consistent
but unproved snapshot and then tries to extend it. This isolates the need for
recursive verification. Generic backend failures are inconclusive and fail the
run; they do not count as a successful invalid-proof rejection. Arithmetic-only
checks separately cover omitted/injected records, incorrect signatures and
public heads, noncanonical sets and capacity overflow.

Review caught missing public parent/operation binding in the initial version.
That compilation was stopped; its partial run is retained under
`evidence/initial-unbound-*`. Corrected-run evidence is separate. No production
binding or runtime consumes this experiment, and no cryptographic deployment
approval is implied.

The next decision is whether to replace the bounded full-set witness with
canonical authenticated-state paths and a constrained CBCL admission/fold
kernel. General application projections, late concurrent replacements,
checkpoint availability and agreed member-head coverage remain integration work.
See `BRIEF.md` for the experimental scope and `RESULTS.md` for observed outcomes.
