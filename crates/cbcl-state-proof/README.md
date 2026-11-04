---
mode: explanation
status: experiment
---
# Bounded CBCL state proofs

`cbcl-state-proof` is an opt-in prototype of a Halo2 proof that an accepted CBCL
message set grew by exactly a committed batch and produced a committed state.
It uses real proofs with the Halo2 IPA backend over Pasta curves.
The prototype requires Rust 1.85 or newer because of its locked proof dependencies. It does not
change the CBCL wire, existing admission, state rules, or production bindings.

Run the example from the repository root:

```sh
RAYON_NUM_THREADS=2 cargo run -p cbcl-state-proof --example checkpoint
```

The example uses public conformance messages: an opener, a register write, and
its replacement. It independently builds prover and verifier profiles and keys,
serializes a proof, verifies it, and checks that changing the state root fails.
The output separates setup costs from proving and verification with cached keys.

## Statement and trust

A verifier chooses the public profile: an installed role-free dialect, a thread,
and up to eight candidate messages with externally authenticated signer labels.
The complete candidate vocabulary is public. The verifier also chooses the
expected statement; accepting whatever statement arrives in a proof is unsafe.

```text
profile identity
previous accepted-set commitment + previous state commitment
added-message-set commitment
next accepted-set commitment     + next state commitment
```

Every root is a domain-separated SHA-256 digest, encoded as two 128-bit limbs.
Set commitments cover sorted canonical messages and their signer labels; state
commitments cover the native fold's canonical JSON. The profile binds the dialect
chain, thread, complete candidates, and a semantics version identifying the base
revision. They are flat set commitments, not Merkle trees with membership paths.
All input hashing happens during trusted profile compilation; SHA-256 is not
implemented inside this circuit.

For each bounded subset, the verifier derives admission using the native kernel
and derives its state with the native fold. It also checks each possible
monotone transition by admitting the added messages against the actual previous
accepted set. Pending acts are retried; rejected or unresolved acts make a set or
transition invalid. Host binding checks require the matching dialect, thread,
and one unambiguous `:from` matching the authenticated signer label.

The circuit constrains Boolean subset selection, exact membership in those
verifier-derived relations, both state roots, grow-only membership, and the
exact batch difference. The table constants and wiring are independent of the
prover's witness. A proof cannot substitute a different table or policy key.
The SHA-256 roots are constrained table outputs, not unconstrained values from
a prover's native admission call. This makes the proof an executable bounded
specialisation of CBCL semantics, not a reimplementation of the kernel in gates.

A successful proof establishes validity relative to that public profile and a
previously trusted or verified checkpoint. It does not establish signatures,
signer enrolment, availability of messages, or completeness relative to unseen
concurrent messages. Authenticate candidates before constructing the profile:
`Candidate::attested(message, signature, signer)` verifies an R4 v2 attestation
over the innermost simple message and takes the label from `:from`;
`Candidate::unauthenticated(text, label)` trusts the host. Both give the same
profile identity for the same text and label.
A small candidate universe can be exhaustively searched: this prototype makes
no useful claim about hiding which facts or messages are present.

## API

`Profile::compile(source, thread, candidates)` recognises and installs the dialect
through CBCL's existing parser and R1–R7 pipeline. Candidate indices are sorted
by their native content addresses. `Profile::mask(addresses)` constructs a
selection independent of input order; `statement(before, after)` returns the
expected roots or an admission error. `state_json(mask)` returns the native fold.

`Prover::new(profile)` and `Verifier::new(profile)` generate reusable parameters
and keys for that exact profile. Construct the verifier from its own expected
inputs. `Prover::prove(before, after)` returns a real `Proof`;
`Verifier::verify(proof, expected)` checks the caller-owned statement and proof.
`Proof::to_json` and `Proof::from_json` recognise the bounded, closed JSON package.

Source limits are 65,536 dialect bytes, 8,192 bytes per candidate, 2,048 bytes
per signer/thread, and 256 native parser expression steps per source/message.
The expression budget also bounds recursive parsing depth. Roles, duplicate
candidate identities, malformed or trailing input, and out-of-profile masks fail
closed. Proofs contain 32–16,384 transcript bytes in 32-byte increments. Packages
are at most 100,000 bytes; JSON rejects unknown fields and trailing input.

## Semantics version

`SEMANTICS_VERSION` (exported from the crate) names the kernel revision whose
admission and fold semantics a profile identity binds. The identity's hash
domain is `cbcl-state-proof/relation-v1/<SEMANTICS_VERSION>`, so two profiles
compiled from the same dialect, thread and candidates under different versions
have different identities and their proofs do not verify against each other.

`test-vectors/state-proof/signer-supersession.json` pins the identity, every
valid checkpoint and one statement for the signer-supersession fixture. The test
`golden_vector_matches_compiled_profile` recompiles and compares. When a change
to admission or fold semantics makes it fail:

1. Confirm the semantic change is intended; the test is the alarm, not the bug.
2. Bump `SEMANTICS_VERSION` in `src/profile.rs` to the new base revision.
3. Regenerate the vector:
   `cargo test -p cbcl-state-proof -- --ignored write_golden_vector`.
4. Commit the constant, the vector and the code together, and record the
   reason for the semantic change in the commit message.

Never edit the vector by hand, and never regenerate it without a version bump.

## Limits and next step

Snapshot enumeration has at most `2^n` rows; transition enumeration has at most
`3^n` pairs before native admission costs. New candidate universes require new
profiles and keys. A set root commits to the retained candidate history, not only
to visible property values: replacement and deletion history is not purged.
The entire retained candidate universe is still needed for profile compilation.

This prototype does not make large-history projection or new-client startup
cheap. It has no Merkle path updates, dynamic candidate admission, recursive
proof composition, or proof accumulation. Supporting those requires a new
constrained transition kernel, explicit authentication/byte-binding boundaries,
and measurements against replay. Role-free admission is the supported profile;
role-declaring dialects are rejected rather than partly proved.

The next experiment is a stable bounded-batch circuit over authenticated state
paths. It must prove native-kernel parity and retain enough conflict, replacement,
and admission metadata for late concurrent messages. A chain of batch proofs
still requires growing verification work unless composition is added.

## Evidence

```sh
RAYON_NUM_THREADS=2 cargo test -p cbcl-state-proof -- --test-threads=1
cargo fmt -p cbcl-state-proof -- --check
cargo clippy -p cbcl-state-proof --all-targets --no-deps -- -D warnings
python3 scripts/state-proof-mutations.py
```

Tests include a real serialized proof, independent verifier setup, commitment and
transcript tampering, invalid and pending candidates, state comparison against
the native corpus, replacement, observed deletion, and a late concurrent edit.
Circuit-level tests bypass honest prechecks. Targeted mutations remove a state
binding and the previous-context admission constraint; named tests must execute
and fail, rather than merely fail to compile.

The experiment scope is recorded in `experiments/state-proof/BRIEF.md`; observed
results and review limitations are recorded in `experiments/state-proof/RESULTS.md`.
This is an experimental cryptographic artefact, not independently audited or
approved for production use.

A subsequent [recursive experiment](../../experiments/recursive-state-proof/README.md)
uses real o1js predecessor-proof verification over arbitrary bounded contribution
sets. It tests exact fork/merge union and public expected-head binding; it is
separate from this Halo2 relation prototype.
