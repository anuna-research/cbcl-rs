---
mode: explanation
status: implemented
---
# Halo2 state checkpoints

`cbcl-state-proof` is an opt-in crate implementing
[SPEC-035](../../specs/SPEC-035-halo2-state-checkpoints.md): a Halo2 proof
that an accepted CBCL message set grew by exactly a committed batch and
produced a committed state. It uses real proofs with the Halo2 IPA backend
over Pasta curves and no trusted setup. The crate requires Rust 1.85 or newer
because of its locked proof dependencies. It does not change the CBCL wire,
existing admission, state rules, or production bindings. Only `cbcl-cli`
depends on it, optionally, behind the `state-proof` feature.

This is an experimental cryptographic artefact. It is not independently
audited and not approved for production use. The status line above records
that the specification's requirements are implemented and tested; it does not
record a cryptographic review. See the open items at the end.

Run the example from the repository root:

```sh
RAYON_NUM_THREADS=2 cargo run -p cbcl-state-proof --example checkpoint --release
```

The example uses public conformance messages: an opener, a register write, and
its replacement. It independently builds prover and verifier profiles and keys,
serializes a proof, verifies it, and checks that changing the state root fails.
The output separates setup costs from proving and verification with cached
keys, then compiles an eight-candidate profile and reports its circuit size
parameter `k` without proving over it.

## What a checkpoint proof states

A *checkpoint* is a pair of commitments: the accepted-set root and the state
root of one subset of the candidate vocabulary. A proof carries a *statement*
of six roots:

```text
profile identity
previous accepted-set commitment + previous state commitment
next accepted-set commitment     + next state commitment
added-message-set commitment
```

A proof that verifies for a statement the receiver chose establishes three
things relative to that profile. The accepted set grew from the previous
checkpoint to the next by exactly the committed batch. Every added message
was admitted by the native kernel against the previous set under the
installed dialect. The next state root is the native fold of the next set.

Every root is a domain-separated SHA-256 digest, encoded as two 128-bit limbs.
Set commitments cover sorted canonical messages and their signer labels; state
commitments cover the native fold's canonical JSON. The profile binds the
dialect chain, thread, complete candidates, and a semantics version identifying
the base revision. They are flat set commitments, not Merkle trees with
membership paths. All input hashing happens during trusted profile
compilation; SHA-256 is not implemented inside this circuit.

## What it does not state

A successful proof establishes validity relative to that public profile and a
previously trusted or verified checkpoint. It does not establish signatures,
signer enrolment, availability of messages, or completeness relative to unseen
concurrent messages. It does not say who signed each candidate; that is the
authentication boundary below. A small candidate universe can be exhaustively
searched: this crate makes no useful claim about hiding which facts or
messages are present. The proof says nothing about any message outside the
vocabulary, and a verifier built from attacker-supplied inputs proves facts
about the attacker's vocabulary.

## Candidate vocabulary and the eight-candidate ceiling

A verifier chooses the public profile: an installed role-free dialect, a
thread, and at most eight candidate messages with externally authenticated
signer labels. The complete candidate vocabulary is public. For each subset
of the vocabulary the verifier derives admission using the native kernel and
derives its state with the native fold. It also checks each possible monotone
transition by admitting the added messages against the actual previous
accepted set. Pending acts are retried; rejected or unresolved acts make a set
or transition invalid. Host binding checks require the matching dialect,
thread, and one unambiguous `:from` matching the authenticated signer label
(REQ-3512); a set containing a foreign candidate is marked invalid, never
silently dropped.

Snapshot enumeration has at most `2^n` rows; transition enumeration has at
most `3^n` pairs before native admission costs. That is why `n` is capped at
eight (`MAX_CANDIDATES`). New candidate universes require new profiles and
keys. The circuit constrains Boolean subset selection, exact membership in
those verifier-derived relations, both state roots, grow-only membership, and
the exact batch difference. The table constants and wiring are independent of
the prover's witness. A proof cannot substitute a different table or policy
key. The SHA-256 roots are constrained table outputs, not unconstrained values
from a prover's native admission call. This makes the proof an executable
bounded specialisation of CBCL semantics, not a reimplementation of the kernel
in gates.

## Authentication boundary

`Candidate` has private fields and two constructors.
`Candidate::attested(message, signature, signer)` reconstructs the R4 v2
attestation header of the message's innermost simple message, verifies the
signature over it, requires exactly one `:from` naming the same key identity
as the header's sender, and takes the label from `:from` as written.
`Candidate::unauthenticated(text, label)` trusts the host; the label is a
precondition the library does not check. Both give the same profile identity
for the same text and label, so a proof never reveals which path was taken.
Authenticate candidates before constructing the profile. The library also
cannot check that the `Signer` passed to `attested` verifies for the key the
header names; a host that passes a verifier for another key authenticates
nothing. The `lang` wrapper is not covered by the signature; the profile binds
it to the installed dialect instead.

## Receiver-owned expectation and chains

The verifier chooses the expected statement; accepting whatever statement
arrives in a proof is unsafe. `Verifier::verify(proof, expected)` rejects a
package whose statement or profile identity differs from the expectation
before any cryptographic work.

A `Chain` carries one profile identity and up to `MAX_LINKS` (64) proofs.
`Chain::verify(verifier, start, expected_end)` takes the start checkpoint
from the receiver, requires the first link to begin there and each later link
to begin at the previous link's after checkpoint, verifies every link, and
returns the final checkpoint, which for an empty chain is the start. A gap,
profile change, start mismatch, expected-end mismatch or failed link rejects
the whole chain. `Profile::genesis()` is the empty-set checkpoint for
receivers that start from nothing. Verification is linear in the number of
links; there is no recursion or accumulation.

## Package grammar

Proof and chain packages are UTF-8 JSON recognised by `serde_json` with
unknown fields denied, exactly as SPEC-035 CON-3502 states: a proof is
`{"statement", "transcript"}`, a statement is `{"profile", "before", "after",
"batch"}`, a checkpoint is `{"accepted", "state"}`, a chain is `{"profile",
"links"}`; digests are arrays of 32 bytes and a byte is an integer 0 to 255.
Proofs contain 32–16,384 transcript bytes in 32-byte increments. A proof
package is at most 100,000 bytes and a chain package at most 1,048,576 bytes
(SPEC-035 CON-3502); JSON rejects unknown or duplicate members, non-integer or
out-of-range bytes and trailing input other than whitespace. Nothing is
verified from a package that failed recognition, and `Prover::prove` fails
closed rather than return a transcript no recogniser would accept.

## API

`Profile::compile(source, thread, candidates)` recognises and installs the
dialect through CBCL's existing parser and R1–R7 pipeline. Candidate indices
are sorted by their native content addresses. `Profile::mask(addresses)`
constructs a selection independent of input order; `statement(before, after)`
returns the expected roots or an admission error. `state_json(mask)` returns
the native fold. `checkpoint(mask)` returns one checkpoint and `circuit_k()`
the Halo2 size parameter the keys are built with.

`Prover::new(profile)` and `Verifier::new(profile)` generate reusable
parameters and keys for that exact profile. Construct the verifier from its
own expected inputs. `Prover::prove(before, after)` returns a real `Proof`;
`Verifier::verify(proof, expected)` checks the caller-owned statement and
proof. `Proof::to_json`, `Proof::from_json`, `Chain::to_json` and
`Chain::from_json` recognise the bounded, closed JSON packages.

## Semantics version

`SEMANTICS_VERSION` (exported from the crate) names the kernel revision whose
admission and fold semantics a profile identity binds. The identity's hash
domain is `cbcl-state-proof/relation-v1/<SEMANTICS_VERSION>`, so two profiles
compiled from the same dialect, thread and candidates under different versions
have different identities and their proofs do not verify against each other.

`test-vectors/state-proof/signer-supersession.json` pins the identity, every
valid checkpoint and one statement for the signer-supersession fixture. The
test `golden_vector_matches_compiled_profile` recompiles and compares. When a
change to admission or fold semantics makes it fail:

1. Confirm the semantic change is intended; the test is the alarm, not the bug.
2. Bump `SEMANTICS_VERSION` in `src/profile.rs` to the new base revision.
3. Regenerate the vector:
   `cargo test -p cbcl-state-proof -- --ignored write_golden_vector`.
4. Commit the constant, the vector and the code together, and record the
   reason for the semantic change in the commit message.

Never edit the vector by hand, and never regenerate it without a version bump.

## Resource limits

Source limits are 65,536 dialect bytes, 8,192 bytes per candidate, 2,048 bytes
per signer/thread, and 256 native parser expression steps per source/message.
The expression budget also bounds recursive parsing depth. Roles, duplicate
candidate identities, malformed or trailing input, and out-of-profile masks
fail closed. Every limit is checked before enumeration or key setup, so an
oversize input is rejected in milliseconds. For eight candidates the circuit
size parameter is `k = 14`.

## Command-line interface

Build `cbcl-cli` with `--features state-proof` to get the `checkpoint`
subcommand; without the feature the subcommand is absent.

```sh
cargo run -p cbcl-cli --features state-proof -- checkpoint compile profile.json
cargo run -p cbcl-cli --features state-proof -- checkpoint prove profile.json \
    --before <addr>,<addr> --after <addr>,<addr>,<addr> --out proof.json
cargo run -p cbcl-cli --features state-proof -- checkpoint verify profile.json proof.json \
    --before <addr>,<addr> --after <addr>,<addr>,<addr>
cargo run -p cbcl-cli --features state-proof -- checkpoint chain-verify profile.json chain.json \
    [--start <addrs>] [--end <addrs>]
```

`profile.json` is `{"dialect", "thread", "candidates": [{"text", "label"}]}`
with unknown members rejected. Address lists are comma-separated
`sha256-<hex64>` wire addresses; the empty list is `-`. Candidates given this
way are unauthenticated, and every operation prints one warning line on stderr
saying so. Exit codes: 0 success, 1 rejection or verification failure, 2 usage
error.

## Limits and open items

A set root commits to the retained candidate history, not only to visible
property values: replacement and deletion history is not purged. The entire
retained candidate universe is still needed for profile compilation.

This crate does not make large-history projection or new-client startup
cheap. It has no Merkle path updates, dynamic candidate admission, recursive
proof composition, or proof accumulation. Supporting those requires a new
constrained transition kernel, explicit authentication/byte-binding boundaries,
and measurements against replay. Role-free admission is the supported profile;
role-declaring dialects are rejected rather than partly proved.

Open items, owned by the CBCL maintainer unless stated:

- Incremental constrained kernel over authenticated state paths, removing the
  eight-candidate ceiling. It must prove native-kernel parity and retain
  enough conflict, replacement, and admission metadata for late concurrent
  messages. A successor specification.
- Recursive proof composition. A chain of batch proofs still requires growing
  verification work unless composition is added. The
  [o1js experiment](../../experiments/recursive-state-proof/README.md) is
  retained as evidence only.
- Human cryptographic review and production authorisation.
- Lean correspondence between the compiled relation and the SPEC-019 model.
- Pairing a `Signer` with the key it embodies is a host obligation the library
  cannot check. Owner: host integrators.

## Evidence

```sh
RAYON_NUM_THREADS=2 cargo test -p cbcl-state-proof --locked -- --test-threads=1
cargo fmt --all --check
cargo clippy -p cbcl-state-proof --all-targets --locked -- -D warnings
python3 scripts/state-proof-mutations.py
```

Tests include a real serialized proof, independent verifier setup, commitment
and transcript tampering, invalid and pending candidates, state comparison
against the native corpus, replacement, observed deletion, a late concurrent
edit, attested candidates, chains, package recognition with a property test
and a fuzz target, and the golden vector. Circuit-level tests bypass honest
prechecks. Targeted mutations remove a state binding and the previous-context
admission constraint; named tests must execute and fail, rather than merely
fail to compile.

The implementation evidence record is
[docs/evidence/SPEC-035-halo2-state-checkpoints.md](../../docs/evidence/SPEC-035-halo2-state-checkpoints.md).
The experiment scope is recorded in `experiments/state-proof/BRIEF.md`;
observed results and review limitations are recorded in
`experiments/state-proof/RESULTS.md`. This is an experimental cryptographic
artefact, not independently audited or approved for production use.
