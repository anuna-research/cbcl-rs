---
id: SPEC-035
title: Halo2 State Checkpoints — bounded proofs of accepted-set growth and native state
version: 0.2.0
status: implementing
last-updated: 2026-11-04
author: Anuna Research (https://anuna.io) — drafted with Claude Fable 5.1
owner: CBCL maintainer
depends-on:
  - SPEC-019 (state rules — the admit and fold kernel the relation is compiled from)
  - SPEC-015 (evidence widening v2 — the R4 v2 attestation header a candidate is authenticated by)
  - SPEC-017 (typed content addresses — the address a candidate is named by)
  - SPEC-003 (verification lattice — accepted sets grow by union and never shrink)
prior-art:
  - experiments/state-proof/BRIEF.md and RESULTS.md — the bounded Halo2 experiment this spec converts
  - experiments/recursive-state-proof — the o1js recursive experiment, retained as evidence and not productised here
  - Marx, Jacob, Hartenstein, Proof-Carrying CRDTs (PaPoC 2025)
repository: https://git.anuna.io/anuna-research/cbcl-rs
---

# SPEC-035: Halo2 State Checkpoints

The key words MUST, MUST NOT, REQUIRED, SHALL, SHALL NOT, SHOULD, SHOULD NOT,
RECOMMENDED, MAY, and OPTIONAL in this document are to be interpreted as
described in BCP 14 (RFC 2119, RFC 8174) when, and only when, they appear in
all capitals.

## Orientation

Intent: let a party that holds a trusted checkpoint of a CBCL thread accept a
later checkpoint by verifying a small proof, instead of replaying the messages
between them. The proof says three things. The accepted set grew by exactly the
stated batch. Every added message was admitted against the previous set under
the installed dialect. The new state is the native fold of the new set.

Vocabulary used below. A *candidate* is one message that could appear in the
thread. The *candidate vocabulary* is the list of at most eight candidates both
prover and verifier agree on; it is public in the sense that both sides know
it, and the circuit's table constants are compiled from it. *Native* means
computed by the Rust kernel of [[SPEC-019-state-rules]], outside any circuit.
*Enumeration* is the verifier's compilation of every subset and every admitted
(before, after) pair of the vocabulary into a table. *Recognition* is the full
parse of a package against its closed grammar before any field is used. A
*role-declaring dialect* is one whose protocol carries `:roles` annotations
([[SPEC-014-role-layer-endpoint-projection]]); such dialects are out of scope.

Metaphor: a notarised ledger page. The house rules are public. The notary
stamps a page only when it follows from the previous page under those rules,
for a known, finite list of entries that could appear. The stamp does not say
who signed each entry. The host checks signatures first and hands the notary
only authenticated entries; a host that skips that step gets a stamp that says
nothing about authorship, and the stamp looks the same either way.

Structure:

```text
 host (effectful shell)                            cbcl-state-proof (pure core, opt-in crate)
┌──────────────────────────┐  dialect, thread,    ┌──────────────────────────────────────────┐
│ authenticate candidates  │  candidates          │ Profile::compile          CON-3500       │
│ R4 v2 attestation        │ ────────────────────▶│  parser + R1–R7 + admit + fold           │
│ CON-3504 (reuse SPEC-015)│                      │  = finite relation (rows, transitions)   │
└──────────────────────────┘                      └──────────────────┬───────────────────────┘
                                                                     │ fixed table constants
┌──────────────────────────┐  expected statement  ┌──────────────────▼───────────────────────┐
│ Verifier compiles its own│ ────────────────────▶│ StateCircuit              CON-3501       │
│ profile; owns expectation│                      │  Boolean masks, exact row equality,      │
│ REQ-3502                 │ ◀── accept / reject ─│  grow-only, exact batch, admitted pair   │
└──────────────────────────┘                      └──────────────────┬───────────────────────┘
                                                                     │ Halo2 IPA transcript
┌──────────────────────────┐  packages in         ┌──────────────────▼───────────────────────┐
│ cbcl checkpoint …  CLI   │ ────────────────────▶│ Proof / Chain recognisers CON-3502       │
│ CON-3505 (feature-gated) │ ◀── results out ─────│ Chain verification        CON-3503       │
└──────────────────────────┘                      └──────────────────────────────────────────┘
 left-to-right arrows carry inputs into the pure core; right-to-left arrows carry results
 back to the shell. Vertical arrows show one core stage feeding the next. The core performs
 no I/O. The Verifier box is a host-side role that calls the core.
```

Decisions:
[[SPEC-035-halo2-state-checkpoints#ADR-3500]] verifier-derived finite relation, not an in-circuit kernel ·
[[SPEC-035-halo2-state-checkpoints#ADR-3501]] Halo2 IPA over Pasta, no trusted setup ·
[[SPEC-035-halo2-state-checkpoints#ADR-3502]] flat SHA-256 set and state commitments, no Merkle tree ·
[[SPEC-035-halo2-state-checkpoints#ADR-3503]] opt-in crate and feature-gated CLI ·
[[SPEC-035-halo2-state-checkpoints#ADR-3504]] reuse R4 v2 attestation for candidate authentication ·
[[SPEC-035-halo2-state-checkpoints#ADR-3505]] chains compose by sequential verification from a receiver-pinned start.

Load-bearing:
[[SPEC-035-halo2-state-checkpoints#REQ-3500]] verifier-compiled relation ·
[[SPEC-035-halo2-state-checkpoints#REQ-3501]] native parity ·
[[SPEC-035-halo2-state-checkpoints#REQ-3504]] authenticated candidates ·
[[SPEC-035-halo2-state-checkpoints#REQ-3505]] checkpoint chain ·
[[SPEC-035-halo2-state-checkpoints#REQ-3506]] semantics version pin ·
[[SPEC-035-halo2-state-checkpoints#REQ-3512]] thread, dialect and signer binding.

Controls (exhaustive):
- [[SPEC-035-halo2-state-checkpoints#REQ-3502]] a single-proof verifier SHALL NOT take its expected statement from the package; a chain verifier SHALL take its start checkpoint from the receiver, never from the package.
- [[SPEC-035-halo2-state-checkpoints#REQ-3503]] a proof SHALL NOT verify when the accepted set shrinks or the batch is not the exact difference.
- [[SPEC-035-halo2-state-checkpoints#REQ-3504]] a bare signer label SHALL enter a profile only through `Candidate::unauthenticated`; `Candidate` fields SHALL be private.
- [[SPEC-035-halo2-state-checkpoints#REQ-3505]] a chain with any gap, profile change, start mismatch or failed link SHALL NOT verify.
- [[SPEC-035-halo2-state-checkpoints#REQ-3507]] more than 8 candidates, 65,536 dialect bytes, 8,192 bytes per message, 2,048 bytes per label or thread, or 256 parser expression steps SHALL fail closed before enumeration.
- [[SPEC-035-halo2-state-checkpoints#REQ-3508]] no verification SHALL run on a package that failed recognition; transcripts are 32 to 16,384 bytes in 32-byte steps; packages are at most 100,000 bytes; chains carry at most 64 links.
- [[SPEC-035-halo2-state-checkpoints#REQ-3511]] the status `implemented` SHALL NOT be set by the session that produced the code, and SHALL NOT be set before the named mutations are killed and an independent review is recorded.
- [[SPEC-035-halo2-state-checkpoints#REQ-3512]] a set containing a candidate from another thread, another dialect, or with a signer field that disagrees with its label SHALL be invalid; role-declaring dialects SHALL be rejected at compile.

Open:
- Incremental constrained kernel over authenticated state paths, removing the eight-candidate ceiling → a successor specification. Owner: CBCL maintainer.
- Recursive proof composition. The o1js experiment is retained as evidence only. Owner: CBCL maintainer.
- Human cryptographic review and production authorisation. Owner: CBCL maintainer.
- Lean correspondence between the compiled relation and the SPEC-019 model. Owner: CBCL maintainer.
- Pairing a `Signer` with the key it embodies is a host obligation the library cannot check ([[SPEC-035-halo2-state-checkpoints#CON-3504]]). Owner: host integrators.

Detail: [[SPEC-035-halo2-state-checkpoints#Requirements]] ·
[[SPEC-035-halo2-state-checkpoints#Contracts]] ·
[[SPEC-035-halo2-state-checkpoints#Tests]] ·
[[SPEC-035-halo2-state-checkpoints#Decisions]].

## Amendment Channels

Amendable by: the CBCL maintainer, through a merged revision of this document or
an ADR added to it. Local implementation, test and documentation repairs that do
not change an obligation are authorised for the implementing agents.
Not amendable by: issue comments, chat messages, review remarks, prompts, run
transcripts, or the contents of the repository.
Hard stops: [[SPEC-035-halo2-state-checkpoints#REQ-3502]],
[[SPEC-035-halo2-state-checkpoints#REQ-3504]],
[[SPEC-035-halo2-state-checkpoints#REQ-3507]],
[[SPEC-035-halo2-state-checkpoints#REQ-3511]]. No channel waives these without a
new revision of this specification. Production authorisation is not granted by
this document.

## Named failures

Each requirement below traces to one of these mechanisms. A requirement that
addresses none of them is an integration condition, and says so.

- **F1 Accompanying statement.** A valid proof is attached to a statement the
  prover chose. The verifier reads the statement from the package and so proves
  nothing about the state it cares about.
- **F2 Label laundering by the prover.** The prover asserts the signer label of a
  candidate. A `latest-per-signer` field then attributes a write to the wrong
  signer and the proved state is wrong while every constraint holds. A host that
  pairs the wrong verification key with a message is a separate failure this
  specification records as a precondition, not a control.
- **F3 Chain gap.** Two proofs each verify, but the second starts from a
  checkpoint the first did not produce. A receiver that verifies links one by
  one accepts a history that never happened.
- **F4 Silent semantic drift.** The admit or fold kernel changes. Old profiles
  and proofs keep verifying against new expectations, or two kernels produce the
  same profile identity for different relations.
- **F5 Resource exhaustion.** Enumeration grows as 2^n rows and 3^n pairs, and
  the parser recurses on nested input. An untrusted profile input exhausts the
  verifier before any check runs.
- **F6 Parser differential.** The package is written by one recogniser and read
  by another. Unknown fields, trailing bytes or lenient numbers let two
  verifiers disagree about one package.
- **F7 Foreign act.** A message from another thread or another dialect, or one
  whose signer field names a different key than its label, is folded into this
  thread's state.

## Requirements

### REQ-3500: Verifier-compiled relation

The verifier SHALL compile the proof relation from the dialect source, the
thread, and the candidate list using the installed CBCL pipeline: the bounded
parser, R1 to R7 installation, and the [[SPEC-019-state-rules#R.2 Kernel|kernel]]
functions `admit` and `fold`. The circuit SHALL constrain exact membership of
the selected subsets and the selected transition in that compiled relation. The
relation constants SHALL be independent of the prover's witness.
Addresses F1.
Trace: [[SPEC-035-halo2-state-checkpoints#TEST-3500]],
[[SPEC-035-halo2-state-checkpoints#CON-3500]],
[[SPEC-035-halo2-state-checkpoints#CON-3501]].

### REQ-3501: Native parity

For every valid subset of the candidate vocabulary, the state commitment SHALL
be the commitment of the canonical JSON rendering of the native fold of that
subset. A transition from set A to set B SHALL be in the relation if and only if
A ⊆ B, both are valid, and native admission of B \ A against A reaches a fixed
point with no rejected or unresolved act. Pending acts SHALL be retried to the
fixed point.
Addresses F1.
Trace: [[SPEC-035-halo2-state-checkpoints#TEST-3500]],
[[SPEC-035-halo2-state-checkpoints#CON-3500]].

### REQ-3502: Receiver-owned expectation

(a) A single-proof verifier SHALL NOT accept the statement carried in a proof
package as the statement to verify. The expected statement SHALL be a caller
input. (b) A package whose statement differs from the expectation, or whose
profile identity differs from the verifier's compiled profile, SHALL be rejected
before cryptographic verification. (c) A chain verifier SHALL take the start
checkpoint from the receiver and SHALL compare each link's before checkpoint to
the running checkpoint; the after checkpoints and batch roots inside the links
are the prover's claims, each proved against the running checkpoint by that
link's circuit. (d) When the receiver supplies an expected final checkpoint,
the chain verifier SHALL reject a chain whose derived final checkpoint differs.
Addresses F1.
Trace: [[SPEC-035-halo2-state-checkpoints#TEST-3501]] (a, b),
[[SPEC-035-halo2-state-checkpoints#TEST-3504]] (c, d),
[[SPEC-035-halo2-state-checkpoints#CON-3503]].

### REQ-3503: Grow-only exact batch

The circuit SHALL reject a witness in which any candidate selected before is not
selected after. The circuit SHALL bind the public batch commitment to the exact
set difference after \ before. Both obligations SHALL hold inside the circuit,
independently of any host precheck.
Addresses F1.
Trace: [[SPEC-035-halo2-state-checkpoints#TEST-3502]],
[[SPEC-035-halo2-state-checkpoints#CON-3501]].

### REQ-3504: Authenticated candidates

(a) `Candidate` SHALL expose no public fields; the only constructors SHALL be
`Candidate::attested` and `Candidate::unauthenticated`. (b) `attested` SHALL
accept a message, a signature and a `Signer`, SHALL reconstruct the R4 v2
attestation header of the message's innermost simple message through
`attestation_header_for`, and SHALL verify the signature over that header. (c)
`attested` SHALL reject a message whose innermost simple message lacks
`:sender` or `:thread`, or whose `:from` field does not name the same key
identity as the header's sender under `KeyId::parse`. (d) The signer label of
an attested candidate SHALL be the `:from` field's text as written. (e)
`unauthenticated` SHALL be documented as a host precondition; a profile built
from an unauthenticated candidate and one built from the attested candidate
with the same label SHALL have the same identity, so a proof never reveals
which path was taken.
Addresses F2.
Trace: [[SPEC-035-halo2-state-checkpoints#TEST-3503]],
[[SPEC-035-halo2-state-checkpoints#CON-3504]].

### REQ-3505: Checkpoint chain

A chain SHALL carry one profile identity and an ordered list of at most 64
proofs. `Chain::verify` SHALL take the receiver's start checkpoint and an
optional expected final checkpoint. It SHALL require that every proof's profile
identity equals the chain's and the verifier's, that the first proof's before
checkpoint equals the start, and that each later proof's before checkpoint
equals the previous proof's after checkpoint. It SHALL verify every link's
proof and SHALL return the final checkpoint, which for an empty chain is the
start. A chain with any gap, profile change, start mismatch, expected-end
mismatch or failed link SHALL NOT verify. The profile's empty-set checkpoint
SHALL be available as `Profile::genesis` for receivers that start from nothing.
Addresses F3.
Trace: [[SPEC-035-halo2-state-checkpoints#TEST-3504]],
[[SPEC-035-halo2-state-checkpoints#CON-3503]].

### REQ-3506: Semantics version pin

(a) The profile identity SHALL bind a named constant `SEMANTICS_VERSION` in its
domain string, and a function `relation_domain(version)` SHALL make that binding
testable. (b) A golden test vector SHALL pin the profile identity, every valid
checkpoint, and one statement for the signer-supersession fixture. (c) A change
to admission or fold semantics that alters any pinned value SHALL be
accompanied by a new `SEMANTICS_VERSION` and a regenerated vector; the
procedure SHALL be written in the crate README. (d) The profile identity SHALL
be independent of candidate order and of insignificant whitespace in candidate
text.
Addresses F4.
Trace: [[SPEC-035-halo2-state-checkpoints#TEST-3505]],
[[SPEC-035-halo2-state-checkpoints#CON-3500]].

### REQ-3507: Resource bounds

Profile compilation SHALL return an error, before any enumeration or key setup,
when (a) the candidate count exceeds 8, (b) the dialect source exceeds 65,536
bytes, (c) a candidate's text exceeds 8,192 bytes, (d) a signer label or the
thread exceeds 2,048 bytes, or (e) parsing the dialect or any candidate needs
more than 256 expression steps. It SHALL also return an error, before
enumeration, for (f) duplicate candidate identities, (g) malformed or trailing
input in the dialect or a candidate, and (h) a role-declaring dialect. The
256-step budget bounds both recursion depth and node count; dialects with more
than 256 S-expression nodes are out of scope.
Addresses F5.
Trace: [[SPEC-035-halo2-state-checkpoints#TEST-3506]],
[[SPEC-035-halo2-state-checkpoints#CON-3500]].

### REQ-3508: Package recognition

(a) Proof and chain packages SHALL be recognised against
[[SPEC-035-halo2-state-checkpoints#CON-3502]] before any field is read for
verification. (b) An unknown member, a duplicate member, a non-integer or
out-of-range byte value, a package over 100,000 bytes, a transcript outside 32
to 16,384 bytes or not a multiple of 32, a chain over 64 links, or trailing
input other than JSON whitespace SHALL be rejected. (c) `Proof` and `Chain`
SHALL implement `PartialEq` and `Eq`, and for every value the crate writes,
reading it back SHALL yield an equal value. (d) `Prover::prove` SHALL fail
closed when its transcript would exceed 16,384 bytes.
Addresses F6.
Trace: [[SPEC-035-halo2-state-checkpoints#TEST-3507]],
[[SPEC-035-halo2-state-checkpoints#CON-3502]].

### REQ-3509: Workspace integration

(a) The crate `cbcl-state-proof` SHALL be a workspace member and SHALL pass the
repository's `make check` gate: formatting, clippy with warnings denied, and
tests under `--locked`. (b) No crate other than `cbcl-cli` SHALL depend on it,
and `cbcl-cli` SHALL depend on it only as an optional dependency behind the
`state-proof` feature. (c) The `no_std`, WebAssembly, FFI and Erlang bindings
SHALL be unaffected. (d) The `examine_re` list in `mutants.toml` SHALL NOT list
the Halo2 crate, and the targeted mutation runner SHALL live at
`scripts/state-proof-mutations.py`.
Addresses no named failure; it is the integration condition the user asked for.
Trace: [[SPEC-035-halo2-state-checkpoints#TEST-3508]].

### REQ-3510: Command-line interface

The `cbcl` binary SHALL offer a `checkpoint` subcommand behind the cargo feature
`state-proof`, with the operations `compile`, `prove`, `verify` and
`chain-verify` as specified in [[SPEC-035-halo2-state-checkpoints#CON-3505]].
Without the feature the subcommand SHALL be absent and the binary SHALL be
unchanged. Every operation SHALL read its inputs through the same recognisers as
the library and SHALL exit non-zero on any rejection.
Addresses F6 at the tool boundary.
Trace: [[SPEC-035-halo2-state-checkpoints#TEST-3509]],
[[SPEC-035-halo2-state-checkpoints#CON-3505]].

### REQ-3511: Evidence before completion

WHEN the implementation is proposed as complete, the implementing agents SHALL
withhold the status `implemented` and SHALL record the evidence file named in
[[SPEC-035-halo2-state-checkpoints#TEST-3510]], with the open items of this
document listed for the CBCL maintainer. The status SHALL remain
`implementing` until every named mutation is killed by an executed failing test
and an independent fresh-context review is recorded. The status SHALL be set by
the reviewing session, not the producing session. Human cryptographic review
and production authorisation SHALL remain recorded as open in this document
until the maintainer closes them.
Addresses the review obligation of a Tier 1 artefact.
Trace: [[SPEC-035-halo2-state-checkpoints#TEST-3510]].

### REQ-3512: Thread, dialect and signer binding

A subset of the vocabulary SHALL be invalid in the compiled relation when it
contains a candidate (a) whose `:thread` differs from the profile thread, (b)
whose dialect wrapper names a dialect other than the installed one, or (c)
whose `:from` field, or `:sender` field when present, is not exactly the
candidate's signer label. Compilation SHALL succeed and mark such sets invalid;
it SHALL NOT silently drop the candidate. A `:from` written as a string and the
same key written as a symbol are distinct candidates with distinct addresses, as
everywhere in CBCL.
Addresses F7.
Trace: [[SPEC-035-halo2-state-checkpoints#TEST-3500]],
[[SPEC-035-halo2-state-checkpoints#CON-3500]].

### NFR-3500: Proof budget

For the three-candidate signer-supersession fixture, cached-key verification
SHALL complete in at most 1,000 ms, the transcript SHALL be at most 16,384
bytes, and the JSON package SHALL be at most 100,000 bytes, measured with two
Rayon workers on a machine whose model and CPU are recorded beside the
measurement. For eight candidates the circuit size parameter k SHALL be at most
14.
Trace: [[SPEC-035-halo2-state-checkpoints#TEST-3511]].

## Contracts

### CON-3500: Profile compiler

Interface: `Profile::compile(source: &str, thread: &str, candidates: &[Candidate]) -> Result<Profile, String>`;
`Profile::id() -> [u8; 32]`; `Profile::genesis() -> Checkpoint`;
`Profile::addresses() -> &[String]`; `Profile::mask(&[&str]) -> Result<u16>`;
`Profile::checkpoint(u16) -> Result<Checkpoint>`; `Profile::state_json(u16) -> Result<&str>`;
`Profile::statement(u16, u16) -> Result<Statement>`.

Input grammar: `source` is one CBCL dialect definition in the S-expression
grammar of `docs/cbcl-grammar.ebnf`, parsed by `cbcl_parser::parser::parse_with_fuel`
with fuel 256. Each candidate's text is one CBCL message in the same grammar
with the same fuel; the message is a `lang`-wrapped simple message as the state
fixtures show. Labels and the thread are UTF-8 strings of at most 2,048 bytes.
No second parser is introduced.

Pre-conditions, one clause per requirement:
- the size and fuel bounds of REQ-3507 (a) to (e) hold before any other work;
- the dialect installs through `parse_and_install_dialect`, has a state clause
  and a protocol, and declares no roles (REQ-3500, REQ-3507 h);
- every candidate parses to a message and to an `Act` under its signer label,
  and identities are distinct (REQ-3507 f, g).

Post-conditions:
- `id()` is `SHA-256` over length-prefixed parts with domain
  `relation_domain(SEMANTICS_VERSION)` = `cbcl-state-proof/relation-v1/<SEMANTICS_VERSION>`,
  over the canonical dialect text, the dialect hash, the thread and the
  (label, canonical text) pairs sorted by candidate content address (REQ-3506);
- one row per subset, indexed by bit mask in candidate-address order, with
  validity, accepted-set commitment and state commitment; a set is valid only
  when REQ-3512 (a) to (c) hold for every member and native admission from the
  empty set reaches a fixed point (REQ-3500, REQ-3501, REQ-3512);
- the sorted list of admitted (before, after) transitions (REQ-3501);
- `addresses()` are wire addresses `sha256-<hex64>` in the order used for bit
  positions; `mask`, `checkpoint`, `state_json` and `statement` reject indices
  outside the profile and sets containing an unadmitted candidate;
- `genesis()` equals `checkpoint(0)`.

Error model: `Err(String)` naming the first failed pre-condition. No partial
profile is returned.

Implements: REQ-3500, REQ-3501, REQ-3506, REQ-3507, REQ-3512.
Verified by: TEST-3500, TEST-3505, TEST-3506.

### CON-3501: Circuit statement

Public instance, in order: profile identity, before accepted-set root, before
state root, after accepted-set root, after state root, batch root. Each 32-byte
digest is two field elements: limb 0 holds bytes 0 to 15 and limb 1 holds bytes
16 to 31, each read as a little-endian 128-bit integer. Twelve field elements.

Gates: Boolean selection of each before and after bit; complement and
conjunction gates building exact subset indicators; fixed-weight accumulation
selecting the row constants for the before set, the after set and the batch;
grow-only gate `old · (1 − new) = 0` per candidate; transition accumulation
whose final total is constrained to one over the compiled admitted pairs; and
constant constraints forcing both selected rows valid and the identity limbs
equal to the compiled profile identity.

Post-condition: a proof verifies if and only if the witness selects a valid
before row, a valid after row, their pair is an admitted transition, after
includes before, and the public limbs equal the selected constants.

Implements: REQ-3500, REQ-3503.
Verified by: TEST-3500, TEST-3502.

### CON-3502: Package grammar

Both packages are JSON texts (RFC 8259), UTF-8, at most 100,000 bytes. The
recogniser is `serde_json::from_slice` into the Rust types below, every struct
carrying `#[serde(deny_unknown_fields)]`. The grammar is the set of JSON texts
that recogniser accepts, which is stated here so a second implementation can be
checked against it:

- JSON whitespace is permitted between tokens and after the final value;
  any other trailing input is rejected.
- Object member order is not significant. A duplicate member is rejected.
- A byte is a JSON integer in 0 to 255 with no fraction, exponent or sign.
- `h32` is an array of exactly 32 bytes. `bytes` is an array of bytes.

```text
Proof     = { "statement": Statement, "transcript": bytes }
            ; transcript length in 32..=16384 and a multiple of 32
Statement = { "profile": h32, "before": Checkpoint, "after": Checkpoint, "batch": h32 }
Checkpoint= { "accepted": h32, "state": h32 }
Chain     = { "profile": h32, "links": [ Proof * ] }   ; 0..=64 links
```

The writer emits members in the order shown, with no whitespace. Size and
length checks run after parsing and before any statement comparison.

Implements: REQ-3508.
Verified by: TEST-3507.

### CON-3503: Verifier and chain

Interface: `Verifier::new(profile: Profile) -> Result<Verifier>`;
`Verifier::verify(&self, proof: &Proof, expected: &Statement) -> Result<()>`;
`Chain { profile: [u8; 32], links: Vec<Proof> }` with private fields and
`Chain::new`, `Chain::to_json`, `Chain::from_json`;
`Chain::verify(&self, verifier: &Verifier, start: Checkpoint, expected_end: Option<Checkpoint>) -> Result<Checkpoint>`.

Pre-conditions:
- for `verify`: `expected.profile == verifier.profile.id()` and
  `proof.statement == expected` (REQ-3502 a, b);
- for `Chain::verify`: `chain.profile == verifier.profile.id()`, every link's
  statement profile equals it, link 0 before equals `start`, link i before
  equals link i−1 after, and `links.len() <= 64` (REQ-3505, REQ-3502 c);
- when `expected_end` is given, the derived final checkpoint equals it
  (REQ-3502 d).

Post-conditions: `verify` returns `Ok(())` only when the Halo2 verifier accepts
the transcript for the expected instance and no transcript bytes remain.
`Chain::verify` returns the last link's after checkpoint, or `start` for an
empty chain, only when every pre-condition held and every link verified under
`verify` with that link's statement as the expectation.

Documented precondition the library cannot check: the verifier compiled its
profile from inputs it trusts. A verifier built from attacker-supplied inputs
proves facts about the attacker's vocabulary.

Error model: `Err(String)`; the first failing condition is named; no partial
result.

Implements: REQ-3502, REQ-3505.
Verified by: TEST-3501, TEST-3504.

### CON-3504: Attested candidate

Interface: `Candidate::attested(message: &Message, signature: &[u8], signer: &dyn Signer) -> Result<Candidate, String>`;
`Candidate::unauthenticated(text: String, label: String) -> Candidate`;
`Candidate::text(&self) -> &str`; `Candidate::label(&self) -> &str`.

Pre-conditions for `attested`, one per REQ-3504 clause:
- (b) `message.innermost_simple()` exists; `attestation_header_for` succeeds
  on it; `verify_attestation_v2(signer, &header.from, &header, signature)` is `Ok`;
- (c) the innermost simple message carries exactly one `:from` field, and
  `KeyId::parse(from_text) == header.from`.

Post-conditions: `text()` is the canonical serialisation of the whole message
as given, including its `lang` wrapper; `label()` is the `:from` text as
written (d). The dialect wrapper is not covered by the signature; it is bound
instead by REQ-3512 (b) against the verifier's installed dialect.

Documented precondition the library cannot check: the host pairs `signer` with
the public key that `header.from` names. `Signer` carries no key identity. A
host that passes a verifier for another key authenticates nothing.

Error model: `Err(String)` naming the defect or the attestation error. No
candidate is returned on failure.

Implements: REQ-3504.
Verified by: TEST-3503.

### CON-3505: Command-line interface

`cbcl checkpoint compile <profile.json>` prints
`{"profile": hex64, "addresses": ["sha256-<hex64>", ..]}`.
`cbcl checkpoint prove <profile.json> --before <addr>[,<addr>..] --after <addr>[,<addr>..] [--out proof.json]`
writes a proof package (stdout when `--out` is absent).
`cbcl checkpoint verify <profile.json> <proof.json> --before .. --after ..`
recompiles the profile, derives the expected statement from the address lists
and verifies. `cbcl checkpoint chain-verify <profile.json> <chain.json> [--start <before-addrs>] [--end <after-addrs>]`
verifies from the genesis checkpoint unless `--start` names a set, and prints
the final checkpoint as JSON.

Input grammar: `profile.json` is
`{"dialect": string, "thread": string, "candidates": [{"text": string, "label": string}]}`
recognised by `serde_json` with `deny_unknown_fields`, at most 1 MiB.
Candidates given this way are `unauthenticated`; every operation prints one
warning line on stderr saying so. Address lists are comma-separated wire
addresses `sha256-<hex64>`; an empty list is written `-`. Proof and chain files
use CON-3502.

Exit codes: 0 success; 1 rejection or verification failure; 2 usage error.
Behaviour is invariant across TTY and pipe output.

Implements: REQ-3510.
Verified by: TEST-3509.

### CON-3506: Prover

Interface: `Prover::new(profile: Profile) -> Result<Prover>`;
`Prover::prove(&self, before: u16, after: u16) -> Result<Proof>`.

Pre-conditions: `profile.statement(before, after)` succeeds, which is the host
precheck that the pair is a valid admitted transition (REQ-3501). The circuit
re-establishes the same facts independently (REQ-3503).

Post-conditions: the returned proof's statement equals
`profile.statement(before, after)`; the transcript satisfies the length rule of
REQ-3508 (d) or `prove` returns `Err`. Blinding randomness comes from `OsRng`;
two proofs of one statement differ in transcript bytes and both verify.

Implements: REQ-3501, REQ-3508 (d).
Verified by: TEST-3501, TEST-3507.

## Purity Boundary Map

### Pure Core (no I/O, no shared state, deterministic)
- `profile.rs`: relation compilation, commitments, statements.
- `circuit.rs`: constraint synthesis.
- `chain.rs`: chain pre-conditions and link iteration.
- `candidate.rs`: attestation header reconstruction and label binding.
- `Verifier::verify`: deterministic given params and key.

### Effectful Shell
- `Prover::prove`: consumes `OsRng` for blinding; otherwise pure.
- `cbcl-cli` `checkpoint`: file and stdio handling.
- Host authentication of candidates before `Candidate::attested`.

### Boundary Contracts
- `Candidate`, `Statement`, `Proof`, `Chain`: inward from shell to core.
- `Checkpoint`, `Result<(), String>`: outward.

### Dependency Rule
Dependencies point inward: CLI → `cbcl-state-proof` → `cbcl-parser` → `cbcl-core`.
No crate other than `cbcl-cli` imports `cbcl-state-proof`.

### Enforcement
Workspace `Cargo.toml` dependency graph; `cargo tree -i cbcl-state-proof` in TEST-3508.

## Tests

Core tests can be written in one sitting with the existing fixtures. Depth tests
need measurement or an outside reviewer and can be deferred when an owner is
named.

### TEST-3500: Relation, parity and binding (core)

For every valid subset of the signer-supersession fixture and the lunch-vote
fixture, the profile's state JSON equals the native fold, and the complete
corpus state equals the recorded expectation. A pending child before its opener
is not a valid set and its raw statement fails the mock prover. A candidate with
a wrong shape, a label that disagrees with `:from`, another thread, or another
dialect name makes every set containing it invalid while compilation succeeds.
Existing tests: `native_fold_and_replacement_match_for_every_valid_subset`,
`complete_native_corpus_snapshots_match_recorded_results`,
`pending_message_cannot_enter_committed_set_even_when_precheck_is_bypassed`,
`invalid_shape_sender_thread_and_dialect_are_constrained`.
Validates: [[SPEC-035-halo2-state-checkpoints#REQ-3500]],
[[SPEC-035-halo2-state-checkpoints#REQ-3501]],
[[SPEC-035-halo2-state-checkpoints#REQ-3512]].

### TEST-3501: Receiver-owned expectation (core)

Positive: an independently compiled verifier accepts a real serialised proof for
its expected statement; two proofs of one statement differ and both verify.
Prohibited-action: flipping any of the six roots in both the package and the
expectation fails; a verifier for a different candidate vocabulary rejects the
proof; `prove` on a non-admitted pair returns `Err`. Scope-invariant:
verification never mutates the verifier or the package. Existing test:
`actual_proof_roundtrip_tampering_and_independent_verifier`.
Validates: [[SPEC-035-halo2-state-checkpoints#REQ-3502]] (a, b),
[[SPEC-035-halo2-state-checkpoints#CON-3506]].

### TEST-3502: Grow-only exact batch (core)

Prohibited-action: a shrinking witness fails; a batch commitment equal to the
whole after set fails. Positive: an identity transition verifies. Every public
limb is constrained without the host precheck. The transition recurrence, when
removed by mutation, has to make the named test fail on an executed assertion.
Existing tests: `grow_only_and_exact_delta_are_circuit_obligations`,
`every_public_limb_is_constrained_without_the_host_precheck`,
`previous_context_relation_is_enforced_independently_of_snapshot_and_growth_checks`.
Validates: [[SPEC-035-halo2-state-checkpoints#REQ-3503]],
[[SPEC-035-halo2-state-checkpoints#REQ-3500]].

### TEST-3503: Attested candidates (core)

Positive: each fixture message, given a `:sender` equal to its `:from` and
signed with a test `Signer` through `sign_attestation_v2` over the innermost
simple message's header, yields a candidate whose label is the `:from` text;
the profile built from those candidates has the same identity as the profile
built from `unauthenticated` candidates with the same texts and labels.
Prohibited-action: a wrong signature, a payload changed after signing, a
message without `:sender` or `:thread`, a `:from` naming a different key than
`:sender`, and a `:from` spelled `@a` with a `:sender` spelled `@ed25519:b`
are rejected by `attested`. `Candidate` cannot be constructed by struct literal
outside the crate, checked by a `compile_fail` doctest.
Validates: [[SPEC-035-halo2-state-checkpoints#REQ-3504]].

### TEST-3504: Checkpoint chain (core)

Positive: a two-link chain from `genesis()` through the fixture's valid
transitions verifies and returns the final checkpoint; a one-link chain from a
trusted non-genesis start verifies; an empty chain returns the start; a chain
with a matching `expected_end` verifies. Prohibited-action: a chain whose first
link does not start at the given start, a chain with swapped link order, a
chain with a foreign profile identity in the header or in one link, a chain
with a corrupted transcript in any link, a chain whose derived end differs from
`expected_end`, and a chain of 65 links are rejected. Removing the
before-equals-previous-after check by mutation has to make the named test fail.
Validates: [[SPEC-035-halo2-state-checkpoints#REQ-3505]],
[[SPEC-035-halo2-state-checkpoints#REQ-3502]] (c, d).

### TEST-3505: Semantics version and golden vector (core)

A vector file `test-vectors/state-proof/signer-supersession.json` records the
profile identity, every valid checkpoint and one statement. The test recompiles
and compares. Reversing candidate order and reserialising candidates yields the
same identity. A test `semantics_version_changes_profile_identity` recomputes
the identity through `relation_domain` with a different version string and
asserts it differs. Existing tests:
`reordered_candidates_and_child_before_opener_use_the_same_relation`,
`canonical_whitespace_and_unknown_candidates`.
Validates: [[SPEC-035-halo2-state-checkpoints#REQ-3506]].

### TEST-3506: Resource bounds (core)

Prohibited-action: nine candidates, a 65,537-byte dialect, an 8,193-byte
candidate, a 2,049-byte label, a 2,049-byte thread, 10,000 nested parentheses
in a dialect and in a candidate, a role-declaring dialect, duplicate identities
and trailing input each return `Err`. For the nine-candidate and oversize cases
the call returns within 100 ms, which rules out enumeration. Existing test:
`candidate_and_parser_limits_fail_closed`; new cases in
`size_bounds_and_roles_fail_before_enumeration`.
Validates: [[SPEC-035-halo2-state-checkpoints#REQ-3507]].

### TEST-3507: Package recognition (core, with a depth fuzz target)

Core: unknown member, duplicate member, byte value 256, negative byte, trailing
non-whitespace, trailing whitespace accepted, oversize package, transcript
length not a multiple of 32, and a 65-link chain behave as CON-3502 states; a
property test over random statements and transcripts shows
`from_json(to_json(x)) == x` for proofs and chains. Depth: a `cargo-fuzz`
target `state_proof_package` feeds arbitrary bytes to `Proof::from_json` and
`Chain::from_json` and asserts no panic. Owner of the depth run: CBCL
maintainer.
Validates: [[SPEC-035-halo2-state-checkpoints#REQ-3508]].

### TEST-3508: Workspace gates (core)

`make check` passes on the integration branch. `cargo tree -i cbcl-state-proof`
lists only `cbcl-state-proof`, and additionally `cbcl-cli` when built with
`--features state-proof`. `cargo check -p cbcl-core --no-default-features` and
the WebAssembly build are unchanged. `scripts/state-proof-mutations.py` runs
and reports every mutant killed. `mutants.toml` does not list the crate.
Validates: [[SPEC-035-halo2-state-checkpoints#REQ-3509]].

### TEST-3509: Command-line interface (core)

With `--features state-proof`: `compile` prints the fixture's identity and
addresses; `prove` then `verify` round-trip with exit 0; `verify` with a
different `--after` list exits 1; a profile file with an unknown member exits 1;
`chain-verify` on a valid chain prints the final checkpoint; every run prints
the unauthenticated warning on stderr. Without the feature, `cbcl checkpoint`
exits 2 as an unknown subcommand.
Validates: [[SPEC-035-halo2-state-checkpoints#REQ-3510]].

### TEST-3510: Evidence record (core review, depth human)

Core: `docs/evidence/SPEC-035-halo2-state-checkpoints.md` records the executed
gate commands and results, the mutation results, the generating model, the
spec-review dispositions, and an independent fresh-context code review with its
findings and dispositions. Prohibited-action: the status is not set to
`implemented` by the session that produced the code; the git history of the
status line shows the reviewing session's commit. Depth: human cryptographic
review. Owner: CBCL maintainer.
Validates: [[SPEC-035-halo2-state-checkpoints#REQ-3511]].

### TEST-3511: Proof budget (depth)

The example `cargo run -p cbcl-state-proof --example checkpoint` with
`RAYON_NUM_THREADS=2` reports cached verification at most 1,000 ms and the size
limits of NFR-3500, with the machine recorded. An eight-candidate profile
reports `k <= 14`. Owner: CBCL maintainer; recorded in the evidence file when
run.
Validates: [[SPEC-035-halo2-state-checkpoints#NFR-3500]].

## Decisions

### ADR-3500: Verifier-derived finite relation

Context: proving CBCL admission and fold in gates would need the parser,
SHA-256, the state kernel and the role layer inside the circuit. The experiment
showed another route: the verifier compiles the complete finite relation
natively and the circuit proves exact membership.
Decision: keep that route. The circuit is a bounded specialisation of
[[SPEC-019-state-rules]] semantics; the native kernel remains the single
definition of admission and fold.
Consequences: the relation has 2^n rows and up to 3^n transitions, so n is
capped at 8 (REQ-3507). A new candidate vocabulary needs a new profile and keys.
Ceiling and upgrade path: an incremental constrained kernel over authenticated
state paths, in a successor specification. Simplicity Ladder rung 4: the kernel
exists; the circuit adds the minimum constraints.

### ADR-3501: Halo2 IPA over Pasta, pinned

Decision: `halo2_proofs = "=0.3.5"` with the IPA commitment scheme over Pasta
curves. No trusted setup. The crate declares `rust-version = "1.85"` because of
its locked dependencies; the workspace minimum stays 1.75 for every other crate.
Consequences: proofs are larger than a KZG system's; verification is cheap at
this size; no ceremony is needed.

### ADR-3502: Flat SHA-256 commitments

Decision: set and state commitments are domain-separated, length-prefixed
SHA-256 digests of sorted canonical content, encoded as two 128-bit limbs. No
Merkle tree.
Consequences: the whole candidate vocabulary is needed to compile a profile;
membership cannot be proved for one message alone. Replacement and deletion
history is retained in the set root, by design. Ceiling: large histories;
upgrade path as in ADR-3500.

### ADR-3503: Opt-in crate and feature-gated CLI

Decision: `cbcl-state-proof` is a workspace member that only `cbcl-cli`
depends on, optionally, behind `state-proof`.
Consequences: default builds, `no_std`, WebAssembly, FFI and Erlang bindings are
unchanged. Principle 15: the CLI already owns the toolkit responsibility, so a
subcommand is the right place; the proof system is its own component.

### ADR-3504: Reuse R4 v2 attestation for candidates

Context: candidates are `lang`-wrapped simple messages. The act identity, the
state kernel and the attestation header all read the innermost simple message.
Decision: `attested` reconstructs the header of the innermost simple message
exactly as [[SPEC-015-evidence-widening-v2#CON-702|equivocation proofs]] do and
verifies through `verify_attestation_v2`. The wrapper is bound by the profile's
dialect check (REQ-3512 b), not by the signature. The label keeps the `:from`
spelling so attested and unauthenticated profiles agree (REQ-3504 e).
Consequences: a v1 full-bytes signature is not accepted for candidates; hosts
with v1 material use `unauthenticated` and carry the precondition. Key identity
is compared through `KeyId::parse`, so `@a` and `@ed25519:a` are one key but
remain two labels; the fixture spelling is the one pinned. Rung 4.

### ADR-3505: Chains compose by sequential verification from a pinned start

Decision: a chain is verified link by link from a receiver-supplied start
checkpoint; cost is linear in the number of links and capped at 64 links per
package. The after checkpoint of each link is the prover's claim, proved
against the running checkpoint by that link's circuit, so the hard stop of
REQ-3502 (a) is kept for the start and the end while the intermediate
statements are necessarily read from the package.
Consequences: no recursion, no accumulation; the receiver still saves the replay
of messages but pays one verification per link. Ceiling: long chains; upgrade
path: recursive composition, kept as an open experiment.

## Evidence

The implementation evidence record is `docs/evidence/SPEC-035-halo2-state-checkpoints.md`.
The experiment record remains in `experiments/state-proof/`. The crate is an
experimental cryptographic artefact until the maintainer closes the open items
above.

## Changelog

<details>
<summary>Revision history — 0.1.0 → 0.2.0</summary>

- 0.2.0 — 2026-11-04 — after fresh-context adversarial review (26 findings)
  and the comprehension gate: attestation now targets the innermost simple
  message with `KeyId` identity comparison and `:from` labels; `Candidate`
  fields private; chain verification takes a receiver-pinned start and an
  a receiver-chosen expected end; REQ-3512 adds thread, dialect and signer binding;
  REQ-3507 to REQ-3509 split into lettered clauses; CON-3502 restated as the
  `serde_json` recogniser's language; CON-3506 adds the prover; limb order,
  sort order, address spelling and node budget fixed. Normative.
- 0.1.0 — 2026-11-04 — first specification, converting the bounded Halo2
  experiment into requirements, contracts and tests. Normative.
</details>
