---
mode: explanation
status: experiment-complete
---
# Private vote export experiment

## Orientation

An ordinary private dialect thread may optionally export its public participant
roster and final vote tally without exporting discussion or individual ballots.
This isolated experiment compares Jolt Dory clear and zero-knowledge modes on
one native-kernel consumer. A passing proof must establish message signatures,
participant eligibility, admission, folding and unanimous closure of the exact
covered set. The recipient pins its expected statement and verifier preprocessing
and receives no history. A missing participant's closure signature rejects even
when the tally is otherwise correct. Closure attests the agreed covered set;
it cannot establish that nobody withheld an undisclosed message.

The experiment uses synthetic data, not a real conversation. Participants are
Ed25519 public keys with unique labels, all eligible. The kernel is pinned to
`6e3ad4e` (native kernel semantics identical to `d1a093d`). Discussion, ballots,
message signatures and a secret random salt are witnesses. The export reveals
thread, semantics, dialect/source commitment, roster, covered count, salted set
commitment, ballot count and tally. The tally can itself imply a person's choice
in small or unanimous groups; zero knowledge does not remove this disclosure.
No public unsalted state hash is emitted.

## Contract and acceptance

### P1: Recognise and bind the statement

Closed serde JSON input/output structs, bounded before use; native parser for
canonical CBCL messages and installed dialect. Exactly one dialect wrapper,
matching dialect/thread/from label. Unique roster labels and keys, unique acts.
Roster order is canonical by label. Signed messages bind source/thread/roster
scope and canonical bytes through domain-separated digests. A salted commitment
binds the sorted canonical message/signer set. Unanimous Ed25519 signatures bind
that commitment, its count, dialect, semantics, thread and roster. The receiver's
expected scope and outcome come from outside the proof package.

### P2: Execute the native kernel

Use current native admission from empty with deterministic pending retries, then
native fold. The dialect has open, discussion and vote acts, typed HLC ballots,
last-write-per-signer and histogram state rules. All counted message authors
must belong to the roster. Export the tally and ballot count, never the ballot
map or discussion fields. Fixture includes two participants with different votes;
a replacement-vote fixture checks native semantics separately.

The experiment deliberately pins one voting dialect, rather than accepting an
arbitrary caller-supplied projection. Options are yes/no; abstention is allowed.
The native latest-HLC/replacement rule determines each participant's current
ballot. Invalid or unresolved messages reject the entire export. A fresh
32-byte OS-random salt is private per export; closure signatures authenticate
the salted set commitment. All signatures use strict Ed25519 verification.

### P3: Privacy and backend comparison

Use the same guest for clear and `zk` Dory builds at Jolt commit
`beebf45d829f5aecc5d330f78879cd914e47541e`. Only the `zk` build is eligible for a
private export. The receiver requires the compiled mode and expected protocol;
clear proofs must not be accepted as private proofs. Advice must be absent from
serialized receiver IO; this check alone is not evidence of zero knowledge.
Privacy relies on upstream BlindFold, not a statistical test over proof bytes.
No upstream cryptographic constraints or authentication checks may be weakened.

### P4: Adversarial evidence

Native and direct guest negatives cover invalid message/closure signatures,
missing closure signer, outsider/duplicate keys, wrong from/thread/dialect,
omitted or duplicated messages, changed ballot, malformed clock and unresolved
causality. A positive control precedes guest negatives; host prechecks cannot
count as guest rejection. Serialized receiver checks cover altered tally,
coherently altered public output and expected statement, corrupt proof/setup,
wrong setup pin, thread/roster/closing commitment, advice leakage and mode.
Mutation checks must demonstrate signature and closure tests detect omitted
checks. Infrastructure failures are not rejection evidence.

### P5: Measurement and resource boundary

Separate native, guest build, count/trace, preprocessing, prove, serialize and
fresh receiver phases. Report proof/public-IO/preprocessing bytes and cold bundle,
including expected statement; exclude verifier software only explicitly. Count
VM rows before attempting a retained trace. Run Cargo/provers sequentially.
Local only, four Rayon threads, sampled 4 GiB process-tree RSS, 1 GiB free-disk
reserve, 30 minutes per child process. Generated binaries/proofs/reports/logs live
outside tracked sources; tracked files contain source, contract and concise
results. Failures are results, never passing proofs. No production API or default
changes, remote proving charges, or extrapolated scalability claims.

### P6: WASM compatibility (stakeholder follow-up)

Check the pinned Dory/ZK prover and verifier library closures against
`wasm32-unknown-unknown`, recording exact features and any build failures.
The native host wrapper itself is not a browser API: it uses a toolchain,
filesystem, processes and a large verification stack. A successful target check
is compilation evidence only, not browser proving or performance evidence.
Browser proving/verification must not be claimed without execution of this
vote workload in a browser. Native proof measurements remain separate.

## Plan and decision

Reuse the existing pinned VM and thin host/guest split (composition first).
Implement a shared no_std vote-export computation with native tests and synthetic
signed fixture generation; build the Dory host in clear and ZK modes; count then
prove bounded fixtures; independently verify serialized artifacts and adversaries.
Record independent review and limitations. Evidence decides whether to pursue
Jolt/Dory, use a result-specific circuit, or first optimize native admission and
signature costs. SP1/Nexus and lattice ZK remain alternatives, not measured here.

The CBCL maintainer owns subsequent protocol/identity/closure policy, larger-host
measurements and production cryptographic review. This brief governs experimental
acceptance only, not production authorisation.
