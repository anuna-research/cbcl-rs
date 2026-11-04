---
mode: explanation
status: experiment
owner: CBCL maintainer
---
# Incremental authenticated register experiment

## Intent and failure mechanism

The user asked to try actual-update proofs over authenticated state after
[[SPEC-035-halo2-state-checkpoints]]. That implementation enumerates possible
subsets and transitions; compilation grows exponentially even for a linear
actual history. This experiment tests whether work can depend on update paths.
Novelty and performance risk are High: use Experiment Governance, leaving the
implemented specification unchanged. Tier 1 experimental cryptography.

## Hypothesis and selected scope

A fixed program using the already pinned o1js 2.2.0 [[experiments/incremental-state-proof/BRIEF#Authenticated state and statement|Merkle tree]] and proof
primitives can prove register updates with constant circuit structure across
different history lengths. Reusing this dependency isolates the state-model
question from writing a hash gadget; this is not a Halo2 performance comparison.
Recursion follows validation of the transition kernel, not this experiment.

Supported inputs are a fixed role-free dialect and trusted admitted opener,
UInt32 values rendered as decimal CBCL strings, signer labels `@writer<N>`
for N in 0..65535, and sequential writes per signer. A signer's first write
has sequence zero and no replacement; each subsequent write has sequence
previous+1 and exactly its current head as replacement. Different signers may
interleave. Stale heads, concurrent/no-replacement writes to existing signers,
multiple replacements, deletion and branch merge are outside this language
and must reject relative to the selected prior checkpoint. Two sibling updates
can each prove from the same prior; excluding forks requires the receiver to
serialize acceptance with a current-checkpoint compare-and-swap. The circuit
does not detect undisclosed siblings or establish a globally latest head.
Native CBCL accepts some excluded cases: this is an explicit
subset, not general admission equivalence.

## Authenticated state and statement

Use existing binary Merkle paths of depth 16 (o1js height 17). One tree stores
per-signer heads; another stores an append-only history log, each with capacity
65536 leaves. A head commits to object, signer, native address limbs, sequence
and value. Each log leaf commits to the full typed operation and object.
Checkpoints contain both roots and the write count. Witnesses contain only the
previous head and two authentication paths, never the full history or candidate
vocabulary. The log root is order-dependent, unlike SPEC-035's canonical set root;
no order-independent identity, branch union or root-level merge is claimed.

Public input binds receiver-owned object, prior checkpoint and operation digest;
public output is the computed next checkpoint. Constraints check prior state
leaf/path/root, signer index, replacement and sequence, empty log append slot,
append index equal to count, capacity, and updated roots/count. The receiver
compares the entire expected input and output before cryptographic verification
under its trusted key. The prior checkpoint must already be trusted: this
nonrecursive proof does not establish earlier history validity.

The native oracle recognises JSON using serde with unknown fields denied:
`{"records":[{"signer":u32,"seq":u32,"value":u32,"replaces":null|string}]}`,
at most 1 MiB and 4096 records. Missing `replaces` defaults to null under
serde's Option recognition. In generated fixtures only, the string
`$head` requests substitution of that signer's preceding generated address
before message construction; it is never a CBCL replacement address. It constructs canonical typed CBCL messages,
admits through the native kernel, then folds. This synthetic harness is not a
service. Mapping native bytes, labels, dialect/thread/opener and SHA-256 addresses
to experimental tuples, and signer authentication, are HOST PRECONDITIONS.
The circuit uses Poseidon on tuples, not CBCL parsing, wire hashing or Ed25519.
Only a host checking those bindings can interpret a proof as a CBCL update.
Neither proof establishes undisclosed-history completeness or data availability.

## Acceptance and adversaries

- P1: native fold and authenticated state agree for first write, replacement,
  interleaved signers and histories of 1, 8, 64 and 256 writes. Reconstruct roots
  from native output independently, not only displayed values.
- P2: wrong old head/path, signer index, replacement/sequence, occupied log slot,
  append index, object/operation, prior roots/count, capacity, replay and
  unsupported concurrency reject in executed circuit constraints. Use witnessed
  inputs and valid controls; host exceptions do not count as circuit rejection.
- P3: real serialized proofs for updates after 8 and 256 writes verify under
  one compiled key. Altered output fails cryptographic verification; a valid
  proof for another expected context fails receiver binding.
- P4: mutations removing state-path binding and replacement binding cause named
  negative tests to fail on assertions. Compilation errors are not kills.
- P5: report rows, witness fields, setup/prove/verify time, proof bytes, sampled
  RSS and native-oracle costs separately. Fixed structure is not constant total
  storage, cheap arbitrary admission, or unbounded scalability.

## Isolation, budget and exit

Branch `experiment/incremental-state-paths`, isolated sibling worktree. Change
only this directory and a synthetic oracle example in the experimental proof
crate. No public API, production CLI, specification status or wire format changes.
Enabling means running the experiment; rollback means stopping it. Synthetic data,
no production participants. One proof worker; real run at most 12 minutes,
4 GiB sampled process-tree RSS and a 1 GiB disk reserve. Overall timebox: this
session, at most 60 minutes of active experiment runs. Report resource stops as
inconclusive rather than silently raising limits. Keep work on its own branch.

Exit with checks, mutation evidence, real proofs or an explicit resource stop,
and fresh-context adversarial review. The CBCL maintainer next decides whether
to specify a successor incremental kernel covering concurrency, canonical set
commitments, byte/authentication binding, capacity policy and proof composition.
Experimental code remains isolated until that decision; no production approval.

## Synthesis record

Intent: “can we try that approach?” following authenticated paths and incremental
state kernels before recursion. Producer: Codex; system model family GPT-6,
exact model version not exposed. Session-default settings. Inputs: the implemented
specification, prior bounded/recursive experiments, native `latest-per-signer`.
Design sequence: identify exponential enumeration; reuse tree primitives; narrow
to one authenticated head per signer; reject unsupported concurrency; separate
host binding from circuit guarantees and log identity from canonical set identity.
Reviewer, measured findings and final decision belong in the results record.
