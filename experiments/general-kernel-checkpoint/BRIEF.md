---
mode: explanation
status: experiment
owner: CBCL maintainer
---
# General kernel checkpoint experiment

## Intent and hypothesis

A new client currently needs historical messages to establish that its current
state was computed correctly. Dialect-specific circuits fail the user's generality
requirement. Hypothesis: execute the existing CBCL parser, dialect installation,
admission and fold in a general-purpose verifiable VM, with the dialect supplied
as data. A client downloads a state snapshot and proof, checks them against a
pinned program image and expected object/history commitment, without downloading
history. This experiment measures feasibility, not production readiness.

Tier 1 execution-proof trust boundary. Use a fresh cross-model adversarial review;
human cryptographic review remains open. Novelty, performance risk and data
uncertainty are high: use the protocol's experiment loop before a successor SPEC.
This isolated branch changes no production kernel or main workspace dependencies.

## Statement and input boundary

Input is a bounded typed JSON object with a dialect source (including ancestor
chain where needed), thread string and ordered message records with authenticated
signer labels and canonical wire messages. Fully recognize the schema and native
S-expression grammar before semantic processing. No precomputed state, admission
verdict or specialized transition circuit is trusted. Install the supplied dialect
through the existing native rules; parse messages, check canonical encoding, and
admit from empty history with cbcl_parser::state_exports::admit, retrying pending dependencies. This is the native consumer API used by cbcl-bus, not AdmissionMonitor or the Agent host-policy path. Commit the entire ordered ancestor/source closure, not just the leaf. Require each innermost thread to equal the requested thread and every present lang wrapper to name the selected leaf identity (human declared name or canonical hash); check nested wrappers as well. Bare role/cast roots remain legal. This wrapper profile does not claim every envelope combination is supported.
Require all supplied unique messages to become accepted. Reject unresolved or
rejected messages. This statement covers a causally closed accepted set, rather
than arbitrarily discarding invalid inputs to produce a convenient state.

Output binds format version, program image (verified by receipt), semantics source
revision (baked into image), dialect source commitment, thread, canonical accepted
message/signer set commitment, count, and state hash. Commitments use SHA-256 with
explicit domain separation and length-delimited encodings. Sorted message records
make set commitments independent of input order; duplicate messages are rejected.
Signers are input assertions, not Ed25519 authentication: that boundary must be
explicit in the output and results. No completeness/freshness claim beyond the
committed set. A verifier must supply expected identity/commitments independently;
checking only a prover-supplied expectation is not acceptance.

A snapshot is the canonical native fold output. State-free dialects may be refused
as having no current-state projection; any state-bearing valid dialect is data,
not a new program. Generality means the wrapper dispatches to the existing kernel
without verb/operator allowlists; bounded resources still limit individual runs.
Snapshot continuation without history and future witnesses is a separate open
question. No claim that a view snapshot alone can resume admission.

## Measurements and acceptance

Use RISC Zero as initial backend because it runs Rust and supports local macOS
execution/proving. Pin SDK/toolchain; use the existing unmodified core and parser.
One program image must handle at least two structurally different valid dialects,
including a drawing-like latest-per-key list payload and an overwrite/collection
example. A third supplied dialect or ancestor-chain test checks no hardcoding.
Compare exact native outputs. This proves the native consumer shape/causal admission and fold, not the separate escrow authorization required before external effects. Restrict external-effects claims accordingly. Capture independently precomputed expected commitments before proving; separate-process verification must use those, not only expected.json written by the prover. Test malformed input, invalid dialect, canonicality,
invalid/rejected/pending messages, duplicate addresses and permutation agreement.

First run native and VM execution to capture cycles and exact agreement. Then
attempt a real locally verified proof at the smallest nontrivial trace; mock/dev
receipts are never evidence of proving. Separately measure execution, proof calls,
verification, receipt bytes, snapshot bytes and raw/gzip/Brotli history versus the
complete snapshot+receipt bundle. State any proof kind: composite receipts may grow
with execution; a succinct receipt is a separate measured claim. Verify serialized
receipt in a separate process without the message input. Reject tampered state,
wrong expected dialect/history/thread, wrong program image and fake receipts.
Use deliberate mutations to show the acceptance checks detect the corresponding
broken behavior. Increase workload only while resource/time caps permit; a
failed local proving attempt is evidence of this environment, not infeasibility
of general kernel proofs. Preserve logs and exact SDK/image/source provenance.

## Limits, exit and next action

Local 8 GiB Apple M2 machine has about 5 GiB free disk. Reserve 1 GiB free;
limit one proof process, one Cargo compilation worker and a Rayon pool of at most four threads, and monitor aggregate RSS of the managed process tree. Cap 4 GiB RSS and
30 minutes per managed build/proof process, 90 minutes total wall time from worktree creation, conservatively including installation and review. Toolchain installation was observed for exit/disk bounds but its peak RSS was not sampled; disclose that evidence gap.
Use small VM segments if supported. Stop at caps with partial results; do not
substitute estimated proof timing. No paid remote proving, private messages,
production traffic or credentials. Install tooling without changing shell profiles.
If a backend cannot fit, retain executable harness and precise blocker; do not
claim a mock receipt or native run proves computation. Producer: Codex, GPT-6
family, model/version and sampling parameters otherwise not exposed.

Maintainer next: assess measured bandwidth and prover cost, then author a successor
specification covering the public checkpoint grammar, authentication boundary,
image/semantics upgrades and resumable state as applicable. Existing specialized
proof results do not establish this experiment's performance.

## Backend steering during execution

The user identified SP1, Nexus and Jolt as alternatives. Record their primary
source requirements and semantics in [[experiments/general-kernel-checkpoint/BACKENDS]].
Do not treat the initial RISC Zero run as a performance result for those backends.
Jolt's untrusted advice model explicitly permits history absent from verifier
inputs without requiring ZK; its panic flag and all advice still require checking.
A cross-backend performance ranking remains a separate measured task.

Tuning amendment: the initial exponent16/single-thread proof attempt was stopped
after more than20minutes without a receipt, with observed RSS below1GiB. Retry
with exponent18 and at most four Rayon threads under the same4GiB/30minute/90minute
caps. Preserve the initial interrupted stage; do not fold it into successful
proof-call timing. Independent native fixture compilation/checks may overlap a
proof, so these are shared-workstation samples rather than dedicated benchmarks.

## Recognized input grammar and prototype bounds

The existing serde_json JSON grammar recognizes one complete document (no trailing
input), then derived typed decoding recognizes exactly these object fields in any
order, rejecting duplicates and unknown fields:

```text
Input  = object { dialect: string, thread: string, messages: array<Record> }
Record = object { signer: string, canonical: string }
```

UTF-8 byte bounds: entire document1,048,576; dialect65,536; thread1..1,024;
signer1..1,024; each canonical message0..8,192; message records0..256. Every
message string must additionally be fully recognized by the native S-expression
and message grammar and equal native canonical serialization. These are local
experiment input bounds, not a VM branching/circuit candidate ceiling. Raising
this profile limit changes the program image and requires explicit versioning;
large-history throughput and bandwidth benefit remain unmeasured here.

The authenticated signer assertion includes its relationship to wire sender and
signed-wrapper metadata. Native consumer admission judges role conformance using
message metadata; changing only the external record label does not authenticate
or invalidate that metadata. No Ed25519 or transport authentication is proved.
