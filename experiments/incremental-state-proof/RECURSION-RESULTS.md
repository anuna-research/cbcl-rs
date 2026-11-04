---
mode: explanation
status: experiment-complete
---

# Recursive authenticated-register findings

One final serialized proof now establishes a complete supported write history
from a fixed empty checkpoint, using the same authenticated-path transition
kernel as the preceding experiment. No trusted intermediate checkpoint is used.
The trusted opener and native byte/address/authentication boundaries remain host
preconditions: this is the experimental typed register relation, not a general
native CBCL proof or production authorization.

The experimental contract is [[experiments/incremental-state-proof/RECURSION-BRIEF]].
The preceding isolated-update measurements remain in
[[experiments/incremental-state-proof/RESULTS]].

## Actual whole-history measurements

| Complete writes | Binary proof bytes | Full proof JSON bytes | Canonical message UTF-8 bytes | Message-string-array JSON bytes |
|---|---|---|---|---|
| 1 | 24381 | 33066 | 203 | 211 |
| 8 | 24381 | 33066 | 1917 | 1974 |
| 32 | 24381 | 33066 | 8541 | 8766 |
| 128 | 24381 | 33066 | 35200 | 36097 |

At 128 writes, canonical-message bytes / binary-proof bytes = 1.444x;
the binary payload is 30.74% smaller than that text.
For complete serialized JSON, message-array bytes / proof JSON bytes = 1.092x
(8.40% reduction).
These are measured fixture comparisons, not general compression bounds. Binary
proof bytes exclude public fields; full proof JSON includes them. Both exclude
the separately pinned verification key and receiver-selected expected tip.
For a fresh receiver, the three actual pretty-printed input files total 35964 bytes, including the one-time key and expected head; key cost is amortized only when reused.
JSON message transport is explicitly `JSON.stringify(canonicalMessageStrings)`,
without synthetic signatures or other unmeasured envelopes. This is verification
compression: the messages cannot be recovered from the proof. Prover data and
availability storage remain separate.

The key is compiled once for base, single-step and fixed-eight-update methods.
Static circuit analyses:

| Method | Rows |
|---|---|
| base | 4 |
| batch | 26697 |
| step | 2182 |

Initial source compilation took 271.553 seconds; each eight-write batch took 68.043–69.689 seconds.
The full managed initial job took 1465.22 seconds, including setup, checkpoints and adversarial checks; peak sampled process-tree RSS was 2401501184 bytes.
Cached final-proof verification took 2.133 seconds. A separate fresh receiver process took 42.786 seconds including backend/process startup during concurrent mutant compilation; these are distinct measurements.

All timings, memory samples, compile observations and per-batch progress are
recorded in `evidence/recursive/`. The initial managed run created the history;
the recovery run verified and resumed that same recursively proved history and
reran the forged-parent check after the harness repairs. Source and environment
metadata are in `environment.json`. No constant proving-work claim is made:
each batch still costs proof generation, even though the final artifact is bounded.

## Why the final proof covers the history

Base constrains both empty roots, count zero and its method/operation tags.
Each later proof cryptographically verifies its predecessor, binds the object
and all checkpoint fields, and executes either one update or exactly eight
consecutive updates. A batch digest commits to its full ordered operation list.
Each transition reuses the existing native-tested authenticated-path constraints.
Count grows exactly from zero; intermediate states cannot be supplied as newly
trusted origins. The receiver checks its key, object and expected final checkpoint
and verifies the selected proof without opening predecessor-proof or message files.

## Executed adversaries and review

Witnessed arithmetic negatives cover forged genesis roots/count/tags, wrong
parent object/output/count/history, wrong batch digest/method, invalid replacements
and paths within a batch, and reordering. Raw tests explicitly do not establish
predecessor cryptographic validity. Their locally consistent forged-parent control
passes: this isolates the real recursion check.

The real negative changes an actual base proof's output to the checkpoint of
eight unproved writes. The strengthened fixture has signer sequence numbers
100+ at count eight, impossible under this model from genesis; its next updates
are locally valid. The altered parent first fails cryptographic verification.
The extension supplies otherwise valid next-eight paths and operations. Result:
`rejected-during-proving`. The recorded backend error is in the progress
record and run log; a generic backend/resource exception is not accepted as evidence.

| Targeted mutation | Named test | Result |
|---|---|---|
| unbound-genesis-state | forged-genesis-state | killed |
| unbound-parent-output | wrong-parent-output | killed |
| unbound-parent-object | wrong-parent-object | killed |
| unbound-batch-digest | wrong-batch-digest | killed |
| batch-unbound-replacement | wrong-operation-inside-batch | killed |

Each kill requires the named assertion to report missing expected rejection;
compilation failures do not count. Sources were restored.

The additional real-proof mutation compiled an isolated unsafe variant with
SelfProof verification omitted, using Cache.None. Its forged parent failed
cryptographic verification, yet its child proof of an unreachable history
verified under the unsafe variant key. The intended negative assertion then
failed, killing the mutation. The honest program key rejected that mutant child.
Its public key, parent and child are retained in
`proof-verification-mutant-artifact.json`; status/resources are in
`proof-verification-mutation.json`. This deliberately unsafe key is test evidence,
not an alternative trusted key. Human/cross-model cryptographic review remains
with the CBCL maintainer.

Fresh-context brief review found no blocking design issue. Fresh-context code
review found milestone-loss risk on resume, an invalid-operation test masked by
digest rejection, and an incomplete wire-size measurement. Repairs save milestones
before advancing an atomic resume checkpoint, reconcile a missing current milestone,
verify the resumed base and require every promised milestone before passing. The
invalid-operation test now recomputes the public digest; JSON message sizes are
explicitly measured. Reinspection found no additional source defect. Reviewers
did not run tests; execution evidence is recorded independently. Review sessions:
`/root/recursion_brief_review` and `/root/recursive_code_review`.

Recovery tests delete the latest milestone report row and recover it from the
verified whole-history proof. Empty or incomplete verifier manifests reject; a
missing old milestone prevents the producer from declaring passed. The final
receiver was also run with an unusable native-oracle path, demonstrating that
verification does not replay native messages. See `recovery-checks.json`,
`receiver-no-oracle.log`, and `reverification.log`.

The red gate first executed and failed the forged-genesis assertion against a
root-unconstrained base (`red-genesis.log`), then passed after roots were bound.
TypeScript checks passed. Changes are confined to this experiment; no Rust library,
CLI, production dependency, protocol/specification status, or existing baseline
evidence is changed.

## Remaining scope and next decision

The sequential-per-signer language, order-dependent history log and height-17
tree ceiling remain. Recursion does not add concurrent replacement, deletion,
exact branch union, native wire/signature binding, freshness, availability, or
safe history pruning. The circuit proves all modeled updates; it cannot prove
that undisclosed messages do not exist.

The result supports specifying an incremental recursive CBCL checkpoint system,
with the maintainer deciding native binding and general state semantics before
production integration. Keep this experiment isolated. Human cryptographic review
and production authorization remain open.
