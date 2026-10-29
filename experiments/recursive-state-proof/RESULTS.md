---
mode: explanation
status: experiment-complete
---

# Recursive state proof findings

The corrected recursive experiment completed successfully. It uses one compiled
program and verification key for different operation payloads and histories.
There is no pre-enumerated candidate relation. The run proves exact append and
union for a bounded signed set, not general CBCL language equivalence.

## Executed cryptographic evidence

The run created and serialized 7 positive proofs. Each was verified
using its expected public context and the same trusted verification key.

| Proof | Binary proof bytes | JSON bytes |
|---|---:|---:|
| base | 25743 | 34575 |
| shared-ancestor | 26842 | 36194 |
| left-fork | 26842 | 36195 |
| right-fork | 26842 | 36194 |
| merge | 27939 | 37656 |
| self-merge | 27939 | 37656 |
| duplicate-append | 26842 | 36196 |

Binary sizes are decoded from the base64 proof encoding. JSON sizes include
public inputs and outputs. Fixed method arity has the same observed binary
size across the executed cases; the test does not measure long-history scaling.

The fork shares Alice’s contribution of 5. The branches add 7 and 3, and the
merged result is count 3, total 15. A naive sum of branch totals would be 20.
Self-merge and duplicate append leave the set root, count and total unchanged.

Changing the serialized total fails cryptographic verification. A valid old
branch or unrelated self-merge fails the receiver’s expected-context check.
The public context commits to object, method kind, both parent roots and the
appended operation identity.

An adversarial predecessor replaced a real proof’s public output with a
locally consistent snapshot of an unproved contribution. The parent proof was
first confirmed invalid. Extending it failed in the backend at `prevs_verified`
with `Constraint unsatisfied (unreduced)`. This is specific recursive-verifier
rejection evidence, not a generic resource/backend exception. The separate
arithmetic control confirms that a locally consistent fabricated parent can
pass local append checks when cryptographic validity is not being tested.

Full records: `evidence/real-proofs.json` and `evidence/real-proof-run.log`.

## Measured costs

| Stage | Seconds |
|---|---:|
| compile | 156.361 |
| base | 32.958 |
| shared-ancestor | 42.503 |
| left-fork | 42.016 |
| right-fork | 41.928 |
| merge-shared-ancestor | 58.187 |
| idempotent-self-merge | 57.339 |
| idempotent-duplicate-append | 41.784 |
| Serialized-proof verification range | 2.058–2.134 |
| Managed run total | 497.08 |

Peak sampled process-tree RSS was 2,047,180,800 bytes.
Minimum observed available disk was 10,972,983,296 bytes.
No resource cap was reached. These are local observations with one proof worker,
not throughput guarantees or comparisons with the different Halo2 workload.

The method analysis records the following constraint rows:

- `append`: 3046 rows; digest `b70d6828f388860bbba16ea5d73f8426`.
- `base`: 292 rows; digest `151859deafa7a79369e0626a76b99094`.
- `merge`: 4318 rows; digest `1b61e1b7c9c49978c85c58da93e6aad5`.

## Native agreement and negative checks

Native CBCL admission/folding matches the empty set, shared ancestor, each
branch, merged set and duplicate-delivery fixture. Native wire message IDs and
experimental record IDs are different constructions. Signature verification is
experimental Schnorr, not CBCL Ed25519; byte binding and general kernel parity
remain outside the proof.

`evidence/constraints-only.json` records the main arithmetic checks.
`evidence/additional-checks.json` additionally rejects a fifth record being
silently omitted from a capacity-four union, verifies public merge-field
binding against a valid positive control, and checks the fabricated-parent
local-arithmetic control. Constraint-only results are not counted as real proofs.

TypeScript checks, the NPM test commands, Rust example build/format/Clippy and
the final diff checks are recorded in `evidence/checks.json`.

## Findings and next decision

The result supports proof-carrying group checkpoints relative to an agreed
collection of parent heads: the receiver verifies those heads and the resulting
state without receiving predecessor proofs or replaying their messages.
It cannot establish that a member published its latest head, disclosed every
message, remained online, or supplied available document data.

The practical cost is substantial even for this small state. Background or
batched checkpoints are a more plausible next experiment than proving every
pointer movement. A scalable implementation needs canonical authenticated state
paths, explicit native-byte and authentication binding, kernel parity, and
a policy for selecting and authenticating member heads.

An initial compilation was stopped after review identified missing public
parent/operation binding; `evidence/initial-unbound-*` records that non-success.
Corrected-run evidence is separate. Fresh review found no additional apparent
soundness or layout defect after the correction. Cross-model, human-domain and
cryptographic deployment reviews remain unverified. No production service or
binding consumes this experiment.

## Targeted arithmetic mutations

The runner removed each constraint from the circuit source, executed the named
negative assertion, and restored the source. Both mutations were caught:

- `unbound-parent`: `append public parent root binding` failed with an executed missing-rejection assertion (exit 1).
- `dropped-right-input`: `merge omitted right contribution` failed with an executed missing-rejection assertion (exit 1).

This mutation run covers public parent binding and right-input preservation.
It does not claim mutation coverage of the recursive verifier; that gate has
the separate real forged-predecessor rejection evidence described above.
