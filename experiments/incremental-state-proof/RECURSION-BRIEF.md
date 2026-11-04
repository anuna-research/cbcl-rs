---
mode: explanation
status: experiment
owner: CBCL maintainer
---
# Recursive composition of authenticated register updates

## Intent and hypothesis

The user requests recursive composition so one final proof establishes a complete
supported write history. The preceding [[experiments/incremental-state-proof/BRIEF]]
proved isolated updates from trusted arbitrary prior checkpoints; a collection
of those proofs still grows with history. This experiment composes that SAME
transition kernel with o1js SelfProof verification and a fixed genesis rule.
Tier 1, governed experiment: novelty and performance risk remain High.

A final proof must establish all experimental register updates since an empty
write checkpoint, for one receiver-selected object and program key. The opener
and mapping to native CBCL remain trusted host inputs. This proves the entire
history of the experimental typed relation, not native byte parsing, wire hashes,
Ed25519 signatures, hidden-message completeness, freshness or availability.
Those boundaries and the sequential-per-signer language remain unchanged.

## Construction and receiver contract

Add a separate program; preserve the nonrecursive program and its evidence.
`base` constrains BOTH roots to the constant empty-tree root, count zero, method
kind zero and operation zero. Object is public. It cannot bless an arbitrary
initial checkpoint. `step` verifies one SelfProof, binds its object and output
to the new context's object and before checkpoint, and calls the existing raw
transition method. `batch` does the same for a fixed array of eight consecutive
updates. Each update consumes the preceding output. The public batch digest
commits to all operations in order with a domain tag. No inactive padding or
omitted updates. Single-step mode handles non-multiple-of-eight tails.

Public input contains object, method kind, before checkpoint and operation/batch
digest; public output is the resulting checkpoint. A receiver pins the compiled
key, object and expected final checkpoint (both roots and count), then verifies
ONE final serialized proof. It needs no intermediate proof, historical message
or previous checkpoint. Intermediate context is cryptographically bound by
recursion; it is not a new trust anchor. A valid proof for a shorter/different
head rejects against the selected expected tip. Receiver selection remains a
host responsibility; two sibling histories may both be valid.

The fixed height-17 trees still cap each history at 65536 writes/signers.
Whole-history validity follows from base plus proof verification plus exact
continuity, not from an off-circuit assertion that a parent was valid. Recursion
must not replace or weaken the authenticated-path kernel.

## Tests and measured acceptance

- R1: witnessed base constraints reject nonempty roots/count, wrong method or
  nonzero operation. Positive base equals the known empty checkpoint.
- R2: raw arithmetic checks reuse the existing kernel for steps and batches,
  including sequential replacement/interleaved signers. Reject foreign object,
  wrong predecessor roots/count, altered operation order/digest, wrong method,
  and invalid operation/path within a batch. Native fold reconstructs expected
  final roots. Raw checks are NOT evidence of recursive proof verification.
- R3: create and serialize real base and composed proofs, including a single
  step and whole histories of 8, 32 and 128 writes under one key. Reverify each
  saved final proof independently with only that proof, key and expected tip;
  compare against native state. A longer 256-write measurement is optional if
  the declared budget permits; never substitute trusted-prefix proofs for these
  whole-history results. Save progress after each batch to make interruptions
  reviewable. Report only lengths actually proved.
- R4: alter a real parent's output to a locally consistent checkpoint, first
  establish that the parent fails cryptographic verification, then try to prove
  an extension with otherwise valid paths and operations. Require a classified
  recursive-verifier rejection; generic backend/resource errors are inconclusive.
  A raw arithmetic control must demonstrate the same forged parent passes local
  transition constraints, isolating the need for recursive verification.
- R5: named assertion tests must fail under removal of genesis-root binding,
  parent-output continuity and object binding. Source restoration is mandatory.
  Removal of SelfProof verification additionally needs a real-proof mutation
  control if budget permits; otherwise record its unexecuted status explicitly
  alongside R4 rather than claiming mutation coverage from raw arithmetic.
- R6: report proof and complete JSON sizes, actual canonical native-message
  UTF-8 bytes, compile/prove/verify time and process RSS separately. A fixed proof
  size is verification compression; it does not make messages recoverable or
  authorize deleting needed history. Compare actual wire JSON too; binary proof
  bytes exclude public fields and a separately pinned verification key.

## Governance and exit

Branch `experiment/recursive-incremental-state`. Changes stay in the existing
experiment directory; no crate API, production dependency, CLI or implemented
specification changes. Synthetic fixtures only. Reuse installed o1js 2.2.0 and
native oracle. One worker, 4 GiB sampled process-tree RSS, 1 GiB disk reserve,
30-minute managed real-proof run, 60-minute total active-run timebox. A resource
stop is recorded as partial/inconclusive, never a passed gate. Enable by explicit
experiment commands; rollback by stopping the process. No production traffic.

Record source/model metadata, red gates, actual commands/results, measurements,
review findings and dispositions. Fresh-context adversarial review must check
base anchoring, complete coverage, predecessor verification, receiver expectations
and claims. Keep production authorization, human/cross-model cryptographic review,
general concurrency and canonical-set merge open. The maintainer next decides
whether to specify a production successor covering native binding and the
remaining state semantics. No automatic promotion of this experiment.

Producer: Codex, system model family GPT-6, exact version not exposed. Settings:
session defaults. User intent: “we need recursive composition then”. Inputs:
existing authenticated-path and bounded recursive experiments. Design trajectory:
identify missing whole-history induction; constrain genesis; reuse transition
constraints; add fixed batches to amortize recursion; measure actual final-proof
coverage and compression; test a cryptographically invalid but locally consistent
parent. Reviewer and final decision are recorded after execution.
