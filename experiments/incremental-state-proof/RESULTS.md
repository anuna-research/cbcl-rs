---
mode: explanation
status: experiment-complete
---

# Incremental authenticated register findings

The experiment supports replacing finite-vocabulary enumeration with a fixed
authenticated-path transition circuit for the declared sequential register subset.
It does not replace [[SPEC-035-halo2-state-checkpoints]], establish general native
kernel equivalence, implement recursion, or authorize production use.

## Executed measurements

Host: Apple M2, macOS-26.5-arm64-arm-64bit, v25.6.1, rustc 1.95.0 (59807616e 2026-04-14).
Backend: o1js 2.2.0, one worker. Environment and source hashes are in
`evidence/environment.json`. Different backend/workload from the Halo2 experiment;
these are observations, not a head-to-head speed comparison.

| Prior writes | Circuit rows | Private witness fields | Binary proof bytes | Prove ms | Verify ms |
|---|---|---|---|---|---|
| 8 | 2178 | 76 | 22382 | 20912 | 2134 |
| 256 | 2178 | 76 | 22382 | 20081 | 2066 |

Compile: 34026 ms. Managed real run: 88.93 s.
Peak sampled process-tree RSS: 702316544 bytes.
Minimum observed free disk: 4426960896 bytes.
No resource cap was crossed. Witnesses contain two paths and one prior head,
not a materialized history. Native fixture construction/replay is measured
separately in `evidence/constraints.json`; it is not part of cached verification.

Both serialized proofs verify against the same compiled key. An independent
artifact-reverification command reconstructed expected roots from fresh native
fold output and verified both saved proofs. Changing the public output failed
cryptographic verification; a valid proof for another object failed the receiver's
full expected-context comparison. Public key and proofs are committed in
`evidence/verification-key.json` and `evidence/real-proofs.json`.

## Acceptance evidence

| Brief criterion | Executed evidence |
|---|---|
| P1 native parity | `native-parity-1`, `native-parity-8`, `native-parity-64`, `native-parity-256` reconstruct native head roots and compare after-root/count; `valid-replacement` checks the witnessed transition. |
| P2 rejection and scope | Witnessed negative tests cover prior head/path/root, signer and append indexes, replacement/sequence, occupied slot, prior count/history root, object/operation, capacity, noncanonical empty head, sequence overflow, replay and excluded concurrent write. Native admission accepts the excluded concurrent control. Sibling controls both prove against one prior and reject against the selected advanced checkpoint. |
| P3 real proofs | `evidence/real-proof-run.log`, `evidence/real-proofs.json`, `evidence/run-status.json`, `evidence/reverification.log`. |
| P4 mutation | `evidence/mutations.json` and named mutant logs below; sources restored. |
| P5 structure/cost | Static circuit analysis and witness arity in `evidence/constraints.json`; proof-stage times above; sampled run resources and native construction costs recorded separately. |

Additional gates: `npm run check`, example Clippy with warnings denied, workspace
formatting check, and native-oracle grammar checks pass. Outputs are committed in
`evidence/typescript.log`, `rust-clippy.log`, `rust-format.log` and
`oracle-checks.json`. Artifact reverification also rejects empty or incomplete promised-proof collections
(`evidence/verifier-input-checks.json`). The vault checker reports no syntax errors but exits nonzero for dead links.
Cross-worktree diagnostic graphs differ, so no unchanged-backlog or clean-link
claim is made (`evidence/vault-check.json`); owner of that follow-up is the CBCL
maintainer. No full workspace regression claim is made for this isolated
example/experiment change.

### Targeted mutations

| Mutation | Named test | Exit | Result |
|---|---|---|---|
| unbound-signer-index | wrong-signer-index | 7 | killed |
| unbound-append-index | wrong-append-index | 7 | killed |
| unbound-state-path | wrong-old-value | 7 | killed |
| unbound-replacement | wrong-replacement | 7 | killed |

Each kill requires the executed negative assertion to report missing expected
rejection after its constraint is removed. Compilation/backend errors do not
qualify. Sources were restored after each attempt.

## Red gate and review trajectory

The first witnessed update failed against an unchanged-checkpoint stub in an
executed circuit assertion (`evidence/red-stub.log`), then passed after the
transition constraints were added (`evidence/first-positive.log`). This is an
actual behavioral red gate, not an import/compilation failure.

An initial wrong-path test accidentally supplied identical zero siblings for a
one-leaf tree and failed to reject. Its log is retained as
`evidence/initial-path-fixture.log`; the repaired test modifies a sibling.

Brief-only fresh-context review identified that sibling proofs from one prior
are each valid; the brief now assigns linear acceptance/CAS to the receiver and
does not promise global fork prevention. The reviewer confirmed the clarification.

Fresh-context code review received only the brief and deliverable, with a mandate
to find defects. It identified two mutation-invisible index tests: each could
reject on root authentication instead of the intended index assertion. The signer
case now uses an empty-state first-write control; the append case authenticates
a different empty slot against the actual prior root. Their new targeted mutants
are killed. The reviewer reinspected both fixes and found no remaining issue in
the declared scope. Final artifact review also requested an exact promised-history
check in the verifier; empty and incomplete proof collections now reject in
executed negative checks. The reviewer did not run tests; the execution evidence above
is separate. Review sessions: `/root/incremental_brief_review` and
`/root/incremental_code_review`. No independent cross-model or human cryptographic
review was obtained; those remain maintainer-owned before any production approval.

## Interpretation and next decision

The measured result removes exponential enumeration from this experiment: fixed
paths and a fixed circuit processed updates after different actual history
lengths, with the same key and binary proof size. Total prover storage still grows
with history and signer state. Tree capacity is finite; the current depth is a
declared resource ceiling, not an unbounded result.

Recommendation to the CBCL maintainer: proceed to a successor specification for
an incremental authenticated native kernel before attempting proof composition.
Carry these findings into its requirements/contracts/tests: authenticated read
and write paths with index-binding mutants; receiver-owned prior/object/key;
canonical byte/authentication binding; native-fold parity over late concurrent
replacement and deletion cases; order-independent accepted-set identity and exact
branch union; explicit tree exhaustion/migration policy; measured costs against
native replay. Current sequential-subset results are evidence for feasibility,
not an implementation of those future requirements.

The next specification must decide what causal, replacement and conflict metadata
is sufficient; one current head per signer cannot handle general concurrent
updates. Recursive composition can later compress proof histories, but does not
solve those state semantics. Keep this prototype isolated on its experiment
branch. No production integration or existing checkpoint-spec status changes.
