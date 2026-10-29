---
mode: explanation
status: experiment-complete
---

# Bounded state proof findings

The prototype demonstrates a real Halo2 proof of accepted-set growth and its
native CBCL state. It does not establish a large-history performance benefit.

## Executed checks

- `parser-state-regression`: pass (31 passed, 0 failed, 1 ignored; filtered tests are not coverage). Evidence: `evidence/parser-state-regression.log`.
- `core-state-regression`: pass (4 passed, 0 failed, 0 ignored; filtered tests are not coverage). Evidence: `evidence/core-state-regression.log`.
- `core-state-properties`: pass (14 passed, 0 failed, 0 ignored; filtered tests are not coverage). Evidence: `evidence/core-state-properties.log`.
- `prototype-tests`: pass (12 passed, 0 failed, 0 ignored; filtered tests are not coverage). Evidence: `evidence/prototype-tests.log`.
- `format`: pass. Evidence: `evidence/format.log`.
- `clippy`: pass. Evidence: `evidence/clippy.log`.
- `example`: pass. Evidence: `evidence/example.log`.

The ignored parser test remains ignored; no result here claims it ran.
The format and Clippy checks cover the new crate. A whole-workspace format
check showed existing base-branch differences; dependency-inclusive Clippy
stopped at existing core warnings. Those unrelated files were not changed.

The mutation results below require an executed assertion failure, not a compiler
error. The runner restores the source in a `finally` block.

- `unbound-after-state`: killed; test `every_public_limb_is_constrained_without_the_host_precheck`; exit 101.
- `unconstrained-admission-transition`: killed; test `previous_context_relation_is_enforced_independently_of_snapshot_and_growth_checks`; exit 101.

## Proof sample

A single local unoptimised run, with two Rayon workers, measured:

| Measurement | Observed |
|---|---:|
| Public candidates | 3 |
| Profile compilation | 7 ms |
| Prover parameters/key setup | 3822 ms |
| Verifier profile/parameters/key setup | 3740 ms |
| Proof creation | 2139 ms |
| Cached-key verification | 94 ms |
| Cryptographic transcript | 3616 bytes |
| JSON package | 13629 bytes |

The package size varies with random bytes rendered as decimal JSON arrays.
The transcript size is fixed for this public circuit layout. Full environment
and output are recorded in `evidence/sample.json` and `evidence/example.log`.
This workload is a tiny replacement history, not a throughput or scalability test.

## Acceptance mapping

| Experiment assertion | Executable evidence |
|---|---|
| P1 native state and actual proof | `native_fold_and_replacement_match_for_every_valid_subset`, `complete_native_corpus_snapshots_match_recorded_results`, `actual_proof_roundtrip_tampering_and_independent_verifier` |
| P2 admission cannot be bypassed | `pending_message_cannot_enter_committed_set_even_when_precheck_is_bypassed`, `invalid_shape_sender_thread_and_dialect_are_constrained`, `previous_context_relation_is_enforced_independently_of_snapshot_and_growth_checks` |
| P3 all public commitments bound | `every_public_limb_is_constrained_without_the_host_precheck`, real proof tampering test, state-binding mutation |
| P4 grow-only exact batch | `grow_only_and_exact_delta_are_circuit_obligations`, transition mutation |
| P5 ordering and resource boundaries | `reordered_candidates_and_child_before_opener_use_the_same_relation`, `candidate_and_parser_limits_fail_closed`, `canonical_whitespace_and_unknown_candidates` |
| P6 expected profile authority | independent verifier and changed-profile rejection in the real proof test |

Observed deletion and an unseen concurrent write are covered by
`register_deletion_preserves_history_and_unseen_concurrent_write`.

## Review and next step

Fresh-session static review found and prompted fixes for parser depth and
previous-context admission. The record is `evidence/review.md`. No independent
cryptographic audit, human domain review or cross-model approval was obtained.
The evidence supports an isolated experiment, not production deployment.

The next implementation decision belongs to the maintainer: replace the
exponential verifier-derived relation with a constrained incremental kernel
over authenticated state paths. Preserve exact canonical byte binding, native
admission/fold parity, conflict/replacement metadata, and the external signer
authentication boundary. Recursive composition or accumulation would be a
separate experiment. The current public-candidate universe and keys do not
extend across arbitrary future history.

The subsequent [recursive experiment](../recursive-state-proof/RESULTS.md)
records real recursive base, append and exact-union proofs, with explicit public
parent/operation binding. Its different workload and backend are not a direct
performance comparison with this bounded relation prototype.
