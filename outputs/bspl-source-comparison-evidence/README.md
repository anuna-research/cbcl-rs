# BSPL local-source comparison evidence

Report: [[cbcl-bspl-source-comparison]]. Review: [[cbcl-bspl-source-review]]. This supplements [[cbcl-systematic-comparison]] rather than replacing its archived evidence.

`source-pins.json` identifies local roots, commits, branch/worktree status and file SHA-256 hashes. BSPL source was copied to `/private/tmp/cbcl-bspl-source-audit` for execution; original checkout remains unchanged. Interpreter/dependencies are in a separate `/private/tmp/cbcl-bspl-review-venv`; exact installed versions are retained in `python-dependencies.txt`. These temporary execution directories are not durable artifacts; recreate them from the pinned source when needed.

## Focused probes

`purchase.bspl` is a parsed executable protocol. `probe_bspl.py` exercises concrete value consistency, duplicates/conflicts, the dependency-checker's early return, receive-path behavior, local nil, information handoff, positive/negative static analysis and the existing refinement example. It imports unmodified BSPL modules. All script assertions passed; results and stderr are retained.

Local replay, after creating the sandbox and installing the recorded dependencies:

```sh
PYTHONPATH=/private/tmp/cbcl-bspl-source-audit/src /private/tmp/cbcl-bspl-review-venv/bin/python outputs/bspl-source-comparison-evidence/probe_bspl.py
```

`probe_cbcl.rs` compares low-level causal/shape behavior and strict R6 locality. Authentication and full monitor admission are outside this probe. `run_cbcl_probe.py` links artifacts after an offline source build and checks the observed outputs; `cbcl-probe-build.json` retains exact compiler arguments and artifact hashes. Replay:

```sh
cargo build -p cbcl-parser --offline
python3 outputs/bspl-source-comparison-evidence/run_cbcl_probe.py
```

## Upstream tests and unsuccessful setup attempts

- `pytest-initial-missing-croniter.log`: declared dependencies did not supply imported croniter; installed it into the isolated environment.
- `pytest-missing-optional-sat.log`: test_bspl imports optional boolexpr. SAT dependency was not installed; no SAT execution is claimed.
- `pytest-missing-fixture.log`: selected test_protocol fixtures request extensionless samples/tests/auction, while checkout has auction.bspl. No upstream test/source was patched to conceal this issue.
- `pytest-final.log`: store/schema/message/core/emission/refinement/path selection passes. Broad sample-liveness traversal deselected; focused positive/negative liveness probes separately executed.

Exact final command, executed with working directory `/private/tmp/cbcl-bspl-source-audit`:

```sh
PYTHONPATH=/private/tmp/cbcl-bspl-source-audit/src /private/tmp/cbcl-bspl-review-venv/bin/python -m pytest tests/test_store.py tests/test_schema.py tests/test_message.py tests/test_core.py tests/test_adapter_emissions.py tests/test_refinement.py tests/test_paths.py -k 'not test_liveness' -q --tb=short
```

## Elephant and integrity

Existing local theory alias `cbcl-systematic-comparison`; ID `d53a04795c45767eabf510bb8c8e5041e61fb91cb75f02e27e05a656820e2701`. New signed source references l01–l03 and scoped findings distinguish observations, caveats and untested coverage. `elephant-operations.jsonl` retains this follow-up's commands/receipts. `elephant-log.json` exports the complete comparison theory journal at this follow-up, `elephant-status.json` the conclusions, `elephant-closure.json` the semantic fingerprint and `elephant-explanation.json` the concrete comparator inference. These supersede no prior archived export; the earlier evidence package remains its historical snapshot.

```sh
python3 outputs/bspl-source-comparison-evidence/verify.py
```

This checks source bytes, observed probe distinctions, the signed conclusion and review presence. It does not prove arbitrary payload correctness, backend equivalence, whole-language safety or network liveness. `verification.json` is the recorded result. No production changes, commit or push were made for this comparison.

## Repository packaging

Curated reports, matrices, source manifests, probe sources and benchmark summaries are committed. Raw browser captures/session transcripts, downloaded papers, full Elephant exports and execution logs remain local and are excluded by `.gitignore`. Hash manifests describe the full local research bundle, including those excluded files; the integrity verifiers require that local bundle and original source snapshots. A fresh checkout alone is not a full evidence archive.
