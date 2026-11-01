# Comparison evidence package

Research date: 2026-11-01. Main report: [[cbcl-systematic-comparison]]. Method: [[cbcl-comparison-method]]. Independent review: [[cbcl-comparison-review]].

## ar-crawl sessions

- Initial session `9df44668-849a-46d4-80ec-164f1cdc051a`: blocked W3C attempt retained in `initial-session.json`.
- Main session `31dc507c-7078-40b9-825c-0de1cba4998c`: `session-recording.json` and `session-transcript.jsonl`.
- Supplement `6805cec0-73bc-4d64-8d63-9d7d3da2e581`: `session2-recording.json` and `session2-transcript.jsonl`.

`S01.json` through `S40.json` retain browser navigation/capture results, source URL and timestamp. `S35.pdf`/`.txt` and `S37.pdf`/`.txt` are explicit primary-origin PDF fallbacks after browser download-navigation failure. W3C publication-page failures S14/S18 are not evidence of missing features; editor-copy alternatives S30/S31 are version-scoped. Manifest filenames `sources*.json` preserve collection labels, including the original `ubl-ebbP` typo and historical combined OpenAPI/AsyncAPI label; the curated matrix supersedes those labels for analysis.

## Elephant

Local alias `cbcl-systematic-comparison`; theory ID `d53a04795c45767eabf510bb8c8e5041e61fb91cb75f02e27e05a656820e2701`.

`elephant-log.json` is the signed full journal, including definitions and retractions. `elephant-operations.jsonl` records CLI arguments, outputs and exit codes, including the corrected unsupported bare closure command. `theory.spl` is an assertion-history convenience file: it includes superseded assertions and omits retractions/definitions; **do not load it as a current-state snapshot**. Use the signed journal for history, `elephant-status.json` for current conclusions, `elephant-vocab.json` for vocabulary and `elephant-closure.json` for the canonical semantic fingerprint. `elephant-trace.json` and `elephant-scope-explanation.json` show derivations.

Assessments are signed human research judgments, not formal proofs about projects. Every assessment cites its row's first source as an index; consult `matrix.json` and the source document for the complete row source set. Only native assessments derive `documented-support`. No rule infers universal uniqueness or full-bundle equivalence from missing support. Defined but unused `full-bundle-demonstrated` is intentionally unasserted. Retractions preserve the independent review's rating corrections.

To inspect the live local theory:

```sh
elephant status -t cbcl-systematic-comparison --json
elephant explain '(finding universal-uniqueness-unestablished)' -t cbcl-systematic-comparison --json
elephant closure fingerprint -t cbcl-systematic-comparison --json
```

## Verification

From the repository root:

```sh
python3 outputs/cbcl-comparison-evidence/verify.py
```

This checks source and local-baseline hashes, matrix coverage, exact active Elephant assessments, native-support derivation and the conservative uniqueness policy. It does not validate the truth of every assessment or make this an exhaustive literature review. `verification.json` records the completed check. No production code, normative specification or protocol implementation was changed for this comparison.

## Repository packaging

Curated reports, matrices, source manifests, probe sources and benchmark summaries are committed. Raw browser captures/session transcripts, downloaded papers, full Elephant exports and execution logs remain local and are excluded by `.gitignore`. Hash manifests describe the full local research bundle, including those excluded files; the integrity verifiers require that local bundle and original source snapshots. A fresh checkout alone is not a full evidence archive.
