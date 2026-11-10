# I-Regexp conformance evidence

This implements the external-conformance portion of SPEC-040 TEST-4003 on the numeric-types branch.
Upstream fixtures and an independent JavaScript engine agree with Rust on the recorded cases.
No production recognizer or matcher changes were necessary.

## Reproduce

Run `scripts/check-iregexp-conformance.sh`.
The script checks pinned upstream checksums and deterministic adaptation, replays JavaScript expectations, and tests actual Rust installation/checking.
The normal Rust suite also runs all committed cases offline without an external runtime.

[Corpus provenance and adaptations](../../test-vectors/contracts/iregexp/README.md) documents licenses, excluded cases, and the known JSONPath anchor correction.
[Live Rust tests](../../crates/cbcl-parser/tests/iregexp_conformance.rs) fail on unexpected compilation or resource errors instead of misclassifying those as mismatches.

## Observed results

- 49 pinned upstream syntax cases pass, including both valid and invalid patterns.
- 297 adapted upstream matching cases pass.
- 338 independently rendered patterns against 300 strings yield 101,400 passing Boolean comparisons.
- Raw `^ab.*` and `.*bc$` pass dedicated positive and negative literal-anchor checks.

The independent engine is V8 through Node 25.2.1, using Unicode 17.0.
Rust uses regex-syntax 0.8.11 and regex-automata 0.4.14, with Unicode 16.0 pinned by the contract profile.
The fixed reference samples avoid newly assigned Unicode 17 scalars; entire Unicode-table equivalence remains untested.

Three temporary mutations each caused an actual assertion failure:

| Mutation | Test detecting it |
|---|---|
| Dot accepts CR by using the host dot behavior | Independent-engine reference goldens |
| Matching accepts substrings by removing whole-string anchors | Adapted upstream matching goldens |
| Recognizer accepts unsupported `\v` | Upstream syntax goldens |

Each mutation was restored before the final passing conformance run.
Execution logs remain outside the repository.

## Formal boundary

These tests strengthen confidence in RFC conformance, but finite cases cannot establish the `RegexCorrect` hypothesis for arbitrary inputs.
The [existing contract mechanisation](mechanisation.md) still states regex correctness as an explicit parameter.

The [LindenRegex I-Regexp mechanisation](https://github.com/LindenRegex/I-regexp_mechanization) is relevant prior work: it defines XSD/I-Regexp semantics and proves translations to ECMAScript.
Its README describes that scope; we have not built or audited those proofs and do not claim they verify CBCL's Rust adapter.
A future refinement proof would connect the Rust recognizer and translation to independently defined RFC semantics and the pinned engine's matching behavior.

Remaining depth includes arbitrary grammar-generated patterns, exhaustive Unicode 16 category tables, broad resource-adversarial patterns, and full adapter/engine refinement.
The corpus is deliberately finite and adds no claim of complete RFC certification.

## Independent review

`formal041_scope_review` checked the adapters, independent renderers, test paths, and evidence boundaries.
Its class-property and positive literal-anchor coverage findings produced the additional cases above.
The reviewer then found no substantive remaining defect and inspected the external mutation/final logs.
Each mutant failed a semantic assertion after successful compilation, and the final conformance run passed.
