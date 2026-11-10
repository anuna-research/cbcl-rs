# I-Regexp conformance corpus

These fixtures exercise SPEC-040 REQ-4003 through actual dialect installation and the shared Rust checker.
They supply external regression evidence, not proof of correctness for every RFC 9485 pattern and string.
Run `scripts/check-iregexp-conformance.sh` to verify provenance, replay the independent engine, and run Rust checks.
Ordinary `cargo test -p cbcl-parser --test iregexp_conformance` runs the checked-in expectations without Python, Node, or network access.

## Upstream provenance

[sources.json](sources.json) pins each original file by full commit, source URL, SHA-256, and license.
The importer verifies every original checksum before generating [upstream-cases.json](upstream-cases.json).
It never calls the CBCL implementation to derive expected answers.
Run `python3 scripts/import-iregexp-fixtures.py --check` to verify deterministic adaptation; omit `--check` to regenerate it.

- `cabo/iregexp` at `e27fe69da658558bf0b160e8fecf3f99a545c1cb`: original `simple.irl`, `simple.out`, and license-bearing `iregexp.gemspec` are preserved under [upstream/cabo](upstream/cabo).
  Upstream author: Carsten Bormann. The retained gemspec declares MIT; the original fixture files supply no separate copyright notice.
- `jsonpath-standard/jsonpath-compliance-test-suite` at `20ebdcce5008c8a777ee9c80ad853ecf606950b5`: original `tests/functions/match.json` and its [BSD-2-Clause license](upstream/jsonpath/LICENSE) are preserved under [upstream/jsonpath](upstream/jsonpath).

## Adaptations

All 49 Cabo syntax entries run, including the three `*` entries whose syntax is valid but whose upstream example generator is known to fail.
Only example strings from `=` entries become matching expectations; `*` example strings are deliberately excluded.
Generated example lists provide positive cases, not complete languages.

The JSONPath adapter uses an explicit selector-to-pattern mapping and validates that mapped patterns occur in their source selectors.
It projects only string candidates and reverses selection when the JSONPath filter negates `match()`.
Six JSONPath-specific cases are explicitly listed as excluded: non-string function arguments, selector/type errors, and a nested `value()` expression.
The adapter does not implement JSONPath and does not treat `search()` substring expectations as full-match expectations.

Two upstream cases incorrectly use `^` and `$` as anchors.
Their originals remain untouched; adapted expectations carry an explicit link to [upstream issue #122](https://github.com/jsonpath-standard/jsonpath-compliance-test-suite/issues/122).
RFC 9485's grammar makes those characters literal outside classes.
Dedicated positive and negative Rust cases additionally check raw `^ab.*` and `.*bc$`.
There are 297 adapted matching cases, including both positive and negative JSONPath expectations.

## Independent reference engine

[scripts/check-iregexp-reference.mjs](../../../scripts/check-iregexp-reference.mjs) constructs small regex ASTs and renders them separately into I-Regexp and ECMAScript.
The ECMAScript renderer never receives a Rust-generated translation, compiled program, or verdict.
Literal scalars become hexadecimal escapes in ECMAScript; dot excludes exactly CR/LF; a strict end assertion prevents JavaScript's final-newline exception.
JavaScript's own Unicode property engine supplies independent matching results.

[reference-cases.json](reference-cases.json) stores 338 patterns and 300 fixed strings, yielding 101,400 Boolean expectations.
It covers empty patterns, supplementary scalars, literal metacharacters, alternation, concatenation, repetitions, nested counted repetitions, ranges, complements, and every RFC-listed Unicode category.
Property escapes appear both alone and inside classes, including the three Cabo cases without reliable generated examples.
The sample set includes CR/LF, other line separators, composed/decomposed text, controls, private-use scalars, and an unassigned scalar.

The generator records the producing Node, V8, and Unicode versions.
This corpus was produced with Node 25.2.1 / Unicode 17.0; Rust's contract profile pins Unicode 16.0.
Fixed samples avoid newly assigned Unicode 17 characters. This is not an equivalence test of the entire Unicode tables.
Replaying the corpus with another engine version compares results, not the generator metadata.
Use `node scripts/check-iregexp-reference.mjs --write` only for an intentional, reviewed refresh.
