# SPEC-040 implementation verification

The implementation covers numeric hierarchy, local flat contracts, composition, exact bounds, I-Regexp, enumerations, length limits, defaults, signatures, schemas, and shared bindings.
The maintainer authorized implementation on `feat/issue-21-numeric-types`; PR 29 contains the change.

## Executable acceptance

| Check | Result |
|---|---|
| `cargo test -p cbcl-core -p cbcl-parser --all-features` | 1558 passed, 0 failed, 31 explicitly ignored |
| `cargo test -p cbcl-wasm -p cbcl-erl --lib --all-features --no-fail-fast` | WASM 68 passed; Erlang 43 passed, 19 existing VM-dependent tests ignored |
| `cargo check --workspace --all-targets --all-features` | Passed |
| `cargo check -p cbcl-core -p cbcl-parser --no-default-features` | Passed |
| Browser-target WASM release build with wasm-bindgen 0.2.114 | Passed; executed in Node's WebAssembly engine |
| `npm --prefix js run check` | Passed |
| `npm --prefix js test` | 29 passed; 3 existing role-root address failures, confirmed against baseline |
| Dedicated `js/test/flat-contracts.test.ts` | All 3 passed, including portable compilation thresholds and maximum-size inputs |
| Internet-Draft Markdown-to-XML generation and XML parsing | Passed |

The 30 [shared vectors](../../test-vectors/contracts/flat-contracts.json) run through the parser, WASM bytes API, Erlang pure NIF entry point, and actual WASM module.
The [core acceptance suite](../../crates/cbcl-parser/tests/flat_contracts.rs) exercises all TEST-4000 through TEST-4006 obligations.
Independent arithmetic and ASCII-format property oracles supplement explicit Unicode, malformed-pattern, and boundary cases.
Normal tests never rewrite fixtures. The signing fixture has an explicit ignored authoring command.

The initial parser run failed five new acceptance cases before integration.
[Mutation evidence](mutations.json) records three deliberately broken guards that made their targeted tests fail:
whole-check reservation, full-string regex anchoring, and mixed-symbol state rejection.
Restoring the implementation returned the contract suite to green.

## Portable resource profile

[The profile](../../specs/SPEC-040-numeric-and-refinement-types.md#implementation-profile) fixes Unicode 16.0.0, syntax, caps, and portable compiled costs.
The pinned regex recognizer translates RFC 9485 into regex-syntax 0.8.11 and regex-automata 0.4.14 Thompson PikeVM execution.
Sparse, dense, union, terminal, and other NFA states have explicit fixed-width accounting, independent of native pointer size.
The shared `a{8000}` and `a{8300}` vectors distinguish admitted compilation from profile resource rejection on native and WASM.
Actual allocator safeguards remain separate operational limits.

Regex work reserves `16 * (states + 1) * (65536 + 1)` units before evaluation.
Each exact numeric bound reserves `16 * 4096 * 4096` units; length and enumeration work include maximum permitted input scanning.
Composition sums conservative work, and cached aliases retain resolved height without copying their programs.
Per-check memoization avoids repeated evaluation of shared nodes; branch permutations have equal reservation requirements.
These units are admission accounting, not a promise about processor cycles.

At the maximum permitted string input, `(a|aa)*b` accepted/rejected adversarial cases completed in approximately 17–21 ms natively in debug tests.
The browser-target release module completed equivalent cases in approximately 6–8 ms under Node.
These are local diagnostic measurements across different build profiles, not a comparative performance claim.
Resource-limit boundaries, large repetitions, member counts, depth, defaults, and long exact decimals are exercised separately.

## Signing and fixture migration

[The signing fixture](../../test-vectors/contracts/signing-v6.json) records old/new canonical bytes and self-addresses for unchanged `number` source.
The R4 test rejects its old-format signature under signing form 6.
Type declarations sort by name; their source definitions, enumeration order, composition, defaults, bounds, and regex strings remain committed.
Existing integer-only authored promises are explicitly rewritten as `integer`.
Historical `state-pre-lvar-bytes.json` remains unchanged; its test translates the old integer spelling explicitly at the read boundary.
The bundled checkpoint code-pin expectation changes with the signing format.

[Resource fixture migration](../../test-vectors/contracts/resource-fixture-migration.json) records refreshed SDK resource-check frames.
They use the already accepted state corpus's current sealed-root histories and explicit integer declarations.
This corrects stale standalone frames without changing resource admission semantics.

## Independent reviews and remaining depth

`impl040_core_review` checked numeric exactness, RFC recognition, purity, defaults, graph bounds, state carrier restrictions, diagnostics, and alias integration.
Its findings were corrected and independently rechecked.
`impl040_completeness_review` checked schemas, grammar, coverage, reservation boundaries, and pointer-width independence.
Its final pass reported no substantive objections.

The complete local name map plus source definitions and resolved representation sets forms the schema's acyclic contract graph.
Optional fields expose requiredness and default source; hosts keep validation in the shared checker.

The three JavaScript corpus failures predate this implementation.
A separately built pre-implementation WASM module at `179e7da` produced exactly the same root-address mismatches.
[Baseline evidence](baseline-addresses.json) records both outputs and the corpus expectations.
The affected tests are bounded-ceiling, bounded-coin, and checklist-roles; their public message-hash helper uses the older simple-address policy.
No new contract test depends on those mismatches.

Maintainer-owned depth follow-up: differential testing against a separate complete I-Regexp implementation and broader target/performance corpora.
The existing ignored Lean and BEAM VM tests retain their documented infrastructure requirements.
The Rust contract checker and signing form 6 are not covered by an additional Lean proof here.
No formal equivalence or universal performance claim is made.

## Formal contract model

[SPEC-041 mechanisation](mechanisation.md) adds kernel-checked contract semantics, finite resolution, and live Rust/Lean comparisons on this branch.
It records the named regex hypothesis and remaining Rust refinement boundary separately from the implementation checks above.

## External I-Regexp conformance

[Upstream fixtures and independent-engine comparisons](iregexp-conformance.md) now cover RFC syntax and matching through the actual checker.
The finite corpus strengthens the regex evidence; complete RFC/engine equivalence remains outside the proof boundary.

## Actionable contract diagnostics

SPEC-040 REQ-4006 now reports alias names, numbered `and`/`or` branches, failed refinement clauses, numeric/length bounds, and full-string regex constraints.
Definition errors include dialect/performative/field context where applicable, with one-based Unicode character positions for recognizer errors in decoded regex patterns.
Invalid ranges are diagnosed at their source endpoints before host adaptation.
Resource details explain required/available work or the input storage, decimal-size, or nesting limit; public shape errors retain the operational category.

Nine [diagnostic acceptance tests](../../crates/cbcl-parser/tests/contract_diagnostics.rs) pass, including nested fields, default-child resource classification, shared alias DAGs, Unicode truncation, and private field contents.
Four of the original five cases failed against the previous messages before implementation.
Deliberate privacy-leak and default-child category mutations each compiled and failed the intended assertion; both were restored.
Existing contract and upstream/reference conformance suites pass, and all 8,986 live Lean-oracle comparisons retain their verdicts.
Final all-features library checks pass: core 881, parser 164, WASM 68, and Erlang 43 tests, with 19 existing VM-dependent tests ignored.
Core/parser checks without default features also pass.
No signed source, canonical format, contract acceptance rule, or portable work reservation changed.

Internal failure reasons are capped at 2048 UTF-8 bytes, with at most eight expanded `or` alternatives and an omitted-branch count.
Public shape metadata can additionally contain the full authored contract; the cap is not a bound on that entire response.
Direct `CheckError::ResourceLimit` remains a stable typed category; the shape boundary supplies its contextual explanation.
Independent review verified the code, final runs, and both mutation logs; no execution logs are committed.
