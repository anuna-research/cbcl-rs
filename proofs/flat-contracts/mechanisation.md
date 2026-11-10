# SPEC-041 mechanisation evidence

The additive `CBCL.FlatContracts` model preserves the legacy Lean atom library and models SPEC-040's tagged values and flat contracts.
The proof is about this Lean model. Rust agreement is tested independently; Rust machine code and the full RFC 9485 engine are not proved.

## Reproduce

Run `scripts/check-flat-contract-proofs.sh` from the repository. The script selects the checked-in Lean toolchain, builds the executable, audits theorems, and runs both contract suites.
For a shared Rust target directory, set `CARGO_TARGET_DIR` before invoking it.
The large differential test is ordinarily ignored because it requires the separately built Lean executable; the script explicitly runs it.

Source:

- [Tagged values and exact rationals](../../lean-cbcl/LeanCbcl/FlatContracts/Value.lean)
- [Denotation, checker, and resource theorems](../../lean-cbcl/LeanCbcl/FlatContracts/Checker.lean)
- [Source expansion, meaning, and cycles](../../lean-cbcl/LeanCbcl/FlatContracts/Resolution.lean)
- [JSON-lines executable](../../lean-cbcl/FlatContractsOracle.lean)
- [Axiom audit and concrete proof cases](../../lean-cbcl/FlatContractsAudit.lean)
- [Live Rust differential test](../../crates/cbcl-parser/tests/flat_contracts_lean.rs)
- [Specification](../../specs/SPEC-041-flat-contract-mechanisation.md)

## Theorem coverage

| Requirement | Kernel-checked statements |
|---|---|
| REQ-4100 numeric bounds | `comparison_correct`: operational crossproducts iff rational order; finite binary64 uses exact bit decoding, including subnormals |
| REQ-4100 contract meaning | `predicate_correct`, `leaf_correct`, `checker_correct`: Boolean acceptance iff independent declarative membership, with named `RegexCorrect` hypothesis |
| REQ-4100 representation | `integer_not_float`, `integer_not_decimal`, `preserves_value`; audit demonstrates numerically equal tagged atoms remain distinct |
| REQ-4101 finite resolution | `resolve_iff_expansion`: iff independently stated finite expansion; `builtin_resolves` supplies nonvacuous successful cases |
| REQ-4101 source meaning | `resolution_semantics`: resolved code means the same as source/environment interpretation |
| REQ-4101 declaration order | `lookup_permutation`, `resolve_permutation`, under consistent unique-name environments; executable installer rejects even identical duplicate names |
| REQ-4101 cycles | `resolved_descendant_no_cycle` covers all reachable branches; `unused_cycle_rejected` covers declarations unrelated to the checked root |
| REQ-4101 resources | `insufficient_work`, `bounded_acceptance`, `bounded_violation`, `reservation_permutation`; acceptance/violation requires input-fit and full reservation |
| REQ-4102 implementation connection | Authored JSON data is decoded independently in Rust and Lean; no verdict or primitive match result is sent to Lean |

The audit also checks exact `1.0`/`1m` rational equality, the minimum positive subnormal, binary64 `0.1` greater than exact decimal `0.1`, integer bounds, and Unicode scalar lengths.

`#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound` for the headline theorems.
Reservation permutation uses only `propext` and `Quot.sound`.
No new axiom, admitted proof, or native-decision shortcut is used.
`RegexCorrect` is an explicit theorem parameter, not a hidden axiom.

## Executable evidence

The pinned Lean 4.27.0 oracle and axiom audit build successfully.
The live suite passes 8,986 independent requests, primarily a Cartesian product of small contracts, values, and work allowances.
This count measures regression cases, not exhaustive installation or regex coverage.
The ordinary SPEC-040 parser acceptance suite passes: 19 tests, with one explicit fixture-authoring test ignored.
The full core/parser all-features regression suite passes: 1558 tests, zero failures, and 32 explicitly ignored tests.
An initial broader run exhausted local disk space; generated build artifacts were cleared before the successful rerun.

Cases include:

- All eleven builtins and all eight value representations, exact mixed numeric endpoints, integer limits, finite float extremes and subnormals.
- Tagged enumerations, scalar string length, immediate list length, conjunction/disjunction, aliases, repeated aliases, and a shared-dependency diamond.
- Declaration and composition permutations; unknown names, duplicate declarations, builtin/reserved shadowing, direct/mutual/unused cycles, and a cyclic union branch.
- Empty or duplicate enums, invalid constructor arity, disjoint conjunction carriers, contradictory numeric/length endpoints, and wrong predicate domains.
- Required-work minus one, equality, and plus one for numeric, enum, length, and composition checks, including acceptance and violation.
- Input storage at 65535/65536 bytes, input/source decimal lengths around 4096, value nesting around 32, alias depth around 32, and source predicate nesting around 32.
- Five closed reference regex languages, both matching and nonmatching Unicode inputs, and explicit unsupported-profile errors.

A deliberate Rust mutation changed `Op::Ge` from inclusive to strict comparison.
The live suite failed on `(integer (>= 0))` with integer zero and sufficient work: Lean accepted while Rust violated.
The mutation was restored, and the complete verification script passed afterward.
No execution logs are committed.

## Explicit boundaries

The binary64-to-rational formula is an explicit definition; there is no separate refinement proof against an external IEEE specification.
The Rust parser, normalized numeric constructors, signing, allocation, cached DAG compiler, and machine code are outside the kernel proof.
`Value.fits` models the specified input estimator; resource theorems prove guard behavior, not actual engine time or allocator bounds.
The resolver proves finite source expansion under explicit fuel and structural validity; it does not prove every Rust installation diagnostic or cache optimization.

The oracle caps combined authored JSON source at 8192 bytes and 128 expression nodes.
It separately reconstructs S-expression source and applies its nesting, storage, and decimal-size guard.
Compiler rejection kinds collapse to `definition-error`; transport/profile errors remain separate.
The oracle is an acceptance regression tool within these ceilings, not a verified arbitrary-input transport or compiler.

The reference regex languages are empty, `.`, `[0-9]{4}`, `INV-[0-9]+`, and literal `^x$`, matched against whole strings.
Other patterns return an explicit unsupported-profile error.
The backend has a proved reflection theorem for these independent finite language predicates.
General regex correctness remains the named `RegexCorrect` hypothesis.
Regex comparisons test zero and sufficient work; the reference backend's work placeholder is not the Rust automaton-state certificate.

## Independent review

`formal041_comprehension` correctly predicted representation-sensitive enums, exact bounds, and the regex/Rust trust boundary from the Orientation.
`formal041_proof_review` checked the numerical formulas and declarative checker/resolver proofs; its descendant-cycle finding produced the stronger theorem above.
`formal041_scope_review` identified source decimal/depth gaps and missing exact-work acceptance cases; source reconstruction and boundary tests address them.
Both reviews were read-only, and execution results above come from the primary agent's actual commands.
