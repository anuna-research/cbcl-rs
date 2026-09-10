# Raw-language DCFL installation evidence

This completes [[SPEC-018-dcfl-installation#REQ-1803]] and the final acceptance
work, building on [[dcfl-foundation-evidence-2026-09-10]] and
[[dcfl-installation-evidence-2026-09-10]].

## Proved language and installation claim

For every finite declaration environment, `CBCL.InstalledSyntax.Raw.environmentDCFL`
constructs a standard finite real-time DPDA recognizing `Raw.language` exactly
on every input word. `Raw.language` is the concrete finite lexer's successful
classified output followed by the independently specified recursive token
grammar. The lexer is the executable definition of CON-1803; no arbitrary
inverse-image closure assertion or assumed tokenization theorem is used.

`Raw.base_dcfl`, `Raw.dcfl_preserved`, and `Raw.dcfl_preserved_many` cover the
base environment, one append, and every finite sequence of appends.
`Raw.accepted_installations_dcfl` covers any installation policy;
`Raw.verified_fresh_installations_dcfl` specializes to the existing Lean
verification conjunction plus freshness. The earlier `pipeline_verified_fresh`
connects this relation to successful `verifyDialectString`. No global bound on
installation count, input length, or nesting depth is imposed. Each fixed
finite environment gets its own finite machine.

## Proof construction

- `LexicalComposition.lean`: a finite lexer emits at most an atom followed by a
  parenthesis per scalar. `advance_correct` fuses these into one top-of-stack
  rewrite. `product_accepts` proves exact composition for arbitrary words,
  including malformed token streams, lexer failure, and a pending final atom.
  Acceptance inspects finite control only; no epsilon transition or external
  end marker is required.
- `InstalledLexer.lean`: a concrete lexer handles whitespace, comments,
  strings and escapes, symbols, keywords, booleans, and signed 64-bit numbers.
  All retained state has an explicit finite codec. Arbitrarily long strings
  and comments are discarded incrementally; name matching uses a bounded
  cursor and candidate vector, and numbers use a bounded magnitude.
- `ScalarCode` is `Fin 0x10f800`, a dense numbering excluding the 2,048
  surrogate code points. `codepoint_scalar`, `codepoint_encodeChar`, and
  `encode_codepoints` prove scalar validity and exact Lean string encoding.
- `LexicalNames.lean`: `wordChar_invariant` and `nameMatches_word` prove exact
  equality with each dictionary name for every environment and arbitrary word
  length. Prefixes and long extensions cannot alias installed/reserved names.
- `tokenCheck_correct` and `check_correct` prove that the executable reference
  checker equals the actual finite DPDA. Tests can therefore exercise complete
  raw recognition without evaluating huge encoded finite-control integers.
- `Raw.recognizes_expression` connects raw recognition to concrete recursive
  admission **given** that lexing produces the expression's classified encoding.
  This is not a separate value-preserving raw-to-AST parser theorem.

## Verification

All commands below run from `lean-cbcl` unless otherwise noted.

| Check | Result |
|---|---|
| `lake build` | Exit 0, 77 jobs; includes all new modules and tests |
| `lake env lean LeanCbcl/LexicalNames.lean` | Exit 0 |
| `lake env lean LeanCbcl/InstalledLexerTests.lean` | Exit 0 |
| `lake env lean DCFLInstallationAudit.lean` | Exit 0 |
| Axiom audit of all exported token/raw capstones | Only `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`, project assumptions, or native-decide trust |
| Escape mutant allowing `q` | Exit 1: original `\q` rejection proposition is false |
| Boolean mutant removing delimiter guard | Exit 1: original `#true`, `#tx`, and complete-message rejection propositions are false |
| Overflow mutant permitting positive `2^63` | Exit 1: original lexical and complete-message overflow rejection propositions are false |
| `zetl check --dead-links --fail-on error` (repo root) | Exit 1: existing dead-link debt; zero syntax, SPL, and predicate errors |
| Runtime diff inspection | No tracked Rust or deployment changes; existing unrelated untracked work preserved |

The original kernel `decide` tests cover both signed endpoints and adjacent
overflows, arbitrarily extensible leading-zero form, malformed numeric runs,
initial-minus dispatch (`--3` is a symbol), boolean boundaries, all allowed
escapes, invalid/dangling escapes, comment EOF, all five whitespace characters,
Unicode strings, unsupported symbols, empty keywords, exact-name collisions,
recursive scope replacement, unknown names, argument restrictions, bare `@`,
unbalanced parentheses, empty input, and trailing expressions. Universal
claims come from the proofs, not the finite examples.

Mutation files were isolated under `/private/tmp`; the source proofs and
original tests were copied together, each mutation changed one lexer guard,
and all other declarations elaborated. Failures were false original test
propositions, not malformed mutants. Durable logs:
`outputs/dcfl-escape-mutation.log`, `outputs/dcfl-boolean-mutation.log`, and
`outputs/dcfl-overflow-mutation.log`. Build and axiom logs:
`outputs/dcfl-full-build-2026-09-10.log` and
`outputs/dcfl-full-axioms-2026-09-10.log`.

## Independent review

Fresh-context reviewer `/root/raw_installation_review` read SPEC-018 and the
finite-machine/lexer construction, independently compiled the exact-name proof
and lexer tests, and passed REQ-1803 within its stated scope. It checked scalar
encoding, finite retained state, top-only rewrites, complete consumption,
EOF handling, exact-name fidelity, and executable-check equality. It required
honest lexical-definition and runtime boundaries. The final build and axiom
audit satisfy its remaining verification condition. Earlier independent
foundation and recursive-installation reviews are recorded in the linked
reports. The reviewer subsequently read the final README, specification,
evidence, build/axiom logs, and mutation results and gave final acceptance:
PASS, with no remaining approval blocker.

## Boundaries

The full **specified syntactic installation claim** is proved. This does not
prove Rust parser, lexer, registry, or additional installation-gate equivalence.
UTF-8 byte decoding is outside the scalar theorem. The IETF example calling
`--3` invalid contradicts its first-character dispatch rule; SPEC-018 and this
lexer follow dispatch. The documented runtime differences for bare `@` and
`:thread`/`:sender` remain maintainer follow-ups. Expansion costs, endpoint
projection, causal validity, and execution behavior are separate claims.

The repository Markdown vault has existing dead-link debt, including the
source-code wikilink documented in SPEC-018. Vault-wide link validation must
not be confused with the successful Lean build and theorem audit.
