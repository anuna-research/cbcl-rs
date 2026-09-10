# Lean proof status

The recursive token and raw Unicode-scalar installation theorems for
[[SPEC-018-dcfl-installation]] are implemented and independently reviewed.
There is no claim of Rust parser or installation-gate equivalence.

`CBCL.FormalLanguage.DPDA` enforces finite input, control-state, and stack-symbol
types. Transitions consume one symbol and replace only the stack top. Missing
transitions reject permanently. Acceptance examines only the final control state
after consuming the complete word.

`ForestAlgebra.isRealtimeDCFL` constructs such a machine for any finite forest
algebra. `ForestAlgebra.accepts_iff` proves equivalence with an independently
defined language of serialized syntax forests, over every token word. The proof
includes malformed input and imposes no nesting bound. Its axiom dependencies
are `propext` and `Quot.sound`.

`InstalledSyntax.environmentDCFL` constructs the recogniser for each finite
installed environment. `decode_encode_atom` proves preservation of concrete
atom predicates; `encoded_direct_tree` and `recognizes_expression` connect
recognition to the independent, scope-indexed `admittedAt` evaluator. The grammar
includes recursive wrappers, nested scope replacement, declared performative
membership, recipients, and restricted keyword values.

`InstalledSyntax.dcfl_preserved_many` covers arbitrary finite append sequences.
`VerifiedFresh` identifies the existing Lean R1/R2/R3 verification conjunction
plus freshness; `pipeline_verified_fresh` connects it to `verifyDialectString`.
`verified_fresh_installations_dcfl` and `verified_sequence_unique` cover that
relation's finite sequences. Rust's additional admission gates are not modelled
as equivalent; the unconditional finite-environment theorem also covers any
finite environments selected by stricter policies.

These results use the standard finite-machine certificate. The older
`CBCL.IsDCFL` and `CBCL.dcfl_preserved` interfaces remain legacy shallow results.

`InstalledSyntax.Raw.environmentDCFL` adds a concrete finite lexer and proves
DCFL membership for the declared raw language. Its input alphabet densely
numbers all Unicode scalars, excluding surrogates. `FiniteLexer.product_accepts`
proves composition over every raw word, including lexical failures; pending
atoms and parentheses can be processed in a single stack-local transition.
`Raw.nameMatches_word` proves exact name matching for arbitrary token lengths.
`Raw.check_correct` connects the executable checker used by tests to the actual
finite DPDA. `Raw.dcfl_preserved_many` and
`Raw.verified_fresh_installations_dcfl` provide the raw installation capstones.

The concrete lexer defines SPEC-018's lexical language. This is not a separate
formal equivalence proof against the IETF prose or existing Rust/Lean parsers.
The spec follows first-character dispatch for `--3` (a symbol), despite a
contradictory draft example. UTF-8 byte decoding, runtime conformance, expansion
costs, and causal validity remain separate obligations.

Run `lake build` here to check the library and grammar examples, and
`lake env lean DCFLInstallationAudit.lean` for the exported axiom audit. The new
capstones use only `propext`, `Classical.choice`, and `Quot.sound`. Grammar tests
use kernel `decide`; the arbitrary-nesting property is proved by induction.

Full evidence: [[dcfl-raw-installation-evidence-2026-09-10]].
