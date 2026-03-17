# Test Vectors

Reference inputs and expected outputs for cross-implementation testing.

These vectors are used to verify that the Rust implementation produces
identical results to the Lean 4 proofs and Guile reference implementation.

## Structure

```
test-vectors/
  sexpr/                S-expression parse/serialize round-trip vectors
    parse.json            Canonical S-expression parsing (RFC 9804)
    serialize.json        Canonical S-expression serialization
    round-trip.json       Parse-serialize round-trip identity
    errors.json           Invalid S-expression inputs
  messages/             CBCL message parsing vectors
    simple.json           Core performative messages (tell, ask, reply, etc.)
    meta.json             Meta messages (query, define, teach)
    wrapped.json          Envelope, signed, and with-limits wrappers
    lang.json             Language-scoped dialect messages
    canonicalization.json Keyword argument canonicalization
    strings.json          String/atom parsing (escapes, identifiers, etc.)
    invalid.json          Invalid message inputs
  dialects/             Dialect definition and verification vectors
    definitions.json      Dialect structure and properties
    verification.json     Dialect verification and cross-dialect checks
    messages.json         Dialect-specific performative messages
  pipeline/             Full pipeline input/output vectors
    template-expansion.json  Template expansion with bindings
    pattern-matching.json    Pattern matching and variable binding
    integration.json         End-to-end multi-step scenarios
    edge-cases.json          Edge cases and type predicates
  r1-r4/                Safety constraint verification vectors
    r1-no-recursion.json     R1: No recursion in templates
    r2-resource-bounds.json  R2: Resource limit enforcement
    r3-core-preservation.json R3: Core performative protection
    r4-signatures.json       R4: Signature and integrity verification
```

## Format

Each vector file is a JSON array of test cases:

```json
[
  {
    "id": "unique-id",
    "description": "human-readable description",
    "input": "(tell @alice \"hello\")",
    "expected": { "type": "success", "value": "..." },
    "source": "tests/file.scm:test-group",
    "spec_ref": "EBNF line or spec section"
  }
]
```

## Sources

Vectors were extracted from:
- `tests/*.scm` — Guile reference implementation test suite (26 files)
- `simulation/*.scm` — Multi-agent simulation scenarios
- `src/cbcl-grammar.ebnf` — Formal grammar specification
- `lean-cbcl/` — Lean 4 proof library type definitions

## Coverage

| Category | Vectors | Sources |
|----------|---------|---------|
| S-expression parse | 12 | test-csexp.scm, test-csexp-standalone.scm |
| S-expression serialize | 6 | test-csexp.scm |
| S-expression round-trip | 7 | test-csexp.scm |
| S-expression errors | 6 | test-csexp.scm |
| Simple messages | 11 | ietf-compliance-test.scm, simple-tests.scm |
| Meta messages | 5 | ietf-compliance-test.scm |
| Wrapped messages | 6 | ietf-compliance-test.scm |
| Lang messages | 2 | ietf-compliance-test.scm |
| Canonicalization | 3 | simple-tests.scm |
| String/atom parsing | 14 | test-grammar-compliance.scm, basic-parser-test.scm |
| Invalid messages | 7 | simple-tests.scm, grammar inference |
| Dialect definitions | 4 | dialect-implementation-tests.scm |
| Dialect verification | 6 | validate-paper-dialects.scm |
| Dialect messages | 10 | test-precision-agriculture.scm |
| R1 no-recursion | 10 | r1-simple-test.scm, test-r1-main-module.scm |
| R2 resource bounds | 8 | test-grammar-compliance.scm |
| R3 core preservation | 10 | test-grammar-compliance.scm |
| R4 signatures | 4 | ietf-compliance-test.scm, test-csexp.scm |
| Template expansion | 8 | test-grammar-compliance.scm |
| Pattern matching | 2 | simple-tests.scm |
| Integration | 5 | test-precision-agriculture.scm |
| Edge cases | 10 | test-precision-agriculture.scm, test-csexp.scm |
| **Total** | **156** | |
