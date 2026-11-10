---
id: SPEC-041
title: Flat Contract Mechanisation
status: implemented
version: 1.0.0
owner: CBCL maintainer
---

# Flat Contract Mechanisation

## Orientation

The failure is a verification gap: tests exercise SPEC-040 contracts but do not prove their semantics for every supported value.
This work mechanises a tagged value model, contract denotation, executable checking, and finite name resolution in Lean.
It remains on the numeric-types branch and preserves existing legacy Lean proofs through an additive model.
[[SPEC-041-flat-contract-mechanisation#REQ-4100]] defines semantic correctness; [[SPEC-041-flat-contract-mechanisation#REQ-4101]] covers installation and resources.
[[SPEC-041-flat-contract-mechanisation#REQ-4102]] separates executable Rust agreement from a proof about Rust machine code.

A successful check preserves its input representation. Conjunction requires every child, and disjunction requires an accepting child.
Integer, decimal, and finite binary64 interpretations compare as exact rationals; enumeration equality retains their distinct tags.
Insufficient reserved work produces resource exhaustion rather than a negative predicate result.
Reordering unique type declarations preserves name lookup and resolution; cyclic dependency expansion cannot resolve successfully.

Regex language membership is an explicit parameter, with a named matcher-correctness hypothesis on the checker theorem.
The proof does not silently assume that Rust regex-automata implements RFC 9485 correctly.
The live oracle uses a declared, closed regex reference profile and rejects unsupported oracle patterns explicitly.

Reviewer path: requirements, theorem statements, axiom audit, executable agreement evidence.
Implementer path: [[SPEC-041-flat-contract-mechanisation#CON-4100]], then [[SPEC-041-flat-contract-mechanisation#TEST-4100]].
Maintainer path: [[SPEC-041-flat-contract-mechanisation#Trust boundary]].

## Requirements

### REQ-4100

The Lean checker SHALL be sound and complete against an independently stated contract denotation, conditional only on declared primitive hypotheses.
The model SHALL distinguish integer, float, decimal, string, symbol, keyword, boolean, and list representations.
Numeric bounds SHALL use exact rational interpretation, including finite binary64 subnormal values.
Acceptance SHALL preserve representation; numeric equality SHALL NOT imply enumeration identity across representations.
Trace: [[SPEC-041-flat-contract-mechanisation#TEST-4100]], [[SPEC-040-numeric-and-refinement-types#REQ-4000]], [[SPEC-040-numeric-and-refinement-types#REQ-4001]].

### REQ-4101

Finite name resolution SHALL reject cyclic expansion and preserve results under permutations of unique declarations.
Resource theorems SHALL distinguish reservation failure from contract violation.
With sufficient work and valid input bounds, acceptance SHALL coincide with denotation, and violation with its negation.
Composition and aliases SHALL retain their denotational meanings.
Resolution SHALL be sound and complete against an independent finite-expansion judgment with explicit depth and structural validity conditions.
Unknown names SHALL reject; installation SHALL inspect unused definitions as well as referenced roots.
The reservation proof concerns accounting and guard behavior, not an unproved bound on regex-engine instructions or allocator costs.
Trace: [[SPEC-041-flat-contract-mechanisation#TEST-4100]], [[SPEC-040-numeric-and-refinement-types#REQ-4002]], [[SPEC-040-numeric-and-refinement-types#NFR-4000]].

### REQ-4102

A live differential test SHALL compare Rust installation and checking with the executable Lean model using actual authored definitions and values.
Oracle requests SHALL NOT contain expected Rust verdicts or substitute those verdicts for primitive semantics.
The verification record SHALL state unsupported profiles, unproved implementation boundaries, and theorem axiom dependencies explicitly.
Trace: [[SPEC-041-flat-contract-mechanisation#TEST-4101]].

## Contracts

### CON-4100

The formal value model adds explicit integer, binary64-bit, and normalized decimal representations beside the existing legacy atom model.
A source expression contains primitive contracts, local references, conjunctions, or disjunctions; closed code retains resolved names for attribution.
A regex backend supplies an executable matcher and mathematical language predicate; their equivalence is a theorem hypothesis.
Input bounds and primitive work costs remain explicit parameters where implementation certificates are not proved.

The oracle accepts one JSON object per line and returns one JSON object per line.
Its transport grammar is a tagged algebraic data format:

```text
atom := ["integer", signed-decimal-text] | ["float", unsigned-bit-text]
      | ["decimal", coefficient-text, nonnegative-scale]
      | ["string" | "symbol" | "keyword", text] | ["bool", boolean]
value := atom | ["list", value*]
expr := ["builtin", name] | ["ref", name] | ["enum", atom*]
      | ["refine", builtin-name, predicate*] | ["all" | "any", expr*]
predicate := [">" | ">=" | "<" | "<=", numeric-atom]
           | ["length", [comparator, nonnegative-bound]*] | ["matches", pattern]
request := {"definitions": [[name, expr]*], "contract": expr,
            "value": value, "work": nonnegative-integer}
response := {"verdict": "accepted" | "violation" | "resource-limit" | "definition-error"}
          | {"error": diagnostic-text}
```

The decoder recognizes whole records, rejects malformed tags and invalid numeric representations, and never treats unsupported regex patterns as value mismatch.
Core non-regex resource comparisons use the installed profile's concrete costs and input estimator.
The oracle limits authored source to 128 expression nodes and 8192 combined JSON bytes, returning explicit unsupported-profile errors above either ceiling.
It reconstructs source S-expressions to check nesting, storage, and numeric-literal bounds independently of compiled code.
Installation rejection categories are collapsed to `definition-error`; compiler diagnostic wording and blame are outside this comparison.
Regex cases use zero or sufficient work; no exact Rust NFA-state-count proof follows from those comparisons.
The closed regex profile contains empty, `.`, `[0-9]{4}`, `INV-[0-9]+`, and literal `^x$` languages.

## Acceptance

### TEST-4100

Build the Lean modules with the pinned toolchain and audit the headline theorem dependencies.
Reject new axioms, admitted proofs, and unchecked native decision shortcuts in theorem proofs.
Check positive and negative values, exact numeric edges, composition, aliases, permutations, cycles, and resource boundaries.
Prove constructor-level acceptance and finite-expansion completeness so an always-rejecting resolver cannot satisfy the proof obligations.
State denotation through declarative composition, rational order, tagged enumeration identity, scalar length, and transparent aliases, independently of checker outcomes.
Run an independent proof review and resolve substantive findings.
Trace: [[SPEC-041-flat-contract-mechanisation#REQ-4100]], [[SPEC-041-flat-contract-mechanisation#REQ-4101]].

### TEST-4101

Build the JSON-lines Lean oracle and run Rust comparisons against actual installation and checking.
Exercise generated non-regex contracts and explicit closed-profile regex cases without passing expected results to Lean.
Reject malformed definitions, duplicates, shadowing, unknown names, unused cycles, disjoint intersections, and contradictory local bounds.
Ensure a deliberately broken Rust checker fails the differential test.
Record limitations alongside passing results.
Trace: [[SPEC-041-flat-contract-mechanisation#REQ-4102]].

## Trust boundary

This stage proves the Lean model, not the Rust compiler, parser, canonical signing encoder, allocator, or regex engine.
The executable oracle supplies regression evidence connecting independent implementations; it is not a Rust refinement theorem.
Full RFC 9485 parser/automaton verification and formal Rust refinement remain explicit future obligations.
No proof assumes regex correctness without naming that hypothesis in its theorem statement.

## Amendment Channels

The maintainer changes semantic scope through reviewed amendments to this specification and [[SPEC-040-numeric-and-refinement-types]].
Oracle data and Rust verdicts cannot amend the formal semantics or discharge proof hypotheses.

## Review status

The pinned Lean build and headline axiom audit pass; [mechanisation evidence](../proofs/flat-contracts/mechanisation.md) maps requirements to theorems and executable checks.
Independent comprehension, proof, and scope reviews identified resource wording, resolution vacuity, descendant cycles, and source-budget gaps; each was corrected.
The proof uses only Lean's standard `propext`, `Classical.choice`, and `Quot.sound` axioms, with matcher correctness explicitly parameterized.
Live comparisons and a caught Rust mutation provide regression evidence within the documented oracle profile.
