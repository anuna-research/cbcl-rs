# ADR-001: Parser Library Choice

| Field        | Value                                      |
|--------------|--------------------------------------------|
| **ID**       | ADR-001                                    |
| **Title**    | Parser Library Choice                      |
| **Status**   | Accepted                                   |
| **Date**     | 2026-03-18                                 |
| **Context**  | SPEC-001 (REQ-040–045, NFR-001, NFR-004)   |
| **Relates**  | PURITY-MAP-001 (parser in pure core)       |

## 1  Context

The CBCL Rust port requires an S-expression parser that:

- Achieves O(n) time complexity with no backtracking (NFR-004).
- Completes in <= 1 us/KiB on x86-64 (NFR-001).
- Supports a configurable fuel limit to prevent unbounded stack growth (REQ-043).
- Compiles to `wasm32-unknown-unknown` within a 256 KiB binary budget (NFR-010).
- Operates under `#![forbid(unsafe_code)]` and `#![no_std]` + `alloc` (NFR-020, CON-030).
- Produces rich, span-aware `ParseError` values for the pipeline (REQ-040).

The grammar is a small, unambiguous S-expression language (atoms + lists)
with six atom types and one list form.  It is deterministic context-free
(DCFL), requires no look-ahead beyond one byte, and has no operator
precedence or associativity concerns.

## 2  Options Considered

### 2.1  nom (v7)

| Dimension         | Assessment |
|-------------------|------------|
| **Maturity**      | Very mature; de-facto Rust parser-combinator library. Large ecosystem. |
| **Performance**   | Excellent zero-copy parsing.  Benchmarks consistently in the top tier. |
| **WASM compat**   | `no_std` + `alloc` supported.  Well-tested on WASM targets. |
| **Binary size**   | Moderate.  Combinator generics monomorphize aggressively; `opt-level=z` + LTO mitigates but typically adds 30-60 KiB to WASM output. |
| **Error quality** | `nom::error::VerboseError` provides reasonable context, but custom error types require boilerplate.  Span tracking requires manual threading. |
| **Fuel/depth**    | No built-in fuel mechanism; must be threaded through a custom state wrapper or external counter. |
| **Learning curve**| Moderate; combinator style is idiomatic but requires familiarity with nom's `IResult` conventions. |
| **Fit for grammar**| Overkill.  nom excels at complex binary/text formats; an S-expression grammar needs only ~10 combinators. |

### 2.2  winnow (v0.6)

| Dimension         | Assessment |
|-------------------|------------|
| **Maturity**      | Fork/successor of nom with improved ergonomics.  Actively maintained but smaller community. |
| **Performance**   | Comparable to nom; shares the same zero-copy core design. |
| **WASM compat**   | `no_std` + `alloc` supported. |
| **Binary size**   | Slightly smaller than nom due to reduced generic surface, but still carries combinator overhead. |
| **Error quality** | Better than nom out of the box; `ContextError` + `StrContext` provide labeled error chains. |
| **Fuel/depth**    | Same limitation as nom: no built-in fuel. |
| **Learning curve**| Lower than nom; API is more consistent.  But ecosystem/docs are thinner. |
| **Fit for grammar**| Same over-engineering concern as nom. |

### 2.3  Hand-Rolled Recursive Descent

| Dimension         | Assessment |
|-------------------|------------|
| **Maturity**      | Technique is mature; implementation is project-specific. |
| **Performance**   | Best possible.  Zero abstraction overhead, zero allocation during scanning, single-pass.  Can match or exceed nom for this grammar class. |
| **WASM compat**   | Trivially `no_std` + `alloc`.  No external dependencies. |
| **Binary size**   | Minimal.  A hand-rolled S-expression parser is typically 200-400 lines.  WASM contribution < 5 KiB. |
| **Error quality** | Full control.  Can produce span-annotated `ParseError` with exact byte offsets, expected-token hints, and fuel-exhaustion diagnostics. |
| **Fuel/depth**    | Trivial to integrate: pass a `&mut usize` fuel counter that decrements on each recursive call.  Directly satisfies REQ-043. |
| **Learning curve**| Lowest for this grammar size.  Any Rust developer can read and modify the parser. |
| **Fit for grammar**| Perfect.  The CBCL S-expression grammar is small, unambiguous, LL(1), and has no features that benefit from parser combinators (no alternation complexity, no precedence climbing, no error recovery strategies). |
| **Risk**          | No community maintenance; bugs are ours to fix.  However, the grammar is small enough that exhaustive testing (property-based + reference suite) provides high confidence. |

## 3  Decision

**Use a hand-rolled recursive-descent parser.**

## 4  Rationale

1. **Grammar simplicity dominates.**  The S-expression grammar has ~6 atom
   productions and one recursive list production.  A combinator library
   adds dependency weight, generic monomorphization cost, and API
   indirection for a grammar that fits in a single file.

2. **Fuel integration is first-class.**  REQ-043 requires a configurable
   fuel limit.  Threading fuel through nom/winnow combinators is awkward
   (requires custom `Stream` or state wrappers).  In a hand-rolled parser,
   fuel is a simple parameter that decrements on recursion.

3. **Binary size matters.**  NFR-010 sets a 256 KiB WASM budget for the
   entire crate.  Eliminating a parser library saves 30-60 KiB, leaving
   headroom for other features.

4. **Zero dependencies for the core.**  CON-030 mandates zero required
   dependencies beyond `alloc`.  A hand-rolled parser satisfies this
   trivially; nom/winnow would either violate CON-030 or require the
   parser to be feature-gated, fragmenting the core.

5. **Error quality.**  The pipeline (REQ-110) surfaces parse errors to
   callers via FFI/WASM/CLI.  Full control over `ParseError` structure
   allows span-annotated, user-friendly diagnostics without fighting a
   library's error model.

6. **Lean correspondence.**  The Lean 4 parser (`Parser.lean`) is itself a
   hand-rolled recursive-descent parser with fuel.  A hand-rolled Rust
   parser maps 1:1 to the Lean structure, simplifying cross-verification
   and traceability.

## 5  Trade-offs Accepted

| Downside                              | Mitigation |
|---------------------------------------|------------|
| No community maintenance of parser code. | Grammar is small and frozen; property-based tests + 180+ reference tests provide regression coverage (NFR-041, NFR-033). |
| Must implement escape handling, whitespace skipping, integer parsing manually. | These are straightforward in Rust; total implementation is ~300 lines. |
| Future grammar extensions require manual parser updates. | CBCL grammar extensibility is through dialects (template expansion), not parser-level syntax.  The core grammar is intentionally stable. |

## 6  Consequences

- The `parser` module will be a single file (`parser.rs`) with no external
  dependencies.
- `parse()` will accept `(input: &str, fuel: Option<usize>)` and return
  `Result<SExpr, ParseError>`.
- `ParseError` will carry byte offset, expected token, and fuel-exhaustion
  flag.
- The parser will be tested against all 180+ Guile reference tests and
  property-based fuzzing via `proptest`.
