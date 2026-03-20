# CBCL

Rust implementation of **CBCL** (Common Business Communication Language) — a self-extensible, formally verified agent communication language.

## The Problem

Language-theoretic security (LangSec) teaches that the computational complexity class of an input language determines the *category* of bugs its parsers can exhibit. Regular languages admit only finite-state bugs; context-free languages add stack-related bugs; Turing-complete inputs make parser correctness undecidable.

Agent communication protocols have moved *up* this hierarchy without acknowledging the security consequences:

| Protocol | Input Complexity | Extensible? | Verifiable? | Weird Machines? |
|----------|-----------------|-------------|-------------|-----------------|
| KQML | CFG | No | Partially | Stack-based |
| FIPA-ACL | CFG | No | Partially | Stack-based |
| MCP | Unrestricted JSON | Yes | No | Turing-complete |
| LLM Agents | Natural language | Yes | No | Turing-complete |
| **CBCL** | **DCFL** | **Yes** | **Yes** | **None (by construction)** |

Early ACLs (KQML, FIPA-ACL) had fixed vocabularies that couldn't evolve without out-of-band standardisation. The modern alternative — natural language and unrestricted JSON (MCP, LLM agent frameworks) — provides unlimited extensibility but creates an input language whose computational complexity is effectively unbounded. Determining whether an arbitrary message will cause harmful behaviour requires solving undecidable problems.

## The Solution

CBCL occupies the "Goldilocks zone" between these extremes: a minimal core vocabulary (8 performatives) with a formal mechanism for agents to define, exchange, and adopt new domain-specific vocabularies ("dialects") at runtime — without centralized coordination and without escaping the DCFL complexity class.

The key insight is *homoiconic self-extension*: dialect definitions are themselves valid CBCL messages in S-expression syntax, parsed and verified by the same deterministic pushdown automaton used for ordinary communication. Three safety constraints — verified in Lean 4 and enforced at runtime — ensure this self-extension is provably safe:

- **R1 (No Recursion):** Dialect templates are purely declarative pattern-template substitutions. No cyclic dependencies, iteration, or reflection.
- **R2 (Resource Bounds):** Every dialect declares static resource limits (depth, expansion size, verification time) enforced at both definition time and runtime.
- **R3 (Core Preservation):** The eight core performatives (`tell`, `ask`, `reply`, `hello`, `bye`, `ok`, `error`, `cancel`) cannot be redefined by any dialect.

**Why DCFL?** It is the minimal complexity class that supports nested structure (agent messages have envelopes wrapping messages, dialects scoping inner messages) while guaranteeing *parser equivalence*: every conformant implementation produces exactly one parse tree for every input. This eliminates parser differential attacks by construction. Regular languages are insufficient for nesting; general CFG introduces ambiguity; anything above DCFL makes validity checking undecidable.

Named after McCarthy's 1982 proposal for a "Common Business Communication Language" that would be "open ended so that as programs improve, programs that can at first only order by stock numbers can later be programmed to inquire about specifications and prices."

Forthcoming paper for the 2026 LangSec workshop with full theoretical framework and proofs, and the initial [Scheme implementation](https://github.com/anuna-research/cbcl) for the original prototype.

## Features

- S-expression parser with O(n) time complexity and fuel-bounded recursion
- Full CBCL message grammar: core performatives, dialects, templates
- Safety constraints R1 (no recursion), R2 (resource bounds), R3 (core preservation), R4 (integrity)
- Deterministic message tagging preserving DCFL properties
- `no_std` + `alloc` compatible pure core
- WASM target (`wasm32-unknown-unknown`) via `wasm-bindgen`
- C FFI via `cbindgen`
- CLI tool for parsing, verification, agent REPL, and gossip simulation

## Workspace

| Crate | Zone | Description |
|-------|------|-------------|
| `cbcl-core` | Pure | Types, constraints (R1-R4), template expansion, gossip, evaluator |
| `cbcl-parser` | Pure | S-expression and message parser, pipeline |
| `cbcl-cli` | Shell | Command-line interface |
| `cbcl-wasm` | Shell | WebAssembly bindings |
| `cbcl-ffi` | Shell | C FFI bindings |
| `lean-cbcl` | Proofs | Lean 4 formal verification of core algorithms |

## Quick Start

```bash
# Run tests (453 tests)
cargo test --workspace

# Parse a message
cargo run -p cbcl-cli -- parse '(tell agent-b "hello")'

# Verify a dialect
cargo run -p cbcl-cli -- verify dialect.scm

# Run benchmarks
cargo bench --workspace

# Build for WASM
cargo build --target wasm32-unknown-unknown -p cbcl-wasm
```

## Formal Verification

The `lean-cbcl/` directory contains Lean 4 proofs that verify the core algorithms. Each Rust module in `cbcl-core` has a corresponding Lean file:

| Rust module | Lean file | What is proved |
|---|---|---|
| `sexpr.rs` | `SExpr.lean` | S-expression type well-formedness |
| `parser.rs` | `Parser.lean`, `DetParser.lean` | Parser is deterministic (DCFL class) |
| `r1.rs` | `R1NoRecursion.lean` | Cycle detection soundness |
| `r2.rs` | `R2ResourceBounds.lean` | Resource bounds termination |
| `r3.rs` | `R3CorePreservation.lean` | Core performative immutability |
| `template.rs` | `TemplateExpansion.lean` | Expansion terminates within bounds |
| `msg_tag.rs` | `DeterministicUnion.lean` | DCFL closure under dialect union |

Differential tests (`crates/cbcl-parser/tests/differential.rs`) run both implementations on the same test vectors and assert identical accept/reject verdicts.

## Architecture

Strict **purity boundary**: the core crates are deterministic, `no_std + alloc`, `#![forbid(unsafe_code)]`. Effectful code (I/O, CLI, WASM bindings, FFI) lives in shell crates that import the core — never the reverse. See `.hence/ADR-004-purity-boundary.md` and `.hence/PURITY-MAP.md`.

## Testing

- **Unit tests**: 263 in cbcl-core, 92 in cbcl-parser
- **Property tests**: 37 proptest suites covering 8 USDD verification properties
- **Differential tests**: 21 integration tests comparing Rust vs Lean on 156 test vectors
- **Fuzz targets**: libFuzzer harnesses for parser trust boundary
- **Mutation testing**: cargo-mutants config targeting 7 critical-path modules (90% kill rate threshold)
- **Benchmarks**: 44 Criterion benchmarks for parser, constraints, template expansion, gossip

## License

Apache-2.0. See [LICENSE](LICENSE).
