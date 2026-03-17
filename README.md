# CBCL

Canonical implementation of CBCL (Conversational Business Communication Language) — a self-extensible, formally-verified agent communication language defined in [RFC 9804](https://datatracker.ietf.org/doc/draft-cbcl/).

Rust implementation with Lean 4 formal proofs. Algorithms in Rust match those verified in Lean; correctness validated via differential testing.

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
