# cbcl-rs

Rust implementation of [CBCL](https://github.com/hyperifyio/cbcl) (Communication-Based Communication Language) — a self-extensible, formally-verified agent communication language.

## Status

**Early development.** Core types and parser are scaffolded; pipeline stages are being implemented.

## Features

- S-expression parser with O(n) time complexity and fuel-bounded recursion
- Full CBCL message grammar: core performatives, dialects, templates
- Safety constraints R1 (no recursion), R2 (resource bounds), R3 (core preservation), R4 (integrity)
- Deterministic message tagging preserving DCFL properties
- `no_std` + `alloc` compatible pure core
- WASM target (`wasm32-unknown-unknown`) with optional `wasm-bindgen` JS bindings
- CLI tool for parsing and pipeline execution

## Workspace Crates

| Crate | Zone | Description |
|-------|------|-------------|
| `cbcl-core` | Pure | Types, verification, serialization |
| `cbcl-parser` | Pure | S-expression parser and pipeline |
| `cbcl-cli` | Shell | Command-line interface |
| `cbcl-wasm` | Shell | WebAssembly bindings |

## Quick Start

```bash
# Run tests
cargo test --workspace

# Parse an S-expression
cargo run -p cbcl-cli -- parse '(tell "hello")'

# Build for WASM
cargo build --target wasm32-unknown-unknown -p cbcl-wasm
```

## Architecture

The codebase enforces a strict **purity boundary** between the deterministic core and the effectful shell. Core crates have zero required dependencies beyond `alloc`, compile to `no_std`, and carry `#![forbid(unsafe_code)]`. See [CLAUDE.md](CLAUDE.md) for details.

## Formal Verification

The Rust implementation mirrors the Lean 4 proof library in `lean-cbcl/`. Each pure core module corresponds to a Lean file, enabling cross-verification of safety properties:

- **R1**: No recursive performative definitions
- **R2**: Resource-bounded evaluation (fuel + depth + expansion limits)
- **R3**: Core performative names cannot be overridden
- **R4**: Cryptographic integrity of dialect signatures

## License

Apache-2.0. See [LICENSE](LICENSE).
