# Changelog

Notable changes to CBCL are recorded here. Released versions follow repository
tags; changes after the latest tag remain under **Unreleased**. The project is
in pre-1.0 development, and compatibility changes are called out explicitly.

## Unreleased

## [0.2.0] — 2026-11-13

### Added

- Bounded public Multikey payload recognition for Ed25519, X25519 and compressed
  P-256/P-384 keys, explicit Ed25519 identity conversion, and CLI inspection.
- Long-lived language-edition design and guidance for offline evidence, identity,
  resource portability, and historical trust boundaries.
- Finite binary64 float and exact arbitrary-precision decimal atoms, alongside
  signed 64-bit integers, with canonical serialization and binding support.
- Named declarative flat contracts: numeric ranges, RFC 9485 I-Regexp matching
  with Unicode 16.0.0 properties, scalar enumerations, string/list length bounds,
  intersections, and alternatives. Diagnostics identify failed constraints and
  nested field paths; resource exhaustion is reported separately.
- The Causal Lattice Observation Kernel (CLOK): lattice-based state interpretation,
  explicit snapshot, threshold, and causal-freeze reads, finite authored lattices,
  context observations, and composed native threshold conditions.
- The `cbcl-checkpoint` companion crate for member-certified cached state opening
  and continuation across all 16 native state rule heads.
- Lean proofs for typed state-kernel correctness, conditional strong eventual
  consistency, checkpoint continuation, and flat contract semantics, plus
  differential conformance and upstream I-Regexp fixtures. Proof boundaries are
  documented in the [Lean guide](lean-cbcl/README.md).
- Protocol-model, state-language, bounded-counter, and admission-model
  documentation and diagrams.
- Operational quasi-determinism proofs for concurrent threshold programs with
  partial delivery: finished runs agree on results and joint evidence, or both
  hold conflicting evidence.
- Role-model proofs of enabledness, deadlock freedom, and fair-run completion
  under realizable-work assumptions; enactability checkers and conflict
  attribution under a single-role choice condition. An executable Lean oracle
  compares protocol construction, acyclicity, and causal verification with Rust.
- Shared canonical message-audience accessors for WebAssembly, JavaScript/TypeScript,
  and Erlang/BEAM, including wrapper and envelope routing and a lax accessor for
  custom host control verbs.

### Changed

- **Migration required:** wire content addresses now use canonical SHA2-256
  multihashes in lowercase multibase base16 (`f1220…`). Legacy bare-hex addresses
  are rejected; persisted references and host integrations must migrate.
- **Migration required:** message keyword fields and recursive dialect shapes are
  canonicalized at public boundaries. Equivalent field orders now share canonical
  bytes and addresses; affected dialect self-addresses and signatures must be
  regenerated. See [SPEC-042](specs/SPEC-042-boundary-canonicalisation.md).
- Replaced the obsolete root Guile/Hoot WASM guide with a link to the Rust
  WebAssembly bindings documentation.
- **Migration required:** `number` now accepts integers, floats, and decimals.
  Use `integer` for declarations that must retain integer-only validation.
- **Migration required:** optional shape defaults use explicit `(default value)`
  syntax.
- **Migration required:** signing form 6 binds the `cbcl-flat-v1-unicode16`
  profile and local type definitions. Existing dialect signatures and
  self-addresses require explicit reissue. See
  [SPEC-040](specs/SPEC-040-numeric-and-refinement-types.md).
- **Migration required:** state role roots use sealed-root addresses; historical
  fixtures and executable coin examples have been migrated. See
  [SPEC-038](specs/SPEC-038-lvar-state-kernel.md).
- Documented and added regression coverage for variadic causal protocol chains:
  `(then begin one two three)` expands to adjacent causal edges.

### Fixed

- Resource depth and expansion arithmetic now refuses overflow consistently in
  debug and release builds.
- Message-audience accessors reject malformed wrapper bodies and trailing proof
  fields instead of routing partially parsed frames. The frame-room corpus records
  the stricter parser results separately from historical hub answers.
- Aligned verdict composition with strong Kleene three-valued logic.
- Restored the `no_std` build of `blame.rs` and added it to `make check`.

## [0.1.1] — 2026-11-04

First tagged release in this repository. This entry summarizes the capabilities
present at the tag rather than changes from an earlier tagged version.

### Added

- Rust parser and deterministic `no_std + alloc` core for extensible CBCL
  dialects, causal protocol verification, and content-addressed message stores.
- Role-aware multiparty protocols, endpoint projection, role-local verification,
  and evidence for selective disclosure and equivocation detection.
- State rules and consensus-free bounded counters with transferable escrow
  rights, plus `fold` and `intend` interfaces.
- CLI, WebAssembly, JavaScript/TypeScript, C FFI, and Erlang/BEAM interfaces.
- Lean formalization, conformance vectors, examples, and verification tooling.
- A release script that checks Rust and Lean, updates the workspace version,
  and pushes a release commit and annotated tag. It does not publish packages
  or binaries.

[Unreleased]: https://git.anuna.io/anuna-research/cbcl-rs/compare/v0.2.0...main
[0.2.0]: https://git.anuna.io/anuna-research/cbcl-rs/compare/v0.1.1...v0.2.0
[0.1.1]: https://git.anuna.io/anuna-research/cbcl-rs/releases/tag/v0.1.1
