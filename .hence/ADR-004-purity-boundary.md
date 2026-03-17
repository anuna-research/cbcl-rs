# ADR-004: Purity Boundary

| Field        | Value                                      |
|--------------|--------------------------------------------|
| **ID**       | ADR-004                                    |
| **Title**    | Purity Boundary: Pure Core vs Effectful Shell |
| **Status**   | Accepted                                   |
| **Date**     | 2026-03-18                                 |
| **Context**  | SPEC-001 (all REQs), NFR-020–023, CON-030  |
| **Relates**  | PURITY-MAP-001, ADR-001, ADR-002, ADR-003  |

## 1  Context

The CBCL crate must simultaneously serve as:

- A formally-verified language runtime whose semantics mirror Lean 4 proofs.
- A `no_std` library embeddable in WASM, IoT, and native contexts.
- A network-capable agent runtime with gossip, I/O, and CLI interfaces.

These goals conflict.  Formal correspondence demands deterministic,
effect-free code.  Agent runtime requires network I/O, mutable state,
and platform APIs.  The architecture must cleanly separate these concerns
so that:

1. The verified core is testable, portable, and auditable in isolation.
2. The effectful shell can evolve (new transports, new UIs) without
   touching verified code.
3. `#![forbid(unsafe_code)]` holds everywhere except the FFI boundary.
4. `no_std` + `alloc` is sufficient for the core (NFR-011, CON-030).

## 2  Options Considered

### 2.1  Flat Module Structure (no boundary)

| Dimension         | Assessment |
|-------------------|------------|
| **Simplicity**    | Simplest initial structure.  All modules at one level. |
| **Purity**        | No enforcement.  I/O can leak into parser or verifier modules over time. |
| **Testability**   | Difficult to test core logic without mocking I/O. |
| **WASM/no_std**   | Entire crate must be `no_std`-compatible, or nothing is. |
| **Lean correspondence** | Unclear which Rust code corresponds to which Lean proof. |
| **Risk**          | High.  Effect leakage is the #1 cause of "works on my machine" bugs in language runtimes. |

### 2.2  Separate Crates (workspace split)

| Dimension         | Assessment |
|-------------------|------------|
| **Enforcement**   | Strongest.  Cargo enforces dependency direction at the crate level. |
| **Overhead**      | High.  Multiple `Cargo.toml` files, cross-crate type visibility issues, version coordination. |
| **Ergonomics**    | Poor for a crate this size.  13 pure modules + 6 shell modules is manageable in one crate. |
| **Lean correspondence** | Good; the `cbcl-core` crate maps 1:1 to Lean modules. |
| **Binary size**   | Slightly worse due to cross-crate LTO limitations (though `lto = true` mitigates). |

### 2.3  Single Crate with Module-Level Boundary + CI Enforcement (Selected)

| Dimension         | Assessment |
|-------------------|------------|
| **Enforcement**   | Strong.  `#![forbid(unsafe_code)]` per module + CI lint checking import direction. |
| **Overhead**      | Low.  One `Cargo.toml`, one crate, standard module tree. |
| **Ergonomics**    | Best.  All types are in one namespace; no cross-crate import gymnastics. |
| **Lean correspondence** | Direct.  Each pure module maps to a Lean file. |
| **Binary size**   | Best.  Single-crate LTO is fully effective. |
| **Risk**          | Moderate.  Relies on lint + convention rather than Cargo-level enforcement.  Mitigated by CI. |

## 3  Decision

**Single crate with a documented module-level purity boundary, enforced
by `#![forbid(unsafe_code)]`, `no_std` feature gating, and a CI lint
that verifies the dependency rule.**

The boundary is fully specified in PURITY-MAP-001.  This ADR records the
architectural decision and trade-off analysis behind that boundary.

## 4  Boundary Definition

### 4.1  Pure Core (13 modules)

`sexpr`, `message`, `dialect`, `parser`, `serializer`, `r1`, `r2`, `r3`,
`r4`, `template`, `pipeline`, `pattern`, `msg_tag`.

**Properties**: deterministic, `#![forbid(unsafe_code)]`, `no_std` +
`alloc` only, no I/O, no RNG, no platform APIs.  Every function is
either total or fuel-bounded.

### 4.2  Effectful Shell (6 modules)

`agent`, `gossip`, `ffi`, `wasm`, `cli`, `prelude`.

**Properties**: may use `std`, `unsafe` (ffi only), mutable state,
network I/O, RNG.

### 4.3  Dependency Rule

**The shell imports the core.  The core never imports the shell.**

```
Shell ──imports──► Core
Core ──never imports──► Shell
```

### 4.4  Boundary Contracts

Four types cross the boundary (all defined in core, consumed/produced by
shell):

| Type            | Direction       | Purpose |
|-----------------|-----------------|---------|
| `SExpr`         | core <-> shell  | Data representation at every boundary. |
| `Message`       | core -> shell   | Pipeline output consumed by agent/gossip. |
| `Dialect`       | core <-> shell  | Parsed/verified in core; installed by agent; propagated by gossip. |
| `PipelineResult`| core -> shell   | Pipeline output translated by FFI/WASM/CLI. |

## 5  Rationale

1. **Lean correspondence is the primary driver.**  The Lean 4 proof
   library (`lean-cbcl/`) verifies properties of the pure core: parser
   correctness, R1 soundness, R2 termination, R3 preservation, DCFL
   determinism.  If pure Rust modules map 1:1 to Lean modules, the
   verified properties transfer by structural correspondence.  Mixing
   effects into core modules would break this mapping.

2. **DCFL preservation requires determinism.**  NFR-030 requires that
   `msg_tag` is deterministic.  NFR-031 requires that dialect installation
   preserves decidability.  These properties hold only if the core is
   effect-free.  Non-determinism (I/O, RNG) in the parser or tag
   dispatcher would invalidate the DCFL guarantee.

3. **WASM and `no_std` are natural consequences.**  If the core has no
   I/O and depends only on `alloc`, it compiles to `wasm32-unknown-unknown`
   and bare-metal targets without conditional compilation.  The boundary
   is not just an architectural choice — it's a compilation requirement.

4. **Single crate over workspace.**  With 19 modules total, a workspace
   split adds build complexity without proportional safety gain.
   `#![forbid(unsafe_code)]` + CI lints provide equivalent enforcement
   with less overhead.  If the crate grows significantly in the future,
   a workspace split remains possible as a non-breaking refactor.

5. **`Signer` trait demonstrates the pattern.**  R4 (`verify_r4`)
   needs cryptographic operations, which are inherently effectful.  The
   trait-object design (`&dyn Signer`) keeps `verify_r4` as a pure
   predicate while deferring actual crypto to shell-provided
   implementations.  This pattern (pure trait definition, effectful
   impl) is the general solution for any future boundary crossings.

## 6  Trade-offs Accepted

| Downside                              | Mitigation |
|---------------------------------------|------------|
| Module-level enforcement is weaker than crate-level. | CI lint checks `use crate::{agent,gossip,ffi,wasm,cli}` in core modules.  `#![forbid(unsafe_code)]` catches unsafe leakage at compile time. |
| `agent` module is in the shell despite being mostly data manipulation. | `install_dialect` mutates state and gossip reception triggers side effects.  Pure operations on agent data (querying dialects) could be factored into a core helper, but the current classification keeps the boundary simple. |
| Adding a new core module requires updating the CI lint allowlist. | New core modules are rare (grammar is stable).  Updating a lint is trivial compared to the cost of a missed boundary violation. |
| The `prelude` module is classified as shell despite having no effects. | It re-exports from both core and shell.  Classifying it as shell is conservative — it cannot accidentally introduce effects into core. |

## 7  Enforcement Mechanisms

| Mechanism                        | What It Catches |
|----------------------------------|-----------------|
| `#![forbid(unsafe_code)]` in each core module | Any `unsafe` block in core code. |
| `#[cfg(feature = "std")]` on shell modules | Core compiling on `no_std` targets without shell. |
| CI lint: grep for shell imports in core | Accidental `use crate::agent` in a core module. |
| `cargo build --target wasm32-unknown-unknown` in CI | Any `std::fs`/`std::net` leaking into core. |
| Code review convention | New modules must be classified and documented in PURITY-MAP-001. |

## 8  Consequences

- All 13 core modules will carry `#![forbid(unsafe_code)]` as the first
  line.
- The crate's `lib.rs` will conditionally compile shell modules behind
  feature flags (`std`, `ffi`, `wasm`).
- PURITY-MAP-001 is the authoritative document for module classification
  and will be updated when modules are added or reclassified.
- The `Signer` trait pattern will be used for any future boundary
  crossings requiring effectful capabilities in a pure context.
- CI will include a WASM build and an import-direction lint as mandatory
  checks.
