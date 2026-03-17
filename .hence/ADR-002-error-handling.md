# ADR-002: Error Handling Strategy

| Field        | Value                                      |
|--------------|--------------------------------------------|
| **ID**       | ADR-002                                    |
| **Title**    | Error Handling Strategy                    |
| **Status**   | Accepted                                   |
| **Date**     | 2026-03-18                                 |
| **Context**  | SPEC-001 (CON-003, CON-030, NFR-010–011)   |
| **Relates**  | ADR-001, PURITY-MAP-001                    |

## 1  Context

The CBCL crate needs an error handling strategy that satisfies competing
constraints:

- **CON-003**: Error types SHALL use `thiserror` and implement
  `std::error::Error` (or a `no_std`-compatible equivalent).
- **CON-030**: Zero required dependencies beyond `alloc`.
- **NFR-010/011**: WASM binary <= 256 KiB; `no_std` compatible.
- **Pure core guarantee**: Errors in the pure core (parser, verifiers,
  pipeline) must be deterministic, structured, and carry enough context
  for the effectful shell to produce user-facing diagnostics.
- **FFI/WASM boundary**: Errors must be translatable to C error codes /
  JS-friendly strings without losing semantic information.

The tension is between CON-003 (which names `thiserror`) and CON-030
(which mandates zero required dependencies).  These can be reconciled
if `thiserror` is optional.

## 2  Options Considered

### 2.1  thiserror (required dependency)

| Dimension         | Assessment |
|-------------------|------------|
| **Ergonomics**    | Excellent.  Derive macros generate `Display`, `Error`, and `From` impls. |
| **Binary size**   | Small runtime footprint (proc-macro at compile time only). |
| **no_std**        | `thiserror` v2.x supports `no_std`.  Requires `core::error::Error` (stabilized in Rust 1.81). |
| **CON-030 compliance** | Violates "zero required dependencies beyond `alloc`" if used as a required dep. |
| **WASM**          | Compatible; no issues. |

### 2.2  anyhow (required dependency)

| Dimension         | Assessment |
|-------------------|------------|
| **Ergonomics**    | Excellent for application code; `anyhow::Error` erases concrete types. |
| **Structured errors** | Poor.  Type erasure prevents pattern matching on error variants, which the pipeline and FFI need. |
| **no_std**        | Supported since anyhow 1.0.79. |
| **CON-030 compliance** | Violates zero-dependency constraint. |
| **Fit**           | Wrong tool.  `anyhow` is for applications; CBCL is a library where callers need typed errors. |

### 2.3  Custom error enums (no dependencies) + thiserror behind feature flag

| Dimension         | Assessment |
|-------------------|------------|
| **Ergonomics**    | Moderate.  Manual `Display` and `Error` impls, but the error surface is small (3-4 enum types). |
| **Structured errors** | Best.  Each pipeline stage gets a dedicated error enum with domain-specific variants. |
| **Binary size**   | Minimal.  No proc-macro overhead; error types are plain enums. |
| **no_std**        | Trivially compatible.  `core::fmt::Display` is all that's needed for the base case. |
| **CON-030 compliance** | Fully compliant: zero required deps.  `thiserror` available behind `thiserror` feature flag for downstream convenience. |
| **FFI/WASM**      | Error enums map cleanly to C error codes and JS strings. |

## 3  Decision

**Use custom error enums with no required dependencies.  Provide
`thiserror` derive macros behind an optional `thiserror` feature flag.**

## 4  Rationale

1. **CON-030 is non-negotiable for the core.**  The spec explicitly
   requires zero required dependencies beyond `alloc`.  `thiserror` and
   `anyhow` are both external crates.  Making error handling work without
   them satisfies the constraint cleanly.

2. **The error surface is small.**  CBCL has three primary error types:
   - `ParseError` — produced by `parse()`, `parse_message()`, `parse_dialect()`.
   - `ValidationError` — produced by R1/R2/R3/R4 verification.
   - `PipelineError` — the union, surfaced by `run_pipeline()`.

   Three enums with a handful of variants each do not justify a
   proc-macro dependency.

3. **CON-003 is satisfied conditionally.**  The spec says error types
   "SHALL use `thiserror`".  By providing a `thiserror` feature flag that
   switches manual impls to derive macros, downstream users who want
   `thiserror` integration get it, while the core remains dependency-free.
   The spirit of CON-003 (structured, `Error`-implementing types) is
   preserved in both modes.

4. **`anyhow` is wrong for a library.**  The pipeline, FFI, and WASM
   boundaries all need to match on error variants.  Type-erased errors
   would force string parsing at the boundary, defeating the purpose of
   structured error types.

5. **`core::error::Error` stabilization.**  Since Rust 1.81,
   `core::error::Error` is available in `no_std`.  Custom error enums can
   implement this trait directly, satisfying CON-003's `Error` impl
   requirement without `std`.

## 5  Design

### 5.1  Error Types

```rust
/// Parser errors with source location.
pub enum ParseError {
    UnexpectedChar { offset: usize, found: char, expected: &'static str },
    UnexpectedEof { offset: usize, expected: &'static str },
    FuelExhausted { offset: usize },
    InvalidEscape { offset: usize, sequence: char },
    IntegerOverflow { offset: usize },
}

/// Verification and semantic errors.
pub enum ValidationError {
    R1SelfReference { performative: String },
    R2ResourceBoundsInvalid { field: &'static str, value: u32 },
    R2FuelExhausted,
    R3CoreOverride { performative: String },
    R4SignatureInvalid,
    MalformedMessage { reason: String },
    MalformedDialect { reason: String },
}

/// Top-level pipeline result (REQ-111).
pub enum PipelineResult {
    Success(Message),
    ParseError(ParseError),
    ValidationError(ValidationError),
}
```

### 5.2  Feature Flag Behavior

```toml
[features]
thiserror = ["dep:thiserror"]
```

- **Without `thiserror` feature**: `Display` and `Error` impls are
  hand-written.  Zero dependencies.
- **With `thiserror` feature**: `#[derive(thiserror::Error)]` replaces
  manual impls.  Behavior is identical.

### 5.3  FFI / WASM Translation

| Rust Error               | C FFI                     | WASM/JS                    |
|--------------------------|---------------------------|----------------------------|
| `ParseError::*`          | Error code + offset field | `{ kind: "parse", offset, message }` |
| `ValidationError::*`     | Error code + reason string| `{ kind: "validation", rule, message }` |
| `PipelineResult::Success`| Status 0 + result pointer | Resolved promise with `Message` |

## 6  Trade-offs Accepted

| Downside                              | Mitigation |
|---------------------------------------|------------|
| Manual `Display`/`Error` impls for ~15 variants. | One-time cost; errors are stable once defined.  A `#[cfg(feature = "thiserror")]` conditional avoids duplication. |
| Downstream users without the feature flag lose `thiserror`'s `#[from]` and `#[source]` conveniences. | Provide explicit `From` impls for the common conversions (e.g., `ParseError` into `PipelineResult`). |
| Slightly more boilerplate than a pure `thiserror` approach. | The total error surface is ~40 lines of manual impls.  Acceptable for a library crate. |

## 7  Consequences

- `ParseError`, `ValidationError`, and `PipelineResult` will be defined
  in their respective modules with manual `Display` + `Error` impls.
- A `thiserror` feature flag will be documented in the crate's
  `Cargo.toml` and README.
- The `ffi` module will map error enums to integer codes.
- The `wasm` module will serialize errors to JSON-like JS objects.
- No dependency on `anyhow` anywhere in the crate.
