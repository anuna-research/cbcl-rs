# ADR-003: WASM API Surface Design

| Field        | Value                                      |
|--------------|--------------------------------------------|
| **ID**       | ADR-003                                    |
| **Title**    | WASM API Surface Design                    |
| **Status**   | Accepted                                   |
| **Date**     | 2026-03-18                                 |
| **Context**  | SPEC-001 (CON-020–023, NFR-010–011)        |
| **Relates**  | ADR-001, ADR-002, PURITY-MAP-001           |

## 1  Context

The CBCL crate must compile to `wasm32-unknown-unknown` and serve two
distinct use cases:

1. **Pure WASM export** (no `wasm-bindgen`): a minimal `.wasm` module
   exposable via any WASM runtime (Wasmtime, browser `WebAssembly` API,
   embedded runtimes).  Used for IoT firmware and polyglot host processes.
2. **JS interop** (with `wasm-bindgen`): ergonomic JS-callable functions
   for browser embedding, Node.js tooling, and the existing CBCL web demo.

The constraints are:

- CON-020: Core WASM build SHALL NOT require `wasm-bindgen`.
- CON-021: A `wasm` feature flag SHALL enable `wasm-bindgen` bindings.
- CON-022: No `std::fs`, `std::net`, or OS-specific APIs in WASM builds.
- CON-023: WASM module SHALL export a linear-memory allocator for string
  buffer passing.
- NFR-010: `.wasm` binary <= 256 KiB (before gzip) at `opt-level=z` + LTO.
- NFR-011: `no_std` compatible data structures where feasible.

The existing Guile-based WASM build (`cbcl-wasm-package/`) uses the Hoot
compiler and a custom wrapper (`wasm-cbcl-wrapper.scm`).  The Rust port
should provide a cleaner, smaller, and faster WASM target.

## 2  Options Considered

### 2.1  wasm-bindgen Only

| Dimension         | Assessment |
|-------------------|------------|
| **Ergonomics**    | Excellent for JS consumers.  `#[wasm_bindgen]` generates TypeScript types and JS glue. |
| **Pure WASM**     | Violates CON-020.  `wasm-bindgen` injects JS glue code; the resulting `.wasm` requires a JS host. |
| **Binary size**   | Adds ~20-40 KiB of glue and serialization overhead. |
| **Non-JS hosts**  | Incompatible.  Wasmtime, WAMR, and embedded runtimes cannot load wasm-bindgen modules without JS shim. |

### 2.2  Pure WASM Only (no wasm-bindgen)

| Dimension         | Assessment |
|-------------------|------------|
| **Ergonomics**    | Poor for JS consumers.  Callers must manually manage linear memory, allocate/free buffers, and decode strings. |
| **Pure WASM**     | Fully compliant with CON-020. |
| **Binary size**   | Minimal. |
| **Non-JS hosts**  | Excellent.  Standard WASM interface works everywhere. |

### 2.3  Two-Tier: Pure WASM Core + wasm-bindgen Feature (Selected)

| Dimension         | Assessment |
|-------------------|------------|
| **Ergonomics**    | Best of both worlds.  Pure WASM for non-JS; ergonomic JS API when `wasm` feature is enabled. |
| **CON-020**       | Compliant.  Core builds without wasm-bindgen. |
| **CON-021**       | Compliant.  `wasm` feature enables bindings. |
| **Binary size**   | Core: ~50-80 KiB.  With wasm-bindgen: ~80-120 KiB.  Both well under 256 KiB budget. |
| **Maintenance**   | Two API surfaces to maintain, but the JS layer is a thin wrapper over the pure layer. |

## 3  Decision

**Two-tier WASM API: a pure WASM export layer (always available on WASM
targets) and a `wasm-bindgen` JS interop layer behind the `wasm` feature
flag.**

## 4  Design

### 4.1  Pure WASM Exports (no feature flag required)

These functions use C ABI conventions and operate on linear memory:

```rust
// Memory management
#[no_mangle] pub extern "C" fn cbcl_alloc(len: u32) -> u32;  // returns ptr
#[no_mangle] pub extern "C" fn cbcl_free(ptr: u32, len: u32);

// Core operations (input/output via linear memory pointers)
#[no_mangle] pub extern "C" fn cbcl_parse(ptr: u32, len: u32) -> u32;
#[no_mangle] pub extern "C" fn cbcl_serialize(ptr: u32, len: u32) -> u32;
#[no_mangle] pub extern "C" fn cbcl_run_pipeline(ptr: u32, len: u32) -> u32;
#[no_mangle] pub extern "C" fn cbcl_verify_dialect(ptr: u32, len: u32) -> u32;

// Result inspection
#[no_mangle] pub extern "C" fn cbcl_result_is_ok(ptr: u32) -> u32;
#[no_mangle] pub extern "C" fn cbcl_result_error_msg(ptr: u32) -> u32;
#[no_mangle] pub extern "C" fn cbcl_free_result(ptr: u32);
```

**Protocol**: Host writes UTF-8 input into allocated buffer, calls
function with `(ptr, len)`, reads result from returned pointer, frees
both buffers.  Result pointers encode a length-prefixed format:
`[u32 status][u32 len][u8; len]`.

### 4.2  wasm-bindgen JS Interop (behind `wasm` feature)

```rust
#[cfg(feature = "wasm")]
mod wasm_bindings {
    use wasm_bindgen::prelude::*;

    #[wasm_bindgen]
    pub fn parse(input: &str) -> Result<JsValue, JsValue>;

    #[wasm_bindgen]
    pub fn run_pipeline(input: &str) -> Result<JsValue, JsValue>;

    #[wasm_bindgen]
    pub fn serialize(sexpr_json: &str) -> Result<String, JsValue>;

    #[wasm_bindgen]
    pub fn verify_dialect(dialect_str: &str) -> Result<JsValue, JsValue>;
}
```

JS callers get native string passing, structured error objects, and
auto-generated TypeScript definitions via `wasm-bindgen`.

### 4.3  Serialization Format at the WASM Boundary

| Layer              | Input                    | Output                    |
|--------------------|--------------------------|---------------------------|
| **Pure WASM**      | UTF-8 S-expression text  | Length-prefixed result: status byte + UTF-8 S-expression or error string |
| **wasm-bindgen**   | JS `string`              | `JsValue` (structured object via `serde-wasm-bindgen`) |

The pure layer keeps serialization simple (text in, text out).  The JS
layer uses `serde-wasm-bindgen` (gated behind `wasm` + `serde` features)
to pass structured objects without manual JSON encoding.

### 4.4  Module Structure

```
src/
  wasm_pure.rs      # Pure WASM exports, always compiled on wasm32 target
  wasm_bindgen.rs   # JS bindings, compiled only with `wasm` feature
```

Both modules import from the pure core and are classified as effectful
shell in PURITY-MAP-001.

## 5  Rationale

1. **CON-020 requires a non-wasm-bindgen path.**  Embedded and non-JS
   WASM runtimes (Wasmtime, WAMR, micro-wasm) are first-class deployment
   targets for CBCL agents on IoT devices.  Mandating wasm-bindgen would
   lock out these environments.

2. **The JS ecosystem expects ergonomic APIs.**  Forcing browser
   developers to manually manage linear memory pointers is impractical.
   The `wasm` feature flag provides the expected DX without bloating the
   core.

3. **Binary budget is generous.**  At an estimated 50-80 KiB for the pure
   WASM build, there is ample headroom within the 256 KiB limit.  Even
   with wasm-bindgen, the total stays well under budget.

4. **Linear-memory allocator is simple.**  CON-023 requires exporting an
   allocator.  A bump allocator (~50 lines) or `dlmalloc` (via
   `wee_alloc` successor) provides this with minimal size overhead.

5. **Existing WASM demo validates approach.**  The Guile WASM build
   (`cbcl-wasm-package/`) demonstrates the use case.  The Rust port will
   provide a drop-in replacement with better performance and smaller size.

## 6  Trade-offs Accepted

| Downside                              | Mitigation |
|---------------------------------------|------------|
| Two WASM API surfaces to maintain.    | The wasm-bindgen layer is a thin adapter (~100 lines) over the pure exports.  Changes propagate from the core, not from the WASM layer. |
| Pure WASM API requires callers to manage memory. | Provide a reference JS wrapper (non-wasm-bindgen) in the docs/examples showing the alloc/call/free pattern.  This is standard practice for WASM libraries. |
| `serde-wasm-bindgen` adds a transitive dependency. | Gated behind `wasm` + `serde` features; does not affect core or pure WASM builds. |
| Bump allocator may fragment under long-lived sessions. | CBCL operations are request/response (parse, pipeline, verify).  A reset-on-each-call pattern avoids fragmentation.  Can upgrade to `dlmalloc` if needed. |

## 7  Consequences

- The `wasm_pure` module will be compiled on all `wasm32` targets
  automatically via `#[cfg(target_arch = "wasm32")]`.
- The `wasm_bindgen` module will be compiled only when both `wasm32`
  target and `wasm` feature are active.
- `Cargo.toml` will declare:
  ```toml
  [features]
  wasm = ["dep:wasm-bindgen", "dep:serde-wasm-bindgen", "serde"]
  ```
- CI will test both build paths: `cargo build --target wasm32-unknown-unknown`
  (pure) and `wasm-pack build --features wasm` (JS interop).
- Binary size will be tracked in CI with a 256 KiB gate.
