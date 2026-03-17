# Purity Boundary Map

| Field        | Value                                      |
|--------------|--------------------------------------------|
| **ID**       | PURITY-MAP-001                             |
| **Title**    | CBCL Rust Port — Purity Boundary Map       |
| **Status**   | Draft                                      |
| **Date**     | 2026-03-18                                 |
| **Derived**  | SPEC-001, lean-cbcl/, AGENT.md             |

## 1  Overview

This document partitions every module in the CBCL Rust crate into exactly
one of two zones:

- **Pure core** — deterministic, `#![forbid(unsafe_code)]`, no I/O, no
  allocation beyond `alloc`, no platform-specific code.  Every function is
  a total or fuel-bounded map from inputs to outputs.
- **Effectful shell** — may perform I/O, hold mutable external state,
  call `unsafe` (FFI only), or depend on platform APIs.

A strict **dependency rule** governs the boundary: the shell imports the
core; the core never imports the shell.  Four **boundary contract types**
cross the frontier.

---

## 2  Pure Core

All modules below are `#![forbid(unsafe_code)]`, `no_std`-compatible
(with `alloc`), and contain zero side effects.

| Module        | REQ / NFR          | Key Types & Functions | Purity Argument |
|---------------|--------------------|-----------------------|-----------------|
| `sexpr`       | REQ-001–005        | `Atom`, `SExpr`, `size()`, `byte_size()`, `depth()`, `is_symbol()` | Algebraic data type + structural recursion only. Mirrors `SExpr.lean`. |
| `message`     | REQ-010–014        | `CorePerformative`, `Performative`, `MessageType`, `Message`, `CORE_PERFORMATIVE_NAMES`, `is_core_performative_name()` | Enum/struct definitions + constant array. No allocation beyond construction. |
| `dialect`     | REQ-020–025        | `ResourceBounds`, `PerformativeDef`, `Dialect`, `BASE_DIALECT`, `is_valid()`, `defines_performative()`, `find_performative()` | Structural queries over immutable data. Mirrors `Dialect.lean`. |
| `parser`      | REQ-040–045, NFR-001/004 | `parse()`, `parse_message()`, `parse_dialect()`, `ParseError` | Recursive-descent with fuel bound. O(n), no backtracking, no I/O. Mirrors `Parser.lean`, `MessageParser.lean`, `DialectParser.lean`. |
| `serializer`  | REQ-050            | `serialize()` | Deterministic SExpr → String. Round-trip guarantee. Mirrors `Serializer.lean`. |
| `r1`          | REQ-060–063        | `contains_self_reference()`, `verify_r1()`, `verify_r1_dialect()` | Boolean predicate over AST. No mutation. Mirrors `R1NoRecursion.lean`. |
| `r2`          | REQ-070–073        | `ResourceState`, `verify_r2()`, `bounded_eval()` | Fuel-bounded evaluation. Termination guaranteed by strictly decreasing fuel. Mirrors `R2ResourceBounds.lean`. |
| `r3`          | REQ-080–081        | `verify_r3()` | Name-set membership check. Mirrors `R3CorePreservation.lean`. |
| `r4`          | REQ-090–091        | `trait Signer`, `verify_r4()` | Trait definition is pure; concrete signers live in the shell. `verify_r4` takes `&dyn Signer` — the function itself is a pure predicate over its inputs. |
| `template`    | REQ-100–101        | `expand_template()` | Substitution + fuel-bounded recursion under R2 limits. Mirrors `TemplateExpansion.lean`. |
| `pipeline`    | REQ-110–111, NFR-002 | `run_pipeline()`, `PipelineResult` | Composition of pure stages: parse → parse_message → validate → verify. Mirrors `Pipeline.lean`. |
| `pattern`     | REQ-130            | pattern matching dispatch | Deterministic tag-based dispatch. Mirrors `PatternMatch.lean`. |
| `msg_tag`     | NFR-030–032        | `MsgTag`, `msg_tag()` | Deterministic classifier: SExpr → MsgTag. Examines head symbol (or head + second for `lang`). Mirrors `DeterministicUnion.lean`. |

**Total: 13 pure modules.**

### 2.1  Purity Invariants

1. **No I/O.** No function in the core reads from or writes to any
   external resource (file, network, clock, RNG).
2. **No `unsafe`.** All core modules carry `#![forbid(unsafe_code)]`.
3. **Deterministic.** Identical inputs always produce identical outputs.
   Required by DCFL preservation (NFR-030).
4. **Termination.** Every recursive function is either structurally
   recursive on `SExpr` or bounded by an explicit fuel parameter.
5. **`no_std` compatible.** Core depends only on `alloc` (Vec, String).

---

## 3  Effectful Shell

| Module         | CON / REQ          | Effects | Purity Violation |
|----------------|--------------------|---------|-----------------------|
| `agent`        | REQ-030–034        | Mutable state (`dialects: Vec<Dialect>`) | `install_dialect` mutates agent state. Gossip reception triggers side effects. |
| `gossip`       | REQ-120–122        | Network I/O, randomness, mutable peer state | `select_peers` requires RNG; `announce_dialect` / `receive_gossip` perform network transport. |
| `ffi`          | CON-010–014        | `unsafe`, raw pointers, C ABI | `extern "C"`, `#[no_mangle]`, opaque pointer handles, manual memory management (`cbcl_free_*`). Only module permitted to use `unsafe`. |
| `wasm`         | CON-020–023        | Platform binding, linear-memory allocator | `wasm-bindgen` glue, JS interop, memory export across WASM boundary. |
| `cli` (future) | —                  | `std::io`, `std::env`, `std::process` | Command-line argument parsing, stdin/stdout, exit codes. |
| `prelude`      | CON-004            | Re-export only | No effects of its own; exists for ergonomic re-export of core types. Classified as shell because it is an API surface concern, not a semantic module. |

**Total: 6 shell modules.**

### 3.1  Shell Invariants

1. **Shell imports core, never reverse.** No `use crate::agent` or
   `use crate::gossip` statement may appear in any core module.
2. **`unsafe` confined to `ffi`.** The `ffi` module is the only module
   without `#![forbid(unsafe_code)]`.
3. **Platform APIs confined to shell.** `std::fs`, `std::net`,
   `std::env`, OS-specific code, and RNG appear only in shell modules.

---

## 4  Boundary Contracts

Four types cross the pure/effectful boundary.  Each is defined in the
core and consumed or produced by the shell.

| Contract Type   | Defined In  | Direction          | Usage |
|-----------------|-------------|--------------------|-------|
| `SExpr`         | `sexpr`     | core → shell, shell → core | FFI/WASM accept raw strings, parse into `SExpr` (entering core), return serialized `SExpr` (leaving core). Agent stores `SExpr` in dialect templates. |
| `Message`       | `message`   | core → shell       | Pipeline produces `Message`; agent/gossip modules consume it for dispatch and state updates. |
| `Dialect`       | `dialect`   | core ↔ shell       | Parsed and verified in core; installed into agent (shell) via `install_dialect`. Gossip (shell) propagates dialect definitions that re-enter core for verification. |
| `PipelineResult`| `pipeline`  | core → shell       | Pipeline returns `PipelineResult`; FFI/WASM/CLI translate it to C structs, JS objects, or exit codes. |

### 4.1  Contract Invariants

1. **Immutability at the boundary.** All four contract types are
   `Clone + Eq + Debug`.  The shell receives owned values; mutation of
   agent state uses the shell's own copy.
2. **Validation before entry.** Any `Dialect` entering the core for
   verification has already been parsed by `parse_dialect` (core).  Any
   `Dialect` entering the agent has been verified by R1+R2+R3 (core).
3. **Serialization is optional.** `serde::Serialize` / `Deserialize`
   on contract types is gated behind the `serde` feature flag (CON-002).

---

## 5  Dependency Rule

```
┌─────────────────────────────────────────────────────────┐
│                    Effectful Shell                       │
│                                                         │
│  ┌──────────┐ ┌────────┐ ┌──────┐ ┌──────┐ ┌────────┐ │
│  │  agent   │ │ gossip │ │ ffi  │ │ wasm │ │  cli   │ │
│  └────┬─────┘ └───┬────┘ └──┬───┘ └──┬───┘ └───┬────┘ │
│       │           │         │        │          │      │
│       ▼           ▼         ▼        ▼          ▼      │
│  ═══════════════════════════════════════════════════════ │
│       │    Boundary: SExpr, Message, Dialect,   │      │
│       │              PipelineResult              │      │
│  ═══════════════════════════════════════════════════════ │
│       │           │         │        │          │      │
│       ▼           ▼         ▼        ▼          ▼      │
│  ┌─────────────────────────────────────────────────────┐│
│  │                    Pure Core                        ││
│  │                                                     ││
│  │  sexpr  message  dialect  parser  serializer        ││
│  │  r1  r2  r3  r4  template  pipeline  pattern        ││
│  │  msg_tag                                            ││
│  └─────────────────────────────────────────────────────┘│
└─────────────────────────────────────────────────────────┘

    ▲ = allowed import direction (shell → core)
    ✗ = core never imports shell
```

### 5.1  Enforcement

| Mechanism | Description |
|-----------|-------------|
| **Crate features** | Core modules compile under `#![no_std]` + `alloc`. Shell modules require `std` or platform-specific features (`wasm`, `ffi`). |
| **`#![forbid(unsafe_code)]`** | Every core module carries this attribute. Violation is a compile error. |
| **Module visibility** | Shell modules are `pub(crate)` or feature-gated. Core modules form `cbcl::prelude`. |
| **CI lint** | A CI step (or `cargo clippy` custom lint) SHALL verify no `use crate::{agent,gossip,ffi,wasm,cli}` appears in core modules. |

---

## 6  Intra-Core Dependency Graph

Within the pure core, modules have a layered dependency structure:

```
                    pipeline
                   /    |    \
                  /     |     \
           parser    template  pattern
           / | \       |
          /  |  \      |
     sexpr msg dialect r2
              |     |
              |     r1, r3, r4
              |
           msg_tag
              |
           serializer
```

- `sexpr` is the leaf — no intra-core dependencies.
- `message` depends on `sexpr`.
- `dialect` depends on `sexpr`, `message`.
- `parser` depends on `sexpr`, `message`, `dialect`.
- `r1`, `r3` depend on `dialect`, `sexpr`.
- `r2` depends on `dialect`, `sexpr`.
- `r4` depends on `dialect`, `sexpr`, `serializer`.
- `template` depends on `sexpr`, `dialect`, `r2`.
- `msg_tag` depends on `sexpr`, `message`.
- `serializer` depends on `sexpr`.
- `pattern` depends on `sexpr`, `message`, `msg_tag`.
- `pipeline` depends on `parser`, `message`, `dialect`, `r1`, `r2`, `r3`, `template`, `msg_tag`.

No cycles exist; the graph is a DAG.

---

## 7  R4 Boundary Design

The `Signer` trait deserves special attention as it straddles the
boundary:

- **Trait definition** (`r4` module, pure core): defines the `sign` /
  `verify` interface.  `verify_r4` is a pure predicate that delegates
  cryptographic operations to the trait object.
- **Trait implementations** (shell): concrete signers (Ed25519, ring,
  etc.) live in the shell or in downstream crates.  They may perform
  heap allocation, call into C libraries, or use platform RNG for key
  generation.

This design preserves core purity while allowing pluggable cryptography.

---

## 8  Traceability

| SPEC-001 Requirement | Zone   | Module(s) |
|-----------------------|--------|-----------|
| REQ-001–005           | Core   | `sexpr` |
| REQ-010–014           | Core   | `message` |
| REQ-020–025           | Core   | `dialect` |
| REQ-030–034           | Shell  | `agent` |
| REQ-040–045           | Core   | `parser` |
| REQ-050               | Core   | `serializer` |
| REQ-060–063           | Core   | `r1` |
| REQ-070–073           | Core   | `r2` |
| REQ-080–081           | Core   | `r3` |
| REQ-090–091           | Core (trait) / Shell (impl) | `r4` / downstream |
| REQ-100–101           | Core   | `template` |
| REQ-110–111           | Core   | `pipeline` |
| REQ-120–122           | Shell  | `gossip` |
| REQ-130               | Core   | `pattern` |
| CON-010–014           | Shell  | `ffi` |
| CON-020–023           | Shell  | `wasm` |
| NFR-030–032           | Core   | `msg_tag` |
