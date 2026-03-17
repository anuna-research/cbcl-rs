# SPEC-001: CBCL Rust Port

| Field        | Value                                      |
|--------------|--------------------------------------------|
| **ID**       | SPEC-001                                   |
| **Title**    | CBCL Rust Port                             |
| **Status**   | Draft                                      |
| **Date**     | 2026-03-18                                 |
| **Derived**  | cbcl-paper-draft.md, lean-cbcl/ (Lean 4)  |

## 1  Purpose

Define the requirements for a Rust implementation of the CBCL
(Communication-Based Communication Language) runtime.  The Rust crate
(`cbcl`) must faithfully reproduce the semantics formalized in the Lean 4
proof library (`lean-cbcl/`) and tested in the Guile reference
implementation (`src/`).  It must additionally compile to WASM and expose a
stable C FFI, enabling embedding in browsers, IoT firmware, and native
host processes.

## 2  Scope

In scope: S-expression codec, message grammar, dialect system, agent
state, parser pipeline, safety constraints R1–R4, gossip protocol,
serialization, template expansion, C FFI, WASM target.

Out of scope: transport layer, cryptographic library selection (R4 uses a
trait), GUI, IDE tooling, specific dialect implementations beyond
`cbcl-base`.

---

## 3  Functional Requirements (REQ)

### 3.1  S-Expression Module

| ID       | Requirement |
|----------|-------------|
| REQ-001  | The crate SHALL define an `Atom` enum with variants `Symbol(String)`, `Str(String)`, `Num(i64)`, `Bool(bool)`, `Keyword(String)`, mirroring `CBCL.Atom` in `SExpr.lean:14–19`. |
| REQ-002  | The crate SHALL define an `SExpr` enum with variants `Atom(Atom)` and `List(Vec<SExpr>)`, mirroring `CBCL.SExpr` in `SExpr.lean:24–27`. |
| REQ-003  | `SExpr` SHALL implement `Eq`, `Clone`, `Debug`, and `Hash`. |
| REQ-004  | The crate SHALL provide `SExpr::size() -> usize`, `SExpr::byte_size() -> usize`, and `SExpr::depth() -> usize` with semantics identical to `SExpr.size`, `SExpr.byteSize`, `SExpr.depth` in `SExpr.lean:60–79`. |
| REQ-005  | The crate SHALL provide `SExpr::is_symbol(name: &str) -> bool` matching `SExpr.isSymbol` in `SExpr.lean:86–88`. |

### 3.2  Message Module

| ID       | Requirement |
|----------|-------------|
| REQ-010  | The crate SHALL define a `CorePerformative` enum with exactly the 8 variants `Tell`, `Ask`, `Reply`, `Error`, `Ok`, `Cancel`, `Hello`, `Bye`, matching `CBCL.CorePerformative` in `Message.lean:16–17`. |
| REQ-011  | The crate SHALL define a `Performative` enum with variants `Core(CorePerformative)` and `Custom(String)`, matching `CBCL.Performative` in `Message.lean:21–23`. |
| REQ-012  | The crate SHALL define a `MessageType` enum with variants `Simple`, `Meta`, `Dialect`, `Wrapped`, matching `CBCL.MessageType` in `Message.lean:33–37`. |
| REQ-013  | The crate SHALL define a `Message` struct with fields `msg_type: MessageType`, `performative: Performative`, `params: Vec<SExpr>`, `thread: Option<String>`, `sender: Option<String>`, matching `CBCL.Message` in `Message.lean:41–47`. |
| REQ-014  | The crate SHALL expose `CORE_PERFORMATIVE_NAMES: &[&str]` containing exactly `["tell", "ask", "reply", "error", "ok", "cancel", "hello", "bye"]` and `is_core_performative_name(s: &str) -> bool`. |

### 3.3  Dialect Module

| ID       | Requirement |
|----------|-------------|
| REQ-020  | The crate SHALL define `ResourceBounds { max_depth: u32, max_expansion_size: u32, verification_time_ms: u32 }`, matching `CBCL.ResourceBounds` in `Dialect.lean:18–22`. |
| REQ-021  | The crate SHALL define `PerformativeDef { name: String, params: Vec<SExpr>, template: SExpr }`, matching `CBCL.PerformativeDef` in `Dialect.lean:27–30`. |
| REQ-022  | The crate SHALL define a `Dialect` struct with fields `name`, `extends`, `author`, `performatives`, `resources`, `examples`, `signature`, `hash`, `protocol`, matching `CBCL.Dialect` in `Dialect.lean:34–44`. |
| REQ-023  | The crate SHALL provide `BASE_DIALECT: Dialect` with name `"cbcl-base"`, 8 core performatives, and resource bounds `{ max_depth: 8, max_expansion_size: 512, verification_time_ms: 10 }`, matching `CBCL.baseDialect` in `Dialect.lean:53–68`. |
| REQ-024  | `ResourceBounds::is_valid()` SHALL return `true` iff all fields are positive and within system limits: `max_depth ≤ 64`, `max_expansion_size ≤ 8192`, `verification_time_ms ≤ 1000`, matching `ResourceBounds.isValid` in `Dialect.lean:101–104`. |
| REQ-025  | `Dialect::defines_performative(name)` and `Dialect::find_performative(name)` SHALL match their Lean counterparts in `Dialect.lean:79–84`. |

### 3.4  Agent Module

| ID       | Requirement |
|----------|-------------|
| REQ-030  | The crate SHALL define `Agent { id: String, dialects: Vec<Dialect> }`, matching `CBCL.Agent` in `Agent.lean:16–19`. |
| REQ-031  | `Agent::new(id)` SHALL create an agent with `dialects == vec![BASE_DIALECT]`, matching `Agent.new` in `Agent.lean:22–23`. |
| REQ-032  | `Agent::is_well_formed()` SHALL return `true` iff `self.dialects[0] == BASE_DIALECT`, matching `Agent.wellFormed` in `Agent.lean:26–27`. |
| REQ-033  | `Agent::find_performative_dialect(name)` SHALL search dialects in reverse order and return the first dialect defining the performative, matching `Agent.findPerformativeDialect` in `Agent.lean:34–35`. |
| REQ-034  | `Agent::install_dialect(d)` SHALL append `d` to `self.dialects`, matching `Agent.installDialect` in `Agent.lean:38–39`. |

### 3.5  Parser Module

| ID       | Requirement |
|----------|-------------|
| REQ-040  | The crate SHALL provide `parse(input: &str) -> Result<SExpr, ParseError>` implementing a recursive-descent S-expression parser with O(n) time complexity in input length. |
| REQ-041  | The parser SHALL recognize atoms: symbols (`[a-zA-Z][a-zA-Z0-9_-]*`), strings (double-quoted with `\n`, `\r`, `\t`, `\\`, `\"` escapes), integers (`-?[0-9]+`), booleans (`#t`, `#f`), and keywords (`:[a-zA-Z][a-zA-Z0-9_-]*`). |
| REQ-042  | The parser SHALL recognize S-expression lists as `(` whitespace-separated elements `)`. |
| REQ-043  | The parser SHALL reject input that exceeds a configurable fuel limit (default: input byte length), preventing unbounded stack growth. |
| REQ-044  | The crate SHALL provide `parse_message(sexpr: &SExpr) -> Option<Message>` matching the semantics of `CBCL.parseMessage` in `MessageParser.lean`. |
| REQ-045  | The crate SHALL provide `parse_dialect(sexpr: &SExpr) -> Result<Dialect, String>` matching the semantics of `CBCL.parseDialect` in `DialectParser.lean`. |

### 3.6  Serializer Module

| ID       | Requirement |
|----------|-------------|
| REQ-050  | The crate SHALL provide `serialize(sexpr: &SExpr) -> String` producing canonical S-expression text (RFC 9804 compatible) that round-trips: `parse(serialize(e)) == Ok(e)` for all valid `e`. |

### 3.7  R1 — No Recursion

| ID       | Requirement |
|----------|-------------|
| REQ-060  | The crate SHALL provide `contains_self_reference(name: &str, expr: &SExpr) -> bool` matching `CBCL.containsSelfReference` in `R1NoRecursion.lean:24–31`. |
| REQ-061  | The crate SHALL provide `verify_r1(perf_name: &str, template: &SExpr) -> bool` returning `!contains_self_reference(perf_name, template)`. |
| REQ-062  | The crate SHALL provide `verify_r1_dialect(d: &Dialect) -> bool` that returns `true` for `cbcl-base` and checks all performatives otherwise, matching `CBCL.verifyR1Dialect` in `R1NoRecursion.lean:38–40`. |
| REQ-063  | The R1 checker SHALL be sound: if `verify_r1` returns `true`, the template contains no occurrence of the performative name as a symbol. This is the Rust-side operational equivalent of `r1_soundness` in `R1NoRecursion.lean:76–82`. |

### 3.8  R2 — Resource Bounds

| ID       | Requirement |
|----------|-------------|
| REQ-070  | The crate SHALL provide `verify_r2(d: &Dialect) -> bool` checking that all resource bound fields are positive and within system limits, matching `CBCL.verifyR2` in `R2ResourceBounds.lean:59–63`. |
| REQ-071  | The crate SHALL define `ResourceState` with fields `current_depth`, `expansion_size`, `max_depth`, `max_exp_size` and methods `enter_depth() -> Option<ResourceState>`, `add_expansion(size) -> Option<ResourceState>`, `exit_depth()`, matching `CBCL.ResourceState` in `R2ResourceBounds.lean:20–56`. |
| REQ-072  | The crate SHALL provide `bounded_eval(fuel: usize, expr: &SExpr, rs: &mut ResourceState) -> Option<SExpr>` that always terminates (fuel strictly decreases), matching `CBCL.boundedEval` in `R2ResourceBounds.lean:71–88`. |
| REQ-073  | `bounded_eval` with `fuel == 0` SHALL return `None`. `bounded_eval` on an `Atom` with `fuel > 0` SHALL return `Some(atom)`. |

### 3.9  R3 — Core Preservation

| ID       | Requirement |
|----------|-------------|
| REQ-080  | The crate SHALL provide `verify_r3(d: &Dialect) -> bool` that returns `true` for `cbcl-base` and checks that no performative in `d` has a core performative name otherwise, matching `CBCL.verifyR3` in `R3CorePreservation.lean:22–24`. |
| REQ-081  | If `verify_r3` returns `true` for a non-base dialect, then `d.defines_performative(core_name)` SHALL be `false` for all core performative names. This is the Rust-side operational equivalent of `core_performative_not_in_r3_dialect` in `R3CorePreservation.lean:40–51`. |

### 3.10  R4 — Integrity (Trait)

| ID       | Requirement |
|----------|-------------|
| REQ-090  | The crate SHALL define a `trait Signer { fn sign(&self, data: &[u8]) -> Vec<u8>; fn verify(&self, data: &[u8], sig: &[u8]) -> bool; }` abstracting the Ed25519 signature scheme used for dialect integrity. |
| REQ-091  | Dialect verification via R4 SHALL be gated behind a `verify_r4(d: &Dialect, signer: &dyn Signer) -> bool` function that checks `d.signature` against the serialized dialect body. |

### 3.11  Template Expansion

| ID       | Requirement |
|----------|-------------|
| REQ-100  | The crate SHALL provide template expansion: given a `PerformativeDef` and argument `SExpr` values, produce the expanded `SExpr` with substitutions applied, matching the semantics of `TemplateExpansion.lean`. |
| REQ-101  | Template expansion SHALL respect resource bounds (R2): expansion must track depth and byte-size, halting if limits are exceeded. |

### 3.12  Pipeline

| ID       | Requirement |
|----------|-------------|
| REQ-110  | The crate SHALL provide `run_pipeline(input: &str) -> PipelineResult` implementing the full verified pipeline: parse → parse_message → validate → (for meta/define: parse_dialect + verify R1+R2+R3) → success, matching `CBCL.runPipeline` in `Pipeline.lean:51–76`. |
| REQ-111  | `PipelineResult` SHALL have variants `Success(Message)`, `ParseError(String)`, `ValidationError(String)`. |

### 3.13  Gossip Protocol

| ID       | Requirement |
|----------|-------------|
| REQ-120  | The crate SHALL provide a `GossipManager` that implements epidemic dialect propagation with O(log n) expected convergence rounds, matching the protocol in `src/cbcl/gossip.scm`. |
| REQ-121  | `GossipManager` SHALL support operations: `announce_dialect(d)`, `receive_gossip(msg) -> Vec<Dialect>`, `select_peers(k) -> Vec<AgentId>` (fan-out selection). |
| REQ-122  | Received dialect definitions SHALL be validated through the R1+R2+R3 pipeline before installation. |

### 3.14  Pattern Matching

| ID       | Requirement |
|----------|-------------|
| REQ-130  | The crate SHALL provide pattern matching for message dispatch, matching the semantics of `PatternMatch.lean`. |

---

## 4  Non-Functional Requirements (NFR)

### 4.1  Performance

| ID       | Requirement |
|----------|-------------|
| NFR-001  | S-expression parsing SHALL complete in ≤ 1 µs per KiB of input on a 2024-era x86-64 core (measured as p99 latency on the reference benchmark suite). |
| NFR-002  | Full pipeline execution (`run_pipeline`) on a typical CBCL message (≤ 512 bytes) SHALL complete in ≤ 10 µs (p99). |
| NFR-003  | Dialect verification (R1+R2+R3) SHALL complete in ≤ 100 µs for dialects within system resource limits. |
| NFR-004  | The parser SHALL achieve O(n) time complexity in input length with no backtracking. |

### 4.2  Binary Size

| ID       | Requirement |
|----------|-------------|
| NFR-010  | The `cbcl` crate compiled to `wasm32-unknown-unknown` with `opt-level = "z"` and `lto = true` SHALL produce a `.wasm` binary ≤ 256 KiB (before gzip). |
| NFR-011  | The crate SHALL use `#![no_std]` compatible data structures where feasible, gated behind a `no_std` feature flag, to minimize binary size for embedded targets. |

### 4.3  Memory Safety

| ID       | Requirement |
|----------|-------------|
| NFR-020  | The crate SHALL compile with `#![forbid(unsafe_code)]` in all modules except the C FFI boundary module. |
| NFR-021  | The crate SHALL contain zero uses of `unsafe` in any module other than the `ffi` module. |
| NFR-022  | The crate SHALL pass `cargo clippy` with no warnings under the default lint set. |
| NFR-023  | The crate SHALL pass `miri` (`cargo +nightly miri test`) with zero undefined-behavior findings. |

### 4.4  DCFL Preservation

| ID       | Requirement |
|----------|-------------|
| NFR-030  | The message tag function (`msg_tag`) SHALL be deterministic: identical `SExpr` input always produces identical `MsgTag` output, matching `msgTag_deterministic` in `DeterministicUnion.lean:69–71`. |
| NFR-031  | Installing an R3-verified dialect into a well-formed agent SHALL preserve decidability of the agent's message language. This is the operational equivalent of `decidable_preserved` in `DeterministicUnion.lean`. |
| NFR-032  | The parser and message-tag dispatch SHALL preserve the DCFL property: the accepted language is recognizable by a deterministic pushdown automaton. Tag dispatch examines only the head symbol (or head + second symbol for `lang` messages), matching `msgTag_head_only` in `DeterministicUnion.lean:73–78`. |
| NFR-033  | The crate SHALL include property-based tests (via `proptest` or `quickcheck`) exercising DCFL tag determinism, round-trip serialization, and R1/R2/R3 verification invariants. |

### 4.5  Correctness

| ID       | Requirement |
|----------|-------------|
| NFR-040  | The crate SHALL include a test suite covering ≥ 95% of branches (measured by `cargo llvm-cov`). |
| NFR-041  | All 180+ assertions from the Guile reference test suite (`tests/simple-tests.scm`) SHALL have corresponding Rust tests producing identical results. |
| NFR-042  | The crate SHALL include integration tests that run the pipeline on every example from `src/cbcl-grammar.ebnf` and the paper appendices. |

---

## 5  Constraints (CON)

### 5.1  Rust Public API

| ID       | Constraint |
|----------|------------|
| CON-001  | The public Rust API SHALL be organized into modules: `sexpr`, `message`, `dialect`, `agent`, `parser`, `serializer`, `r1`, `r2`, `r3`, `r4`, `template`, `pipeline`, `gossip`, `pattern`. |
| CON-002  | All public types SHALL derive `serde::Serialize` and `serde::Deserialize` behind a `serde` feature flag. |
| CON-003  | Error types SHALL use `thiserror` and implement `std::error::Error` (or a `no_std`-compatible equivalent when `no_std` is active). |
| CON-004  | The crate SHALL expose a prelude module (`cbcl::prelude`) re-exporting the most-used types: `SExpr`, `Atom`, `Message`, `Dialect`, `Agent`, `PipelineResult`, `parse`, `run_pipeline`. |
| CON-005  | The crate SHALL use Rust 2021 edition and maintain an MSRV (Minimum Supported Rust Version) of 1.75.0 or later. |

### 5.2  C FFI

| ID       | Constraint |
|----------|------------|
| CON-010  | The crate SHALL expose a `cbcl_ffi` module producing a C-compatible shared library (`cdylib`). |
| CON-011  | The FFI SHALL expose at minimum: `cbcl_parse(input: *const c_char, len: usize) -> *mut CbclSExpr`, `cbcl_run_pipeline(input: *const c_char, len: usize) -> *mut CbclPipelineResult`, `cbcl_free_sexpr(ptr: *mut CbclSExpr)`, `cbcl_free_result(ptr: *mut CbclPipelineResult)`. |
| CON-012  | All FFI functions SHALL be `extern "C"` with `#[no_mangle]`. |
| CON-013  | The FFI SHALL use opaque pointer handles; callers must not dereference internal struct fields. |
| CON-014  | A C header file (`cbcl.h`) SHALL be auto-generated via `cbindgen` on each release. |

### 5.3  WASM Target

| ID       | Constraint |
|----------|------------|
| CON-020  | The crate SHALL compile to `wasm32-unknown-unknown` without requiring `wasm-bindgen` for the core library (pure WASM export). |
| CON-021  | A `wasm` feature flag SHALL enable `wasm-bindgen` bindings for browser/JS interop, exposing `parse`, `run_pipeline`, `serialize`, and `verify_dialect` as JS-callable functions. |
| CON-022  | WASM builds SHALL NOT depend on `std::fs`, `std::net`, or any OS-specific APIs. |
| CON-023  | The WASM module SHALL export a linear-memory allocator for passing string buffers across the JS/WASM boundary. |

### 5.4  Dependency Constraints

| ID       | Constraint |
|----------|------------|
| CON-030  | The core crate (`cbcl`) SHALL have zero required dependencies beyond `alloc`. Optional features may pull in `serde`, `thiserror`, `wasm-bindgen`. |
| CON-031  | The `cbcl-ffi` crate (if separate) MAY depend on `cbcl` and `libc`. |
| CON-032  | Dev-dependencies MAY include `proptest`, `criterion`, `cargo-llvm-cov`, `insta` (snapshot testing). |

---

## 6  Traceability Matrix

| Lean Module               | REQ          | NFR          | CON          |
|---------------------------|--------------|--------------|--------------|
| `SExpr.lean`              | REQ-001–005  | NFR-020–023  | CON-001      |
| `Message.lean`            | REQ-010–014  |              | CON-001      |
| `Dialect.lean`            | REQ-020–025  |              | CON-001–002  |
| `Agent.lean`              | REQ-030–034  | NFR-031      | CON-001      |
| `Parser.lean`             | REQ-040–043  | NFR-001, 004 | CON-001      |
| `MessageParser.lean`      | REQ-044      | NFR-002      | CON-001      |
| `DialectParser.lean`      | REQ-045      | NFR-003      | CON-001      |
| `Serializer.lean`         | REQ-050      |              | CON-001      |
| `R1NoRecursion.lean`      | REQ-060–063  | NFR-033      | CON-001      |
| `R2ResourceBounds.lean`   | REQ-070–073  | NFR-033      | CON-001      |
| `R3CorePreservation.lean` | REQ-080–081  | NFR-031, 033 | CON-001      |
| `DetParser.lean`          |              | NFR-030–032  |              |
| `DeterministicUnion.lean` |              | NFR-030–032  |              |
| `TemplateExpansion.lean`  | REQ-100–101  |              | CON-001      |
| `Pipeline.lean`           | REQ-110–111  | NFR-002, 040 | CON-001, 004 |
| `gossip.scm`              | REQ-120–122  |              | CON-001      |
| `PatternMatch.lean`       | REQ-130      |              | CON-001      |
| (FFI)                     |              | NFR-020–021  | CON-010–014  |
| (WASM)                    |              | NFR-010–011  | CON-020–023  |
| (Security / R4)           | REQ-090–091  |              |              |

---

## 7  Definitions

| Term                | Definition |
|---------------------|------------|
| **CBCL**            | Communication-Based Communication Language — a self-extensible, formally-verified agent communication language. |
| **DCFL**            | Deterministic Context-Free Language — a language class recognizable by a deterministic pushdown automaton. CBCL's grammar is DCFL, and this property is preserved under dialect installation. |
| **Dialect**         | A named collection of custom performative definitions with declared resource bounds. Dialects extend the base vocabulary. |
| **Performative**    | A speech-act verb (e.g., `tell`, `ask`) that determines how a message is interpreted. Core performatives are immutable; extension performatives are defined in dialects. |
| **R1–R4**           | The four safety constraints: R1 (no recursion), R2 (resource bounds), R3 (core preservation), R4 (cryptographic integrity). |
| **Fuel**            | A strictly-decreasing counter used to guarantee termination of evaluation and parsing. |
| **Gossip Protocol** | An epidemic protocol for peer-to-peer dialect propagation achieving O(log n) convergence. |
| **Pipeline**        | The sequence: parse → parse_message → validate → (verify dialect) → success/error. |

---

## 8  Acceptance Criteria

1. `cargo test` passes with zero failures.
2. `cargo clippy` reports zero warnings.
3. `cargo +nightly miri test` reports zero UB findings.
4. `cargo build --target wasm32-unknown-unknown` succeeds; binary ≤ 256 KiB.
5. `cbindgen` generates `cbcl.h` without errors.
6. All Guile reference tests have Rust equivalents producing identical output.
7. `run_pipeline` produces identical `PipelineResult` variants for all inputs tested against the Lean `runPipeline` function.
8. Property tests for DCFL determinism, round-trip serialization, and R1/R2/R3 pass ≥ 10,000 iterations.
