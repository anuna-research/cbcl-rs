---
id: SPEC-009
title: Erlang Binding for CBCL — `cbcl-erl` Crate
status: draft
version: 0.1.0
audience: cbcl-rs-maintainers, binding-implementors, beam-consumers
created: 2026-04-29
source-protocol: ../../handbook/engineering/usdd-agent-protocol.md
related:
  - ./SPEC-002-structural-contracts.md
  - ./SPEC-003-verification-lattice.md
  - ./SPEC-010-binding-conformance.md  # planned — cross-cutting binding regime
  - ../../cbcl-lfe-router/specs/SPEC-008-rust-parser-bindings.md  # first downstream consumer
license: CC BY 4.0
---

# SPEC-009: Erlang Binding for CBCL — `cbcl-erl` Crate

## Information Table

| Field | Value |
| --- | --- |
| Document ID | SPEC-009 |
| Title | Erlang Binding for CBCL — `cbcl-erl` Crate |
| Status | draft |
| Version | 0.1.0 |
| Date | 2026-04-29 |
| Owners | Anuna Research |
| Primary audience | cbcl-rs maintainers, future binding implementors, BEAM consumers |
| Source protocol | `../../handbook/engineering/usdd-agent-protocol.md` |
| AI Trust tier | Tier 2 — protocol parsing at trust boundary; cross-model review + human review required |
| Sibling spec (planned) | `./SPEC-010-binding-conformance.md` — cross-cutting concerns for N language bindings |
| First downstream consumer | `../../cbcl-lfe-router/specs/SPEC-008-rust-parser-bindings.md` |
| Position | First BEAM binding alongside `cbcl-ffi` (C ABI), `cbcl-wasm` (browser), and future `cbcl-py` / `cbcl-node` / etc. |

---

## 1. Purpose

This specification defines the `cbcl-erl` crate: an Erlang-callable native library exposing CBCL parsing and dialect verification to BEAM consumers (Erlang, LFE, Elixir, Gleam). It is the canonical Erlang binding for CBCL, sibling to the existing `cbcl-ffi` (C ABI) and `cbcl-wasm` (browser) bindings.

The crate's scope is bounded to **message parsing** and **dialect verification** — surfaces in `cbcl-core` and `cbcl-parser` that are stable today. Structural contract enforcement (SPEC-002, SPEC-003) is deferred to SPEC-011 because building bindings against a `draft` upstream specification creates churn.

The design is motivated by four properties:

1. **Native Erlang term surface, not strings.** Unlike `cbcl-ffi`, which returns canonical serialised strings, `cbcl-erl` returns Erlang terms directly (atoms for enums, maps for structs, binaries for strings). This avoids the parse-twice penalty consumers would otherwise pay.
2. **Idiomatic BEAM integration.** A NIF loaded into the consuming application — not an external port executable — to keep parse latency on the BEAM hot path acceptable for high-throughput message routers.
3. **Multi-binding family member.** `cbcl-erl` is designed from day one as a member of the multi-binding family, with cross-cutting concerns (conformance suite, error taxonomy, lifetime contract, threading promises, versioning) deferred to the planned SPEC-010.
4. **Safety at the BEAM boundary.** A panic in a NIF crashes the entire BEAM scheduler, not just the calling process. The crate explicitly rejects this failure mode through `#![forbid(unsafe_code)]`, panic-to-error conversion at every export, and a per-binding fuzzing baseline.

---

## 2. Principals and Scope

**In scope:**

- The Cargo crate at `cbcl-rs/crates/cbcl-erl/`.
- Erlang/LFE-callable APIs for message parsing (strict and lax) and dialect verification.
- The mapping between Rust types in `cbcl-core` and Erlang terms.
- Crash-safety baseline at the BEAM boundary.
- Conformance with the test-vector suite and the (forthcoming) SPEC-010 regime.

**Out of scope:**

- Structural contract enforcement bindings — deferred to SPEC-011.
- Agent lifecycle bindings (opaque handle for `Agent`, `MessageStore`) — out of scope for v0.1.0; will be added when a downstream consumer needs them.
- Replacement of `cbcl-ffi`'s C ABI — `cbcl-erl` is a sibling, not a successor.
- Build-time integration in any specific downstream consumer (e.g. how a router pins `cbcl-rs.sha` or wires its rebar3 build) — that is the consumer's responsibility, captured in the consumer's adoption spec (e.g. `cbcl-lfe-router/SPEC-008`).

**Out of scope (deferred to SPEC-010):**

The following concerns affect every binding (`cbcl-erl`, `cbcl-ffi`, `cbcl-wasm`, future `cbcl-py` / `cbcl-node` / etc.) and belong in a single upstream specification:

- **Binding conformance test suite** — promotion of `test-vectors/` to a versioned, schema-documented artefact every binding passes as a release gate.
- **Cross-language error taxonomy** — canonical error categories (parse, message, dialect, verification, encoding) and the rule that each binding maps them to its host idiom.
- **Opaque-handle lifetime contract** — clone semantics, Send/Sync promises, finalizer obligations.
- **Threading and concurrency model** — what cbcl-core types may be called from multiple host threads.
- **Versioning strategy** — when cbcl-core publishes SemVer to crates.io and bindings declare version ranges.
- **Distribution matrix** — pre-built native artefacts per (platform × architecture × binding).
- **Trust boundary baselines** — minimum hardening that all bindings inherit; per-binding addenda for host-specific risks.
- **Documentation separation** — protocol semantics live in cbcl-rs SPECs; each binding ships a thin host-specific README only.

SPEC-009 is consistent with the expected shape of SPEC-010 but does not depend on its ratification: where this spec makes a BEAM-specific choice (e.g. CON-001's binary-prefixed error strings) it is explicitly framed as the BEAM-idiomatic mapping of the eventual SPEC-010 taxonomy.

**Principals:**

- **`cbcl-rs` maintainers** — own the crate; commit to API stability for the parser/verify surface for the lifetime of SPEC-009 v0.1.x.
- **Downstream BEAM consumers** — any Erlang/LFE/Elixir/Gleam project; the first is `cbcl-lfe-router` (SPEC-008).
- **Future binding implementors** — `cbcl-py`, `cbcl-node`, etc. — read SPEC-009 as the canonical example of how to build a CBCL binding.

---

## 3. User Profiles

### 3.1 cbcl-rs Maintainer

Goals: ship parser/dialect changes once; have BEAM consumers pick them up via a pinned revision; not maintain a parallel implementation.

### 3.2 BEAM Consumer Maintainer

Goals: call CBCL parsing from idiomatic Erlang/LFE; pattern-match on parsed messages without re-parsing; trust that "the parser" is THE parser.

### 3.3 Future Binding Implementor

Goals: read SPEC-009 to understand how a CBCL binding is structured, what conformance obligations it inherits, and what host-specific decisions are theirs to make.

---

## 4. Functional Requirements

### REQ-001: Crate Location and Layout

A new Cargo crate SHALL be created at `cbcl-rs/crates/cbcl-erl/`, sibling to the existing `cbcl-ffi`, `cbcl-wasm`, and `cbcl-cli` crates. The crate SHALL declare `crate-type = ["cdylib"]` and depend on `cbcl-core` and `cbcl-parser` as workspace path dependencies. The crate SHALL use the `rustler` crate to expose Erlang-callable functions returning Erlang terms directly (not serialised strings).

**Rationale:** Bindings live with the thing they bind (precedent: `cbcl-wasm`, `cbcl-ffi`). Returning native Erlang terms avoids the parse-twice penalty that `cbcl-ffi`'s string surface imposes on BEAM consumers.

**Trace:**
- ADR-002
- TEST-001
- CON-001

### REQ-002: Message Parsing API

The crate SHALL expose `parse_message/1` accepting a binary and returning `{ok, Message} | {error, Reason}` where `Message` is an Erlang map keyed by atoms (`performative`, `recipient`, `content`, `params`, `thread`, `sender`, `caused_by`) and `Reason` is a binary error description. The function SHALL preserve the semantics of `cbcl_parser::parse_message` for all inputs covered by the canonical `test-vectors/` corpus.

**Acceptance criteria:**
- All vectors that `cbcl-parser::parse_message` accepts SHALL be accepted, producing semantically equal output.
- All vectors `cbcl-parser::parse_message` rejects SHALL be rejected, with error categorisation matching CON-001's taxonomy.

**Trace:**
- TEST-002
- CON-001
- REQ-006 (conformance)

### REQ-003: Lax Parsing Variant

The crate SHALL expose `parse_message_lax/1` with the same return shape as REQ-002, accepting messages that omit fields the strict parser requires. The behaviour SHALL track `cbcl-parser`'s lax mode for any input that exercises it.

**Trace:**
- TEST-003
- CON-001

### REQ-004: Dialect Verification API

The crate SHALL expose `verify_dialect/1` accepting a binary containing a dialect definition and returning `ok | {error, Reason}` where verification covers the R1, R2, and R3 rules defined in `cbcl-core`. Behaviour SHALL match the existing `cbcl_verify_dialect` C ABI export.

**Trace:**
- TEST-004
- CON-002

### REQ-005: Crash Containment at the BEAM Boundary

The crate SHALL NOT panic on any input. Rust panics inside `cbcl-erl` SHALL be converted to `{error, Reason}` returns at the rustler boundary (rustler's default panic-to-`badarg` behaviour SHALL be overridden to produce a categorised error). The crate manifest SHALL declare `#![forbid(unsafe_code)]`.

**Rationale:** A panic in a NIF crashes the BEAM scheduler, not just the calling process. CBCL bindings parse untrusted bytes — the trust boundary is hostile.

**Trace:**
- TEST-005 (fuzz)
- NFR-002

### REQ-006: Conformance Suite Participation

The crate SHALL execute the canonical CBCL test-vector suite (currently `test-vectors/`, prospectively the SPEC-010 conformance corpus) as a gating CI check on every cbcl-rs change touching `cbcl-core`, `cbcl-parser`, or `cbcl-erl`. The crate SHALL emit results in the schema declared by SPEC-010 once SPEC-010 is approved; until then, the existing JSON vector format is sufficient.

**Rationale:** With multiple bindings the conformance suite — not pairwise differential testing — is the mechanism that keeps bindings aligned with each other and with the canonical Rust implementation.

**Trace:**
- TEST-006
- TEST-007 (cross-binding conformance gate)

---

## 5. Non-Functional Requirements

### NFR-001: Cold-Start Binary Size

The release `libcbcl_erl.{so,dylib}` SHALL be ≤ 8 MB stripped on Linux x86_64 and macOS arm64. Larger sizes require an ADR amendment justifying the cost.

**Trace:**
- TEST-NFR-001

### NFR-002: Fuzz Resilience

The crate SHALL survive 10⁹ fuzzer-generated inputs (coverage-guided, drawn from the existing `cbcl-rs/fuzz/` corpus extended with rustler-encoding-boundary generators) without a single panic, hang, or memory-safety violation. This is `cbcl-erl`'s host-specific addendum to the SPEC-010 baseline.

**Trace:**
- TEST-005

### NFR-003: Term Encoding Cost

Encoding a parsed `Message` as an Erlang term SHALL allocate ≤ 4× the original input byte size in BEAM-side resident memory, averaged over the canonical test-vector distribution. Single-message worst case ≤ 16× input size.

**Trace:**
- TEST-NFR-003

---

## 6. Architecture Decisions

### ADR-001: Rustler NIF vs Erlang Port vs Reuse `cbcl-ffi`

**Decision:** Build `cbcl-erl` as a Rustler-based NIF (in-process, native call), not as an external port executable nor as a thin LFE wrapper over the existing `cbcl-ffi` C ABI.

**Alternatives considered:**

- **Erlang Port (out-of-process)** — safer (a port crash does not crash the BEAM scheduler), but adds a per-message IPC cost. For high-throughput message routers (the first downstream consumer is exactly this) the latency cost is unacceptable. Revisit if NFR-002 fuzz testing reveals unfixable robustness issues.
- **Thin BEAM wrapper over `cbcl-ffi`** — would reuse existing C ABI. Rejected because `cbcl-ffi` returns serialised canonical strings, forcing BEAM consumers to parse twice. Acceptable for one-off shell-out use cases (which is `cbcl-ffi`'s actual target audience) but wrong for high-frequency parsing.
- **Wasmex (WASM-in-NIF)** — embeds a WASM runtime inside a NIF. Two VM layers, larger binary, slower per-call. The existing `cbcl-wasm` crate targets browsers (Hoot/wasm-bindgen), not BEAM embedding. Rejected as solving the wrong problem.

**Tradeoff accepted:** A panic in `cbcl-erl` crashes the BEAM scheduler. Mitigated by `#![forbid(unsafe_code)]` (REQ-005), the existing fuzz suite extended for the rustler boundary (NFR-002), and rustler's panic-to-error wrapping at every export.

### ADR-002: Crate Lives Upstream in `cbcl-rs`

**Decision:** `cbcl-erl` lives in `cbcl-rs/crates/cbcl-erl/` as a workspace member, not vendored in any consumer's tree.

**Rationale:** Bindings live with the thing they bind. Precedent: `cbcl-ffi`, `cbcl-wasm` are also single-consumer-of-one bindings hosted upstream. When `cbcl-core`/`cbcl-parser` evolves, the binding evolves in the same PR with the same Rust CI and workspace path dependencies — no version juggling.

**Alternatives considered:**

- **Vendor inside the consumer's tree** (e.g. `cbcl-lfe-router/native/cbcl-erl/`) — simpler for a single consumer but breaks immediately when a second BEAM consumer appears.
- **Standalone repo `cbcl-erl/`** — cleanest separation, worst ergonomics; three-repo coordination for every change.

**Tradeoff accepted:** Cross-repo coordination cost between cbcl-rs and downstream consumers. Mitigated by SemVer (when SPEC-010 ratifies) or pinned-SHA conventions in each consumer's adoption spec.

### ADR-003: Erlang Term Mapping Strategy

**Decision:** Map Rust types to BEAM-idiomatic terms (atoms for enums, maps with atom keys for structs, binaries for strings) rather than to a generic `{tag, value}` envelope.

**Rationale:** Idiomatic terms cost the same to encode and are dramatically nicer to pattern-match in Erlang/LFE/Elixir. The mapping table is fixed in CON-001 and changes require a SPEC amendment.

**Tradeoff accepted:** Rust-side enum additions become breaking changes for BEAM consumers (a new performative variant produces a new atom they may not match on). Acceptable because cbcl-core enums are protocol-level and rarely change; downstream consumers can use a catch-all clause.

### ADR-004: Conform to the (Forthcoming) Multi-Binding Regime

**Decision:** `cbcl-erl` is designed as a member of a multi-binding family from day one. SPEC-009 explicitly defers cross-cutting concerns to the planned SPEC-010. Where this spec must make a concrete choice before SPEC-010 ratifies, it picks the BEAM-idiomatic option and documents the SPEC-010 hook so the choice can be retroactively framed without amendment.

**Concrete consequences:**

| Cross-cutting concern | SPEC-009 stance | SPEC-010 hook |
|---|---|---|
| Conformance suite | REQ-006 mandates participation; uses today's JSON vectors | Migrate to SPEC-010 schema when ratified |
| Error taxonomy | CON-001 binary prefixes (`parse error: ...`, etc.) | Each prefix maps 1:1 to a SPEC-010 category |
| Lifetime contract | No opaque handles in v0.1.0; deferred to SPEC-011 | SPEC-011 declares its handles per SPEC-010 |
| Threading | NIF calls are scheduler-bound; cbcl-core types must be `Send + Sync` for dirty-CPU NIFs | SPEC-010 audits and declares cbcl-core thread safety |
| Versioning | Workspace path deps; pinned-SHA in downstream consumers | SPEC-010 establishes cbcl-core SemVer policy |
| Trust boundary | NFR-002 fuzz budget over rustler boundary | SPEC-010 baseline + per-binding addenda |
| Documentation | Crate README points at cbcl-rs SPECs for protocol semantics | SPEC-010 forbids re-explaining the protocol per binding |

**Tradeoff accepted:** SPEC-009 ships with placeholder language that becomes ratified when SPEC-010 lands. If SPEC-010 ratifies a category SPEC-009 did not anticipate, SPEC-009 receives a minor amendment, not a rewrite.

---

## 7. Contracts

### CON-001: `cbcl_erl:parse_message/1` and `parse_message_lax/1`

**Module:** `cbcl_erl` (Erlang NIF module loaded from `libcbcl_erl.{so,dylib}`)

**Signature:**
```
parse_message(Bytes :: binary()) ->
    {ok, Message :: message()} | {error, Reason :: binary()}.

parse_message_lax(Bytes :: binary()) ->
    {ok, Message :: message()} | {error, Reason :: binary()}.
```

**Message term shape:**
```
message() ::
    #{ performative := atom()
     , recipient    := binary() | undefined
     , content      := sexpr_term()
     , params       := #{atom() => sexpr_term()}
     , thread       := binary() | undefined
     , sender       := binary() | undefined
     , caused_by    := [binary()]   %% list of content hashes
     }.
```

**Pre-conditions:** `Bytes` is a UTF-8 encoded binary. Non-UTF-8 input returns `{error, <<"invalid utf-8">>}`.

**Post-conditions:** On `{ok, Message}`, `Message` is canonicalisable via `cbcl-core`'s serializer to bytes that re-parse to an equal `Message`.

**Error model:** Reason binaries are categorised by prefix. Each prefix is the BEAM-idiomatic mapping of a category in the planned cross-binding error taxonomy (SPEC-010):

| Binary prefix (BEAM mapping) | SPEC-010 category | Source |
|---|---|---|
| `<<"parse error: ...">>` | `ParseError` | lexical/syntactic failure in `cbcl-parser::parser::parse` |
| `<<"message error: ...">>` | `MessageError` | structural failure in `cbcl-parser::parse_message` |
| `<<"dialect error: ...">>` | `DialectError` | dialect-definition parse failure (CON-002) |
| `<<"verification failed: ...">>` | `VerificationError` | R1/R2/R3 violation during `verify_dialect/1` (CON-002) |
| `<<"invalid utf-8">>` | `EncodingError` | input bytes not UTF-8 |

Adding a new prefix is a contract change requiring a SPEC-009 amendment. Removing or repurposing a prefix is a breaking change for downstream BEAM consumers.

**Implements:** REQ-002, REQ-003.

**Verified by:** TEST-002, TEST-003, TEST-006.

### CON-002: `cbcl_erl:verify_dialect/1`

**Signature:**
```
verify_dialect(Bytes :: binary()) ->
    ok | {error, Reason :: binary()}.
```

**Pre-conditions:** `Bytes` is a UTF-8 encoded dialect definition.

**Post-conditions:** `ok` iff the dialect parses and satisfies R1, R2, and R3 rules per `cbcl-core::dialect::DialectRegistry::install`.

**Error model:** Reason binaries follow the CON-001 taxonomy; failure paths include `dialect error:` (parse) and `verification failed:` (R1/R2/R3 violation).

**Implements:** REQ-004.

**Verified by:** TEST-004.

---

## 8. Test Specifications

| ID | Description | Technique | Tier |
|---|---|---|---|
| TEST-001 | `cbcl-erl` crate compiles standalone in cbcl-rs CI on Linux x86_64 and macOS arm64 | Example | 4 |
| TEST-002 | `parse_message/1` matches all `test-vectors/` cases with correct error categorisation | Example + roundtrip property | 2 |
| TEST-003 | `parse_message_lax/1` matches lax-mode vectors | Example | 2 |
| TEST-004 | `verify_dialect/1` matches `cbcl_verify_dialect` C ABI behaviour on shared corpus | Example | 2 |
| TEST-005 | Fuzz per NFR-002: 10⁹ inputs across the rustler boundary | Coverage-guided fuzzing | 1 |
| TEST-006 | Conformance suite: every `test-vectors/` JSON case is exercised on every cbcl-erl PR | Build-system | 2 |
| TEST-007 | Cross-binding conformance: `cbcl-erl`, `cbcl-ffi`, `cbcl-wasm` agree on the test-vector matrix (parity check) | Build-system | 2 |
| TEST-NFR-001..003 | Non-functional requirement verification | Benchmark | 3 |

**Verification techniques selected** (per USDD §Verification): example-based for the parity matrix, roundtrip property tests for the canonical-form invariant, coverage-guided fuzzing across the rustler boundary (the existing `cbcl-rs/fuzz/` corpus does not exercise the term-encoding path).

---

## 9. Purity Boundary Map

### Pure Core (no I/O, no shared state, deterministic)
- `cbcl-core`: grammar, R1/R2/R3 verification, canonical serialisation
- `cbcl-parser`: tokenizer, parser, message construction

### Effectful Shell (orchestrates I/O, calls pure core)
- `cbcl-erl`: marshals binaries → `SExpr`, calls `cbcl-parser`, encodes results as Erlang terms via rustler

### Boundary Contracts (data types crossing the boundary)
- `binary()` (BEAM) ↔ `&[u8]` (Rust): UTF-8 encoded message bytes
- `message()` Erlang map ↔ `cbcl_core::message::Message`: parsed message
- `atom()` (BEAM) ↔ `cbcl_core::message::Performative`: enum performatives

### Dependency Rule
Dependencies point inward: BEAM consumer → `cbcl-erl` (shell) → `cbcl-parser` / `cbcl-core` (pure core). The pure core MUST NOT call back into the BEAM. This is statically enforced by the rustler crate type system (no `Env` is available in pure functions).

### Enforcement
- `#![forbid(unsafe_code)]` in `cbcl-erl`'s manifest.
- Rust workspace clippy lints; cbcl-rs CI fails the build on warnings in the `cbcl-erl` crate.
- Cross-repo: cbcl-rs CI runs cbcl-erl tests on every cbcl-core/cbcl-parser change, even when no Rust source in `cbcl-erl` itself has changed.

---

## 10. Observability

The crate is a library; observability is the consumer's responsibility. SPEC-009 specifies only what the crate makes observable:

### OBS-001: NIF Version Constants

The crate SHALL export compile-time constants for the cbcl-rs git revision, the cbcl-core version, and the cbcl-erl version. Consumers SHALL be able to log these at NIF load time to aid in debugging version-mismatch issues.

### OBS-002: Per-Call Tracing Hooks

When the `tracing` Cargo feature is enabled, the crate SHALL emit `tracing` events on entry to and exit from every public function, with the input size and outcome (`ok` or error category) as fields.

---

## 11. Open Questions

The following are explicitly unresolved and SHOULD be answered before promoting status from `draft` to `approved`:

1. **Scheduler safety strategy.** Should `parse_message/1` be a regular NIF, a dirty-CPU NIF, or scheduled with `enif_consume_timeslice`? Depends on measured per-call duration on the production message size distribution. Recommend a microbenchmark before settling.
2. **Error categorisation granularity.** CON-001 lists five prefixes; consumers may want finer granularity (e.g. distinguishing recipient-format errors from missing-field errors within `MessageError`). Audit the first downstream consumer's error-handling to determine whether the taxonomy needs sub-categories.
3. **`cbcl-csexp` co-binding.** The CSEXP receipt format is currently router-internal. If a future consumer wants it bound, decide whether to add CSEXP exports here or split into a separate crate.
4. **SPEC-010 ownership and timing.** SPEC-010 (binding conformance) is a forward reference. Identify an owner and confirm whether it drafts before, alongside, or after SPEC-009 implementation.
5. **Cross-binding conformance harness.** TEST-007 asserts `cbcl-erl`, `cbcl-ffi`, `cbcl-wasm` agree. The harness driving this comparison does not yet exist; designing it is part of SPEC-010 but a working prototype helps inform the design.

---

## 12. Status and Review

This specification is `draft`. Per USDD Constitutional Principle 12 (Adversarial Review), no implementation work begins until:

- Cross-model adversarial review of this document from a clean session.
- Human review by cbcl-rs maintainer and the first downstream consumer's owner (SPEC-008 author).
- Resolution of all items in §11.

On promotion to `approved`, status moves to `implementing` and SPEC-008 (the first downstream adoption) can proceed in parallel against the agreed API surface.

---

**END OF SPECIFICATION**
