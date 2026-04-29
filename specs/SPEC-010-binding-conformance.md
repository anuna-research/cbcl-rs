---
id: SPEC-010
title: CBCL Binding Conformance — Cross-Cutting Regime for Language Bindings
status: draft
version: 0.1.0
audience: cbcl-rs-maintainers, binding-implementors
created: 2026-04-29
source-protocol: ../../handbook/engineering/usdd-agent-protocol.md
related:
  - ./SPEC-002-structural-contracts.md
  - ./SPEC-003-verification-lattice.md
  - ./SPEC-009-erlang-binding.md  # first instance covered by this regime
  - ../../cbcl-lfe-router/specs/SPEC-008-rust-parser-bindings.md  # first downstream consumer
license: CC BY 4.0
---

# SPEC-010: CBCL Binding Conformance — Cross-Cutting Regime for Language Bindings

## Information Table

| Field | Value |
| --- | --- |
| Document ID | SPEC-010 |
| Title | CBCL Binding Conformance — Cross-Cutting Regime for Language Bindings |
| Status | draft |
| Version | 0.1.0 |
| Date | 2026-04-29 |
| Owners | Anuna Research |
| Primary audience | cbcl-rs maintainers, current and future binding implementors |
| Source protocol | `../../handbook/engineering/usdd-agent-protocol.md` |
| AI Trust tier | Tier 2 — protocol-level; cross-model review + human review required |
| Governs | `cbcl-ffi` (C ABI), `cbcl-wasm` (browser), `cbcl-erl` (BEAM), and any future binding (`cbcl-py`, `cbcl-node`, `cbcl-go`, `cbcl-swift`, …) |
| Companion spec | `./SPEC-009-erlang-binding.md` — first concrete instance, informs this regime |

---

## 1. Purpose

CBCL is a protocol; a protocol is consumed from many languages. As of 2026-Q2, three Rust-side bindings exist (`cbcl-ffi`, `cbcl-wasm`, `cbcl-erl`) and additional bindings (`cbcl-py`, `cbcl-node`, others) are anticipated. Without a cross-cutting regime, each binding re-derives its own answers to the same questions — what tests gate a release, how errors are mapped, how opaque handles live and die, what threading guarantees the core makes, how versions are coordinated, where the documentation lives. The cost of that re-derivation compounds with bindings, and silent divergence between bindings becomes inevitable.

This specification defines the **binding conformance regime**: a single set of cross-cutting obligations and definitions that every CBCL binding inherits. Per-binding specifications (e.g. `cbcl-rs/SPEC-009` for `cbcl-erl`) declare *how* they satisfy SPEC-010 in their host ecosystem; SPEC-010 itself defines *what* compliance means.

The design is motivated by four properties:

1. **One conformance suite, many bindings.** A canonical test-vector corpus that every binding passes as a release gate. Pairwise differential testing does not scale with N bindings; a shared corpus does.
2. **One error taxonomy, many host idioms.** Categories are defined once; each binding maps them to its host's idiomatic error type (atoms, exceptions, sentinel values, Result enums).
3. **One core API, predictable lifetimes.** Opaque handle types in `cbcl-core` declare their clone semantics, Send/Sync promises, and finalisation obligations once. Bindings inherit those promises and need not re-derive thread safety per host.
4. **One protocol document, many binding READMEs.** Protocol semantics are defined in `cbcl-rs/specs/`. Binding READMEs cover host-specific ergonomics only. No binding re-explains CBCL.

---

## 2. Scope

**In scope:**

- The conformance test-vector suite: schema, location, governance, gating policy.
- The cross-language error taxonomy: canonical categories and mapping rules.
- The opaque-handle lifetime contract: clone, drop, Send/Sync, session boundaries.
- The cbcl-core threading and concurrency promise.
- SemVer policy for `cbcl-core`, `cbcl-parser`, and downstream binding crates.
- The distribution matrix: which platform × architecture × binding artefacts are produced and where they are published.
- Trust boundary baselines: minimum hardening that every binding inherits, plus per-binding addenda.
- Documentation separation: what lives in cbcl-rs SPECs vs. binding READMEs.
- The per-binding spec template and naming convention.

**Out of scope:**

- The protocol itself (parsing rules, dialect verification, structural contracts, the verification lattice) — owned by SPEC-002, SPEC-003, and the canonical Rust crates.
- Host-specific decisions for any single binding (NIF vs port for `cbcl-erl`, GIL strategy for `cbcl-py`, async runtime for `cbcl-node`) — owned by each binding's own spec.
- Specific test vectors — the corpus content is data, not specification; SPEC-010 defines its schema and gate policy only.

---

## 3. Principals and Audience

### 3.1 cbcl-rs Maintainer

Goals: ship cbcl-core changes once and have all bindings update predictably; prevent silent divergence between bindings.

### 3.2 First-Party Binding Maintainer

Owns one of `cbcl-ffi`, `cbcl-wasm`, `cbcl-erl`, etc. Goals: know exactly what the binding must satisfy at release time; not re-derive cross-binding decisions per binding.

### 3.3 Third-Party Binding Author

Wants to write a CBCL binding for a host not in the workspace (community `cbcl-py`, an OCaml binding, etc.). Goals: read SPEC-010 + an existing per-binding spec (e.g. SPEC-009) and have a complete picture of the obligations.

---

## 4. Functional Requirements

### REQ-001: Canonical Conformance Test-Vector Suite

A single conformance corpus SHALL be maintained at `cbcl-rs/test-vectors/` as the canonical test-vector suite for all bindings. The corpus SHALL be versioned via a top-level `manifest.json` declaring the corpus schema version, the count of vectors per category, and a content hash of the corpus directory. Adding, removing, or modifying vectors SHALL bump the corpus schema version per CON-002.

**Rationale:** N×N differential testing does not scale; a shared canonical corpus does. The corpus is the contract between the protocol and every binding.

**Trace:**
- TEST-001
- CON-001
- CON-002

### REQ-002: Conformance Gate on Every Binding

Every binding's CI SHALL execute the conformance corpus on every PR touching the binding or any of its Rust dependencies (`cbcl-core`, `cbcl-parser`, future protocol crates). A binding SHALL NOT be released with a corpus version older than the cbcl-rs main branch's current corpus version.

**Acceptance criteria:** Each binding's repo or workspace member ships a `conformance.toml` (or host-equivalent manifest) declaring the minimum corpus version it satisfies. CI fails the build if the declared version is below cbcl-rs main.

**Trace:**
- TEST-002

### REQ-003: Cross-Language Error Taxonomy

CBCL bindings SHALL map all error returns to one of the following canonical categories:

| Category | Source | Examples |
|---|---|---|
| `ParseError` | `cbcl-parser::parser::parse` | unclosed paren, invalid escape, unterminated string |
| `MessageError` | `cbcl-parser::parse_message` | missing recipient, malformed performative, invalid params shape |
| `DialectError` | `cbcl-parser::parse_dialect` | dialect-definition syntax failure |
| `VerificationError` | `cbcl-core::dialect::install` | R1/R2/R3 violation |
| `ContractError` | (future) `cbcl-core::protocol`, `::shape` | causal-protocol violation, shape mismatch (SPEC-002) |
| `EncodingError` | binding boundary | non-UTF-8 input, invalid host encoding |
| `ResourceError` | binding boundary | invalid handle, freed handle, allocation failure |

Each binding SHALL document its host-idiomatic mapping in its per-binding spec. Mapping is required to be 1:1 for the categories above; bindings MAY introduce host-specific sub-categories (e.g. distinguishing `RecipientFormatError` within `MessageError`) provided the canonical category is recoverable.

**Trace:**
- CON-003

### REQ-004: Opaque-Handle Lifetime Contract

For every opaque handle type exposed by `cbcl-core` (current: `Agent`; future: `MessageStore`, `DialectRegistry`, `ProtocolMonitor`), `cbcl-core` SHALL declare in its rustdoc:

1. **Clone semantics:** trivially cheap (Arc-based), expensive (deep copy), or non-cloneable.
2. **Send + Sync status:** explicitly affirmed or denied.
3. **Drop behaviour:** infallible, may block (with bound), may panic (forbidden).
4. **Session boundary:** whether the handle outlives a request, a connection, or the process.

Every binding SHALL preserve the upstream contract in its host idiom: a `Send + Sync` handle SHALL be safe to share across host threads/workers; a non-cloneable handle SHALL be exposed as a host-idiomatic move-only or single-ownership type.

**Trace:**
- TEST-003

### REQ-005: Threading and Concurrency Promise

`cbcl-core` SHALL declare which functions are safe to call concurrently from multiple threads. The default SHALL be that all pure-function exports (`parse_message`, `verify_dialect`, lattice operations) are thread-safe; exceptions are documented per-function. Bindings SHALL NOT impose stronger safety claims on consumers than `cbcl-core` provides; bindings MAY impose weaker claims (e.g. `cbcl-py` may serialise calls due to GIL) and SHALL document the weakening.

**Trace:**
- TEST-004

### REQ-006: SemVer Policy for `cbcl-core` and `cbcl-parser`

`cbcl-core` and `cbcl-parser` SHALL be published to crates.io under SemVer 2.0.0 with the following discipline:

- **Patch:** internal refactors, performance improvements, bug fixes that do not change parsed output for any input in the conformance corpus.
- **Minor:** additive changes — new performatives, new dialect rules, new opaque handle methods. Existing inputs SHALL continue to produce identical outputs.
- **Major:** breaking changes to message shape, error taxonomy, or handle semantics. Major bumps SHALL coincide with a new `cbcl-rs/specs/` SPEC document.

Binding crates SHALL declare cbcl-core/cbcl-parser version ranges per host conventions (Cargo `~`, npm caret, pip `~=`, hex `~>`).

**Migration from SHA-pinning:** First-party bindings (`cbcl-ffi`, `cbcl-wasm`, `cbcl-erl`) and downstream consumers using SHA pinning (`cbcl-lfe-router/SPEC-008/ADR-001`) SHALL migrate to SemVer ranges within one minor release of `cbcl-core` reaching v1.0.0 on crates.io.

**Trace:**
- ADR-002

### REQ-007: Per-Binding Specification Mandatory Sections

Every binding SHALL be governed by a per-binding spec at `cbcl-rs/specs/SPEC-NNN-<lang>-binding.md` containing at minimum:

1. Information table identifying SPEC-010 as the governing regime.
2. Crate location and language ecosystem details.
3. Public API surface in the host language.
4. Error mapping table (category → host idiom).
5. Lifetime contract instantiation per opaque handle.
6. Threading promises and any weakening from REQ-005.
7. Trust boundary baseline and host-specific addenda.
8. Conformance corpus version satisfied.
9. Distribution artefacts produced.
10. Open questions and host-specific tradeoffs.

`cbcl-rs/SPEC-009` (the `cbcl-erl` spec) SHALL be the canonical example.

**Trace:**
- CON-004

### REQ-008: Naming Convention

Binding crate names SHALL follow `cbcl-<short-language-id>` where the language ID is taken from the table below:

| Language | ID | Example crate |
|---|---|---|
| C ABI (no specific language) | `ffi` | `cbcl-ffi` |
| WebAssembly | `wasm` | `cbcl-wasm` |
| Erlang/BEAM | `erl` | `cbcl-erl` |
| Python | `py` | `cbcl-py` |
| Node.js / JavaScript | `node` | `cbcl-node` |
| Go | `go` | `cbcl-go` |
| Swift | `swift` | `cbcl-swift` |
| Ruby | `rb` | `cbcl-rb` |
| .NET / C# | `dotnet` | `cbcl-dotnet` |
| OCaml | `ocaml` | `cbcl-ocaml` |

Adding a language SHALL require a SPEC-010 amendment registering the new ID. The host's package-manager name MAY differ (e.g. PyPI `cbcl`, npm `@cbcl/cbcl`); the workspace crate name follows the table above.

### REQ-009: Documentation Boundaries

Protocol semantics — what CBCL is, how messages are structured, how dialects verify, how contracts enforce — SHALL be documented in `cbcl-rs/specs/` only. Binding READMEs SHALL cover only host-specific concerns (installation, API ergonomics, performance characteristics, host-idiomatic examples) and SHALL link out to cbcl-rs SPECs for protocol semantics.

A binding README MAY include a one-paragraph "What is CBCL?" preamble linking to the cbcl-rs landing spec; it SHALL NOT include a full protocol primer.

**Rationale:** With N bindings, N parallel "what is CBCL?" preambles drift. One source of truth, many entry points.

**Trace:**
- TEST-005 (audit)

### REQ-010: Distribution Manifest

Each binding's per-binding spec SHALL declare its distribution matrix: target platforms, architectures, host package managers, and signing/provenance attestations. cbcl-rs CI SHALL produce the artefacts declared and SHALL fail the release if any declared artefact is missing.

**Trace:**
- TEST-006

### REQ-011: Deprecation Policy

Categories in REQ-003, opaque handles in REQ-004, or other regime elements MAY be deprecated. Deprecation SHALL follow:

1. **Announce:** SPEC-010 amendment marking the element `deprecated` with a target removal date ≥ 6 months out.
2. **Warn:** `cbcl-core` emits a deprecation warning in builds; bindings surface it in their host idiom (Python `DeprecationWarning`, Erlang `?DEPRECATED`, etc.).
3. **Remove:** target date reached, element removed in a major version of `cbcl-core`.

---

## 5. Non-Functional Requirements

### NFR-001: Conformance Suite Stability

The conformance corpus SHALL grow monotonically: vectors MAY be added; existing vectors SHALL NOT be modified or removed within a major version of the corpus schema (CON-002). Modifying an existing vector requires a major schema bump; removing a vector requires a major schema bump and an entry in the deprecation log.

### NFR-002: Trust Boundary Baseline

Every binding SHALL satisfy:

- `#![forbid(unsafe_code)]` on the Rust side of the binding (the host glue MAY require unsafe; the binding's Rust crate SHALL NOT).
- Panic-to-error conversion at every host-callable export.
- A documented fuzzing baseline appropriate to the binding's trust posture (per-binding addendum).
- No process-fatal failure mode under any conformance corpus input.

Per-binding addenda strengthen this baseline; they cannot weaken it.

### NFR-003: Documentation Freshness

The cross-reference between a binding's declared corpus version (REQ-002) and the cbcl-rs main corpus version SHALL NOT lag by more than one minor version of the corpus schema for more than 30 days. CI in cbcl-rs SHALL surface lagging bindings on a dashboard.

---

## 6. Architecture Decisions

### ADR-001: Single Canonical Conformance Corpus

**Decision:** One corpus at `cbcl-rs/test-vectors/`, governed by SPEC-010, exercised by all bindings. Per-binding test suites exist but do not replace the canonical corpus.

**Alternatives considered:**

- **Per-binding corpora maintained independently** — silently diverge; the coupling cost reappears as drift between bindings. Rejected.
- **No formal corpus; rely on differential testing** — N×N comparison cost; works for two bindings, breaks at four.

### ADR-002: SemVer for `cbcl-core`, Version Ranges for Bindings

**Decision:** Establish SemVer 2.0.0 discipline on `cbcl-core` and `cbcl-parser` once they reach v1.0.0; bindings declare host-idiomatic version ranges. SHA pinning is permitted only for in-development work and is required to migrate to SemVer per REQ-006.

**Tradeoff accepted:** SemVer discipline imposes ongoing cost on cbcl-rs maintainers (no silent breaking changes). The cost is paid once; the value compounds with bindings.

### ADR-003: First-Party Bindings Live in the cbcl-rs Workspace

**Decision:** First-party bindings (`cbcl-ffi`, `cbcl-wasm`, `cbcl-erl`, plus future workspace-hosted bindings) live as crates inside `cbcl-rs/crates/`. Third-party bindings live in their own repos and consume `cbcl-core`/`cbcl-parser` from crates.io.

**Rationale:** Workspace bindings update in lockstep with `cbcl-core` and share CI; third-party bindings get a stable SemVer surface and freedom to release on their own cadence.

### ADR-004: Bindings Map Errors Idiomatically; the Taxonomy is Canonical

**Decision:** REQ-003 fixes the canonical category set. Each binding chooses its idiomatic representation (atoms, exception classes, sentinel errors, Result variants, error structs). Mapping is 1:1 from category to idiom.

**Tradeoff accepted:** Adding a category to the canonical set is a SPEC-010 amendment and a coordinated bump across all bindings. Acceptable because new categories are rare (one expected when SPEC-002 contract enforcement lands: `ContractError`, already pre-listed in REQ-003).

---

## 7. Contracts

### CON-001: Conformance Corpus Schema

The corpus at `cbcl-rs/test-vectors/` SHALL contain JSON files of shape:

```
{
  "id": "vec-NNNN",
  "category": "parse|message|dialect|verification|contract|encoding",
  "input": "<UTF-8 string or base64-encoded bytes>",
  "input_encoding": "utf8|base64",
  "expected": {
    "outcome": "ok|error",
    "canonical": "<string when outcome=ok>",
    "error_category": "<one of REQ-003 categories when outcome=error>",
    "error_detail": "<host-idiomatic detail substring; bindings MAY check substring presence>"
  },
  "tags": ["..."],
  "added_in_corpus_version": "X.Y.Z"
}
```

The top-level `manifest.json` declares the schema version, the count per category, and a SHA-256 of the corpus directory.

**Implements:** REQ-001.

### CON-002: Corpus Versioning

The corpus version is a SemVer triple. Patch increments cover metadata-only changes (tag refinements, error_detail tightening). Minor increments cover added vectors. Major increments cover any modification or removal of an existing vector.

**Implements:** REQ-001, NFR-001.

### CON-003: Error Mapping Table (Per-Binding)

Each per-binding spec SHALL include a table of shape:

| Canonical category (REQ-003) | Host-idiomatic representation | Notes |

The table SHALL cover all categories listed in REQ-003. A binding MAY include host-specific sub-categories as additional rows, marked as such.

**Implements:** REQ-003, REQ-007.

### CON-004: Per-Binding Spec Template

A template for `SPEC-NNN-<lang>-binding.md` SHALL be maintained at `cbcl-rs/specs/_templates/binding-spec.md`. New bindings SHALL be drafted from this template. The template tracks REQ-007's mandatory sections.

**Implements:** REQ-007.

---

## 8. Test Specifications

| ID | Description | Technique | Tier |
|---|---|---|---|
| TEST-001 | Conformance corpus schema validates against `cbcl-rs/test-vectors/manifest.json` on every PR | Schema validation | 4 |
| TEST-002 | Each first-party binding's CI runs the conformance corpus and fails on any mismatch | Build-system | 2 |
| TEST-003 | Lifetime contract: handle `Send + Sync` claims verified by Rust's type system; cross-thread tests in each binding | Static + Integration | 2 |
| TEST-004 | Threading: `cbcl-core` exports are exercised concurrently in stress tests (10⁵ concurrent calls) | Stress | 3 |
| TEST-005 | Documentation audit: binding READMEs do not contain protocol-primer paragraphs (lint check on heading taxonomy) | Lint | 4 |
| TEST-006 | Distribution manifest: every artefact declared in a binding's spec is produced in cbcl-rs CI release builds | Build-system | 3 |
| TEST-NFR-001..003 | Non-functional requirement verification per §5 | Various | 3 |

---

## 9. Open Questions

1. **Corpus governance.** Who reviews and accepts new vectors? Default: same review path as `cbcl-core` PRs. Confirm.
2. **Cross-binding parity gate.** Should the conformance gate require *all* first-party bindings to pass before any can release, or does each release independently against its declared corpus version? The former is stricter; the latter avoids cross-binding bottlenecks. Recommend independent releases with a dashboard alert (NFR-003) when bindings lag.
3. **Third-party binding registration.** How does an OCaml/Ruby/etc. binding declare itself a CBCL binding? Lightweight: a PR adding a row to a `BINDINGS.md` table in cbcl-rs. Heavyweight: a per-binding spec submitted upstream. Recommend lightweight + optional spec adoption.
4. **Corpus tagging strategy.** Vectors carry `tags` (CON-001). Define the canonical tag vocabulary (e.g. `regression`, `corner-case`, `fuzz-derived`, `spec-002`) before corpus version 1.0.0.
5. **Deprecation log location.** REQ-011 references a deprecation log; decide whether it lives in this SPEC, in a sibling `DEPRECATIONS.md`, or in CHANGELOG entries.
6. **Cbcl-core v1.0.0 timing.** REQ-006 mandates SemVer once v1.0.0 ships. Identify which open work (SPEC-002 contract surface, SPEC-005 mechanisation outputs) gates that release.
7. **Pre-built artefact signing.** REQ-010 mentions provenance attestations; choose a concrete scheme (Sigstore, SLSA level, GPG-signed releases) before the first non-Rust binding ships.

---

## 10. Status and Review

This specification is `draft`. Per USDD Constitutional Principle 12 (Adversarial Review), no enforcement of SPEC-010 against existing bindings begins until:

- Cross-model adversarial review of this document from a clean session.
- Human review by `cbcl-rs` maintainers and the maintainer of each existing first-party binding (`cbcl-ffi`, `cbcl-wasm`, `cbcl-erl`).
- Resolution of all items in §9.
- A migration plan for the existing bindings (which currently pre-date SPEC-010 and may not satisfy all sections of REQ-007 retroactively).

On promotion to `approved`, status moves to `implementing` and a SPEC-010 conformance pass is opened against each existing binding. Per-binding specs created before SPEC-010 (`cbcl-rs/SPEC-009`) SHALL be reviewed for conformance and amended where necessary.

---

**END OF SPECIFICATION**
