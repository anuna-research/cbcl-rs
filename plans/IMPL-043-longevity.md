---
id: IMPL-043
title: Long-Lived CBCL Foundation
status: implemented
mode: reference
---

# Long-Lived CBCL Foundation

| Field | Value |
|---|---|
| ID | IMPL-043 |
| Title | Long-Lived CBCL Foundation |
| Governing design | [[SPEC-043-explicit-cbcl-release]] |
| Next actor | Implementer supplies executable evidence; independent reviewer challenges contracts and code |

This branch works through the longevity audit before any edition is declared final.
Existing signed canonical bytes are compatibility constraints, not a convenient
place to introduce breaking changes. User authorization covers the edition policy,
backward compatibility, bounded-extension investigation and implementing Multikey.
It does not publish a language report or grant trust to received public keys.

The executable ledger is `IMPL-043-longevity.spl`, theory `cbcl-longevity`.

| Task | Prerequisite | Acceptance | Owner |
|---|---|---|---|
| design | None | Each audit issue has a placement decision, compatibility boundary and evidence obligation | Implementer |
| multikey | Design | Strict standard vectors, bounded recognition, wrong codec rejection, identity integration and existing preimages unchanged | Implementer |
| deterministic | Design | Portable resource overflow refusals and deterministic numeric golden vectors; no silent wire migration | Implementer |
| review | Multikey and deterministic checks | Fresh review; findings repaired and relevant checks pass | Independent reviewer |

## Decisions for each audit issue

1. Crypto: retain `no_std` and W3C payload compatibility as explicitly selected by
   the maintainer on 2026-11-11. The `multi-key` container was evaluated and is not
   a drop-in replacement; see [[SPEC-043-explicit-cbcl-release#ADR-4303]].
   Reuse W3C Multikey payloads (multicodec varint plus public-key bytes,
   base58btc). Add a pure bounded codec and an explicit `KeyId::from_multikey` API adapter.
   Existing suite-explicit canonical spelling stays unchanged. Unsupported suites
   fail closed; no unimplemented post-quantum verification is advertised. Key
   rotation and evidence renewal remain host trust policy, documented separately.
2. Identity: keep self-name and named signing-form integrity hash distinct;
   reproduce their acyclic construction in regression tests. A new edition may
   not rewrite existing addresses. Old dialect signing form remains 7 on this
   foundation branch; the draft edition grammar is not silently enabled.
3. Dependencies: retain old runtime APIs for existing objects; the new edition
   requires pinned parent self-names and explicit closure validation. The edition
   runtime and signed lock grammar require the planned signing-form migration,
   rather than silently changing historical `extends` meaning in this patch.
4. Library dependence: freeze old float examples and canonical vectors; define
   float spelling independently and use an exact conversion algorithm if the
   standard formatter cannot guarantee those bytes. Keep regex dependencies pinned;
   changing compiler-state accounting requires profile-specific evidence or a new
   named resource profile. Do not claim current NFA cost is a universal algorithm.
5. Resources: keep declared limits for historical bytes; separate mathematical
   meaning, portable work, and host budgets. Fix overflow to refuse rather than
   wrap/panic. Milliseconds are an operational cap, not a portable cost proof.
6. Extension: stable native primitives and conservative embedding remain the core
   boundary. An edition-2 claim needs old positive/negative vectors plus general
   semantics evidence; macro bounds and non-redefinition alone are insufficient.
7. Archives: specify a complete offline package and trust context, built from the
   existing causal closure and checkpoint facilities. Do not mistake pending-queue
   retention for archival durability; recovery must not depend on online aliases.
8. Authority: the new language report must outrank implementations; classify
   historical drafts and grammar as informative until harmonized. Keep the report
   unratified rather than advertising a made-up `cbcl-1` support claim.

## Validation

Foundation verification (2026-11-10):

- `cargo test --locked -p cbcl-core -p cbcl-cli`: passed, including core properties,
  integration suites, CLI inspection, identity preimages and longevity fixtures.
- `cargo test --locked -p cbcl-parser --lib`: passed.
- `cargo test --locked --release -p cbcl-core --test longevity`: passed. Release
  LTO was disabled to reduce build storage; release overflow behavior remains tested.
- `cargo check --locked -p cbcl-core --no-default-features`: passed.
- `python3 scripts/check-longevity-mutations.py`: executed tests rejected key-length,
  signing-codec, depth-overflow and expansion-overflow mutants; sources restored and
  clean baseline passed.
- The first regression run failed against the Multikey stubs and the existing R2
  overflow panic; implemented behavior then passed. The exact-rational float oracle
  first exposed an equal-distance decimal tie, now specified explicitly in
  [[SPEC-043-explicit-cbcl-release#CON-4302]] without changing production bytes.
- Independent review found principal reinterpretation and insufficient identity
  goldens; both repaired. A separate Orientation-only reader correctly predicted
  compatibility and the foundation/runtime boundary. Final code review found no blockers.
- Design and plan wikilink targets/heading anchors and `git diff --check`: passed.

Builds used `CARGO_INCREMENTAL=0 CARGO_PROFILE_DEV_DEBUG=0
CARGO_PROFILE_TEST_DEBUG=0` after storage exhaustion; generated build artifacts
were cleaned with `cargo clean`. Repository-wide strict Clippy encounters existing
warnings in `r7.rs`, `contracts.rs` and `state_properties.rs`. Scoped core/CLI
checks cover changed library, binary and test targets, allowing the existing
`collapsible_match`, `single_match` and `type_complexity` warnings.

Edition installation, signed parent-lock migration, authenticated full-archive
recovery and portable-edition proofs remain explicitly deferred gates under
[[SPEC-043-explicit-cbcl-release#Deferred edition-runtime gates]]. Implemented
status here applies to the compatible foundation ledger, not to the full edition
proposal or century-scale security/retention claims.
