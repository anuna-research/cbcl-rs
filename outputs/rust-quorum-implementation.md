---
title: Rust quorum implementation evidence
mode: reference
status: implemented-library
---

# Rust quorum implementation evidence

[[SPEC-026-rust-quorum-certification]] is implemented in the consensus-free Rust
library on state-rules-spec. The selected mathematical model is
[[SPEC-025-consensus-free-refinement]]. No consensus service, shared account
reservation ledger, vote reset or timeout unlock is present.

## Implementation

`certification.rs` recognizes declaration defaults, canonical committee membership
and exact 3f+1 / 2f+1 parameters. Existing host-gate hashes and behavior are preserved.
The textual parser and JSON contract authoring share the counter recognizer.

`quorum/context.rs` authenticates and reconstructs genesis, ignores forged Instance
caches, and pins dialect/thread/root/opener/field/committee into the context ID.
`quorum/types.rs` defines versioned canonical preimages and strict typed proof
structures. `quorum/engine.rs` enforces local scaled budgets, separate operation
and effects QCs, owner-authorized fences, cancellation-backed release, complete
sealed reports, cumulative checkpoint books, successor choices and local installs.

Every state mutation appends a complete typed event before exposing signing bytes.
CAS and storage failure roll back tentative state. Recovery replays semantic guards
and verifies received proofs. Safety evidence is retained at capacity limits.
Public queries expose dependency-closed known-final evidence, not a complete latest
balance. The shared intent binder adds epoch/dependencies/nonce before external
owner signing. Existing stateless bindings fail closed for quorum rules.

## Executed validation

| Obligation | Executed evidence | Result |
|---|---|---|
| Declaration/defaults and canonicalization | `quorum_runtime.rs`, defaults, JSON/text, invalid programmatic/serde rosters | Pass |
| Coin trace and recovery | `rust-quorum-runtime-tests.log`; Treasury 1150, Alice 75, Bob 20, supply 1245 | Pass |
| Forged/context-confused proof rejection | Correctly signed wrong context/kind/payload/nonmember probes, duplicate member and corrupted signature cases | Pass |
| Local capacity and effects/fence discipline | Triangle, missing operation QC, cancellation and no early final-balance cases | Pass |
| Checkpoint/reclamation | Seals, omitted candidates, successor splits, alternate report bundles, cumulative refunds, late old effects | Pass |
| Durability and asynchronous receipt | Storage failure, competing CAS writers, recovery, corrupted logs, missing-proof fetch/retry and duplicate delivery | Pass |
| Optional ceiling | Mint capacity, headroom transfer, burn credits and issuer rejection independent of protocol role | Pass |
| Workspace compatibility | `cargo test --workspace --all-features --quiet`; `rust-quorum-workspace-tests.log` | Pass |
| no_std and serde | Core without default features plus serde; parser without default features; `rust-quorum-no-std.log` | Pass |
| Guard mutation sensitivity | `proofs/rust-quorum/check_mutations.py`; `rust-quorum-mutations.json` and per-mutant logs | Pass |
| Independent review | [[rust-quorum-security-review]], `rust-quorum-security-delta-tests.log` | No unresolved blocker reported |
| Orientation comprehension | [[rust-quorum-orientation-review]] | Pass |
| Spec controlled language | `rust-quorum-spec-lint.log` | No errors or warnings |

The mutation runner copies the implementation into a temporary isolated workspace.
Its baseline passes; weakening quorum, budget, fence, seal, successor, release,
coverage and durable-append guards causes real executed assertion failures.
Compilation errors and collection failures do not count as killed mutants.

`cargo clippy -p cbcl-core -p cbcl-parser --all-features --tests` completes with
pre-existing warnings in other code. Strict `-D warnings` is not a clean repository
gate; no new quorum/configuration/test warnings remain in the captured final log.
The vault check retains existing cross-vault dead links; it is not claimed clean.
Its specs-only scan also reports the new spec's links to retained output artifacts,
which exist outside that scan root. Requirement/contract/test anchors resolve.
The maintainer owns unifying vault roots; these output-link deferrals do not block
the Rust library checks. The retained USDD count-tool
output is not used as a four-digit artifact inventory: that tool's three-digit
identifier matcher collapses these IDs. Requirements and tests are linked directly.

## Review corrections

Independent review found programmatic keys outside parser symbol grammar and
unknown fields accepted inside nested resource allocations. Both findings produced
failing executable probes before correction, then passing independent probes and
maintained regressions. Candidate depth limits also reject before authentication;
context construction derives roles and opener caches from authenticated genesis.

The requested primary-source bibliography review is retained in
[[consensusless-literature-review]], with ar-crawl source provenance in
`outputs/consensusless-literature-evidence/crawl-manifest.json`. It identified
progress, completeness and storage boundaries without requiring a replacement of
the selected safety protocol.

## Integration boundaries

Host implementations still supply real signature verification, normal CBCL act
admission, key custody, networking and a nonforking durable journal. The test
providers are explicitly deterministic authentication and in-memory CAS storage.
They are not production cryptography or physical durability demonstrations.

Rust/model correspondence has executable traces, negative tests, guard mutations
and independent review. Rust is not extracted from Lean and has no formal
correspondence proof. Split successor or effects/fence votes can stall indefinitely;
full-balance spendability and complete-history read protocols are not provided.
Human security review remains a production deployment gate; this change adds a
library implementation and does not deploy validators.
