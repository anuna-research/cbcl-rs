<img src="https://imagedelivery.net/O-SJhBv1S1zUZFvTxrBOhQ/0ab77afb-28f0-44cd-4c8f-ddc2522ca500/smalllogo" alt="CBCL logo" width="350">

# CBCL

**A language for composing multi-agent protocols.**

CBCL (Common Business Communication Language) lets agents define, exchange, and participate in multiparty protocols at runtime, without a central coordinator or a shared global message order. This repository provides the Rust implementation and Lean proofs.

Agents teach each other new interaction vocabularies as messages. Decidable checks constrain those extensions, while signed, content-addressed evidence supports verification of public protocol behaviour and detection of equivocation.

These guarantees concern observable interactions. They do not establish that an agent’s claims are true or that compliant actions are beneficial.

## Quick start

Install Rust stable, then:

```bash
git clone https://codeberg.org/anuna/cbcl-rs
cd cbcl-rs
cargo run -p cbcl-cli -- parse '(tell agent-b "hello")'
cargo run -p cbcl-cli -- verify '(define greeting () @alice (extend greet (who) (tell who "hello")))'
```

AArch64 Unix builds also require a target C compiler/assembler (Xcode Command Line Tools on macOS). WASM builds do not use that assembly dependency.

The workspace declares Rust 1.75 as its minimum version; `rust-toolchain.toml` selects stable.

## Usage

The CLI supports parsing, dialect verification, an agent REPL, and gossip simulation:

```bash
cargo run -p cbcl-cli -- agent --id @alice
cargo run -p cbcl-cli -- --help
```

`parse`, `verify`, and `simulate` read from stdin when their input argument is omitted. To verify your own dialect file, use `cargo run -p cbcl-cli -- verify < dialect.scm`.

Custom performatives require an explicit `(lang …)` scope; installed dialects do not provide an unscoped fallback.

For bindings, see [[js/README]], [[README-WASM]], and [[crates/cbcl-erl/README]]. The JavaScript/TypeScript package includes a JSON-authored object runtime.

## Current capabilities

- **Causal contracts:** three-valued verification (`Unknown`, `Valid`, `Violation`) over mergeable message stores, with accepted-history admission and an extractable causal kernel.
- **Distributed state (R7):** optional state rules fold accepted acts into order-independent, duplicate-insensitive state; `intend` binds new acts against that accepted set. The state APIs are exported through every binding. See [[specs/SPEC-019-state-rules]].
- **Quorum counters:** escrow bounded counters and authenticated quorum-budget certification, with durable journals. See [[docs/reference/quorum-runtime]] and `dialects/example-coin.cbcl`.
- **Multiparty roles:** endpoint projection and role-local verification under R6 causal locality. See [[specs/SPEC-014-role-layer-endpoint-projection]].
- **Evidence widening:** payload-free causal evidence, bounded protocol repetition, and equivocation detection. See [[specs/SPEC-015-evidence-widening-v2]].
- **Typed content addresses:** Merkle roots over message fields, v3 root signatures, and authenticated field-openings for selective disclosure. Openings support causal safety; completion-level fan-in still requires full messages. See [[specs/SPEC-017-typed-content-addresses]] (implementation present; spec marked draft).

Field-openings preserve the need for causal evidence: a bare hash cannot establish a missing predecessor's type. See [[specs/SPEC-016-splicing-boundary]].

## Architecture

`cbcl-core` and `cbcl-parser` form the deterministic `no_std + alloc` core and forbid unsafe code. CLI, WASM, C FFI, and Erlang NIF crates provide the effectful interfaces. See [[.hence/ADR-004-purity-boundary]] and [[.hence/PURITY-MAP]].

Lean proofs live in `lean-cbcl/`, including R1–R5 properties, endpoint-projection correspondence, finite-time delivery results, and R6 DCFL preservation. Splicing and selective-disclosure results concern abstract predecessor-type evidence; concrete field-opening authentication remains a separate refinement obligation. The concrete R6 checks are tested in Rust; their semantic guarantees are mechanised in Lean. The axiom audit allowlist includes explicit content-hash and causal-accessor assumptions. For proof boundaries, see [[proofs/epp-correspondence/design]] and `scripts/check-axioms.sh`.

## API reference

Generate local Rust documentation with `cargo doc --workspace --no-deps`. Start with:

| Task | API |
|------|-----|
| Parse and validate | `cbcl_parser::run_pipeline` |
| Verify causal evidence | `cbcl_core::protocol::verify_causal` |
| Compute state and bind intent | `cbcl_core::state::fold`, `cbcl_core::intend::intend` |
| Project and verify roles | `cbcl_core::projection::{project, verify_causal_for_role}` |
| Open committed fields | `cbcl_core::typed_addr::{typed_root, open, verify_opening}` |
| Authenticate disclosed evidence | `cbcl_core::envelope::{build_opened, verify_opened}` |

## Development

```bash
cargo test --workspace
cargo bench --workspace
```

For proof changes, install Lean via elan and run `lake build` and `lake exe runLinter LeanCbcl` from `lean-cbcl/`. Run `scripts/check-axioms.sh` from the repository root. For mutation testing, see [[docs/mutation-testing]].

Contributions are welcome. Specs live under `specs/`, implementation plans under `plans/`, and bug reports under `bugs/`. Link changes to their governing requirements and verification evidence.

State conformance vectors live in `test-vectors/state/`. For client-observed certificate finality measurements, see [[tools/quorum-e2e/README]].

## Background and license

The theoretical framework appears in the [LangSec ’26 preprint](https://arxiv.org/abs/2604.14512). The original prototype is the [Scheme implementation](https://github.com/anuna-research/cbcl).

Apache-2.0; see LICENSE.

## Citation

```bibtex
@misc{cbcl2026,
  title         = {CBCL: Safe Self-Extending Agent Communication},
  author        = {O'Connor, Hugo},
  year          = {2026},
  eprint        = {2604.14512},
  archivePrefix = {arXiv},
  primaryClass  = {cs.CR},
  url           = {https://arxiv.org/abs/2604.14512},
  note          = {LangSec '26}
}
```
