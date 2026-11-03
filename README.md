<img src="https://imagedelivery.net/O-SJhBv1S1zUZFvTxrBOhQ/0ab77afb-28f0-44cd-4c8f-ddc2522ca500/smalllogo" alt="CBCL logo" width="350">

# CBCL

**A language for composing multi-agent protocols.**

CBCL (Common Business Communication Language) lets agents define, exchange, and participate in multiparty protocols at runtime, without a central coordinator or a shared global message order. This repository provides the Rust implementation and Lean proofs.

Agents teach each other new interaction vocabularies as messages. Protocols can also define shared state and bounded resources: replicas derive state from accepted acts, while escrow rights constrain concurrent spending. Signed, content-addressed evidence supports verification of public protocol behaviour and detection of equivocation.

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

For bindings, see [JavaScript/TypeScript](js/README.md), [WebAssembly](README-WASM.md), and [Erlang/BEAM](crates/cbcl-erl/README.md). The JavaScript/TypeScript package includes a JSON-authored object runtime.

## Current capabilities

- **Causal contracts:** three-valued verification (`Unknown`, `Valid`, `Violation`) over mergeable message stores, with accepted-history admission and an extractable causal kernel.
- **Multiparty roles:** endpoint projection and role-local verification under R6 causal locality.
- **Evidence widening:** payload-free causal evidence, bounded protocol repetition, and equivocation detection.
- **Typed content addresses:** Merkle roots over message fields, v3 root signatures, and authenticated field-openings for selective disclosure. Openings support causal safety; completion-level fan-in still requires full messages.

Field-openings preserve the need for causal evidence: a bare hash cannot establish a missing predecessor's type.

## State and bounded counters

An optional `(state …)` declaration gives a protocol's messages a shared state interpretation. Registers, sets, maps, and counters are derived from the accepted acts in a thread. The same accepted set produces the same state regardless of arrival order or duplicate delivery. `fold` computes that state; `intend` binds a proposed act against it. These primitives are exposed through the Rust, JavaScript/TypeScript, WASM, C, and Erlang interfaces.

The **bounded-counter primitive** adds escrow rights to an integer counter. Each account can decrement within its allocation; transferring rights changes who can spend without changing the total. An optional ceiling adds per-account headroom for increments. This supports balances, quotas, and shared resource pools without relying on a global observed balance to authorize concurrent operations.

| Operation | Effect |
|-----------|--------|
| Increment | Raises the value; requires issuer authority and, when capped, headroom |
| Decrement | Lowers the value; consumes the signer's rights |
| Transfer | Moves rights between accounts; preserves the value |

Account ownership and collective ownership support individual allocations and pools consumed by distinct authorized signers. Examples: `dialects/example-coin.cbcl`, `dialects/example-capped-coin.cbcl`, and `dialects/example-collective-tickets.cbcl`. See [bounded-counter guide](docs/concepts/bounded-counter.md) for declarations and invariants.

The default certification profile requires a durable host issuance gate. `(certification quorum-budget)` selects the Rust validator runtime with authenticated quorums, multi-parent DAG adoption, durable journals, and cancellation-backed refunds. Signing, authentication, persistence, and external-effect deduplication remain host responsibilities. Quorum balance queries report known-final local views, with completeness unknown. See [quorum runtime API](docs/reference/quorum-runtime.md).

## Architecture

`cbcl-core` and `cbcl-parser` form the deterministic `no_std + alloc` core and forbid unsafe code. CLI, WASM, C FFI, and Erlang NIF crates provide the effectful interfaces.

Lean proofs live in `lean-cbcl/`, including R1–R5 properties, endpoint-projection correspondence, finite-time delivery results, and R6 DCFL preservation. Splicing and selective-disclosure results concern abstract predecessor-type evidence; concrete field-opening authentication remains a separate refinement obligation. State-fold and binder properties are proved in `State.lean`; corpus tests check Rust/model correspondence, while universal Rust-driver refinement remains open. The concrete R6 checks are tested in Rust; their semantic guarantees are mechanised in Lean. The axiom audit allowlist includes explicit content-hash and causal-accessor assumptions. For proof boundaries, see [proof design notes](proofs/epp-correspondence/design.md) and `scripts/check-axioms.sh`.

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

For proof changes, install Lean via elan and run `lake build` and `lake exe runLinter LeanCbcl` from `lean-cbcl/`. Run `scripts/check-axioms.sh` from the repository root. For mutation testing, see [mutation-testing guide](docs/mutation-testing.md).

Contributions are welcome. Specs live under `specs/`, implementation plans under `plans/`, and bug reports under `bugs/`. Link changes to their governing requirements and verification evidence.

State conformance vectors live in `test-vectors/state/`. For client-observed certificate finality measurements, see [quorum benchmark](tools/quorum-e2e/README.md).

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
